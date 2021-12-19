
open Ast
open Ast_typing
open X86_64

type Smap = Map.Make(String)

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let ntl = ref 0
let new_text_label () =
  incr ntl ;
  Format.sprintf "T%d" !ntl
  
let ndl = ref 0
let new_data_label () =
  incr ndl ;
  Format.sprintf "D%d" !ntl s

let rec cp_expr cls var e = match e with
  | Enull -> nop, nop
  | Esimple es -> cp_expr_simple cls var es
  | Eequal (a, e) ->
			cp_acces cls var a += 
			movq (reg rax) (reg rbx) +++
			cp_expr cls var +=
			movq (reg rax) (ind (reg rbx))
  | Eunop (Uneg, e) -> cp_expr cls var e += negq (reg rax)
  | Eunop (Unot ,e) -> cp_expr cls var e += notq (reg rax)
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
      cp_expr cls var e1 +=
			movq (reg rax) (red rdi) +++
			cp_expr cls var e2 +=
			cmpq (reg rax) (reg rdi) +=
			begin match op with
				| Beq -> sete | Bneq -> setne
				| Blt -> setl | Ble -> setle
				| Bgt -> setg | Bge -> setge
			end (reg rax)
	| Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1 , e2) ->
			cp_expr cls var e1 +=
			pushq (reg rax) +++
			cp_expr cls var e2 +=
			movq (reg rax) (reg rdi) +=
			popq (reg rax) +=
			begin match op with
				| Badd -> addq (reg rdi) (reg rax)
				| Bsub -> subq (reg rdi) (reg rax)
				| Bmul -> imulq (reg rdi) (reg rax)
				| Bdiv -> idivq (reg rdi)
				| Bmod -> idivq (reg rdi) ++ movq (reg rdx) (reg rax) end
	| Ebinop (Band | Bor as op, e1, e2) ->
			let lbl = new_text_label () in
			cp_expr cls var e1 +=
			testq (reg rax) (reg rax) +=
			(match op with | Band -> je | Bor -> jne) lbl +++
			cp_expr cls var e2 +=
			label lbl
			
and cp_expr_simple cls var es = match es with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_data_label () in
               movq (lab lbl) (reg rax), label_lab ++ string s
  | ESthis ->
  | ESexpr e -> cp_expr cls var e
  | ESnew (nt, l)  ->
  | ESacces_meth (a, l) ->
  | ESacces_var a -> cp_acces cls var a
	
and cp_acces cls var a = match a with
	| Aident id -> movq (imm (Smap.find id var)) (reg rax)
	| Achemin (es, id) ->

let rec cp_instruc cls var st = match st with
	| Inil -> nop, nop
	| Isimple es -> cp_expr_simple cls var es
	| Iequal (a, e) ->
			cp_acces cls var a += 
			movq (reg rax) (reg rbx) +++
			cp_expr cls var +=
			movq (reg rax) (ind (reg rbx))
	| Idef (jt, id) ->
	| Idef_init (jt, id, e) ->
	| Iif (e, s1, s2) ->
			let lbl1 = new_label_text () in
			let lbl2 = new_label_text () in
			cp_expr cls var e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls var s1 +=
			jmp lbl1 +=
			lab lbl2 +++
			cp_instruc cls var s2 +=
			lab lbl1
	| Iwhile (e, s) ->
			let lbl1 = new_label_text () in
			let lbl2 = new_label_text () in
			(lab lbl1, nop) +++
			cp_expr cls var e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls var s +=
			jmp lbl1 +=
			lab lbl2
	| Ibloc l -> let aux cd s = cd +++ cp_instruc cls var s
							 in List.fold_left aux (nop, nop) l
	| Ireturn None -> (nop, nop) += leave += ret
	| Ireturn (Some e) -> cp_expr cls var e += leave += ret
									 
