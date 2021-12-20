
open Ast
open Ast_typing
open X86_64

type Smap = Map.Make(String)

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let nlbl = ref 0
let new_lbl () =
  incr ntl ;
  Format.sprintf "%d" !ntl

let rec cp_expr cls var e = match e with
  | Enull -> nop, nop
  | Esimple es -> cp_expr_simple cls var es
  | Eequal (a, e) ->
			cp_acces cls var a += 
			pushq (reg rax) +++
			cp_expr cls var e +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
  | Eunop (Uneg, e) -> cp_expr cls var e += negq (reg rax)
  | Eunop (Unot ,e) -> cp_expr cls var e += notq (reg rax)
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
      cp_expr cls var e1 +=
			pushq (reg rax) +++
			cp_expr cls var e2 +=
			popq (reg rbx)
			cmpq (reg rax) (reg rbx) +=
			begin match op with
				| Beq -> sete | Bneq -> setne
				| Blt -> setl | Ble -> setle
				| Bgt -> setg | Bge -> setge
			end (reg rax)
	| Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1 , e2) ->
			cp_expr cls var e1 +=
			pushq (reg rax) +++
			cp_expr cls var e2 +=
			movq (reg rax) (reg rbx) +=
			popq (reg rax) +=
			begin match op with
				| Badd -> addq (reg rbx) (reg rax)
				| Bsub -> subq (reg rbx) (reg rax)
				| Bmul -> imulq (reg rbx) (reg rax)
				| Bdiv -> idivq (reg rbx)
				| Bmod -> idivq (reg rbx) ++ movq (reg rdx) (reg rax) end
	| Ebinop (Band | Bor as op, e1, e2) ->
			let lbl = new_lbl () in
			cp_expr cls var e1 +=
			testq (reg rax) (reg rax) +=
			(match op with | Band -> je | Bor -> jne) lbl +++
			cp_expr cls var e2 +=
			label lbl
			
and cp_expr_simple cls var es = match es with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_data_label () in
               movq (lab lbl) (reg rax), label lbl ++ string s
  | ESthis -> 
  | ESexpr e -> cp_expr cls var e
  | ESnew (nt, l)  ->
  | ESacces_meth (a, l) ->
  | ESacces_var a -> cp_acces cls var a
	
and cp_acces cls var a = match a with
	| Aident id ->
	| Achemin (es, id) ->

let rec cp_instruc cls var st = match st with
	| Inil -> nop, nop
	| Isimple es -> cp_expr_simple cls var es
	| Iequal (a, e) ->
			cp_acces cls var a += 
			pushq (reg rax) +++
			cp_expr cls var z +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
	| Idef (jt, id) ->
	| Idef_init (jt, id, e) ->
	| Iif (e, s1, s2) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			cp_expr cls var e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls var s1 +=
			jmp lbl1 +=
			lab lbl2 +++
			cp_instruc cls var s2 +=
			lab lbl1
	| Iwhile (e, s) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
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
									 
