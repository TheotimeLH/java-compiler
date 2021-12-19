
open Ast
open Ast_typing
open X86_64

let ntl = ref 0
let new_text_label () =
  incr ntl ;
  Format.sprintf "T%d" !ntl
  
let ndl = ref 0
let new_data_label () =
  incr ndl ;
  Format.sprintf "D%d" !ntl s

let rec cp_expr e = match e with
  | Enull ->
  | Esimple es -> cp_expr_simple es
  | Eequal (a, e) ->                     
  | Eunop (Uneg, e) -> let t, d = cp_expr e in
                       t ++ negq (reg rax), d 
  | Eunop (Unot ,e) -> let t, d = cp_expr e in
                       t ++ notq (reg rax), d
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
      let t1, d1 = cp_expr e1 in
			let t2, d2 = cp_expr e2 in
			t1 ++ movq (reg rax) (red rdi) ++
			t2 ++ cmpq (reg rax) (reg rdi) ++
			begin match op with
				| Beq -> sete | Bneq -> setne
				| Blt -> setl | Ble -> setle
				| Bgt -> setg | Bge -> setge
			end (reg rax), d1 ++ d2
	| Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1 , e2) ->
			let t1, d1 = cp_expr e1 in
			let t2, d2 = cp_expr e2 in
			t1 ++ pushq (reg rax) ++
			t2 ++ movq (reg rax) (reg rdi) ++ popq (reg rax) ++
			begin match op with
				| Badd -> addq (reg rdi) (reg rax)
				| Bsub -> subq (reg rdi) (reg rax)
				| Bmul -> imulq (reg rdi) (reg rax)
				| Bdiv -> idivq (reg rdi)
				| Bmod -> idivq (reg rdi) ++ movq (reg rdx) (reg rax)
			end, d1 ++ d2
	| Ebinop (Band | Bor as op, e1, e2) ->
			let t1, d1 = cp_expr e1 in
			let t2, d2 = cp_expr e2 in
			let lbl = new_text_label () in
			t1 ++ testq (reg rax) (reg rax) ++
			(match op with | Band -> je | Bor -> jne) lbl ++
			t2 ++ label lbl, d1 ++ d2
and cp_expr_simple es = match es with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_data_label () in
               movq (lab lbl) (reg rax), label_lab ++ string s
  | ESthis ->
  | ESexpr e -> cp_expr e
  | ESnew (nt, l)  ->
  | ESacces_meth (a, l) ->
  | ESacces_var a ->
and cp_acces a = match a with
	| Aident id ->
	| Achemin (es, id) ->

let rec cp_instruction st = match st with
	| Inil -> nop, nop
	| Isimple es -> cp_expr_simple es
	| Iequal (a, e) ->
	| Idef (jt, id) ->
	| Idef_init (jt, id, e) ->
	| Iif (e, s1, s2) ->
			let t0, d0 = cp_expr e in
			let t1, d1 = cp_instruction s1 in
			let t2, d2 = cp_instruction s2 in
			let lbl1 = new_label_text () in
			let lbl2 = new_label_text () in
			t0 ++ testq (reg rax) (reg rax) ++ je lbl2 ++
			t1 ++ jmp lbl1 ++ lab lbl2 ++
			t2 ++ lab lbl1,	d0 ++ d1 ++ d2
	| Iwhile (e, s) ->
			let te, de = cp_expr e in
			let ts, ds = cp_instruction s in
			let lbl1 = new_label_text () in
			let lbl2 = new_label_text () in
			lab lbl1 ++ te ++ testq (reg rax) (reg rax) ++
			je lbl2 ++ ts ++ jmp lbl1 ++ lab lbl2, de ++ ds
	| Ibloc l -> let aux (t, d) s =
								 let ti, di = cp_instruction s in
								 t ++ ti, d ++ di
							 in List.fold aux (nop, nop) l
	| Ireturn opt ->
