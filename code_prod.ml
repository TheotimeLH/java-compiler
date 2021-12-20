
open Ast
open Ast_typing
open X86_64

let (+=) (t1, d) t2 = t1 ++ t2, d
let (=+) d1 (t, d2) = t, d1 ++ d2
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let nlbl = ref 0
let cls = Hashtbl.create 8

let new_lbl () =
  incr nlbl ;
  Format.sprintf "%d" !nlbl

let rec cp_expr var e = match e with
  | Enull -> nop, nop
  | Esimple es -> cp_expr_simple var es
  | Eequal (a, e) ->
			cp_acces var a += 
			pushq (reg rax) +++
			cp_expr var e +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
  | Eunop (Uneg, e) -> cp_expr var e += negq (reg rax)
  | Eunop (Unot ,e) -> cp_expr var e += notq (reg rax)
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
      cp_expr var e1 +=
			pushq (reg rax) +++
			cp_expr var e2 +=
			popq (reg rbx)
			cmpq (reg rax) (reg rbx) +=
			begin match op with
				| Beq -> sete | Bneq -> setne
				| Blt -> setl | Ble -> setle
				| Bgt -> setg | Bge -> setge
			end (reg rax)
	| Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1 , e2) ->
			cp_expr var e1 +=
			pushq (reg rax) +++
			cp_expr var e2 +=
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
			cp_expr var e1 +=
			testq (reg rax) (reg rax) +=
			(match op with | Band -> je | Bor -> jne) lbl +++
			cp_expr var e2 +=
			label lbl
			
and cp_expr_simple var es = match es with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_data_label () in
               movq (lab lbl) (reg rax), label lbl ++ string s
  | ESthis -> 
  | ESexpr e -> cp_expr var e
  | ESnew (nt, l)  ->
  | ESacces_meth (a, l) ->
  | ESacces_var a -> cp_acces var a
	
and cp_acces var a = match a with
	| Aident id ->
	| Achemin (es, id) ->

let rec cp_instruc var st = match st with
	| Inil -> nop, nop
	| Isimple es -> cp_expr_simple var es
	| Iequal (a, e) ->
			cp_acces var a += 
			pushq (reg rax) +++
			cp_expr var z +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
	| Idef (jt, id) ->
	| Idef_init (jt, id, e) ->
	| Iif (e, s1, s2) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			cp_expr var e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc var s1 +=
			jmp lbl1 +=
			lab lbl2 +++
			cp_instruc var s2 +=
			lab lbl1
	| Iwhile (e, s) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			(lab lbl1, nop) +++
			cp_expr var e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc var s +=
			jmp lbl1 +=
			lab lbl2
	| Ibloc l -> let loc = Hashtbl.copy var in
							 List.fold_left (+++) (nop, nop)
							 (List.map (cp_instruc loc) l)
	| Ireturn None -> (nop, nop) += leave += ret
	| Ireturn (Some e) -> cp_expr cls var e += leave += ret

let cp_classe c =

let rec cp_fichier f = match f with
		| [{desc = Class c}]::q -> cp_classe c =+ cp_fichier q
		| [{desc = Interface _}]::q -> cp_fichier q
		| [{desc = Main l}]::q -> let var = Hashtbl.create 8 in
															cp_instruc var (Ibloc l) +++ cp_fichier q
		| _ -> (nop, nop)

let prod prog =
	let t, d = cp_fichier prog in
	{ text = globl "main" ++ t ;
		data = d }
