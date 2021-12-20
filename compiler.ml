
open Ast
open Ast_typing
open X86_64

type 'a tbl = (ident, 'a) Hashtbl
type clas = { params: _ ; champs: ident list ;
							meths: meth tbl ; conss: cons tbl }
type meth = {etiq: label; args: ident list}
type cons = {etiq: label; args: ident list}
type var = Pile of int | Tas of int

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let nlbl = ref 0
let cls = Hashtbl.create 8

let new_lbl () =
  incr nlbl ;
  Format.sprintf "%d" !nlbl

let rec cp_expr vars e = match e with
  | Enull -> nop, nop
  | Esimple es -> cp_expr_simple vars es
  | Eequal (a, e) ->
			cp_acces vars a += 
			pushq (reg rax) +++
			cp_expr vars e +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
  | Eunop (Uneg, e) -> cp_expr vars e += negq (reg rax)
  | Eunop (Unot ,e) -> cp_expr vars e += notq (reg rax)
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
      cp_expr vars e1 +=
			pushq (reg rax) +++
			cp_expr vars e2 +=
			popq (reg rbx)
			cmpq (reg rax) (reg rbx) +=
			begin match op with
				| Beq -> sete | Bneq -> setne
				| Blt -> setl | Ble -> setle
				| Bgt -> setg | Bge -> setge
			end (reg rax)
	| Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1 , e2) ->
			cp_expr vars e1 +=
			pushq (reg rax) +++
			cp_expr vars e2 +=
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
			cp_expr vars e1 +=
			testq (reg rax) (reg rax) +=
			(match op with | Band -> je | Bor -> jne) lbl +++
			cp_expr vars e2 +=
			label lbl
	| Ebinop (Bcat, e1, e2) ->
			
and cp_expr_simple vars es = match es with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_data_label () in
               movq (lab lbl) (reg rax), label lbl ++ string s
  | ESthis -> 
  | ESexpr e -> cp_expr vars e
  | ESnew (nt, l)  ->
  | ESacces_meth (a, l) ->
  | ESacces_var a -> cp_acces vars a
	
and cp_acces vars a = match a with
	| Aident id -> match Hashtbl.find vars id with
									| Pile n -> movq (ind ~ofs:n (reg rbp)) (reg rax)
									| Tas s -> movq (ilab s) (reg rax)
	| Achemin (es, id) ->

let rec cp_instruc var st = match st with
	| Inil -> nop, nop
	| Isimple es -> cp_expr_simple vars es
	| Iequal (a, e) ->
			cp_acces vars a += 
			pushq (reg rax) +++
			cp_expr vars z +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
	| Idef (jt, id) ->
	| Idef_init (jt, id, e) ->
	| Iif (e, s1, s2) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			cp_expr vars e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc vars s1 +=
			jmp lbl1 +=
			lab lbl2 +++
			cp_instruc vars s2 +=
			lab lbl1
	| Iwhile (e, s) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			(lab lbl1, nop) +++
			cp_expr vars e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc vars s +=
			jmp lbl1 +=
			lab lbl2
	| Ibloc l -> let loc = Hashtbl.copy vars in
							 List.fold_left (+++) (nop, nop)
							 (List.map (cp_instruc loc) l)
	| Ireturn None -> (nop, nop) += leave += ret
	| Ireturn (Some e) -> cp_expr cls vars e += leave += ret	

let cp_classe c =
	let ci = match c.extd with
		| None -> {	params = [] ; champs = [] ;
								meths = Hashtbl.create 8 ;
								conss = Hashtbl.create 8 }
		| Some {desc = Ntype (id ,l)} -> Hashtbl.find cls nt.id
		
	in let rec aux d = match d with
		| [{desc = Dchamp h}]::q -> 
		| [{desc = Dconstr h}]::q -> let hi = { lbl = new_label () ; args = h.params } in
																 Hashtbl.replace info.conss h.nom hi ;
																 aux d += label hi.lbl +++
																 cp_instr (Hashtbl.create 8) (Ibloc hi.body)
		| [{desc = Dmeth h}]::q -> 	let hi = { etiq = new_label () ; args = h.params } in
																Hashtbl.replace info.meths h.nom hi ;
																aux d += label hi.lbl +++
																cp_instr (Hashtbl.create 8) (Ibloc hi.body)
		| [] -> (nop, nop)

let prod prog =
	let main = ref [] in
	let rec cp_fichier f = match f with
		| [{desc = Class c}]::q -> cp_classe c +++ cp_fichier q
		| [{desc = Interface _}]::q -> cp_fichier q
		| [{desc = Main l}]::q -> main:=l ; cp_fichier q
		| _ -> (nop, nop)
	in let tc, dc = cp_fichier prog in
	let tm, dm = cp_instr (Hashtbl.create 8) (Ibloc !main) in
	{ text =
			globl "main" ++
			label "main" ++
			tm ++
			movq (imm 0) (reg rax) ++
			ret ++
			tc ;
		data = dc ++ dm }
