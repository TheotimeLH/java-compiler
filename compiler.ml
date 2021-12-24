
open Ast
open X86_64

type 'a tbl = (string, 'a) Hashtbl
type champ = {tp: jtype; ofs: int }
type meth = {tp: jtype; lbl: label}
type cls = {params: 'a tbl;
						champs: champ tbl;
						mutable cons: label option;
						meths: meth tbl}
type adresse = Pile of int | Tas of int*int | Lbl of label
type var = {tp: jtype; adrs: adressse} tbl

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let nlbl = ref 0
let jnt nt = Jntype { desc = nt ;
		loc = Lexing.dummy_pos, Lexing.dummy_pos }

let new_lbl () =
  incr nlbl ;
  Format.sprintf "%d" !nlbl

let rec tp_expr cls var e = match e with
	| Enull -> Jtypenull
	| Esimple es | Eequal (_, es) -> tp_expr_simple lls var es
	| Ebinop (Badd,e1,e2) ->
			if tp_expr cls var e1 = Jint && tp_expr cls var e 2 = Jint
			then Jint else jnt ( Ntype ("String", []) )
	| Ebinop(Bsub | Bmul | Bdiv | Bmod,_,_)
	| Eunop (Uneg, _) -> Jint
	| Eunop _ | Ebinop _ -> Jboolean
and tp_expr_simple cls var es = match es with
	| ESint -> Jint
	| ESboll -> Jboolean
	| ESstr -> jstring
	| ESthis -> (Hasstbl.find var "this").tp
	| ESexpr e -> tp_expr cls var e
	| ESnew (nt, _) -> jnt nt
	| ESacces_meth (a, _) -> tp_acces cls var a
	| ESacces_var a ->  tp_acces cls var a
and tp_acces cls var a = match a with
	| Aident id -> (Hashtbl.find var id).tp
	| Achemin (es, id) ->
			let c = match tp_expr_simple cls var es with
				| Jntype { desc = Ntype (nom, _) } -> Hashtbl.find cls nom
				| _ -> exit 1
			in try (Hashtbl.find c.champs id).tp
			with Not_found -> (Hashtbl.find c.meths id).tp

let rec cp_expr cls vars e = match e with
  | Enull -> nop, nop
  | Esimple es -> cp_expr_simple cls var es
  | Eequal (a, e) ->
			cp_acces cls var a += 
			pushq (reg rax) +++
			cp_expr cls var e +=
			popq (reg rdx) +=
			movq (reg rax) (ind (reg rdx))
  | Eunop (Uneg, e) -> cp_expr cls var e += negq (reg rax)
  | Eunop (Unot ,e) -> cp_expr cls var e += notq (reg rax)
	| Ebinop (Badd, e1, e2) when tp_expr cls var e1 <> Jint
														|| tp_expr cls var e2 <> Jint ->
		(* A COMPLETER  *)
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
      cp_expr cls var e1 +=
			pushq (reg rax) +++
			cp_expr cls var e2 +=
			popq (reg rdx)
			cmpq (reg rax) (reg rdx) +=
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
  | ESstr s -> let lbl = new_lbl () in
               movq (label lbl) (reg rax), lbl lbl ++ string s
  | ESthis -> movq (ind (~ofs:16) (reg rbp)) (reg rax)
  | ESexpr e -> cp_expr cls var e
  | ESnew (Ntype (id, _), l)  ->
			(* A COMPLETER *)
  | ESacces_meth (a, l) ->
			(* A COMPlETER *)
  | ESacces_var a -> cp_acces cls var a
	
and cp_acces cls var a = match a with
	| Aident id ->
			(* A COMPLETER *)
	| Achemin (es, id) ->
			match tp_expr_simple cls var es with
				| Jntype { desc = Ntype (nom, _) } ->
						let c = Hashtbl.find cls nom in
						try let m = Hashtbl.find c.meths id in
								cp_expr_simple cls var es +=
								pushq (reg rax) +=
								call m.lbl +=
								popq (reg rcx)
						with Not_found ->
								let ch = Hashtbl.find c.champs id in
								cp_expr_simple cls var es +=
								movq (reg rax) (reg rbx) +=
								movq (ind (~ods:ch.ofs) (reg rbx)) (reg rax)
				| _ -> exit 1 in
			

let rec cp_instruc cls var st = match st with
	| Inil -> nop, nop
	| Isimple es -> cp_expr_simple cls var es
	| Iequal (a, e) ->
			cp_acces cls var a += 
			pushq (reg rax) +++
			cp_expr cls var e +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
	| Idef (jt, id) ->
		(* A COMPLETER *)
	| Idef_init (jt, id, e) ->
		(* A COMPLETER *)
	| Iif (e, s1, s2) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			cp_expr cls var e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls var s1 +=
			jmp lbl1 +=
			label lbl2 +++
			cp_instruc cls var s2 +=
			label lbl1
	| Iwhile (e, s) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			(label lbl1, nop) +++
			cp_expr cls var e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls var s +=
			jmp lbl1 +=
			label lbl2
	| Ibloc l -> let loc = Hashtbl.copy var in
							 List.fold_left (+++) (nop, nop)
							 (List.map (cp_instruc cls loc) l)
	| Ireturn None -> leave ++ ret, nop
	| Ireturn (Some e) -> cp_expr cls var e += leave += ret	

let cp_classe cls c =
	let cinfo = Hashtbl.find cls c in
	let rec aux d = match d with
		| [{desc = Dconstr cs}]::q ->
				let var = Hashtbl.create 8 and k = ref 8 in
				(* A COMPLETER *)
		| [{desc = Dmeth m}]::q ->
				let var = Hashtbl.create 8 and k = ref 16 in
				(* A COMPLETER *)
		| _::q -> aux q
		| [] -> nop, nop
	in aux c.body
	
let cinit cls c =
	let cinfo = match c.extd with
		| None -> { params = Hashtbl.create 8 ;
								champs = Hashtbl.create 8 ;
								meths = Hashtbl.create 8 ; cons = None }
		| Some { desc = Ntype (id, _) } -> Hashtbl.find cls id
	in let k = ref 0 in
	let rec aux d = match d with
		| [{desc = Dchamp (jt, id) }]::q ->
				Hashtbl.replace cinfo.champs id
				{ tp = jt.desc ; ofs = !k*8 } ;
				incr k ; aux q
		| [{desc = Dconstr _}]::q ->
				cinfo.cons = Some (new_lbl ()) ; aux q
		| [{desc = Dmeth {desc = m} }]::q ->
				let jtp = match m.info.desc.typ with
					| None -> Jtypenull | Some jt -> jt in
				Hashtbl.replace cinfo.meths m.info.desc.nom
				{ tp = jtp ; lbl = new_lbl () } ; aux q
		| [] -> ()
	in aux c.body ;
	Hashtbl.replace cls c.nom cinfo

let cp_fichier prog =
	let cls = Hashtbl.create 8 in
	let init f = match f with
		| [{desc = Class c}]::q -> cinit cls c ; init q
		| _::q -> init q
		| _ -> ()
	in init prog ;
	let rec code f = match f with
		| [{desc = Class c}]::q -> aux q +++ cp_classe cls c
		| [{desc = Main l}]::q ->
				cp_instruc cls (Hashtbl.create 8) (Ibloc l) +=
				movq (imm 0) (reg rax) += ret +++ aux q
		| _::q -> aux q 
		| [] -> nop, nop
	in let t, d = aux prog in
	{ text =
			globl "Main" ++
			label "Main" ++
			t ;
		data = d }
