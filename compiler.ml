
open Ast
open X86_64

exception System
exception System_out

type 'a tbl = (ident, 'a) Hashtbl.t
type var = {tp: jtype; ofs: int}
type champ = {tp: jtype; ofs: int}
type meth = {tp: jtype; lbl: label}
type cls = {mutable cons: label;
						champs: champ tbl;
						meths: meth tbl}

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let p = ref 0
let var = Hashtbl.create 8
let size c = 8*(Hashtbl.length c.champs)+8

let dp = Lexing.dummy_pos
let jnt nt = Jntype { desc = nt ; loc = dp, dp }
let this id = { loc = dp, dp ; desc = Achemin
		({ desc =  ESthis ; loc = dp, dp }, id)  }

let nlbl = ref 0
let new_lbl () =
  incr nlbl ;
  Format.sprintf "%d" !nlbl

let rec tp_expr cls e = match e.desc with
	| Enull -> Jtypenull
	| Esimple es -> tp_expr_simple cls es
	| Eequal (_, e0) -> tp_expr cls e0
	| Ebinop (e1, Badd, e2) ->
			if tp_expr cls e1 = Jint && tp_expr cls e2 = Jint
			then Jint else jnt ( Ntype ("String", []) )
	| Ebinop (_, (Bsub | Bmul | Bdiv | Bmod), _)
	| Eunop (Uneg, _) -> Jint
	| Eunop _ | Ebinop _ -> Jboolean
and tp_expr_simple cls es = match es.desc with
	| ESint _ -> Jint
	| ESbool _ -> Jboolean
	| ESstr _ -> jnt ( Ntype ("String", []) )
	| ESthis -> (Hashtbl.find var "this").tp
	| ESexpr e -> tp_expr cls e
	| ESnew (nt, _) -> jnt nt.desc
	| ESacces_meth (a, _) -> tp_acces cls a
	| ESacces_var a ->  tp_acces cls a
and tp_acces cls a = match a.desc with
	| Aident id -> 
			if id = "System" then raise System ;
			begin try (Hashtbl.find var id).tp
			with Not_found -> tp_acces cls (this id) end
	| Achemin (es, id) ->
			match tp_expr_simple cls es with
				| Jntype { desc = Ntype (nom, _) } ->
						let c = Hashtbl.find cls nom in
						begin try (Hashtbl.find c.champs id).tp
						with Not_found -> (Hashtbl.find c.meths id).tp end
				| exception System -> raise System_out
				| exception System_out -> Jtypenull
				| _ -> exit 1

let rec cp_expr cls e = match e.desc with
  | Enull -> movq (imm 0) (reg rax), nop
  | Esimple es -> cp_expr_simple cls es
  | Eequal (a, e0) ->
			cp_acces cls a += 
			pushq (reg rax) +++
			cp_expr cls e0 +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
  | Eunop (Uneg, e0) -> cp_expr cls e0 += negq (reg rax)
  | Eunop (Unot ,e0) -> cp_expr cls e0 += notq (reg rax)
	| Ebinop (e1, Badd, e2) when tp_expr cls e1 <> Jint
														|| tp_expr cls e2 <> Jint ->
			cp_expr cls e1 +=
			(	if tp_expr cls e1 <> Jint then nop
				else
					movq (reg rax) (reg rdi) ++
					call "0convert" ) +=
			movq (reg rax) (reg rsi) ++
			cp_expr cls e2 +=
			movq (reg rax) (reg rdi) +=
			( if tp_expr cls e2 <> Jint then nop
				else
					call "0convert" ++
					movq (reg rax) (reg rdi) ) +=
			call "0concat"
  | Ebinop (e1, (Beq | Bneq | Blt | Ble | Bgt | Bge as op), e2) ->  
      cp_expr cls e1 +=
			pushq (reg rax) +++
			cp_expr cls e2 +=
			popq (reg rdx)
			cmpq (reg rax) (reg rdx) +=
			begin match op with
				| Beq -> sete | Bneq -> setne
				| Blt -> setl | Ble -> setle
				| Bgt -> setg | Bge -> setge
			end (reg rax)
	| Ebinop (e1, (Badd | Bsub | Bmul | Bdiv | Bmod as op), e2) ->
			cp_expr cls e1 +=
			pushq (reg rax) +++
			cp_expr cls e2 +=
			movq (reg rax) (reg rbx) +=
			popq (reg rax) +=
			begin match op with
				| Badd -> addq (reg rbx) (reg rax)
				| Bsub -> subq (reg rbx) (reg rax)
				| Bmul -> imulq (reg rbx) (reg rax)
				| Bdiv -> idivq (reg rbx)
				| Bmod -> idivq (reg rbx) ++ movq (reg rdx) (reg rax) end
	| Ebinop (e1, (Band | Bor as op), e2) ->
			let lbl = new_lbl () in
			cp_expr cls e1 +=
			testq (reg rax) (reg rax) +=
			(match op with | Band -> je | Bor -> jne) lbl +++
			cp_expr cls e2 +=
			label lbl
			
and cp_expr_simple cls es = match es.desc with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_lbl () ^ "string" in
               movq (imm lbl) (reg rax), label lbl ++ string s
  | ESthis -> movq (ind ~ofs:16 rbp) (reg rax), nop
  | ESexpr e -> cp_expr cls e
  | ESnew (Ntype (id, _), l)  ->
			let c = Hashtbl.find cls id in
			let aux cd e =
				cp_expr cls e +=
				pushq (reg rax) +++
				cd += popq (reg rcx) 
			in List.fold_left aux (
			movq (imm (size c)) (reg rdi) ++
			call "malloc" ++
			pushq (reg rax) ++
			call c.cons ++
			popq (reg rax), nop) l			
  | ESacces_meth (a, l) ->
			let aux cd e =
				cp_expr cls e +=
				pushq (reg rax) +++
				cd += popq (reg rcx) 
			in List.fold_left aux (cp_acces cls a) l
  | ESacces_var a ->
			cp_acces cls a +=
			movq (reg rax) (reg rbx) +=
			movq (ind (reg rbx)) (reg rax)

and cp_acces cls a = match a.desc with
	| Aident id ->
			if id == "System" then raise System ;
			begin try let n = (Hashtbl.find var id).adrs in
			leaq (ind ~ofs:n rbp) (reg rax), nop
			with Not_found -> cp_acces cls (this id) end
	| Achemin (es, id) ->
			match tp_expr_simple cls es with
				| Jntype { desc = Ntype (nom, _) } ->
						let c = Hashtbl.find cls nom in
						begin try let m = Hashtbl.find c.meths id in
								cp_expr_simple cls es +=
								pushq (reg rax) +=
								movq (ind (reg rax)) (reg rbx) +=
								call m.lbl +=
								popq (reg rcx)
						with Not_found ->
								let ch = Hashtbl.find c.champs id in
								cp_expr_simple cls es +=
								movq (reg rax) (reg rbx) +=
								leaq (ind ~ods:ch.ofs rbx) (reg rax) end
				| exception System -> raise System_out
				| exception System_out ->
						movq (ind (reg rsp)) (reg rdi) ++
						movq (imm O) (reg rax)
						call "printf", nop
				| _ -> exit 1			

let rec cp_instruc cls st = match st.desc with
	| Inil -> nop, nop
	| Isimple es -> cp_expr_simple cls es
	| Iequal (a, e) ->
			cp_acces cls a += 
			pushq (reg rax) +++
			cp_expr cls e +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
	| Idef (jt, id) -> decr p ;
			Hashtbl.replace var id { tp = jt ; ofs = !p*8 } ;
			pushq $0, nop
	| Idef_init (jt, id, e) -> decr p ;
			Hashtbl.replace var id { tp = jt ; ofs = !p*8 } ;
			cp_expr cls e += pushq (reg rax)
	| Iif (e, s1, s2) ->
			let n = new_lbl () in
			let lbl1 = n^"if" in
			let lbl2 = n^"else" in 
			cp_expr cls e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls s1 +=
			jmp lbl1 +=
			label lbl2 +++
			cp_instruc cls s2 +=
			label lbl1
	| Iwhile (e, s) ->
			let n = new_lbl () in
			let lbl1 = n^"deb" in
			let lbl2 = n^"fin" in
			(label lbl1, nop) +++
			cp_expr cls e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls s +=
			jmp lbl1 +=
			label lbl2
	| Ibloc l -> List.fold_left (+++) (nop, nop)
							 (List.map (cp_instruc cls) l)
	| Ireturn None -> leave ++ ret, nop
	| Ireturn (Some e) -> cp_expr cls e += leave += ret	

let cp_classe cls c =
	let cinfo = Hashtbl.find cls c.nom in
	let rec aux d = match d with
		| [{desc = Dconstr cs}]::q ->
				Hashtbl.clear var ;
				let k = ref 2 in
				let aux { desc = prm } = incr k ;
					Hashtbl.replace var prm.nom
					{ tp = prm.typ.desc ; ofs = !k*8}
				in List.iter aux cs.params ;
				aux q += label cinfo.cons +++
				cp_instruc cls (Ibloc cs.body) +=
				leave += ret
		| [{desc = Dmeth m}]::q ->
				Hashtbl.clear var ;
				let k = ref 2 in
				let aux { desc = prm } = incr k ;
					Hashtbl.replace var prm.nom
					{ tp = prm.typ.desc ; ofs = !k*8}
				in List.iter aux m.info.desc.params ;
				let mi = Hashtbl.find cinfo.meths m.info.desc.nom in
				aux q += label mi.lbl +++
				cp_instruc cls (Ibloc m.body) +=
				leave += ret
		| _::q -> aux q
		| [] -> nop
	in aux c.body
	
let cinit cls c =
	let cinfo = match c.extd with
		| None -> { cons = "0new" ;
								champs = Hashtbl.create 8 ;
								meths = Hashtbl.create 8 }
		| Some { desc = Ntype (id, _) } ->
				let ext = Hashtbl.find cls id in
				{ cons = "0new" ;
					champs = Hashtbl.copy ext.champs ;
					meths = Hashtbl.create ext.meths }
	in let k = ref 0 and n = new_lbl () in
	let rec aux d = match d with
		| [{desc = Dchamp (jt, id) }]::q ->
				Hashtbl.replace cinfo.champs id
				{ tp = jt.desc ; ofs = !k*8 } ;
				incr k ; aux q
		| [{desc = Dmeth {desc = m} }]::q ->
				let jtp = match m.info.desc.typ with
					| None -> Jtypenull | Some jt -> jt in
				Hashtbl.replace cinfo.meths m.info.desc.nom
				{ tp = jtp ; lbl = n^c.nom^"_"^m.info.desc.nom } ;
				incr b ; aux q
		| _::q -> cinfo.cons = n^c.nom^"_new" ; aux q
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
				cp_instruc cls (Ibloc l) +=
				movq (imm 0) (reg rax) +=
				ret +++ aux q
		| _::q -> aux q 
		| [] -> nop, nop
	in let t, d = aux prog in
	{ text =
			globl "Main" ++
			label "Main" ++
			t ++ 
			label "0new" ++
			leave ++ ret ++
			label "0convert" ++
			(* A COMPLETER *)
			label "0concat" ++
			(* A COMPLETER *)
			label "0equals" 
			(* A COMPLETER *) ;
		data = d }
