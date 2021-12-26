
open Ast
open X86_64

type 'a tbl = (ident, 'a) Hashtbl
type obj = {tp: jtype; ofs: int}
type cls = {params: 'a tbl;
						champs: obj tbl;
						meths: obj tbl}

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let p = ref 0
let var = Hashtbl.create 8

let size c = 8*(Hashtbl.length c.champs)+8
let jnt nt = Jntype { desc = nt ;
		loc = Lexing.dummy_pos, Lexing.dummy_pos }

let nlbl = ref 0
let new_lbl () =
  incr nlbl ;
  Format.sprintf "%d" !nlbl

let rec tp_expr cls e = match e with
	| Enull -> Jtypenull
	| Esimple es | Eequal (_, es) -> tp_expr_simple cls es
	| Ebinop (Badd,e1,e2) ->
			if tp_expr cls e1 = Jint && tp_expr cls e 2 = Jint
			then Jint else jnt ( Ntype ("String", []) )
	| Ebinop(Bsub | Bmul | Bdiv | Bmod,_,_)
	| Eunop (Uneg, _) -> Jint
	| Eunop _ | Ebinop _ -> Jboolean
and tp_expr_simple cls es = match es with
	| ESint -> Jint
	| ESboll -> Jboolean
	| ESstr -> jnt ( Ntype ("String", []) )
	| ESthis -> (Hasstbl.find var "this").tp
	| ESexpr e -> tp_expr cls e
	| ESnew (nt, _) -> jnt nt
	| ESacces_meth (a, _) -> tp_acces cls a
	| ESacces_var a ->  tp_acces cls a
and tp_acces cls a = match a with
	| Aident id -> (Hashtbl.find var id).tp
	| Achemin (es, id) ->
			let c = match tp_expr_simple cls es with
				| Jntype { desc = Ntype (nom, _) } -> Hashtbl.find cls nom
				| _ -> exit 1
			in try (Hashtbl.find c.champs id).tp
			with Not_found -> (Hashtbl.find c.meths id).tp

let rec cp_expr cls e = match e with
  | Enull -> movq (imm 0) (reg rax), nop
  | Esimple es -> cp_expr_simple cls es
  | Eequal (a, e) ->
			cp_acces cls a += 
			pushq (reg rax) +++
			cp_expr cls e +=
			popq (reg rbx) +=
			movq (reg rax) (ind (reg rbx))
  | Eunop (Uneg, e) -> cp_expr cls e += negq (reg rax)
  | Eunop (Unot ,e) -> cp_expr cls e += notq (reg rax)
	| Ebinop (Badd, e1, e2) when tp_expr cls e1 <> Jint
														|| tp_expr cls e2 <> Jint ->
		(* A COMPLETER  *)
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
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
	| Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1 , e2) ->
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
	| Ebinop (Band | Bor as op, e1, e2) ->
			let lbl = new_lbl () in
			cp_expr cls e1 +=
			testq (reg rax) (reg rax) +=
			(match op with | Band -> je | Bor -> jne) lbl +++
			cp_expr cls e2 +=
			label lbl
			
and cp_expr_simple cls es = match es with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_lbl () in
               movq (imm lbl) (reg rax), label lbl ++ string s
  | ESthis -> movq (ind (~ofs:16) (reg rbp)) (reg rax), nop
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
			call id ++
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

and cp_acces cls a = match a with
	| Aident id ->
			let n = Hashtbl.find var id).adrs in
			leaq (ind (~ofs:n) (reg rbp)) (reg rax), nop
	| Achemin (es, id) ->
			match tp_expr_simple cls es with
				| Jntype { desc = Ntype (nom, _) } ->
						let c = Hashtbl.find cls nom in
						try let m = Hashtbl.find c.meths id in
								cp_expr_simple cls es +=
								pushq (reg rax) +=
								movq (ind (reg rax)) (reg rbx) +=
								call (ind (~ofs:m.ofs) (reg rbx)) +=
								popq (reg rcx)
						with Not_found ->
								let ch = Hashtbl.find c.champs id in
								cp_expr_simple cls es +=
								movq (reg rax) (reg rbx) +=
								movq (ind (~ods:ch.ofs) (reg rbx)) (reg rax)
				| _ -> exit 1			

let rec cp_instruc cls st = match st with
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
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
			cp_expr cls e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls s1 +=
			jmp lbl1 +=
			label lbl2 +++
			cp_instruc cls s2 +=
			label lbl1
	| Iwhile (e, s) ->
			let lbl1 = new_lbl () in
			let lbl2 = new_lbl () in
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
	let b = ref false in
	let rec aux d = match d with
		| [{desc = Dconstr cs}]::q ->
				Hashtbl.clear var ;
				b:=true ;
				let k = ref 2 in
				let aux1 id ch = incr k ;
					Hashtbl.replace var id
					{ tp = ch.tp ; ofs = !k*8 }
				in Hashtbl.iter aux1 cls.champs ;
				let aux2 { desc = prm } = incr k ;
					Hashtbl.replace var prm.nom
					{ tp = prm.typ.desc ; ofs = !k*8}
				in List.iter aux2 cs.params ;
				(label c.nom, nop) +++
				cp_instruc cls (Ibloc cs.body) +=
				leave += ret +++ aux q 
		| [{desc = Dmeth m}]::q ->
				Hashtbl.clear var ;
				let k = ref 2 in
				let aux1 id ch = incr k ;
					Hashtbl.replace var id
					{ tp = ch.tp ; ofs = !k*8 }
				in Hashtbl.iter aux1 cls.champs ;
				let aux2 { desc = prm } = incr k ;
					Hashtbl.replace var prm.nom
					{ tp = prm.typ.desc ; ofs = !k*8}
				in List.iter aux2 m.info.desc.params ;
				(label (new_lbl ()), nop) +++
				cp_instruc cls (Ibloc m.body) +=
				leave += ret +++ aux q
		| _::q -> aux q
		| [] -> if !b then (nop, nop)
						else (label c.nom ++ leave ++ ret, nop)
	in aux c.body
	
let cinit cls c =
	let cinfo = match c.extd with
		| None -> { params = Hashtbl.create 8 ;
								champs = Hashtbl.create 8 ;
								meths = Hashtbl.create 8 }
		| Some { desc = Ntype (id, _) } -> Hashtbl.find cls id
	in let a = ref 0 and b = ref 0 in
	let rec aux d = match d with
		| [{desc = Dchamp (jt, id) }]::q ->
				Hashtbl.replace cinfo.champs id
				{ tp = jt.desc ; ofs = !a*8 } ;
				incr a ; aux q
		| [{desc = Dmeth {desc = m} }]::q ->
				let jtp = match m.info.desc.typ with
					| None -> Jtypenull | Some jt -> jt in
				Hashtbl.replace cinfo.meths m.info.desc.nom
				{ tp = jtp ; ofs = !b*8 } ;
				incr b ; aux q
		| _::q -> aux q
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
			t ;
		data = d }
