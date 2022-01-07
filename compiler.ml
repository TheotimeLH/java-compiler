
open Ast
open X86_64
open Precompil

module Smap = Map.Make(String)
module Sset = Set.Make(String)

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let nllb = ref 0
let new_lbl () =
  incr nlbl ;
  Format.sprintf ".%d" !nlbl

let rec cp_expr vars p e = match e with
  | T_Enull -> movq (imm 0) (reg rax), nop
  | T_Eequal (a, e0) ->
			cp_acces cls a += 
			pushq (reg rax) +++
			cp_expr cls e0 +=
			popq rbx +=
			movq (reg rax) (ind rbx)
  | T_Eunop (Uneg, e0) -> cp_expr cls e0 += negq (reg rax)
  | T_Eunop (Unot ,e0) -> cp_expr cls e0 += notq (reg rax)
  | T_Eunop (Convert, e0) ->
      cp_expr vars p e0 +=
      movq (reg rax) (reg rsi) +=
      movq (ilab "Convert.0" (reg rdi) +=
      movq (imm 0) (reg rax)
	| T_Ebinop (e1, Bconcat, e2) ->
			cp_expr cls e1 +=
			pushq (reg rax) +++
			cp_expr cls e2 +=
			popq rdx +=
			movq (reg rax) (reg rsi) +=
			movq (ilab "Concat.0") (reg rdi) +=
			movq (imm 0) (reg rax) +=
			call "sprintf"
  | T_Ebinop (e1, (Beq | Bneq | Blt | Ble | Bgt | Bge as op), e2) ->  
      cp_expr cls e1 +=
			pushq (reg rax) +++
			cp_expr cls e2 +=
			popq rbx +=
			cmpq (reg rax) (reg rbx) +=
			begin match op with
				| Beq -> sete | Bneq -> setne
				| Blt -> setl | Ble -> setle
				| Bgt -> setg | Bge -> setge
			end (reg bl) +=
                        movq (imm 0) (reg rax) +=
                        movb (reg bl) (reg al)
	| T_Ebinop (e1, (Badd | Bsub | Bmul | Bdiv | Bmod as op), e2) ->
			cp_expr cls e1 +=
			pushq (reg rax) +++
			cp_expr cls e2 +=
			movq (reg rax) (reg rbx) +=
			popq rax +=
			begin match op with
				| Badd -> addq (reg rbx) (reg rax)
				| Bsub -> subq (reg rbx) (reg rax)
				| Bmul -> imulq (reg rbx) (reg rax)
				| Bdiv -> idivq (reg rbx)
				| Bmod -> idivq (reg rbx) ++ movq (reg rdx) (reg rax) end
	| T_Ebinop (e1, (Band | Bor as op), e2) ->
			let lbl = new_lbl () in
			cp_expr cls e1 +=
			testq (reg rax) (reg rax) +=
			(match op with | Band -> je | Bor -> jne) lbl +++
			cp_expr cls e2 +=
			label lbl
  | T_Eint n -> movq (imm n) (reg rax), nop
  | T_Ebool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | T_Estr s -> let lbl = "String" ^ new_lbl () in
               movq (ilab lbl) (reg rax), label lbl ++ string s
  | T_Ethis -> movq (ind ~ofs:16 rbp) (reg rax), nop
  | T_Eexpr e -> cp_expr cls e
  | T_Enew ({desc = Ntype (id, _)}, l)  ->
			let c = Hashtbl.find cls id in
			let aux cd e =
				cp_expr cls e +=
				pushq (reg rax) +++
				cd += popq rcx
			in List.fold_left aux (
			movq (imm (size c)) (reg rdi) ++
			call "malloc" ++
			pushq (reg rax) ++
			call c.cons ++
			popq rax, nop) l			
  | T_Eacces_meth (a, l) ->
			let aux cd e =
				cp_expr cls e +=
				pushq (reg rax) +++
				cd += popq rcx
			in List.fold_left aux (cp_acces cls a) l
  | T_Eacces_var a ->
			cp_acces cls a +=
			movq (reg rax) (reg rbx) +=
			movq (ind rbx) (reg rax)

and cp_acces cls a = match a.desc with
	| T_Aident id ->
			if id == "System" then raise System ;
			begin try let n = (Hashtbl.find var id).ofs in
			leaq (ind ~ofs:n rbp) (reg rax), nop
			with Not_found -> cp_acces cls (this id) end
	| T_Achemin (es, id) ->
			match tp_expr_simple cls es with
				| Jntype { desc = Ntype (nom, _) } ->
						let c = Hashtbl.find cls nom in
						begin try let m = Hashtbl.find c.meths id in
								cp_expr_simple cls es +=
								pushq (reg rax) +=
								movq (ind rax) (reg rbx) +=
								call m.lbl +=
								popq rcx
						with Not_found ->
								let ch = Hashtbl.find c.champs id in
								cp_expr_simple cls es +=
								movq (reg rax) (reg rbx) +=
								leaq (ind ~ods:ch.ofs rbx) (reg rax) end
				| exception System -> raise System_out
				| exception System_out ->
						movq (ind rsp) (reg rsi) ++
						movq (imm (ilab "Print_0")) (reg rdi) ++
						movq (imm O) (reg rax) ++
						call "printf", nop
				| _ -> exit 1			

let rec cp_instruc cls st = match st.desc with
	| T_Inil -> nop, nop
	| T_Isimple es -> cp_expr_simple cls es
	| T_Iequal (a, e) ->
			cp_acces cls a += 
			pushq (reg rax) +++
			cp_expr cls e +=
			popq rbx +=
			movq (reg rax) (ind rbx)
	| T_Idef (jt, id) -> decr p ;
			Hashtbl.replace var id { tp = jt ; ofs = !p*8 } ;
			pushq $0, nop
	| T_Idef_init (jt, id, e) -> decr p ;
			Hashtbl.replace var id { tp = jt ; ofs = !p*8 } ;
			cp_expr cls e += pushq (reg rax)
	| T_Iif (e, s1, s2) ->
			let n = new_lbl () in
			let lbl1 = "T_If"^n in
			let lbl2 = "Else"^n in 
			cp_expr cls e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls s1 +=
			jmp lbl1 +=
			label lbl2 +++
			cp_instruc cls s2 +=
			label lbl1
	| T_Iwhile (e, s) ->
			let n = new_lbl () in
			let lbl1 = "Deb"^n in
			let lbl2 = "Fin"^n in
			(label lbl1, nop) +++
			cp_expr cls e +=
			testq (reg rax) (reg rax) +=
			je lbl2 +++
			cp_instruc cls s +=
			jmp lbl1 +=
			label lbl2
	| T_Ibloc l -> List.fold_left (+++) (nop, nop)
							 (List.map (cp_instruc cls) l)
	| T_Ireturn None -> leave ++ ret, nop
	| T_Ireturn (Some e) -> cp_expr cls e += leave += ret	

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
		| None -> { cons = "New_0" ;
								champs = Hashtbl.create 8 ;
								meths = Hashtbl.create 8 }
		| Some { desc = Ntype (id, _) } ->
				let ext = Hashtbl.find cls id in
				{ cons = "New_0" ;
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
				{ tp = jtp ; lbl = c.nom^"_"^m.info.desc.nom^n } ;
				incr b ; aux q
		| _::q -> cinfo.cons = c.nom^"_new"^n ; aux q
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
			label "new" ++
			leave ++ ret ++
			label "String.equals" 
			(* A COMPLETER *) ;
		data = d ++
			label "Convert.0" ++
			string "%d" ++
			label "Concat.0" ++
			string "%s%s" ++
			label "Print.0" ++
			string "%s" ++
	    label "Println.0" ++
      string "%s\n" }

