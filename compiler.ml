
open Ast
open X86_64

type adresse = Ofs of int | Lbl of label | No
type obj = {tp: jtype; adrs: adresse}
type cls = {params: obj tbl; champs: obj tbl;
						mutable cons: adresse; meths: obj tbl}
let jnt nt = Jntype { desc = nt ;
		loc = Lexing.dummy_pos, Lexing.dummy_pos }

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let nlbl = ref 0
let clss = Hashtbl.create 8

let new_lbl () =
  incr nlbl ;
  Format.sprintf "%d" !nlbl

let rec tp_expr vars e = match e with
	| Enull -> Jtypenull
	| Esimple es | Eequal (_, es) -> tp_expr_simple vars es
	| Ebinop (Badd,e1,e2) ->
			if tp_expr vars e1 = Jint && tp_expr vars e2 = Jint
			then Jint else jnt ( Ntype ("String", []) )
	| Ebinop(Bsub | Bmul | Bdiv | Bmod,_,_)
	| Eunop (Uneg, _) -> Jint
	| Eunop _ | Ebinop _ -> Jboolean
and tp_expr_simple vars es = match es with
	| ESint -> Jint
	| ESboll -> Jboolean
	| ESstr -> jstring
	| ESthis -> (Hasstbl.find vars "this").tp
	| ESexpr e -> tp_expr vars e
	| ESnew (nt, _) -> jnt nt
	| ESacces_meth (a, _) -> tp_acces vars a
	| ESacces_var a ->  tp_acces vars a
and tp_acces vars a = match a with
	| Aident id -> (Hashtbl.find vars id).tp
	| Achemin (es, id) ->
			let c = match tp_expr_simple vars es with
				| Jntype { desc = Ntype (nom, _) } -> Hashtbl.find clss nom
				| _ -> exit 1
			in (Hashtbl.find c id).tp

let rec cp_expr vars e = match e with
  | Enull -> nop, nop
  | Esimple es -> cp_expr_simple vars es
  | Eequal (a, e) ->
			cp_acces vars a += 
			pushq (reg rax) +++
			cp_expr vars e +=
			popq (reg rdx) +=
			movq (reg rax) (ind (reg rdx))
  | Eunop (Uneg, e) -> cp_expr vars e += negq (reg rax)
  | Eunop (Unot ,e) -> cp_expr vars e += notq (reg rax)
	| Ebinop (Badd, e1, e2) when tp_expr vars e1 <> Jint || tp_expr vars e2 <> Jint ->
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->  
      cp_expr vars e1 +=
			pushq (reg rax) +++
			cp_expr vars e2 +=
			popq (reg rdx)
			cmpq (reg rax) (reg rdx) +=
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
			cp_expr vars e1 +=
			pushq (reg rax) +++
			cp_expr vars e2 +=
			popq (reg rdi) +=
			movq (reg rax) (reg rsi) +=
			call "String.concat"
			
and cp_expr_simple vars es = match es with
  | ESint n -> movq (imm n) (reg rax), nop
  | ESbool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
  | ESstr s -> let lbl = new_label () in
               movq (lab lbl) (reg rax), label lbl ++ string s
  | ESthis -> movq (ind (~ofs:+16) (reg rbp)) (reg rax)
  | ESexpr e -> cp_expr vars e
  | ESnew (Ntype (id, _), l)  ->
			let aux cd e = cp_expr vars e +=
										 pushq (reg rax) +++
										 cd += popq (reg rcx)
			and c = (Hashtbl.find clss id).cons in
			List.fold_left aux (call c) l
  | ESacces_meth (a, l) ->
			let aux cd e = cp_expr vars e +=
										 pushq (reg rax) +++
										 cd += popq (reg rcx)
			in List.fold_left aux (cp_acces vars a) l
  | ESacces_var a -> cp_acces vars a
	
and cp_acces vars a = match a with
	| Aident id -> match Hashtbl.find vars id with
									| Ofs n -> movq (ind (~ofs:n) (reg rbp)) (reg rax)
									| Lbl s -> movq (ilab s) (reg rax)
	| Achemin (es, id) ->
			let lbl = match tp_expr_simple vars es with
				| Jntype { desc = Ntype (nom, _) } ->
						let c = Hashtbl.find clss nom in
						(Hashtbl.find c.meths id).adrs
				| _ -> exit 1 in
			cp_expr_simple vars es +=
			pushq (reg rax) +=
			call lbl +=
			popq (reg rcx)

let rec cp_instruc vars st = match st with
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
	let cinfo = Hashtbl.find clss c in
	let rec aux d = match d with
		| [{desc = Dconstr cs}]::q ->
				let vars = Hashtbl.create 8 and k = ref 8 in
				List.iter ( fun p -> incr k ; Hashtbl.replace vars p.nom
									{ tp = p.typ.desc ; adrs = Ofs !k } ) cs.param ;
				aux q += lab cinfo.cons +++
				cp_instruc vars (Ibloc cs.body)
		| [{desc = Dmeth m}]::q ->
				let vars = Hashtbl.create 8 and k = ref 16 in
				List.iter
		| _::q -> aux q
		| [] -> (nop,nop)
	in aux c.body
	
let cinit c =
	let cinfo = match c.extd with
		| None -> { params = Hashtbl.create 8 ; 
								champs = Hashtbl.create 8 ;
								cons = No ;	meths = Hashtbl.create 8 }
		| Some { desc = Ntype (id, _) } -> Hashtbl.find clss id
	in let k = ref 0 in
	let rec aux d = match d with
		| [{desc = Dchamp (jt, id) }]::q ->
				Hashtbl.replace cinfo.champs id
				{ tp = jt.desc ; adrs = Ofs !k*8 } ;
				incr k ; aux q
		| [{desc = Dconstr _}]::q ->
				cinfo.cons = Lbl (new_label ()) ; aux q
		| [{desc = Dmeth {desc = m} }]::q ->
				let jtp = match m.info.desc.typ with
					| None -> Jtypenull | Some jt -> jt in
				Hashtbl.replace cinfo.meths m.info.desc.nom
				{ tp = jtp ; adrs = Lbl (new_label ()) } ; aux q
		| [] -> ()
	in aux c.body

let cp_fichier prog =
	let init f = match f with
		| [{desc = Class c}]::q -> cinit c ; init q
		| _::q -> init q
		| _ -> ()
	in init prog ;
	let main = ref [] in
	let rec code f = match f with
		| [{desc = Class c}]::q -> cp_classe c +++ aux q
		| [{desc = Interface _}]::q -> aux q
		| [{desc = Main l}]::q -> main:=l ; aux q
		| _ -> (nop, nop)
	in let tc, dc = aux prog in
	let tm, dm = cp_instr (Hashtbl.create 8) (Ibloc !main) in
	{ text =
			globl "Main" ++
			label "Main" ++
			tm ++
			movq (imm 0) (reg rax) ++
			ret ++
			tc ;
		data = dc ++ dm }
