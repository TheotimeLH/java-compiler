
open Ast
open X86_64
open Precompiler

let (+=) (t1, d) t2 = t1 ++ t2, d
let (+++) (t1, d1) (t2, d2) = t1 ++ t2, d1 ++ d2 

let setr = ref IdSet.empty
let size c = Hashtbl.length c * 8 + 8

let nllb = ref 0
let new_lbl () =
  incr nlbl ;
  Format.sprintf ".%d" !nlbl

let cp_fichier f =
  let meths, champs = mk_offset_tbl f.classes in

  let rec cp_expr vars p e = match e with
    | T_Enull -> movq (imm 0) (reg rax), nop
    | T_Eequal (a, e0) ->
        cp_acces vars p a += 
        pushq (reg rax) +++
        cp_expr vars p e0 +=
        popq rbx +=
        movq (reg rax) (ind rbx)
    | T_Eunop (T_Uneg, e0) -> cp_expr vars p e0 += negq (reg rax)
    | T_Eunop (T_Unot ,e0) -> cp_expr vars p e0 += notq (reg rax)
    | T_Eunop (T_Uconvert, e0) ->
        cp_expr vars p e0 +=
        movq (reg rax) (reg rsi) +=
        movq (ilab "Convert.0") (reg rdi) +=
        movq (imm 0) (reg rax)
    | T_Ebinop (e1, Bconcat, e2) ->
        cp_expr vars p e1 +=
        pushq (reg rax) +++
        cp_expr vars p e2 +=
        popq rdx +=
        movq (reg rax) (reg rsi) +=
        movq (ilab "Concat.0") (reg rdi) +=
        movq (imm 0) (reg rax) +=
        call "sprintf"
    | T_Ebinop (e1, (Beq | Bneq | Blt | Ble | Bgt | Bge as op), e2) ->  
        cp_expr vars p e1 +=
        pushq (reg rax) +++
        cp_expr vars p e2 +=
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
        cp_expr vars p e1 +=
        pushq (reg rax) +++
        cp_expr vars p e2 +=
        movq (reg rax) (reg rbx) +=
        popq rax +=
        begin match op with
          | Badd -> addq (reg rbx) (reg rax)
          | Bsub -> subq (reg rbx) (reg rax)
          | Bmul -> imulq (reg rbx) (reg rax)
          | Bdiv -> idivq (reg rbx)
          | Bmod -> idivq (reg rbx) ++ movq (reg rdx) (reg rax) end
    | T_Ebinop (e1, (Band | Bor as op), e2) ->
        let lbl = (match op with Band -> "And" | Bor -> "Or") ^ new_lbl () in
        cp_expr vars p e1 +=
        testq (reg rax) (reg rax) +=
        (match op with Band -> je | Bor -> jne) lbl +++
        cp_expr vars p e2 +=
        label lbl
    | T_Eint n -> movq (imm n) (reg rax), nop
    | T_Ebool b -> movq (imm (if b then 1 else 0)) (reg rax), nop
    | T_Estr s -> 
        let lbl = "String." ^ s in
        setr := IdSet.add s !setr ;
        movq (ilab lbl) (reg rax), nop
    | T_Ethis -> movq (ind ~ofs:16 rbp) (reg rax), nop
    | T_Enew (id, l) ->
        let c = IdMap.find id champs in
        let aux cd e =
          cp_expr vars p e +=
          pushq (reg rax) +++
          cd += popq rbx
        in List.fold_left aux (
        movq (imm (size c)) (reg rdi) ++
        call "malloc" ++
        pushq (reg rax) ++
        movq (ilab id) (ind rax) ++
        movq (ind rax) (reg rbx) ++
        call (ind rbx) ++
        popq rax, nop) l			
    | T_Eacces_meth (a, l) ->
        let aux cd e =
          cp_expr vars p e +=
          pushq (reg rax) +++
          cd += popq rcx
        in List.fold_left aux (cp_acces vars p a) l
    | T_Eacces_var a ->
        cp_acces vars p a +=
        movq (ind rax) (reg rax)
    | T_Eprint e0 ->
        cp_expr vars p e0 +=
        movq (reg rax) (reg rsi) +=
        movq (ilab "Print.0") (reg rdi) +=
        movq (imm O) (reg rax) +=
        call "printf"
    | T_Eprintln e0 ->
        cp_expr vars p e0 +=
        movq (reg rax) (reg rsi) +=
        movq (ilab "Println.0") (reg rdi) +=
        movq (imm O) (reg rax) +=
        call "printf"
    | T_Estr_equal (e1, e2) -> 
        cp_expr vars p e1 +=
        pushq (reg rax) +++
        cp_expr vars p e2 +=
        popq rdi +=
        movq (reg rax) (reg rdi) +=
        call "String.equals.0"

  and cp_acces vars p a = match a.desc with
    | T_Aident id ->
        let n = Hashtbl.find var id in
        leaq (ind ~ofs:n rbp) (reg rax), nop
    | T_Achemin_meth (es, id) ->
        let n = Hashtbl.find meths id in
          cp_expr vars p es +=
          pushq (reg rax) +=
          movq (ind rax) (reg rbx)
          call (ind ~ofs:n rbx) +=
          popq rbx
    | T_Achemin_ch ((es, tp), id)
        let cls = IdMap.find tp champs in
        let n = Hashtbl.find cls id in
        cp_expr vars p es +=
        movq (ind ~ods:n rax) (reg rax) 

  and cp_instruc (cd, vars, p) st = match st with
    | T_Inil -> cd, vars, p 
    | T_Isimple e -> cp_expr vars p e, vars, p
    | T_Iequal (a, e) ->
        cd +=
        cp_acces vars p a += 
        pushq (reg rax) +++
        cp_expr vars p e +=
        popq rbx +=
        movq (reg rax) (ind rbx),
        vars, p
    | T_Idef (jt, id) -> decr p ;
        cd += pushq (imm 0),
        IdMap.add id p vars, p-8
    | T_Idef_init (jt, id, e) ->
        cd +=
        cp_expr vars p e +=
        pushq (reg rax),
        IdMap.add id p vars, p-8
    | T_Iif (e, s1, s2) ->
        let n = new_lbl () in
        let lbl1 = "If."^n in
        let lbl2 = "Else."^n in
        let cd0 =
          cd +=
          cp_expr vars p e +=
          testq (reg rax) (reg rax) +=
          je lbl2
        in
        let cd1, v1, p1 = cp_instruc (cd0, vars, p) s1 in
        let cd2 = cd1 += jmp lbl1 += label lbl2 in
        let cd3, v2, p2 = cp_instruc (cd2, v1, p1) s2 in
        cd3 += label lbl1, v2, p2
    | T_Iwhile (e, s) ->
        let n = new_lbl () in
        let lbl1 = "Deb."^n in
        let lbl2 = "Fin."^n in
        let cd0 =
          cd +=
          label lbl1 +++
          cp_expr vars p e +=
          testq (reg rax) (reg rax) +=
          je lbl2
        in
        let cd1, v1, p1 = cp_instruc (cd0, vars, p) s in
        cd1 += jmp lbl1 += label lbl2, v1, p1
    | T_Ibloc l ->
        let cd0, _, _ = List.fold_left cp_instruc (cd, vars, p) l in
        cd0, vars, p
    | T_Ireturn opt ->
        cd +++ cp_expr vars p
        (match opt with None -> T_Enull | Some -> e) +=
        leave += ret, vars, p
  in

  let (text_meths, data_meths), _, _ =
    let aux key info cd =
      let k = ref 2 in
      let lmbd id v = incr k ; IdMap.add id (!k*8) v in
      let vars = List.fold_left lmbd IdMap.empty info.params in
      let lbl = fst key ^ "." ^ snd key in
      let cd0 = cd += label lbl in
      List.fold_left cp_instruc (cd0, vars, -8) l
    in Hashtbl.fold aux f.tbl_meth (nop, nop)
  in

  let (text_main, data_main), _, _ =
    List.fold cp_instruc ((nop, nop), IdMap.empty, -8) f.body_main
  in

  let data_setr =
    let aux s d = d ++ label ("String."^s) ++ strinf s in
    IdSet.fold aux setr nop
  in

  let (text_cons, data_descr) =
    (* A COMPLETER *)

	{ text =
			globl "Main" ++
			label "Main" ++
			text_main ++
      text_meths ++
      text_cons ++ 
			label "new.0" ++
			leave ++ ret ++
			label "String.equals.0" 
			(* A COMPLETER *) ;
		data =
      data_descr
      data_main ++
      data_meths ++
      data_cstr ++
			label "Convert.0" ++
			string "%d" ++
			label "Concat.0" ++
			string "%s%s" ++
			label "Print.0" ++
			string "%s" ++
	    label "Println.0" ++
      string "%s\n" }

