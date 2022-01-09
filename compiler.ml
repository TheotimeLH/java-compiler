
open Ast
open Ast_typing
open X86_64
open Pre_compiler

let setr = ref IdSet.empty
let size c = IdMap.cardinal c * 8 + 8

let nlbl = ref 0
let new_lbl () =
  incr nlbl ;
  Format.sprintf ".%d" !nlbl

let cp_fichier f =
  let meths, champs = mk_offset_tbl f.classes f.node_obj in

  let rec cp_expr vars p e = match e with
    | T_Enull -> movq (imm 0) (reg rax)
    | T_Eequal (a, e0) ->
        cp_acces vars p a ++ 
        pushq (reg rax) ++
        cp_expr vars p e0 ++
        popq rbx ++
        movq (reg rax) (ind rbx)
    | T_Eunop (T_Uneg, e0) -> cp_expr vars p e0 ++ negq (reg rax)
    | T_Eunop (T_Unot ,e0) -> cp_expr vars p e0 ++ notq (reg rax)
    | T_Eunop (T_Uconvert, e0) ->
        cp_expr vars p e0 ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Convert.0") (reg rdi) ++
        movq (imm 0) (reg rax)
    | T_Ebinop (e1, T_Bconcat, e2) ->
        cp_expr vars p e1 ++
        pushq (reg rax) ++
        cp_expr vars p e2 ++
        popq rdx ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Concat.0") (reg rdi) ++
        movq (imm 0) (reg rax) ++
        call "sprintf"
    | T_Ebinop (e1, (T_Beq | T_Bneq | T_Blt | T_Ble | T_Bgt | T_Bge as op), e2) ->  
        cp_expr vars p e1 ++
        pushq (reg rax) ++
        cp_expr vars p e2 ++
        popq rbx ++
        cmpq (reg rax) (reg rbx) ++
        begin match op with
          | T_Beq -> sete | T_Bneq -> setne
          | T_Blt -> setl | T_Ble -> setle
          | T_Bgt -> setg | _ -> setge
        end (reg bl) ++
        movq (imm 0) (reg rax) ++
        movb (reg bl) (reg al)
    | T_Ebinop (e1, (T_Band | T_Bor as op), e2) ->
        let lbl = (match op with T_Bor -> "Or" | _ -> "And") ^ new_lbl () in
        cp_expr vars p e1 ++
        testq (reg rax) (reg rax) ++
        (match op with T_Bor -> jne | _ -> je) lbl ++
        cp_expr vars p e2 ++
        label lbl
    | T_Ebinop (e1, (_  as op), e2) ->
        cp_expr vars p e1 ++
        pushq (reg rax) ++
        cp_expr vars p e2 ++
        movq (reg rax) (reg rbx) ++
        popq rax ++
        begin match op with
          | T_Badd_int -> addq (reg rbx) (reg rax)
          | T_Bsub -> subq (reg rbx) (reg rax)
          | T_Bmul -> imulq (reg rbx) (reg rax)
          | T_Bdiv -> idivq (reg rbx)
          | _ -> idivq (reg rbx) ++ movq (reg rdx) (reg rax) end
    | T_Eint n -> movq (imm n) (reg rax)
    | T_Ebool b -> movq (imm (if b then 1 else 0)) (reg rax)
    | T_Estr s -> 
        let lbl = "String." ^ s in
        setr := IdSet.add s !setr ;
        movq (ilab lbl) (reg rax)
    | T_Ethis -> movq (ind ~ofs:16 rbp) (reg rax)
    | T_Enew (id, l) ->
        let c = Hashtbl.find champs id in
        let aux cd e =
          cp_expr vars p e ++
          pushq (reg rax) ++
          cd ++
          popq rbx
        in List.fold_left aux (
        movq (imm (size c)) (reg rdi) ++
        call "malloc" ++
        pushq (reg rax) ++
        movq (ilab id) (ind rax) ++
        movq (ind rax) (reg rbx) ++
        call_star (ind rbx) ++
        popq rax) l			
    | T_Eacces_meth (a, l) ->
        let aux cd e =
          cp_expr vars p e ++
          pushq (reg rax) ++
          cd ++
          popq rcx
        in List.fold_left aux (cp_acces vars p a) l
    | T_Eacces_var a ->
        cp_acces vars p a ++
        movq (ind rax) (reg rax)
    | T_Eprint e0 ->
        cp_expr vars p e0 ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Print.0") (reg rdi) ++
        movq (imm 0) (reg rax) ++
        call "printf"
    | T_Eprintln e0 ->
        cp_expr vars p e0 ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Println.0") (reg rdi) ++
        movq (imm 0) (reg rax) ++
        call "printf"
    | T_Estr_equal (e1, e2) -> 
        cp_expr vars p e1 ++
        pushq (reg rax) ++
        cp_expr vars p e2 ++
        popq rdi ++
        movq (reg rax) (reg rdi) ++
        call "String.equals.0"

  and cp_acces vars p a = match a with
    | T_Aident id ->
        let n = IdMap.find id vars in
        leaq (ind ~ofs:n rbp) rax
    | T_Achemin_meth (es, id) ->
        Printf.printf "%s \n" id ;
        let n = Hashtbl.find meths id in
          cp_expr vars p es ++
          pushq (reg rax) ++
          movq (ind rax) (reg rbx) ++
          call_star (ind ~ofs:n rbx) ++
          popq rbx
    | T_Achemin_ch ((es, tp), id) ->
        let cls = Hashtbl.find champs tp in
        let n = IdMap.find id cls in
        cp_expr vars p es ++
        movq (ind ~ofs:n rax) (reg rax) 

  and cp_instruc (cd, vars, p) st = match st with
    | T_Inil -> cd, vars, p 
    | T_Isimple e -> cp_expr vars p e, vars, p
    | T_Iequal (a, e) ->
        cd ++
        cp_acces vars p a ++ 
        pushq (reg rax) ++
        cp_expr vars p e ++
        popq rbx ++
        movq (reg rax) (ind rbx),
        vars, p
    | T_Idef id -> 
        cd ++ pushq (imm 0),
        IdMap.add id p vars, p-8
    | T_Idef_init (id, e) ->
        cd ++
        cp_expr vars p e ++
        pushq (reg rax),
        IdMap.add id p vars, p-8
    | T_Iif (e, s1, s2) ->
        let n = new_lbl () in
        let lbl1 = "If."^n in
        let lbl2 = "Else."^n in
        let cd0 =
          cd ++
          cp_expr vars p e ++
          testq (reg rax) (reg rax) ++
          je lbl2
        in
        let cd1, v1, p1 = cp_instruc (cd0, vars, p) s1 in
        let cd2 = cd1 ++ jmp lbl1 ++ label lbl2 in
        let cd3, v2, p2 = cp_instruc (cd2, v1, p1) s2 in
        cd3 ++ label lbl1, v2, p2
    | T_Iwhile (e, s) ->
        let n = new_lbl () in
        let lbl1 = "Deb."^n in
        let lbl2 = "Fin."^n in
        let cd0 =
          cd ++
          label lbl1 ++
          cp_expr vars p e ++
          testq (reg rax) (reg rax) ++
          je lbl2
        in
        let cd1, v1, p1 = cp_instruc (cd0, vars, p) s in
        cd1 ++ jmp lbl1 ++ label lbl2, v1, p1
    | T_Ibloc l ->
        let cd0, _, _ = List.fold_left cp_instruc (cd, vars, p) l in
        cd0, vars, p
    | T_Ireturn opt ->
        cd ++ cp_expr vars p
        (match opt with None -> T_Enull | Some e -> e) ++
        leave ++ ret, vars, p
  in

  let text_meths =
    let aux key info t =
      let k = ref 2 in
      let aux1 v id = incr k ; IdMap.add id (!k*8) v in
      let vars = List.fold_left aux1 IdMap.empty info.params in
      let lbl = fst key ^ "." ^ snd key in
      let cd = t ++ label lbl in
      let cd0, _, _ = List.fold_left cp_instruc (cd, vars, -8) info.body in
      cd0
    in Hashtbl.fold aux f.tbl_meth nop 
  in

  let text_main, _, _ =
    List.fold_left cp_instruc (nop, IdMap.empty, -8) f.main_body
  in

  let data_setr =
    let aux s d = d ++ label ("String."^s) ++ string s in
    IdSet.fold aux !setr nop
  in

  let text_cons =
    let aux t c = match c.constructeur with
      | None -> t
      | Some m -> 
          let k = ref 2 in
          let aux1 v id = incr k ; IdMap.add id (!k*8) v in
          let vars = List.fold_left aux1 IdMap.empty m.params in
          let lbl = c.nom ^ ".new" in
          let cd = t ++ label lbl in
          let cd0, _, _  = List.fold_left cp_instruc (cd, vars, -8) m.body in
          cd0
    in List.fold_left aux nop f.classes
  in

  let data_descr =
    let aux d c =
      let aux1 k x = max (Hashtbl.find meths (snd x)) k in
      let n = List.fold_left aux1 0 c.cle_methodes in
      let t = Array.make n None in
      let aux2 x = t.(Hashtbl.find meths (snd x)) <- Some x in
      List.iter aux2 c.cle_methodes ;
      d ++ label c.nom ++ address
      (match c.constructeur with None -> ["new"] | Some _ -> [c.nom^".new"]) ++
      Array.fold_left ( fun dt opt -> match opt with
                          | None -> dt ++ dquad [0]
                          | Some (x, y) -> dt ++ address [x^"."^y] ) nop t
    in List.fold_left aux nop f.classes
  in

	{ text =
			globl "Main" ++
			label "Main" ++
			text_main ++
      movq (imm 0) (reg rax) ++
			label "new" ++
			leave ++ ret ++
      text_cons ++
      text_meths ++
			label "String.equals.0" ++
      movq (imm 0) (reg rcx) ++
      movq (imm 1) (reg rax) ++
      label "Deb.0" ++
      cmpq (ind ~index:rcx rdi) (ind ~index:rcx rsi) ++
      jne "Fin.0" ++
      testq (ind ~index:rcx rdi) (ind ~index:rcx rsi) ++
      jne "Deb.0" ++
      movq (imm 1) (reg rax) ++
      label "Fin.0" ;
		data =
      data_descr ++
			label "Convert.0" ++
			string "%d" ++
			label "Concat.0" ++
			string "%s%s" ++
			label "Print.0" ++
			string "%s" ++
	    label "Println.0" ++
      string "%s\n" ++
      data_setr }

