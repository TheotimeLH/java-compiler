
open Ast
open Ast_typing
open X86_64
open Pre_compiler

let cstr = ref IdMap.empty
let size c = IdMap.cardinal c * 8 + 8

let nlbl = ref 0
let new_lbl () =
  incr nlbl ;
  Format.sprintf ".%d" !nlbl

let cp_fichier f =
  let meths, champs = mk_offset_tbl f.classes f.node_obj in

  let rec cp_expr vars e = match e with
    | T_Enull -> movq (imm 0) (reg rax)
    | T_Eequal (a, e0) ->
        cp_acces vars a ++ 
        pushq (reg rax) ++
        cp_expr vars e0 ++
        popq rbx ++
        movq (reg rax) (ind rbx)
    | T_Eunop (T_Uneg, e0) -> cp_expr vars e0 ++ negq (reg rax)
    | T_Eunop (T_Unot ,e0) -> cp_expr vars e0 ++ notq (reg rax)
    | T_Eunop (T_Uconvert, e0) ->
        cp_expr vars e0 ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Convert.0") (reg rdi) ++
        call "Align.0" ++
        subq (reg rbx) (reg rsp) ++
        movq (imm 0) (reg rax) ++
        call "sprintf" ++
        addq (reg rbx) (reg rsp)
    | T_Ebinop (e1, T_Bconcat, e2) ->
        cp_expr vars e1 ++
        pushq (reg rax) ++
        cp_expr vars e2 ++
        popq rcx ++
        call "Align.0" ++
        subq (reg rbx) (reg rsp) ++
        movq (reg rcx) (reg rdx) ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Concat.0") (reg rdi) ++
        movq (imm 0) (reg rax) ++
        call "sprintf" ++
        addq (reg rbx) (reg rsp)
    | T_Ebinop (e1, (T_Beq | T_Bneq | T_Blt | T_Ble | T_Bgt | T_Bge as op), e2) ->  
        cp_expr vars e1 ++
        pushq (reg rax) ++
        cp_expr vars e2 ++
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
        cp_expr vars e1 ++
        testq (reg rax) (reg rax) ++
        (match op with T_Bor -> jne | _ -> je) lbl ++
        cp_expr vars e2 ++
        label lbl
    | T_Ebinop (e1, (_  as op), e2) ->
        cp_expr vars e1 ++
        pushq (reg rax) ++
        cp_expr vars e2 ++
        movq (reg rax) (reg rbx) ++
        popq rax ++
        begin match op with
          | T_Badd_int -> addq (reg rbx) (reg rax)
          | T_Bsub -> subq (reg rbx) (reg rax)
          | T_Bmul -> imulq (reg rbx) (reg rax)
          | T_Bdiv -> movq (imm 0) (reg rdx) ++ idivq (reg rbx)
          | _ ->
              movq (imm 0) (reg rdx) ++
              idivq (reg rbx) ++
              movq (reg rdx) (reg rax) end
    | T_Eint n -> movq (imm n) (reg rax)
    | T_Ebool b -> movq (imm (if b then 1 else 0)) (reg rax)
    | T_Estr s -> 
        let lbl = "string"^
          begin try IdMap.find s !cstr 
          with Not_found ->
            let n = new_lbl () in
            cstr := IdMap.add s n !cstr ;
            n end
        in movq (ilab lbl) (reg rax)
    | T_Ethis -> movq (ind ~ofs:16 rbp) (reg rax)
    | T_Enew (id, l) ->
        let c = Hashtbl.find champs id in
        let aux cd e =
          cp_expr vars e ++
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
          cp_expr vars e ++
          pushq (reg rax) ++
          cd ++
          popq rcx
        in List.fold_left aux (cp_acces vars a) l
    | T_Eacces_var a ->
        cp_acces vars a ++
        movq (ind rax) (reg rax)
    | T_Eprint e0 ->
        cp_expr vars e0 ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Print.0") (reg rdi) ++
        call "Align.0" ++
        subq (reg rbx) (reg rsp) ++
        movq (imm 0) (reg rax) ++
        call "printf" ++
        addq (reg rbx) (reg rsp)
    | T_Eprintln e0 ->
        cp_expr vars e0 ++
        movq (reg rax) (reg rsi) ++
        movq (ilab "Println.0") (reg rdi) ++
        call "Align.0" ++
        subq (reg rbx) (reg rsp) ++
        movq (imm 0) (reg rax) ++
        call "printf" ++
        addq (reg rbx) (reg rsp)
    | T_Estr_equal (e1, e2) -> 
        cp_expr vars e1 ++
        pushq (reg rax) ++
        cp_expr vars e2 ++
        popq rdi ++
        movq (reg rax) (reg rsi) ++
        call "String.equals"

  and cp_acces vars a = match a with
    | T_Aident id ->
        let n = IdMap.find id vars in
        leaq (ind ~ofs:n rbp) rax
    | T_Achemin_meth (es, id) ->
        let n = Hashtbl.find meths id in
          cp_expr vars es ++
          pushq (reg rax) ++
          movq (ind rax) (reg rbx) ++
          call_star (ind ~ofs:n rbx) ++
          popq rbx
    | T_Achemin_ch ((es, tp), id) ->
        let cls = Hashtbl.find champs tp in
        let n = IdMap.find id cls in
        cp_expr vars es ++
        leaq (ind ~ofs:n rax) rax 

  and cp_instruc (cd, vars, p) st = match st with
    | T_Inil -> cd, vars, p 
    | T_Isimple e -> cd ++ cp_expr vars e, vars, p
    | T_Iequal (a, e) ->
        cd ++
        cp_acces vars a ++ 
        pushq (reg rax) ++
        cp_expr vars e ++
        popq rbx ++
        movq (reg rax) (ind rbx),
        vars, p
    | T_Idef id -> 
        cd ++ pushq (imm 0),
        IdMap.add id p vars, p-8
    | T_Idef_init (id, e) ->
        cd ++
        cp_expr vars e ++
        pushq (reg rax),
        IdMap.add id p vars, p-8
    | T_Iif (e, s1, s2) ->
        let n = new_lbl () in
        let lbl1 = "If"^n in
        let lbl2 = "Else"^n in
        let cd0 =
          cd ++
          cp_expr vars e ++
          testq (reg rax) (reg rax) ++
          je lbl2
        in
        let cd1, v1, p1 = cp_instruc (cd0, vars, p) s1 in
        let cd2 = cd1 ++ jmp lbl1 ++ label lbl2 in
        let cd3, v2, p2 = cp_instruc (cd2, v1, p1) s2 in
        cd3 ++ label lbl1, v2, p2
    | T_Iwhile (e, s) ->
        let n = new_lbl () in
        let lbl1 = "Deb"^n in
        let lbl2 = "Fin"^n in
        let cd0 =
          cd ++
          label lbl1 ++
          cp_expr vars e ++
          testq (reg rax) (reg rax) ++
          je lbl2
        in
        let cd1, v1, p1 = cp_instruc (cd0, vars, p) s in
        cd1 ++ jmp lbl1 ++ label lbl2, v1, p1
    | T_Ibloc l ->
        let cd0, _, _ = List.fold_left cp_instruc (cd, vars, p) l in
        cd0, vars, p
    | T_Ireturn opt ->
        cd ++ cp_expr vars
        (match opt with None -> T_Enull | Some e -> e) ++
        leave ++ ret, vars, p
  in

  let text_meths =
    let aux key info t =
      let k = ref 2 in
      let aux1 v id = incr k ; IdMap.add id (!k*8) v in
      let vars = List.fold_left aux1 IdMap.empty info.params in
      let lbl = fst key ^ "." ^ snd key in
      let cd =
        t ++
        label lbl ++
        pushq (reg rbp) ++
        movq (reg rsp) (reg rbp)
      in
      let cd0, _, _ = List.fold_left cp_instruc (cd, vars, -8) info.body in
      cd0 ++ leave ++ ret
    in Hashtbl.fold aux f.tbl_meth nop 
  in

  let text_main, _, _ =
    List.fold_left cp_instruc (nop, IdMap.empty, -8) f.main_body
  in

  let text_cons =
    let aux t c = match c.constructeur with
      | None -> t
      | Some m -> 
          let k = ref 2 in
          let aux1 v id = incr k ; IdMap.add id (!k*8) v in
          let vars = List.fold_left aux1 IdMap.empty m.params in
          let lbl = c.nom ^ ".new" in
          let cd =
            t ++
            label lbl ++
            pushq (reg rbp) ++ 
            movq (reg rsp) (reg rbp)
          in
          let cd0, _, _  = List.fold_left cp_instruc (cd, vars, -8) m.body in
          cd0 ++ leave ++ ret
    in List.fold_left aux nop f.classes
  in

  let data_descr =
    let aux d c =
      let aux1 k x = max (Hashtbl.find meths (snd x)/8) k in
      let n = List.fold_left aux1 0 c.cle_methodes in
      let t = Array.make n None in
      let aux2 x = t.(Hashtbl.find meths (snd x)/8-1) <- Some x in
      List.iter aux2 c.cle_methodes ;
      d ++ label c.nom ++ address
      (match c.constructeur with None -> ["new"] | Some _ -> [c.nom^".new"]) ++
      Array.fold_left ( fun dt opt -> match opt with
                          | None -> dt ++ dquad [0]
                          | Some (x, y) -> dt ++ address [x^"."^y] ) nop t
    in List.fold_left aux nop f.classes
  in

  let data_cstr =
    let aux s n d = d ++ label ("string"^n) ++ string s ++ dquad [0] in
    IdMap.fold aux !cstr nop
  in

	{ text =
			globl "main" ++
			label "main" ++
      movq (reg rsp) (reg rbp) ++
			text_main ++
      movq (imm 0) (reg rax) ++
			label "new" ++
			ret ++
      text_cons ++
      text_meths ++
			label "String.equals" ++
      movq (imm 0) (reg rcx) ++
      movq (imm 1) (reg rax) ++
      label "Deb.0" ++
      movq (ind ~index:rcx rdi) (reg rbx) ++
      cmpq (reg rbx) (ind ~index:rcx rsi) ++
      jne "Fin.0" ++
      addq (imm 1) (reg rcx) ++
      testq (reg rbx) (reg rbx) ++
      jne "Deb.0" ++
      movq (imm 1) (reg rax) ++
      label "Fin.0" ++
      leave ++ ret ++
      label "Align.0" ++
      movq (imm 0) (reg rdx) ++
      movq (reg rsp) (reg rax) ++
      movq (imm 16) (reg rbx) ++
      idivq (reg rbx) ++
      movq (imm 8) (reg rbx) ++
      subq (reg rax) (reg rbx) ++
      ret ;
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
      data_cstr }

