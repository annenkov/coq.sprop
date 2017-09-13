(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open CErrors
open Util
open Pp
open Names
open Nameops
open Libnames
open Pputils
open Ppextend
open Notation_term
open Constrexpr
open Constrexpr_ops
open Decl_kinds
open Misctypes
(*i*)

module Tag =
struct
  let keyword   = "constr.keyword"
  let evar      = "constr.evar"
  let univ      = "constr.type"
  let notation  = "constr.notation"
  let variable  = "constr.variable"
  let reference = "constr.reference"
  let path      = "constr.path"

end

let do_not_tag _ x = x
let tag t s = Pp.tag t s
let tag_keyword     = tag Tag.keyword
let tag_evar        = tag Tag.evar
let tag_type        = tag Tag.univ
let tag_unparsing   = function
| UnpTerminal s -> tag Tag.notation
| _ -> do_not_tag ()
let tag_constr_expr = do_not_tag
let tag_path = tag Tag.path
let tag_ref = tag Tag.reference
let tag_var = tag Tag.variable


  let keyword s = tag_keyword (str s)
  let sep_v = fun _ -> str"," ++ spc()
  let pr_tight_coma () = str "," ++ cut ()

  let latom = 0
  let lprod = 200
  let llambda = 200
  let lif = 200
  let lletin = 200
  let lletpattern = 200
  let lfix = 200
  let lcast = 100
  let larg = 9
  let lapp = 10
  let lposint = 0
  let lnegint = 35 (* must be consistent with Notation "- x" *)
  let ltop = (200,E)
  let lproj = 1
  let ldelim = 1
  let lsimpleconstr = (8,E)
  let lsimplepatt = (1,E)

  let prec_less child (parent,assoc) =
    if parent < 0 && Int.equal child lprod then true
    else
      let parent = abs parent in
      match assoc with
        | E -> (<=) child parent
        | L -> (<) child parent
        | Prec n -> child<=n
        | Any -> true

  let prec_of_prim_token = function
    | Numeral (_,b) -> if b then lposint else lnegint
    | String _ -> latom

  open Notation

  let print_hunks n pr pr_binders (terms, termlists, binders) unps =
    let env = ref terms and envlist = ref termlists and bll = ref binders in
    let pop r = let a = List.hd !r in r := List.tl !r; a in
    let return unp pp1 pp2 = (tag_unparsing unp pp1) ++ pp2 in
    (* Warning:
       The following function enforces a very precise order of
       evaluation of sub-components.
       Do not modify it unless you know what you are doing! *)
    let rec aux = function
      | [] ->
        mt ()
      | UnpMetaVar (_, prec) as unp :: l ->
        let c = pop env in
        let pp2 = aux l in
        let pp1 = pr (n, prec) c in
        return unp pp1 pp2
      | UnpListMetaVar (_, prec, sl) as unp :: l ->
        let cl = pop envlist in
        let pp1 = prlist_with_sep (fun () -> aux sl) (pr (n,prec)) cl in
        let pp2 = aux l in
        return unp pp1 pp2
      | UnpBinderListMetaVar (_, isopen, sl) as unp :: l ->
        let cl = pop bll in
        let pp2 = aux l in
        let pp1 = pr_binders (fun () -> aux sl) isopen cl in
        return unp pp1 pp2
      | UnpTerminal s as unp :: l ->
        let pp2 = aux l in
        let pp1 = str s in
        return unp pp1 pp2
      | UnpBox (b,sub) as unp :: l ->
        let pp1 = ppcmd_of_box b (aux sub) in
        let pp2 = aux l in
        return unp pp1 pp2
      | UnpCut cut as unp :: l ->
        let pp2 = aux l in
        let pp1 = ppcmd_of_cut cut in
        return unp pp1 pp2
    in
    aux unps

  let pr_notation pr pr_binders s env =
    let unpl, level = find_notation_printing_rule s in
    print_hunks level pr pr_binders env unpl, level

  let pr_delimiters key strm =
    strm ++ str ("%"^key)

  let pr_generalization bk ak c =
    let hd, tl =
      match bk with
        | Implicit -> "{", "}"
        | Explicit -> "(", ")"
    in (* TODO: syntax Abstraction Kind *)
    str "`" ++ str hd ++ c ++ str tl

  let pr_com_at n =
    if !Flags.beautify && not (Int.equal n 0) then comment (CLexer.extract_comments n)
    else mt()

  let pr_with_comments ?loc pp = pr_located (fun x -> x) (Loc.tag ?loc pp)

  let pr_sep_com sep f c = pr_with_comments ?loc:(constr_loc c) (sep() ++ f c)

  let pr_univ l =
    match l with
      | [_,x] -> Name.print x
      | l -> str"max(" ++ prlist_with_sep (fun () -> str",") (fun x -> Name.print (snd x)) l ++ str")"

  let pr_univ_annot pr x = str "@{" ++ pr x ++ str "}"

  let pr_glob_sort = function
    | GProp -> tag_type (str "Prop")
    | GSet -> tag_type (str "Set")
    | GType [] -> tag_type (str "Type")
    | GType u -> hov 0 (tag_type (str "Type") ++ pr_univ_annot pr_univ u)

  let pr_glob_level = function
    | GProp -> tag_type (str "Prop")
    | GSet -> tag_type (str "Set")
    | GType None -> tag_type (str "Type")
    | GType (Some (_, u)) -> tag_type (Name.print u)

  let pr_qualid sp =
    let (sl, id) = repr_qualid sp in
    let id = tag_ref (pr_id id) in
    let sl = match List.rev (DirPath.repr sl) with
    | [] -> mt ()
    | sl ->
      let pr dir = tag_path (pr_id dir) ++ str "." in
      prlist pr sl
    in
    sl ++ id

  let pr_id = pr_id
  let pr_name = pr_name
  let pr_qualid = pr_qualid
  let pr_patvar = pr_id

  let pr_glob_sort_instance = function
    | GProp ->
      tag_type (str "Prop")
    | GSet ->
      tag_type (str "Set")
    | GType u ->
      (match u with
        | Some (_,u) -> Name.print u
        | None -> tag_type (str "Type"))

  let pr_universe_instance l =
    pr_opt_no_spc (pr_univ_annot (prlist_with_sep spc pr_glob_sort_instance)) l

  let pr_reference = function
  | Qualid (_, qid) -> pr_qualid qid
  | Ident (_, id) -> tag_var (pr_id id)

  let pr_cref ref us =
    pr_reference ref ++ pr_universe_instance us

  let pr_expl_args pr (a,expl) =
    match expl with
      | None -> pr (lapp,L) a
      | Some (_,ExplByPos (n,_id)) ->
        anomaly (Pp.str "Explicitation by position not implemented.")
      | Some (_,ExplByName id) ->
        str "(" ++ pr_id id ++ str ":=" ++ pr ltop a ++ str ")"

  let pr_opt_type_spc pr = function
    | { CAst.v = CHole (_,Misctypes.IntroAnonymous,_) } -> mt ()
    | t ->  str " :" ++ pr_sep_com (fun()->brk(1,2)) (pr ltop) t

  let pr_lident (loc,id) =
    match loc with
    | None     -> pr_id id
    | Some loc -> let (b,_) = Loc.unloc loc in
                  pr_located pr_id @@ Loc.tag ~loc:(Loc.make_loc (b,b + String.length (Id.to_string id))) id

  let pr_lname = function
    | (loc,Name id) -> pr_lident (loc,id)
    | lna -> pr_located Name.print lna

  let pr_or_var pr = function
    | ArgArg x -> pr x
    | ArgVar (loc,s) -> pr_lident (loc,s)

  let pr_prim_token = function
    | Numeral (n,s) -> str (if s then n else "-"^n)
    | String s -> qs s

  let pr_evar pr id l =
    hov 0 (
      tag_evar (str "?" ++ pr_id id) ++
        (match l with
          | [] -> mt()
          | l ->
            let f (id,c) = pr_id id ++ str ":=" ++ pr ltop c in
            str"@{" ++ hov 0 (prlist_with_sep pr_semicolon f (List.rev l)) ++ str"}"))

  let las = lapp
  let lpator = 100
  let lpatrec = 0

  let rec pr_patt sep inh p =
    let (strm,prec) = match CAst.(p.v) with
      | CPatRecord l ->
        let pp (c, p) =
          pr_reference c ++ spc() ++ str ":=" ++ pr_patt spc (lpatrec, Any) p
        in
        str "{| " ++ prlist_with_sep pr_semicolon pp l ++ str " |}", lpatrec

      | CPatAlias (p, id) ->
        pr_patt mt (las,E) p ++ str " as " ++ pr_id id, las

      | CPatCstr (c, None, []) ->
        pr_reference c, latom

      | CPatCstr (c, None, args) ->
        pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp

      | CPatCstr (c, Some args, []) ->
        str "@" ++ pr_reference c ++ prlist (pr_patt spc (lapp,L)) args, lapp

      | CPatCstr (c, Some expl_args, extra_args) ->
        surround (str "@" ++ pr_reference c ++ prlist (pr_patt spc (lapp,L)) expl_args)
        ++ prlist (pr_patt spc (lapp,L)) extra_args, lapp

      | CPatAtom (None) ->
        str "_", latom

      | CPatAtom (Some r) ->
        pr_reference r, latom

      | CPatOr pl ->
        hov 0 (prlist_with_sep pr_bar (pr_patt spc (lpator,L)) pl), lpator

      | CPatNotation ("( _ )",([p],[]),[]) ->
        pr_patt (fun()->str"(") (max_int,E) p ++ str")", latom

      | CPatNotation (s,(l,ll),args) ->
        let strm_not, l_not = pr_notation (pr_patt mt) (fun _ _ _ -> mt()) s (l,ll,[]) in
        (if List.is_empty args||prec_less l_not (lapp,L) then strm_not else surround strm_not)
        ++ prlist (pr_patt spc (lapp,L)) args, if not (List.is_empty args) then lapp else l_not

      | CPatPrim p ->
        pr_prim_token p, latom

      | CPatDelimiters (k,p) ->
        pr_delimiters k (pr_patt mt lsimplepatt p), 1
      | CPatCast _ ->
        assert false
    in
    let loc = p.CAst.loc in
    pr_with_comments ?loc
      (sep() ++ if prec_less prec inh then strm else surround strm)

  let pr_patt = pr_patt mt

  let pr_eqn pr (loc,(pl,rhs)) =
    let pl = List.map snd pl in
    spc() ++ hov 4
      (pr_with_comments ?loc
         (str "| " ++
            hov 0 (prlist_with_sep pr_bar (prlist_with_sep sep_v (pr_patt ltop)) pl
                   ++ str " =>") ++
            pr_sep_com spc (pr ltop) rhs))

  let begin_of_binder l_bi = 
    let b_loc l = fst (Option.cata Loc.unloc (0,0) l) in
    match l_bi with
    | CLocalDef((loc,_),_,_) -> b_loc loc
    | CLocalAssum((loc,_)::_,_,_) -> b_loc loc
    | CLocalPattern(loc,(_,_)) -> b_loc loc
    | _ -> assert false

  let begin_of_binders = function
    | b::_ -> begin_of_binder b
    | _ -> 0

  let surround_impl k p =
    match k with
      | Explicit -> str"(" ++ p ++ str")"
      | Implicit -> str"{" ++ p ++ str"}"

  let surround_implicit k p =
    match k with
      | Explicit -> p
      | Implicit -> (str"{" ++ p ++ str"}")

  let pr_binder many pr (nal,k,t) =
    match k with
      | Generalized (b, b', t') ->
        assert (match b with Implicit -> true | _ -> false);
        begin match nal with
          |[loc,Anonymous] ->
            hov 1 (str"`" ++ (surround_impl b'
                                ((if t' then str "!" else mt ()) ++ pr t)))
          |[loc,Name id] ->
            hov 1 (str "`" ++ (surround_impl b'
                                 (pr_lident (loc,id) ++ str " : " ++
                                    (if t' then str "!" else mt()) ++ pr t)))
          |_ -> anomaly (Pp.str "List of generalized binders have alwais one element.")
        end
      | Default b ->
        match t with
          | { CAst.v = CHole (_,Misctypes.IntroAnonymous,_) } ->
            let s = prlist_with_sep spc pr_lname nal in
            hov 1 (surround_implicit b s)
          | _ ->
            let s = prlist_with_sep spc pr_lname nal ++ str " : " ++ pr t in
            hov 1 (if many then surround_impl b s else surround_implicit b s)

  let pr_binder_among_many pr_c = function
    | CLocalAssum (nal,k,t) ->
      pr_binder true pr_c (nal,k,t)
    | CLocalDef (na,c,topt) ->
      surround (pr_lname na ++
                pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr_c t) topt ++
                str" :=" ++ spc() ++ pr_c c)
    | CLocalPattern (loc,(p,tyo)) ->
      let p = pr_patt lsimplepatt p in
      match tyo with
        | None ->
          str "'" ++ p
        | Some ty ->
          str "'" ++ surround (p ++ spc () ++ str ":" ++ ws 1 ++ pr_c ty)

  let pr_undelimited_binders sep pr_c =
    prlist_with_sep sep (pr_binder_among_many pr_c)

  let pr_delimited_binders kw sep pr_c bl =
    let n = begin_of_binders bl in
    match bl with
      | [CLocalAssum (nal,k,t)] ->
        kw n ++ pr_binder false pr_c (nal,k,t)
      | (CLocalAssum _ | CLocalPattern _ | CLocalDef _) :: _ as bdl ->
        kw n ++ pr_undelimited_binders sep pr_c bdl
      | [] -> assert false

  let pr_binders_gen pr_c sep is_open =
    if is_open then pr_delimited_binders pr_com_at sep pr_c
    else pr_undelimited_binders sep pr_c

  let rec extract_prod_binders = let open CAst in function
  (*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_prod_binders c in
      if bl = [] then [], x else CLocalDef (na,b) :: bl, c*)
    | { v = CProdN ([],c) } ->
      extract_prod_binders c
    | { loc; v = CProdN ([[_,Name id],bk,t],
              { v = CCases (LetPatternStyle,None, [{ v = CRef (Ident (_,id'),None)},None,None],[(_,([_,[p]],b))])} ) }
         when Id.equal id id' && not (Id.Set.mem id (Topconstr.free_vars_of_constr_expr b)) ->
      let bl,c = extract_prod_binders b in
      CLocalPattern (loc, (p,None)) :: bl, c
    | { loc; v = CProdN ((nal,bk,t)::bl,c) } ->
      let bl,c = extract_prod_binders (CAst.make ?loc @@ CProdN(bl,c)) in
      CLocalAssum (nal,bk,t) :: bl, c
    | c -> [], c

  let rec extract_lam_binders ce = let open CAst in match ce.v with
  (*  | CLetIn (loc,na,b,c) as x ->
      let bl,c = extract_lam_binders c in
      if bl = [] then [], x else CLocalDef (na,b) :: bl, c*)
    | CLambdaN ([],c) ->
      extract_lam_binders c
    | CLambdaN ([[_,Name id],bk,t],
                { v = CCases (LetPatternStyle,None, [{ v = CRef (Ident (_,id'),None)},None,None],[(_,([_,[p]],b))])} )
         when Id.equal id id' && not (Id.Set.mem id (Topconstr.free_vars_of_constr_expr b)) ->
      let bl,c = extract_lam_binders b in
      CLocalPattern (ce.loc,(p,None)) :: bl, c
    | CLambdaN ((nal,bk,t)::bl,c) ->
      let bl,c = extract_lam_binders (CAst.make ?loc:ce.loc @@ CLambdaN(bl,c)) in
      CLocalAssum (nal,bk,t) :: bl, c
    | _ -> [], ce

  let split_lambda = CAst.with_loc_val (fun ?loc -> function
    | CLambdaN ([[na],bk,t],c) -> (na,t,c)
    | CLambdaN (([na],bk,t)::bl,c) -> (na,t, CAst.make ?loc @@ CLambdaN(bl,c))
    | CLambdaN ((na::nal,bk,t)::bl,c) -> (na,t, CAst.make ?loc @@ CLambdaN((nal,bk,t)::bl,c))
    | _ -> anomaly (Pp.str "ill-formed fixpoint body.")
    )

  let rename na na' t c =
    match (na,na') with
      | (_,Name id), (_,Name id') ->
        (na',t,Topconstr.replace_vars_constr_expr (Id.Map.singleton id id') c)
      | (_,Name id), (_,Anonymous) -> (na,t,c)
      | _ -> (na',t,c)

  let split_product na' = CAst.with_loc_val (fun ?loc -> function
    | CProdN ([[na],bk,t],c) -> rename na na' t c
    | CProdN (([na],bk,t)::bl,c) -> rename na na' t (CAst.make ?loc @@ CProdN(bl,c))
    | CProdN ((na::nal,bk,t)::bl,c) ->
      rename na na' t (CAst.make ?loc @@ CProdN((nal,bk,t)::bl,c))
    | _ -> anomaly (Pp.str "ill-formed fixpoint body.")
    )

  let rec split_fix n typ def =
    if Int.equal n 0 then ([],typ,def)
    else
      let (na,_,def) = split_lambda def in
      let (na,t,typ) = split_product na typ in
      let (bl,typ,def) = split_fix (n-1) typ def in
      (CLocalAssum ([na],default_binder_kind,t)::bl,typ,def)

  let pr_recursive_decl pr pr_dangling dangling_with_for id bl annot t c =
    let pr_body =
      if dangling_with_for then pr_dangling else pr in
    pr_id id ++ (if bl = [] then mt () else str" ") ++
      hov 0 (pr_undelimited_binders spc (pr ltop) bl ++ annot) ++
      pr_opt_type_spc pr t ++ str " :=" ++
      pr_sep_com (fun () -> brk(1,2)) (pr_body ltop) c

  let pr_guard_annot pr_aux bl (n,ro) =
    match n with
      | None -> mt ()
      | Some (loc, id) ->
        match (ro : Constrexpr.recursion_order_expr) with
          | CStructRec ->
            let names_of_binder = function
              | CLocalAssum (nal,_,_) -> nal
              | CLocalDef (_,_,_) -> []
              | CLocalPattern _ -> assert false
            in let ids = List.flatten (List.map names_of_binder bl) in
               if List.length ids > 1 then
                 spc() ++ str "{" ++ keyword "struct" ++ spc () ++ pr_id id ++ str"}"
               else mt()
          | CWfRec c ->
            spc() ++ str "{" ++ keyword "wf" ++ spc () ++ pr_aux c ++ spc() ++ pr_id id ++ str"}"
          | CMeasureRec (m,r) ->
            spc() ++ str "{" ++ keyword "measure" ++ spc () ++ pr_aux m ++ spc() ++ pr_id id++
              (match r with None -> mt() | Some r -> str" on " ++ pr_aux r) ++ str"}"

  let pr_fixdecl pr prd dangling_with_for ((_,id),ro,bl,t,c) =
    let annot = pr_guard_annot (pr lsimpleconstr) bl ro in
    pr_recursive_decl pr prd dangling_with_for id bl annot t c

  let pr_cofixdecl pr prd dangling_with_for ((_,id),bl,t,c) =
    pr_recursive_decl pr prd dangling_with_for id bl (mt()) t c

  let pr_recursive pr_decl id = function
    | [] -> anomaly (Pp.str "(co)fixpoint with no definition.")
    | [d1] -> pr_decl false d1
    | dl ->
      prlist_with_sep (fun () -> fnl() ++ keyword "with" ++ spc ())
        (pr_decl true) dl ++
        fnl() ++ keyword "for" ++ spc () ++ pr_id id

  let pr_asin pr na indnalopt =
    (match na with (* Decision of printing "_" or not moved to constrextern.ml *)
      | Some na -> spc () ++ keyword "as" ++ spc () ++  pr_lname na
      | None -> mt ()) ++
      (match indnalopt with
        | None -> mt ()
        | Some t -> spc () ++ keyword "in" ++ spc () ++ pr_patt lsimplepatt t)

  let pr_case_item pr (tm,as_clause, in_clause) =
    hov 0 (pr (lcast,E) tm ++ pr_asin pr as_clause in_clause)

  let pr_case_type pr po =
    match po with
      | None | Some { CAst.v = CHole (_,Misctypes.IntroAnonymous,_) } -> mt()
      | Some p ->
        spc() ++ hov 2 (keyword "return" ++ pr_sep_com spc (pr lsimpleconstr) p)

  let pr_simple_return_type pr na po =
    (match na with
      | Some (_,Name id) ->
        spc () ++ keyword "as" ++ spc () ++ pr_id id
      | _ -> mt ()) ++
      pr_case_type pr po

  let pr_proj pr pr_app a f l =
    hov 0 (pr (lproj,E) a ++ cut() ++ str ".(" ++ pr_app pr f l ++ str ")")

  let pr_appexpl pr (f,us) l =
    hov 2 (
      str "@" ++ pr_reference f ++
        pr_universe_instance us ++
        prlist (pr_sep_com spc (pr (lapp,L))) l)

  let pr_app pr a l =
    hov 2 (
      pr (lapp,L) a  ++
        prlist (fun a -> spc () ++ pr_expl_args pr a) l)

  let pr_record_body_gen pr l =
    spc () ++
    prlist_with_sep pr_semicolon
      (fun (id, c) -> h 1 (pr_reference id ++ spc () ++ str":=" ++ pr ltop c)) l

  let pr_forall n = keyword "forall" ++ pr_com_at n ++ spc ()

  let pr_fun n = keyword "fun" ++ pr_com_at n ++ spc ()

  let pr_fun_sep = spc () ++ str "=>"

  let pr_dangling_with_for sep pr inherited a =
    match a.CAst.v with
      | (CFix (_,[_])|CCoFix(_,[_])) ->
        pr sep (latom,E) a
      | _ ->
        pr sep inherited a

  let pr pr sep inherited a =
    let return (cmds, prec) = (tag_constr_expr a cmds, prec) in
    let (strm, prec) = match CAst.(a.v) with
      | CRef (r, us) ->
        return (pr_cref r us, latom)
      | CFix (id,fix) ->
        return (
          hov 0 (keyword "fix" ++ spc () ++
                   pr_recursive
                   (pr_fixdecl (pr mt) (pr_dangling_with_for mt pr)) (snd id) fix),
          lfix
        )
      | CCoFix (id,cofix) ->
        return (
          hov 0 (keyword "cofix" ++ spc () ++
                   pr_recursive
                   (pr_cofixdecl (pr mt) (pr_dangling_with_for mt pr)) (snd id) cofix),
          lfix
        )
      | CProdN _ ->
        let (bl,a) = extract_prod_binders a in
        return (
          hov 0 (
            hov 2 (pr_delimited_binders pr_forall spc
                     (pr mt ltop) bl) ++
              str "," ++ pr spc ltop a),
          lprod
        )
      | CLambdaN _ ->
        let (bl,a) = extract_lam_binders a in
        return (
          hov 0 (
            hov 2 (pr_delimited_binders pr_fun spc
                     (pr mt ltop) bl) ++
              pr_fun_sep ++ pr spc ltop a),
          llambda
        )
      | CLetIn ((_,Name x), ({ CAst.v = CFix((_,x'),[_])}
                          |  { CAst.v = CCoFix((_,x'),[_]) } as fx), t, b)
          when Id.equal x x' ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++ pr mt ltop fx
                   ++ spc ()
                   ++ keyword "in") ++
              pr spc ltop b),
          lletin
        )
      | CLetIn (x,a,t,b) ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++ pr_lname x
                   ++ pr_opt_no_spc (fun t -> str " :" ++ ws 1 ++ pr mt ltop t) t
                   ++ str " :=" ++ pr spc ltop a ++ spc ()
                   ++ keyword "in") ++
              pr spc ltop b),
          lletin
        )
      | CAppExpl ((Some i,f,us),l) ->
        let l1,l2 = List.chop i l in
        let c,l1 = List.sep_last l1 in
        let p = pr_proj (pr mt) pr_appexpl c (f,us) l1 in
        if not (List.is_empty l2) then
          return (p ++ prlist (pr spc (lapp,L)) l2, lapp)
        else
          return (p, lproj)
      | CAppExpl ((None,Ident (_,var),us),[t])
      | CApp ((_, {CAst.v = CRef(Ident(_,var),us)}),[t,None])
          when Id.equal var Notation_ops.ldots_var ->
        return (
          hov 0 (str ".." ++ pr spc (latom,E) t ++ spc () ++ str ".."),
          larg
        )
      | CAppExpl ((None,f,us),l) ->
        return (pr_appexpl (pr mt) (f,us) l, lapp)
      | CApp ((Some i,f),l) ->
        let l1,l2 = List.chop i l in
        let c,l1 = List.sep_last l1 in
        assert (Option.is_empty (snd c));
        let p = pr_proj (pr mt) pr_app (fst c) f l1 in
        if not (List.is_empty l2) then
          return (
            p ++ prlist (fun a -> spc () ++ pr_expl_args (pr mt) a) l2,
            lapp
          )
        else
          return (p, lproj)
      | CApp ((None,a),l) ->
        return (pr_app (pr mt) a l, lapp)
      | CRecord l ->
        return (
          hv 0 (str"{|" ++ pr_record_body_gen (pr spc) l ++ str" |}"),
          latom
        )
      | CCases (LetPatternStyle,rtntypopt,[c,as_clause,in_clause],[(_,([(loc,[p])],b))]) ->
        return (
          hv 0 (
            keyword "let" ++ spc () ++ str"'" ++
              hov 0 (pr_patt ltop p ++
                       pr_asin (pr_dangling_with_for mt pr) as_clause in_clause ++
                       str " :=" ++ pr spc ltop c ++
                       pr_case_type (pr_dangling_with_for mt pr) rtntypopt ++
                       spc () ++ keyword "in" ++ pr spc ltop b)),
          lletpattern
        )
      | CCases(_,rtntypopt,c,eqns) ->
        return (
          v 0
            (hv 0 (keyword "match" ++ brk (1,2) ++
                     hov 0 (
                       prlist_with_sep sep_v
                         (pr_case_item (pr_dangling_with_for mt pr)) c
                       ++ pr_case_type (pr_dangling_with_for mt pr) rtntypopt) ++
                     spc () ++ keyword "with") ++
               prlist (pr_eqn (pr mt)) eqns ++ spc()
             ++ keyword "end"),
          latom
        )
      | CLetTuple (nal,(na,po),c,b) ->
        return (
          hv 0 (
            hov 2 (keyword "let" ++ spc () ++
              hov 1 (str "(" ++
                       prlist_with_sep sep_v pr_lname nal ++
                       str ")" ++
                       pr_simple_return_type (pr mt) na po ++ str " :=") ++
                       pr spc ltop c
                     ++ keyword " in") ++
              pr spc ltop b),
          lletin
        )
      | CIf (c,(na,po),b1,b2) ->
      (* On force les parenthèses autour d'un "if" sous-terme (même si le
         parsing est lui plus tolérant) *)
        return (
          hv 0 (
            hov 1 (keyword "if" ++ spc () ++ pr mt ltop c
                   ++ pr_simple_return_type (pr mt) na po) ++
              spc () ++
              hov 0 (keyword "then"
                     ++ pr (fun () -> brk (1,1)) ltop b1) ++ spc () ++
              hov 0 (keyword "else" ++ pr (fun () -> brk (1,1)) ltop b2)),
        lif
        )

      | CHole (_,Misctypes.IntroIdentifier id,_) ->
        return (str "?[" ++ pr_id id ++ str "]", latom)
      | CHole (_,Misctypes.IntroFresh id,_) ->
        return (str "?[?" ++ pr_id id ++ str "]", latom)
      | CHole (_,_,_) ->
        return (str "_", latom)
      | CEvar (n,l) ->
        return (pr_evar (pr mt) n l, latom)
      | CPatVar p ->
        return (str "@?" ++ pr_patvar p, latom)
      | CSort s ->
        return (pr_glob_sort s, latom)
      | CCast (a,b) ->
        return (
          hv 0 (pr mt (lcast,L) a ++ spc () ++
                  match b with
                    | CastConv b -> str ":" ++ ws 1 ++ pr mt (-lcast,E) b
                    | CastVM b -> str "<:" ++ ws 1 ++ pr mt (-lcast,E) b
                    | CastNative b -> str "<<:" ++ ws 1 ++ pr mt (-lcast,E) b
                    | CastCoerce -> str ":>"),
          lcast
        )
      | CNotation ("( _ )",([t],[],[])) ->
        return (pr (fun()->str"(") (max_int,L) t ++ str")", latom)
      | CNotation (s,env) ->
        pr_notation (pr mt) (pr_binders_gen (pr mt ltop)) s env
      | CGeneralization (bk,ak,c) ->
        return (pr_generalization bk ak (pr mt ltop c), latom)
      | CPrim p ->
        return (pr_prim_token p, prec_of_prim_token p)
      | CDelimiters (sc,a) ->
        return (pr_delimiters sc (pr mt (ldelim,E) a), ldelim)
    in
    let loc = constr_loc a in
    pr_with_comments ?loc
      (sep() ++ if prec_less prec inherited then strm else surround strm)

  type term_pr = {
    pr_constr_expr   : constr_expr -> Pp.t;
    pr_lconstr_expr  : constr_expr -> Pp.t;
    pr_constr_pattern_expr  : constr_pattern_expr -> Pp.t;
    pr_lconstr_pattern_expr : constr_pattern_expr -> Pp.t
  }

  type precedence =  Notation_term.precedence * Notation_term.parenRelation
  let modular_constr_pr = pr
  let rec fix rf x = rf (fix rf) x
  let pr = fix modular_constr_pr mt

  let transf env c =
    if !Flags.beautify_file then
      let r = Constrintern.for_grammar (Constrintern.intern_constr env) c in
      Constrextern.extern_glob_constr (Termops.vars_of_env env) r
    else c

  let pr prec c = pr prec (transf (Global.env()) c)

  let pr_simpleconstr = function
    | { CAst.v = CAppExpl ((None,f,us),[]) } -> str "@" ++ pr_cref f us
    | c -> pr lsimpleconstr c

  let default_term_pr = {
    pr_constr_expr   = pr_simpleconstr;
    pr_lconstr_expr  = pr ltop;
    pr_constr_pattern_expr  = pr_simpleconstr;
    pr_lconstr_pattern_expr = pr ltop
  }

  let term_pr = ref default_term_pr

  let set_term_pr = (:=) term_pr

  let pr_constr_expr c   = !term_pr.pr_constr_expr   c
  let pr_lconstr_expr c  = !term_pr.pr_lconstr_expr  c
  let pr_constr_pattern_expr c  = !term_pr.pr_constr_pattern_expr  c
  let pr_lconstr_pattern_expr c = !term_pr.pr_lconstr_pattern_expr c

  let pr_cases_pattern_expr = pr_patt ltop

  let pr_record_body = pr_record_body_gen pr

  let pr_binders = pr_undelimited_binders spc (pr ltop)

