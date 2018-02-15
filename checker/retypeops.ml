(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Cic
open Environ

let get_relevance = function
  | LocalAssum (_,r,_) | LocalDef (_,r,_,_) -> r

let relevance_of_rel env n =
  let decl = lookup_rel n env in
  get_relevance decl

let relevance_of_constant env (c,_) =
  let decl = lookup_constant c env in
  decl.const_relevance

let relevance_of_constructor env (((mi,i),_),_) =
  let decl = lookup_mind mi env in
  let packet = decl.mind_packets.(i) in
  packet.mind_relevant

let relevance_of_projection env p =
  let pb = lookup_projection p env in
  pb.proj_relevance

let rec relevance_of_rel_extra env extra n =
  match extra with
  | [] -> relevance_of_rel env n
  | r :: _ when Int.equal n 1 -> r
  | _ :: extra -> relevance_of_rel_extra env extra (n-1)

let relevance_of_flex env extra lft = function
  | ConstKey c -> relevance_of_constant env c
  | VarKey x -> assert false
  | RelKey p -> relevance_of_rel_extra env extra (Esubst.reloc_rel p lft)

let rec relevance_of_fterm env extra lft f =
  let open Closure in
  match fterm_of f with
  | FRel n -> relevance_of_rel_extra env extra (Esubst.reloc_rel n lft)
  | FAtom c -> relevance_of_term_extra env extra lft (Esubst.subs_id 0) c
  | FCast (c, _, _) -> relevance_of_fterm env extra lft c
  | FFlex key -> relevance_of_flex env extra lft key
  | FInd _ -> Relevant
  | FConstruct c -> relevance_of_constructor env c
  | FApp (f, _) -> relevance_of_fterm env extra lft f
  | FProj (p, _) -> relevance_of_projection env p
  | FFix (((_,i),(_,lr,_,_)), _) -> lr.(i)
  | FCoFix ((i,(_,lr,_,_)), _) -> lr.(i)
  | FCaseT (ci, _, _, _, _) -> ci.ci_relevance
  | FCaseInvert (_, _, _, _, _, _) -> Relevant
  | FLambda (len, tys, bdy, e) ->
    (* TODO check order *)
    let extra = List.rev_append (List.rev_map pi2 tys) extra in
    let lft = Esubst.el_liftn len lft in
    relevance_of_term_extra env extra lft e bdy
  | FProd (_, r, _, codom) ->
    let extra = r :: extra in
    let lft = Esubst.el_lift lft in
    relevance_of_fterm env extra lft codom
  | FLetIn (_, r, _, _, bdy, e) ->
    relevance_of_term_extra env (r :: extra) (Esubst.el_lift lft) (Esubst.subs_lift e) bdy
  | FLIFT (k, f) -> relevance_of_fterm env extra (Esubst.el_shft k lft) f
  | FCLOS (c, e) -> relevance_of_term_extra env extra lft e c

  | FEvar (_, _) -> Relevant (* let's assume evars are relevant for now *)
  | FLOCKED -> assert false

and relevance_of_term_extra env extra lft subs c =
  match c with
  | Rel n ->
    (match Esubst.expand_rel n subs with
     | Inl (k, f) -> relevance_of_fterm env extra (Esubst.el_liftn k lft) f
     | Inr (n, _) -> relevance_of_rel_extra env extra (Esubst.reloc_rel n lft))
  | Var x -> assert false
  | Sort _ -> Relevant
  | Cast (c, _, _) -> relevance_of_term_extra env extra lft subs c
  | Prod (_, r, _, codom) ->
    relevance_of_term_extra env (r::extra) (Esubst.el_lift lft) (Esubst.subs_lift subs) codom
  | Lambda (_, r, _, bdy) ->
    relevance_of_term_extra env (r::extra) (Esubst.el_lift lft) (Esubst.subs_lift subs) bdy
  | LetIn (_, r, _, _, bdy) ->
    relevance_of_term_extra env (r::extra) (Esubst.el_lift lft) (Esubst.subs_lift subs) bdy
  | App (c, _) -> relevance_of_term_extra env extra lft subs c
  | Const c -> relevance_of_constant env c
  | Ind _ -> Relevant
  | Construct c -> relevance_of_constructor env c
  | Case (ci, _, _, _, _) -> ci.ci_relevance
  | Fix ((_,i),(_,lr,_,_)) -> lr.(i)
  | CoFix (i,(_,lr,_,_)) -> lr.(i)
  | Proj (p, _) -> relevance_of_projection env p

  | Meta _ | Evar _ -> Relevant (* let's assume metas and evars are relevant for now *)
