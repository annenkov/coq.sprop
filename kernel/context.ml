(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of names.ml as part of the
   rebuilding of Coq around a purely functional abstract type-checker,
   Aug 1999 *)
(* Miscellaneous extensions, restructurations and bug-fixes by Hugo
   Herbelin and Bruno Barras *)

(* This file defines types and combinators regarding indexes-based and
   names-based contexts *)

(** The modules defined below represent a {e local context}
    as defined by Chapter 4 in the Reference Manual:

    A {e local context} is an ordered list of of {e local declarations}
    of names that we call {e variables}.

    A {e local declaration} of some variable can be either:
    - a {e local assumption}, or
    - a {e local definition}.
*)

open Util
open Names

(** Representation of contexts that can capture anonymous as well as non-anonymous variables.
    Individual declarations are then designated by de Bruijn indexes. *)
module Rel =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (* local declaration *)
    type ('constr, 'types) pt =
      | LocalAssum of Name.t * Sorts.relevance * 'types            (** name, type *)
      | LocalDef of Name.t * Sorts.relevance * 'constr * 'types   (** name, value, type *)

    type t = (Constr.constr, Constr.types) pt

    (** Return the name bound by a given declaration. *)
    let get_name = function
      | LocalAssum (na,_,_)
      | LocalDef (na,_,_,_) -> na

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,_,v,_) -> Some v
                                 
    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,_,ty)
      | LocalDef (_,_,_,ty) -> ty

    let get_relevance = function
      | LocalAssum (_,r,_)
      | LocalDef (_,r,_,_) -> r

    (** Set the name that is bound by a given declaration. *)
    let set_name na = function
      | LocalAssum (_,r,ty) -> LocalAssum (na, r, ty)
      | LocalDef (_,r,v,ty) -> LocalDef (na, r, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (na,r,_) -> LocalAssum (na, r, ty)
      | LocalDef (na,r,v,_) -> LocalDef (na, r, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalAssum _ -> false
      | LocalDef _ -> true

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, _, ty) -> f ty
      | LocalDef (_, _, v, ty) -> f v || f ty

      (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, _, ty) -> f ty
      | LocalDef (_, _, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (n1,r1,ty1), LocalAssum (n2, r2, ty2) ->
          Name.equal n1 n2 && r1 == r2 && eq ty1 ty2
      | LocalDef (n1,r1,v1,ty1), LocalDef (n2,r2,v2,ty2) ->
          Name.equal n1 n2 && r1 == r2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** Map the name bound by a given declaration. *)
    let map_name f = function
      | LocalAssum (na, r, ty) as decl ->
          let na' = f na in
          if na == na' then decl else LocalAssum (na', r, ty)
      | LocalDef (na, r, v, ty) as decl ->
          let na' = f na in
          if na == na' then decl else LocalDef (na', r, v, ty)

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, r, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, r, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (na, r, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, r, ty')
      | LocalDef (na, r, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (na, r, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (na, r, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, r, ty')
      | LocalDef (na, r, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (na, r, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_,_,ty) -> f ty
      | LocalDef (_,_,v,ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl acc =
      match decl with
      | LocalAssum (n,_,ty) -> f ty acc
      | LocalDef (n,_,v,ty) -> f ty (f v acc)

    let to_tuple = function
      | LocalAssum (na, r, ty) -> na, r, None, ty
      | LocalDef (na, r, v, ty) -> na, r, Some v, ty

  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list
  type t = Declaration.t list

  (** empty rel-context *)
  let empty = []

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  let add d ctx = d :: ctx

  (** Return the number of {e local declarations} in a given context. *)
  let length = List.length

  (** [extended_rel_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the local definitions of [Γ] skipped in
      [args]. Example: for [x:T,y:=c,z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
  let nhyps ctx =
    let open Declaration in
    let rec nhyps acc = function
      | [] -> acc
      | LocalAssum _ :: hyps -> nhyps (succ acc) hyps
      | LocalDef _ :: hyps -> nhyps acc hyps
    in
    nhyps 0 ctx

  (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index is not present in the designated rel-context. *)
  let rec lookup n ctx =
    match n, ctx with
    | 1, decl :: _ -> decl
    | n, _ :: sign -> lookup (n-1) sign
    | _, []        -> raise Not_found

  (** Check whether given two rel-contexts are equal. *)
  let equal eq l = List.equal (fun c -> Declaration.equal eq c) l

  (** Map all terms in a given rel-context. *)
  let map f = List.smartmap (Declaration.map_constr f)

  (** Perform a given action on every declaration in a given rel-context. *)
  let iter f = List.iter (Declaration.iter_constr f)

  (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init = List.fold_left f init

  (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f l ~init = List.fold_right f l init

  (** Map a given rel-context to a list where each {e local assumption} is mapped to [true]
      and each {e local definition} is mapped to [false]. *)
  let to_tags l =
    let rec aux l = function
      | [] -> l
      | Declaration.LocalDef _ :: ctx -> aux (true::l) ctx
      | Declaration.LocalAssum _ :: ctx -> aux (false::l) ctx
    in aux [] l

  (** [extended_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the {e local definitions} of [Γ] skipped in
      [args]. Example: for [x:T, y:=c, z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
  let to_extended_list mk n l =
    let rec reln l p = function
      | Declaration.LocalAssum _ :: hyps -> reln (mk (n+p) :: l) (p+1) hyps
      | Declaration.LocalDef _ :: hyps -> reln l (p+1) hyps
      | [] -> l
    in
    reln [] 1 l

  (** [extended_vect n Γ] does the same, returning instead an array. *)
  let to_extended_vect mk n hyps = Array.of_list (to_extended_list mk n hyps)
end

(** This module represents contexts that can capture non-anonymous variables.
    Individual declarations are then designated by the identifiers they bind. *)
module Named =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (** local declaration *)
    type ('constr, 'types) pt =
      | LocalAssum of Id.t * Sorts.relevance * 'types             (** identifier, type *)
      | LocalDef of Id.t * Sorts.relevance * 'constr * 'types    (** identifier, value, type *)

    type t = (Constr.constr, Constr.types) pt

    (** Return the identifier bound by a given declaration. *)
    let get_id = function
      | LocalAssum (id,_,_) -> id
      | LocalDef (id,_,_,_) -> id

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,_,v,_) -> Some v

    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,_,ty)
      | LocalDef (_,_,_,ty) -> ty

    let get_relevance = function
      | LocalAssum (_,r,_)
      | LocalDef (_,r,_,_) -> r

    (** Set the identifier that is bound by a given declaration. *)
    let set_id id = function
      | LocalAssum (_,r,ty) -> LocalAssum (id, r, ty)
      | LocalDef (_, r, v, ty) -> LocalDef (id, r, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (id,r,_) -> LocalAssum (id, r, ty)
      | LocalDef (id,r,v,_) -> LocalDef (id, r, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalDef _ -> true
      | LocalAssum _ -> false

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, _, ty) -> f ty
      | LocalDef (_, _, v, ty) -> f v || f ty

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, _, ty) -> f ty
      | LocalDef (_, _, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (id1, r1, ty1), LocalAssum (id2, r2, ty2) ->
          Id.equal id1 id2 && r1 == r2 && eq ty1 ty2
      | LocalDef (id1, r1, v1, ty1), LocalDef (id2, r2, v2, ty2) ->
          Id.equal id1 id2 && r1 == r2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** Map the identifier bound by a given declaration. *)
    let map_id f = function
      | LocalAssum (id, r, ty) as decl ->
          let id' = f id in
          if id == id' then decl else LocalAssum (id', r, ty)
      | LocalDef (id, r, v, ty) as decl ->
          let id' = f id in
          if id == id' then decl else LocalDef (id', r, v, ty)

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, r, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, r, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (id, r, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, r, ty')
      | LocalDef (id, r, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (id, r, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (id, r, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, r, ty')
      | LocalDef (id, r, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (id, r, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_, _, ty) -> f ty
      | LocalDef (_, _, v, ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl a =
      match decl with
      | LocalAssum (_, _, ty) -> f ty a
      | LocalDef (_, _, v, ty) -> a |> f v |> f ty

    let to_tuple = function
      | LocalAssum (id, r, ty) -> id, r, None, ty
      | LocalDef (id, r, v, ty) -> id, r, Some v, ty

    let of_tuple = function
      | id, r, None, ty -> LocalAssum (id, r, ty)
      | id, r, Some v, ty -> LocalDef (id, r, v, ty)

    let of_rel_decl f = function
      | Rel.Declaration.LocalAssum (na,r,t) ->
          LocalAssum (f na, r, t)
      | Rel.Declaration.LocalDef (na,r,v,t) ->
          LocalDef (f na, r, v, t)
            
    let to_rel_decl = function
      | LocalAssum (id,r,t) ->
          Rel.Declaration.LocalAssum (Name id, r, t)
      | LocalDef (id,r,v,t) ->
          Rel.Declaration.LocalDef (Name id,r,v,t)
  end

  (** Named-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list
  type t = Declaration.t list

  (** empty named-context *)
  let empty = []

  (** empty named-context *)
  let add d ctx = d :: ctx

  (** Return the number of {e local declarations} in a given named-context. *)
  let length = List.length

(** Return a declaration designated by a given identifier
    @raise Not_found if the designated identifier is not present in the designated named-context. *)
  let rec lookup id = function
    | decl :: _ when Id.equal id (Declaration.get_id decl) -> decl
    | _ :: sign -> lookup id sign
    | [] -> raise Not_found

  (** Check whether given two named-contexts are equal. *)
  let equal eq l = List.equal (fun c -> Declaration.equal eq c) l

  (** Map all terms in a given named-context. *)
  let map f = List.smartmap (Declaration.map_constr f)

  (** Perform a given action on every declaration in a given named-context. *)
  let iter f = List.iter (Declaration.iter_constr f)

  (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init = List.fold_left f init

  (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f l ~init = List.fold_right f l init

  (** Return the set of all identifiers bound in a given named-context. *)
  let to_vars l =
    List.fold_left (fun accu decl -> Id.Set.add (Declaration.get_id decl) accu) Id.Set.empty l

  (** [instance_from_named_context Ω] builds an instance [args] such
      that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  let to_instance mk l =
    let filter = function
      | Declaration.LocalAssum (id, _, _) -> Some (mk id)
      | _ -> None
    in
    List.map_filter filter l
end

module Compacted =
  struct
    module Declaration =
      struct
        type ('constr, 'types) pt =
          | LocalAssum of (Id.t * Sorts.relevance) list * 'types
          | LocalDef of (Id.t * Sorts.relevance) list * 'constr * 'types

        type t = (Constr.constr, Constr.types) pt

        let map_constr f = function
          | LocalAssum (ids, ty) as decl ->
             let ty' = f ty in
             if ty == ty' then decl else LocalAssum (ids, ty')
          | LocalDef (ids, c, ty) as decl ->
             let ty' = f ty in
             let c' = f c in
             if c == c' && ty == ty' then decl else LocalDef (ids,c',ty')

        let of_named_decl = function
          | Named.Declaration.LocalAssum (id,r,t) ->
              LocalAssum ([id,r],t)
          | Named.Declaration.LocalDef (id,r,v,t) ->
              LocalDef ([id,r],v,t)

        let to_named_context = function
          | LocalAssum (ids, t) ->
             List.map (fun (id,r) -> Named.Declaration.LocalAssum (id,r,t)) ids
          | LocalDef (ids, v, t) ->
             List.map (fun (id,r) -> Named.Declaration.LocalDef (id,r,v,t)) ids
      end

    type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list
    type t = Declaration.t list

    let fold f l ~init = List.fold_right f l init
  end
