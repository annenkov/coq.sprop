(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** We can take advantage of non-cumulativity of SProp to avoid fully
   retyping terms when we just want to know if they inhabit some
   proof-irrelevant type. *)

val relevance_of_term : Environ.env -> Constr.constr -> Sorts.relevance

val relevance_of_fterm : Environ.env -> Sorts.relevance list ->
  Esubst.lift -> CClosure.fconstr ->
  Sorts.relevance
