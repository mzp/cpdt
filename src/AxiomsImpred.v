(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Additional axioms not in the Coq standard library, including those that need impredicativity *)

Set Implicit Arguments.

Require Import Axioms.
Export Axioms.

Theorem ext_eq_forall_Set : forall (A : Type)
  (f g : A -> Set),
  (forall x, f x = g x)
  -> @eq Set (forall x, f x) (forall x, g x).
  intros.
  rewrite (ext_eq _ _ _ H); trivial.
Qed.

Ltac ext_eq := (apply ext_eq || apply ext_eq_Set
  || apply ext_eq_forall || apply ext_eq_forall_Set); intro.
