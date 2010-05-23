(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Additional axioms not in the Coq standard library *)

Set Implicit Arguments.

Axiom ext_eq : forall (A : Type) (B : A -> Type)
  (f g : forall x, B x),
  (forall x, f x = g x)
  -> f = g.

Theorem ext_eq_Set : forall (A : Set) (B : A -> Set)
  (f g : forall x, B x),
  (forall x, f x = g x)
  -> f = g.
  intros.
  rewrite (ext_eq _ _ _ H); reflexivity.
Qed.

Theorem ext_eq_forall : forall (A : Type)
  (f g : A -> Set),
  (forall x, f x = g x)
  -> @eq Type (forall x, f x) (forall x, g x).
  intros.
  rewrite (ext_eq _ _ _ H); trivial.
Qed.

Ltac ext_eq := (apply ext_eq || apply ext_eq_Set
  || apply ext_eq_forall); intro.


Theorem eta : forall (A B : Type) (f : A -> B),
  (fun x => f x) = f.
  intros; ext_eq; trivial.
Qed.
