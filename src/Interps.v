(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import String List.

Require Import Axioms Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Type-Theoretic Interpreters}% *)

(** Throughout this book, we have given semantics for programming languages via executable interpreters written in Gallina.  PHOAS is quite compatible with that model, when we want to formalize many of the wide variety of interesting non-Turing-complete programming languages.  Most such languages have very straightforward elaborations into Gallina.  In this chapter, we show how to extend our past approach to higher-order languages encoded with PHOAS, and we show how simple program transformations may be proved correct with respect to these elaborative semantics. *)


(** * Simply-Typed Lambda Calculus *)

(** We begin with a copy of last chapter's encoding of the syntax of simply-typed lambda calculus with natural numbers and addition.  The primes at the ends of constructor names are gone, since here our primary subject is [exp]s instead of [Exp]s. *)

Module STLC.
  Inductive type : Type :=
  | Nat : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

  Section vars.
    Variable var : type -> Type.

    Inductive exp : type -> Type :=
    | Var : forall t,
      var t
      -> exp t

    | Const : nat -> exp Nat
    | Plus : exp Nat -> exp Nat -> exp Nat

    | App : forall t1 t2,
      exp (t1 --> t2)
      -> exp t1
      -> exp t2
    | Abs : forall t1 t2,
      (var t1 -> exp t2)
      -> exp (t1 --> t2).
  End vars.

  Definition Exp t := forall var, exp var t.

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments Plus [var].
  Implicit Arguments App [var t1 t2].
  Implicit Arguments Abs [var t1 t2].

  (** The definitions that follow will be easier to read if we define some parsing notations for the constructors. *)

  Notation "# v" := (Var v) (at level 70).

  Notation "^ n" := (Const n) (at level 70).
  Infix "+^" := Plus (left associativity, at level 79).

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

  (** A few examples will be useful for testing the functions we will write. *)

  Example zero : Exp Nat := fun _ => ^0.
  Example one : Exp Nat := fun _ => ^1.
  Example zpo : Exp Nat := fun _ => zero _ +^ one _.
  Example ident : Exp (Nat --> Nat) := fun _ => \x, #x.
  Example app_ident : Exp Nat := fun _ => ident _ @ zpo _.
  Example app : Exp ((Nat --> Nat) --> Nat --> Nat) := fun _ => \f, \x, #f @ #x.
  Example app_ident' : Exp Nat := fun _ => app _ @ ident _ @ zpo _.

  (* EX: Define an interpreter for [Exp]s. *)

(* begin thide *)
  (** To write our interpreter, we must first interpret object language types as meta language types. *)

  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
    end.

  (** The crucial trick of the expression interpreter is to represent variables using the [typeDenote] function.  Due to limitations in Coq's syntax extension system, we cannot take advantage of some of our notations when they appear in patterns, so, to be consistent, in patterns we avoid notations altogether. *)

  Fixpoint expDenote t (e : exp typeDenote t) : typeDenote t :=
    match e with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).
(* end thide *)

  (** Some tests establish that [ExpDenote] produces Gallina terms like we might write manually. *)

  Eval compute in ExpDenote zero.
  (** %\vspace{-.15in}% [[
     = 0
     : typeDenote Nat
     ]] *)

  Eval compute in ExpDenote one.
  (** %\vspace{-.15in}% [[
     = 1
     : typeDenote Nat
     ]] *)

  Eval compute in ExpDenote zpo.
  (** %\vspace{-.15in}% [[
     = 1
     : typeDenote Nat
     ]] *)

  Eval compute in ExpDenote ident.
  (** %\vspace{-.15in}% [[
     = fun x : nat => x
     : typeDenote (Nat --> Nat)
     ]] *)

  Eval compute in ExpDenote app_ident.
  (** %\vspace{-.15in}% [[
     = 1
     : typeDenote Nat
     ]] *)

  Eval compute in ExpDenote app.
  (** %\vspace{-.15in}% [[
     = fun (x : nat -> nat) (x0 : nat) => x x0
     : typeDenote ((Nat --> Nat) --> Nat --> Nat)
     ]] *)

  Eval compute in ExpDenote app_ident'.
  (** %\vspace{-.15in}% [[
     = 1
     : typeDenote Nat
     ]] *)


  (* EX: Define a constant-folding function for [Exp]s. *)

  (** We can update to the higher-order case our common example of a constant folding function.  The workhorse function [cfold] is parameterized to apply to an [exp] that uses any [var] type.  An output of [cfold] uses the same [var] type as the input.  As in the definition of [expDenote], we cannot use most of our notations in patterns, but we use them freely to make the bodies of [match] cases easier to read. *)

(* begin thide *)
  Section cfold.
    Variable var : type -> Type.

    Fixpoint cfold t (e : exp var t) : exp var t :=
      match e with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' return _ with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' +^ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => \x, cfold (e' x)
      end.
  End cfold.

  Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).
(* end thide *)

  (* EX: Prove the correctness of constant-folding. *)

  (** Now we would like to prove the correctness of [Cfold], which follows from a simple inductive lemma about [cfold]. *)

(* begin thide *)
  Lemma cfold_correct : forall t (e : exp _ t),
    expDenote (cfold e) = expDenote e.
    induction e; crush; try (ext_eq; crush);
      repeat (match goal with
                | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
              end; crush).
  Qed.

  Theorem Cfold_correct : forall t (E : Exp t),
    ExpDenote (Cfold E) = ExpDenote E.
    unfold ExpDenote, Cfold; intros; apply cfold_correct.
  Qed.
(* end thide *)
End STLC.


(** * Adding Products and Sums *)

(** The example is easily adapted to support products and sums, the basis of non-recursive datatypes in ML and Haskell. *)

Module PSLC.
  (* EX: Extend the development with products and sums. *)

(* begin thide *)
  Inductive type : Type :=
  | Nat : type
  | Arrow : type -> type -> type
  | Prod : type -> type -> type
  | Sum : type -> type -> type.
(* end thide *)

  Infix "-->" := Arrow (right associativity, at level 62).
  Infix "**" := Prod (right associativity, at level 61).
  Infix "++" := Sum (right associativity, at level 60).

(* begin thide *)
  Section vars.
    Variable var : type -> Type.

    Inductive exp : type -> Type :=
    | Var : forall t,
      var t
      -> exp t

    | Const : nat -> exp Nat
    | Plus : exp Nat -> exp Nat -> exp Nat

    | App : forall t1 t2,
      exp (t1 --> t2)
      -> exp t1
      -> exp t2
    | Abs : forall t1 t2,
      (var t1 -> exp t2)
      -> exp (t1 --> t2)

    | Pair : forall t1 t2,
      exp t1
      -> exp t2
      -> exp (t1 ** t2)
    | Fst : forall t1 t2,
      exp (t1 ** t2)
      -> exp t1
    | Snd : forall t1 t2,
      exp (t1 ** t2)
      -> exp t2

    | Inl : forall t1 t2,
      exp t1
      -> exp (t1 ++ t2)
    | Inr : forall t1 t2,
      exp t2
      -> exp (t1 ++ t2)
    | SumCase : forall t1 t2 t,
      exp (t1 ++ t2)
      -> (var t1 -> exp t)
      -> (var t2 -> exp t)
      -> exp t.
  End vars.

  Definition Exp t := forall var, exp var t.
(* end thide *)

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments Abs [var t1 t2].
  Implicit Arguments Inl [var t1 t2].
  Implicit Arguments Inr [var t1 t2].

  Notation "# v" := (Var v) (at level 70).

  Notation "^ n" := (Const n) (at level 70).
  Infix "+^" := Plus (left associativity, at level 78).

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

  Notation "[ e1 , e2 ]" := (Pair e1 e2).
  Notation "#1 e" := (Fst e) (at level 75).
  Notation "#2 e" := (Snd e) (at level 75).

  Notation "'case' e 'of' x => e1 | y => e2" := (SumCase e (fun x => e1) (fun y => e2))
    (at level 79).

  (** A few examples can be defined easily, using the notations above. *)

  Example swap : Exp (Nat ** Nat --> Nat ** Nat) := fun _ => \p, [#2 #p, #1 #p].
  Example zo : Exp (Nat ** Nat) := fun _ => [^0, ^1].
  Example swap_zo : Exp (Nat ** Nat) := fun _ => swap _ @ zo _.

  Example natOut : Exp (Nat ++ Nat --> Nat) := fun _ =>
    \s, case #s of x => #x | y => #y +^ #y.
  Example ns1 : Exp (Nat ++ Nat) := fun _ => Inl (^3).
  Example ns2 : Exp (Nat ++ Nat) := fun _ => Inr (^5).
  Example natOut_ns1 : Exp Nat := fun _ => natOut _ @ ns1 _.
  Example natOut_ns2 : Exp Nat := fun _ => natOut _ @ ns2 _.

  (** The semantics adapts without incident. *)

(* begin thide *)
  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
      | t1 ** t2 => typeDenote t1 * typeDenote t2
      | t1 ++ t2 => typeDenote t1 + typeDenote t2
    end%type.

  Fixpoint expDenote t (e : exp typeDenote t) : typeDenote t :=
    match e with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)

      | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
      | Fst _ _ e' => fst (expDenote e')
      | Snd _ _ e' => snd (expDenote e')

      | Inl _ _ e' => inl _ (expDenote e')
      | Inr _ _ e' => inr _ (expDenote e')
      | SumCase _ _ _ e' e1 e2 =>
        match expDenote e' with
          | inl v => expDenote (e1 v)
          | inr v => expDenote (e2 v)
        end
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).
(* end thide *)

  Eval compute in ExpDenote swap.
  (** %\vspace{-.15in}% [[
     = fun x : nat * nat => (let (_, y) := x in y, let (x0, _) := x in x0)
     : typeDenote (Nat ** Nat --> Nat ** Nat)
     ]] *)

  Eval compute in ExpDenote zo.
  (** %\vspace{-.15in}% [[
     = (0, 1)
     : typeDenote (Nat ** Nat)
     ]] *)

  Eval compute in ExpDenote swap_zo.
  (** %\vspace{-.15in}% [[
     = (1, 0)
     : typeDenote (Nat ** Nat)
     ]] *)

  Eval cbv beta iota delta -[plus] in ExpDenote natOut.
  (** %\vspace{-.15in}% [[
     = fun x : nat + nat => match x with
                            | inl v => v
                            | inr v => v + v
                            end
     : typeDenote (Nat ++ Nat --> Nat)
     ]] *)

  Eval compute in ExpDenote ns1.
  (** %\vspace{-.15in}% [[
     = inl nat 3
     : typeDenote (Nat ++ Nat)
     ]] *)

  Eval compute in ExpDenote ns2.
  (** %\vspace{-.15in}% [[
     = inr nat 5
     : typeDenote (Nat ++ Nat)
     ]] *)

  Eval compute in ExpDenote natOut_ns1.
  (** %\vspace{-.15in}% [[
     = 3
     : typeDenote Nat
     ]] *)

  Eval compute in ExpDenote natOut_ns2.
  (** %\vspace{-.15in}% [[
     = 10
     : typeDenote Nat
     ]] *)

  (** We adapt the [cfold] function using the same basic dependent-types trick that we applied in an earlier chapter to a very similar function for a language without variables. *)

(* begin thide *)
  Section cfold.
    Variable var : type -> Type.

    Definition pairOutType t :=
      match t return Type with
        | t1 ** t2 => option (exp var t1 * exp var t2)
        | _ => unit
      end.

    Definition pairOutDefault (t : type) : pairOutType t :=
      match t with
        | _ ** _ => None
        | _ => tt
      end.

    Definition pairOut t1 t2 (e : exp var (t1 ** t2))
      : option (exp var t1 * exp var t2) :=
      match e in exp _ t return pairOutType t with
        | Pair _ _ e1 e2 => Some (e1, e2)
        | _ => pairOutDefault _
      end.

    Fixpoint cfold t (e : exp var t) : exp var t :=
      match e with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' return _ with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' +^ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => \x, cfold (e' x)

        | Pair _ _ e1 e2 => [cfold e1, cfold e2]
        | Fst t1 _ e' =>
          let e'' := cfold e' in
            match pairOut e'' with
              | None => #1 e''
              | Some (e1, _) => e1
            end
        | Snd _ _ e' =>
          let e'' := cfold e' in
            match pairOut e'' with
              | None => #2 e''
              | Some (_, e2) => e2
            end

        | Inl _ _ e' => Inl (cfold e')
        | Inr _ _ e' => Inr (cfold e')
        | SumCase _ _ _ e' e1 e2 =>
          case cfold e' of
            x => cfold (e1 x)
          | y => cfold (e2 y)
      end.
  End cfold.

  Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).

  (** The proofs are almost as straightforward as before.  We first establish two simple theorems about pairs and their projections. *)

  Section pairs.
    Variables A B : Type.

    Variable v1 : A.
    Variable v2 : B.
    Variable v : A * B.

    Theorem pair_eta1 : (v1, v2) = v -> v1 = fst v.
      destruct v; crush.
    Qed.

    Theorem pair_eta2 : (v1, v2) = v -> v2 = snd v.
      destruct v; crush.
    Qed.
  End pairs.

  Hint Resolve pair_eta1 pair_eta2.

  (** To the proof script for the main lemma, we add just one more [match] case, detecting when case analysis is appropriate on discriminees of matches over sum types. *)

  Lemma cfold_correct : forall t (e : exp _ t),
    expDenote (cfold e) = expDenote e.
    induction e; crush; try (ext_eq; crush);
      repeat (match goal with
                | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
                | [ |- match ?E with inl _ => _ | inr _ => _ end = _ ] => destruct E
              end; crush); eauto.
  Qed.

  Theorem Cfold_correct : forall t (E : Exp t),
    ExpDenote (Cfold E) = ExpDenote E.
    unfold ExpDenote, Cfold; intros; apply cfold_correct.
  Qed.
(* end thide *)
End PSLC.
