(* Copyright (c) 2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Higher-Order Operational Semantics}% *)

(** The last few chapters have shown how PHOAS can make it relatively painless to reason about program transformations.  Each of our example languages so far has had a semantics that is easy to implement with an interpreter in Gallina.  Since Gallina is designed to rule out non-termination, we cannot hope to give interpreter-based semantics to Turing-complete programming languages.  Falling back on standard operational semantics leaves us with the old bureaucratic concerns about capture-avoiding substitution.  Can we encode Turing-complete, higher-order languages in Coq without sacrificing the advantages of higher-order encoding?

   Any approach that applies to basic untyped lambda calculus is likely to extend to most object languages of interest.  We can attempt the "obvious" way of equipping a PHOAS definition for use in an operational semantics, without mentioning substitution explicitly.  Specifically, we try to work with expressions with [var] instantiated with a type of values. *)

Section exp.
  Variable var : Type.

  Inductive exp : Type :=
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : (var -> exp) -> exp.
End exp.

(** [[
Inductive val : Type :=
| VAbs : (val -> exp val) -> val.

Error: Non strictly positive occurrence of "val" in
 "(val -> exp val) -> val".
 
 ]]

 We would like to represent values (which are all function abstractions) as functions from variables to expressions, where we represent variables as the same value type that we are defining.  That way, a value can be substituted in a function body simply by applying the body to the value.  Unfortunately, the positivity restriction rejects this definition, for much the same reason that we could not use the classical HOAS encoding.

 We can try an alternate approach based on defining [val] like a usual class of syntax. *)

Section val.
  Variable var : Type.

  Inductive val : Type :=
  | VAbs : (var -> exp var) -> val.
End val.

(** Now the puzzle is how to write the type of an expression whose variables are represented as values.  We would like to be able to write a recursive definition like this one:

   [[
Fixpoint expV := exp (val expV).

   ]]

  Of course, this kind of definition is not structurally recursive, so Coq will not allow it.  Getting "substitution for free" seems to require some similar kind of self-reference.

  In this chapter, we will consider an alternate take on the problem.  We add a level of indirection, introducing more explicit syntax to break the cycle in type definitions.  Specifically, we represent function values as numbers that index into a %\emph{%#<i>#closure heap#</i>#%}% that our operational semantics maintains alongside the expression being evaluated. *)


(** * Closure Heaps *)

(** The essence of the technique is to store function bodies in lists that are extended monotonically as function abstractions are evaluated.  We can define a set of functions and theorems that implement the core functionality generically. *)

Section lookup.
  Variable A : Type.

  (** We start with a [lookup] function that generalizes last chapter's function of the same name.  It selects the element at a particular position in a list, where we number the elements starting from the end of the list, so that prepending new elements does not change the indices of old elements. *)

  Fixpoint lookup (ls : list A) (n : nat) : option A :=
    match ls with
      | nil => None
      | v :: ls' => if eq_nat_dec n (length ls') then Some v else lookup ls' n
    end.

  Infix "##" := lookup (left associativity, at level 1).

  (** The second of our two definitions expresses when one list extends another.  We will write [ls1 ~> ls2] to indicate that [ls1] could evolve into [ls2]; that is, [ls1] is a suffix of [ls2]. *)

  Definition extends (ls1 ls2 : list A) := exists ls, ls2 = ls ++ ls1.
  Infix "~>" := extends (no associativity, at level 80).

  (** We prove and add as hints a few basic theorems about [lookup] and [extends]. *)

  Theorem lookup1 : forall x ls,
    (x :: ls) ## (length ls) = Some x.
    crush; match goal with
             | [ |- context[if ?E then _ else _] ] => destruct E
           end; crush.
  Qed.

  Theorem extends_refl : forall ls, ls ~> ls.
    exists nil; reflexivity.
  Qed.

  Theorem extends1 : forall v ls, ls ~> v :: ls.
    intros; exists (v :: nil); reflexivity.
  Qed.

  Theorem extends_trans : forall ls1 ls2 ls3,
    ls1 ~> ls2
    -> ls2 ~> ls3
    -> ls1 ~> ls3.
    intros ? ? ? [l1 ?] [l2 ?]; exists (l2 ++ l1); crush.
  Qed.

  Lemma lookup_contra : forall n v ls,
    ls ## n = Some v
    -> n >= length ls
    -> False.
    induction ls; crush;
      match goal with
        | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
      end; crush.
  Qed.

  Hint Resolve lookup_contra.

  Theorem extends_lookup : forall ls1 ls2 n v,
    ls1 ~> ls2
    -> ls1 ## n = Some v
    -> ls2 ## n = Some v.
    intros ? ? ? ? [l ?]; crush; induction l; crush;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; crush; elimtype False; eauto.
  Qed.
End lookup.

Infix "##" := lookup (left associativity, at level 1).
Infix "~>" := extends (no associativity, at level 80).

Hint Resolve lookup1 extends_refl extends1 extends_trans extends_lookup.

(** We are dealing explicitly with the nitty-gritty of closure heaps.  Why is this better than dealing with the nitty-gritty of variables?  The inconvenience of modeling lambda calculus-style binders comes from the presence of nested scopes.  Program evaluation will only involve one %\emph{%#<i>#global#</i>#%}% closure heap.  Also, the short development that we just finished can be reused for many different object languages.  None of these definitions or theorems needs to be redone to handle specific object language features.  By adding the theorems as hints, no per-object-language effort is required to apply the critical facts as needed. *)


(** * Languages and Translation *)

(** For the rest of this chapter, we will consider the example of CPS translation for untyped lambda calculus with boolean constants.  It is convenient to include these constants, because their presence makes it easy to state a final translation correctness theorem. *)

Module Source.
  (** We define the syntax of source expressions in our usual way. *)

  Section exp.
    Variable var : Type.

    Inductive exp : Type :=
    | Var : var -> exp
    | App : exp -> exp -> exp
    | Abs : (var -> exp) -> exp
    | Bool : bool -> exp.
  End exp.

  Implicit Arguments Bool [var].

  Definition Exp := forall var, exp var.

  (** We will implement a big-step operational semantics, where expressions are mapped to values.  A value is either a function or a boolean.  We represent a function as a number that will be interpreted as an index into the global closure heap. *)

  Inductive val : Set :=
  | VFun : nat -> val
  | VBool : bool -> val.

  (** A closure, then, follows the usual representation of function abstraction bodies, where we represent variables as values. *)

  Definition closure := val -> exp val.
  Definition closures := list closure.

  (** Our evaluation relation has four places.  We map an initial closure heap and an expression into a final closure heap and a value.  The interesting cases are for [Abs], where we push the body onto the closure heap; and for [App], where we perform a lookup in a closure heap, to find the proper function body to execute next. *)

  Inductive eval : closures -> exp val -> closures -> val -> Prop :=
  | EvVar : forall cs v,
    eval cs (Var v) cs v

  | EvApp : forall cs1 e1 e2 cs2 v1 c cs3 v2 cs4 v3,
    eval cs1 e1 cs2 (VFun v1)
    -> eval cs2 e2 cs3 v2
    -> cs2 ## v1 = Some c
    -> eval cs3 (c v2) cs4 v3
    -> eval cs1 (App e1 e2) cs4 v3

  | EvAbs : forall cs c,
    eval cs (Abs c) (c :: cs) (VFun (length cs))

  | EvBool : forall cs b,
    eval cs (Bool b) cs (VBool b).

  (** A simple wrapper produces an evaluation relation suitable for use on the main expression type [Exp]. *)

  Definition Eval (cs1 : closures) (E : Exp) (cs2 : closures) (v : val) :=
    eval cs1 (E _) cs2 v.

  (** To prove our translation's correctness, we will need the usual notions of expression equivalence and well-formedness. *)

  Section exp_equiv.
    Variables var1 var2 : Type.

    Inductive exp_equiv : list (var1 * var2) -> exp var1 -> exp var2 -> Prop :=
    | EqVar : forall G v1 v2,
      In (v1, v2) G
      -> exp_equiv G (Var v1) (Var v2)

    | EqApp : forall G f1 x1 f2 x2,
      exp_equiv G f1 f2
      -> exp_equiv G x1 x2
      -> exp_equiv G (App f1 x1) (App f2 x2)
    | EqAbs : forall G f1 f2,
      (forall v1 v2, exp_equiv ((v1, v2) :: G) (f1 v1) (f2 v2))
      -> exp_equiv G (Abs f1) (Abs f2)

    | EqBool : forall G b,
      exp_equiv G (Bool b) (Bool b).
  End exp_equiv.

  Definition Wf (E : Exp) := forall var1 var2, exp_equiv nil (E var1) (E var2).
End Source.

(** Our target language can be defined without introducing any additional tricks. *)

Module CPS.
  Section exp.
    Variable var : Type.

    Inductive prog : Type :=
    | Halt : var -> prog
    | App : var -> var -> prog
    | Bind : primop -> (var -> prog) -> prog

    with primop : Type :=
    | Abs : (var -> prog) -> primop

    | Bool : bool -> primop

    | Pair : var -> var -> primop
    | Fst : var -> primop
    | Snd : var -> primop.
  End exp.

  Implicit Arguments Bool [var].

  Notation "x <- p ; e" := (Bind p (fun x => e))
    (right associativity, at level 76, p at next level).

  Definition Prog := forall var, prog var.
  Definition Primop := forall var, primop var.

  Inductive val : Type :=
  | VFun : nat -> val
  | VBool : bool -> val
  | VPair : val -> val -> val.
  Definition closure := val -> prog val.
  Definition closures := list closure.

  Inductive eval : closures -> prog val -> val -> Prop :=
  | EvHalt : forall cs v,
    eval cs (Halt v) v

  | EvApp : forall cs n v2 c v3,
    cs ## n = Some c
    -> eval cs (c v2) v3
    -> eval cs (App (VFun n) v2) v3

  | EvBind : forall cs1 p e cs2 v1 v2,
    evalP cs1 p cs2 v1
    -> eval cs2 (e v1) v2
    -> eval cs1 (Bind p e) v2

  with evalP : closures -> primop val -> closures -> val -> Prop :=
  | EvAbs : forall cs c,
    evalP cs (Abs c) (c :: cs) (VFun (length cs))

  | EvPair : forall cs v1 v2,
    evalP cs (Pair v1 v2) cs (VPair v1 v2)
  | EvFst : forall cs v1 v2,
    evalP cs (Fst (VPair v1 v2)) cs v1
  | EvSnd : forall cs v1 v2,
    evalP cs (Snd (VPair v1 v2)) cs v2

  | EvBool : forall cs b,
    evalP cs (Bool b) cs (VBool b).

  Definition Eval (cs : closures) (P : Prog) (v : val) := eval cs (P _) v.
End CPS.

Import Source CPS.

(** Finally, we define a CPS translation in the same way as in our previous example for simply-typed lambda calculus. *)

Reserved Notation "x <-- e1 ; e2" (right associativity, at level 76, e1 at next level).

Section cpsExp.
  Variable var : Type.

  Import Source.

  Fixpoint cpsExp (e : exp var)
    : (var -> prog var) -> prog var :=
    match e with
      | Var v => fun k => k v

      | App e1 e2 => fun k =>
        f <-- e1;
        x <-- e2;
        kf <- CPS.Abs k;
        p <- Pair x kf;
        CPS.App f p
      | Abs e' => fun k =>
        f <- CPS.Abs (var := var) (fun p =>
          x <- Fst p;
          kf <- Snd p;
          r <-- e' x;
          CPS.App kf r);
        k f

      | Bool b => fun k =>
        x <- CPS.Bool b;
        k x
    end

    where "x <-- e1 ; e2" := (cpsExp e1 (fun x => e2)).
End cpsExp.

Notation "x <-- e1 ; e2" := (cpsExp e1 (fun x => e2)).

Definition CpsExp (E : Exp) : Prog := fun _ => cpsExp (E _) (Halt (var := _)).


(** * Correctness Proof *)

(** Our proof for simply-typed lambda calculus relied on a logical relation to state the key induction hypothesis.  Since logical relations proceed by recursion on type structure, we cannot apply them directly in an untyped setting.  Instead, we will use an inductive judgment to relate source-level and CPS-level values.  First, it is helpful to define an abbreviation for the compiled version of a function body. *)

Definition cpsFunc var (e' : var -> Source.exp var) :=
  fun p : var =>
    x <- Fst p;
    kf <- Snd p;
    r <-- e' x;
    CPS.App kf r.

(** Now we can define our correctness relation [cr], which is parameterized by source-level and CPS-level closure heaps. *)

Section cr.
  Variable s1 : Source.closures.
  Variable s2 : CPS.closures.

  Import Source.

  (** Only equal booleans are related.  For two function addresses [l1] and [l2] to be related, they must point to valid functions in their respective closure heaps.  The address [l1] must point to a function [f1], and [l2] must point to the result of compiling function [f2].  Further, [f1] and [f2] must be equivalent syntactically in some variable environment [G], and every variable pair in [G] must itself belong to the relation we are defining. *)

  Inductive cr : Source.val -> CPS.val -> Prop :=
  | CrBool : forall b,
    cr (Source.VBool b) (CPS.VBool b)

  | CrFun : forall l1 l2 G f1 f2,
    (forall x1 x2, exp_equiv ((x1, x2) :: G) (f1 x1) (f2 x2))
    -> (forall x1 x2, In (x1, x2) G -> cr x1 x2)
    -> s1 ## l1 = Some f1
    -> s2 ## l2 = Some (cpsFunc f2)
    -> cr (Source.VFun l1) (CPS.VFun l2).
End cr.

Notation "s1 & s2 |-- v1 ~~ v2" := (cr s1 s2 v1 v2) (no associativity, at level 70).

Hint Constructors cr.

(** To prove our main lemma, it will be useful to know that source-level evaluation never removes old closures from a closure heap. *)

Lemma eval_monotone : forall cs1 e cs2 v,
  Source.eval cs1 e cs2 v
  -> cs1 ~> cs2.
  induction 1; crush; eauto.
Qed.

(** Further, [cr] continues to hold when its closure heap arguments are evolved in legal ways. *)

Lemma cr_monotone : forall cs1 cs2 cs1' cs2',
  cs1 ~> cs1'
  -> cs2 ~> cs2'
  -> forall v1 v2, cs1 & cs2 |-- v1 ~~ v2
    -> cs1' & cs2' |-- v1 ~~ v2.
  induction 3; crush; eauto.
Qed.

Hint Resolve eval_monotone cr_monotone.

(** We state a trivial fact about the validity of variable environments, so that we may add this fact as a hint that [eauto] will apply. *)

Lemma push : forall G s1 s2 v1' v2',
  (forall v1 v2, In (v1, v2) G -> s1 & s2 |-- v1 ~~ v2)
  -> s1 & s2 |-- v1' ~~ v2'
  -> (forall v1 v2, (v1', v2') = (v1, v2) \/ In (v1, v2) G -> s1 & s2 |-- v1 ~~ v2).
  crush.
Qed.

Hint Resolve push.

(** Our final preparation for the main lemma involves adding effective hints about the CPS language's operational semantics.  The following tactic performs one step of evaluation.  It uses the Ltac code [eval hnf in e] to compute the %\emph{%#<i>#head normal form#</i>#%}% of [e], where the head normal form of an expression in an inductive type is an application of one of that inductive type's constructors.  The final line below uses [solve] to ensure that we only take a [Bind] step if a full evaluation derivation for the associated primop may be found before proceeding. *)

Ltac evalOne :=
  match goal with
    | [ |- CPS.eval ?cs ?e ?v ] =>
      let e := eval hnf in e in
        change (CPS.eval cs e v);
          econstructor; [ solve [ eauto ] | ]
  end.

(** For primops, we rely on [eauto]'s usual approach.  For goals that evaluate programs, we instead ask to treat one or more applications of [evalOne] as a single step, which helps us avoid passing [eauto] an excessively large bound on proof tree depth. *)

Hint Constructors evalP.
Hint Extern 1 (CPS.eval _ _ _) => evalOne; repeat evalOne.

(** The final lemma proceeds by induction on an evaluation derivation for an expression [e1] that is equivalent to some [e2] in some environment [G].  An initial closure heap for each language is quantified over, such that all variable pairs in [G] are compatible.  The lemma's conclusion applies to an arbitrary continuation [k], asserting that a final CPS-level closure heap [s2] and a CPS-level program result value [r2] exist.

   Three conditions establish that [s2] and [r2] are chosen properly: Evaluation of [e2]'s compilation with continuation [k] must be equivalent to evaluation of [k r2].  The original program result [r1] must be compatible with [r2] in the final closure heaps.  Finally, [s2'] must be a proper evolution of the original CPS-level heap [s2]. *)

Lemma cpsExp_correct : forall s1 e1 s1' r1,
  Source.eval s1 e1 s1' r1
  -> forall G (e2 : exp CPS.val),
    exp_equiv G e1 e2
    -> forall s2,
      (forall v1 v2, In (v1, v2) G -> s1 & s2 |-- v1 ~~ v2)
      -> forall k, exists s2', exists r2,
        (forall r, CPS.eval s2' (k r2) r
          -> CPS.eval s2 (cpsExp e2 k) r)
        /\ s1' & s2' |-- r1 ~~ r2
        /\ s2 ~> s2'.

  (** The proof script follows our standard approach.  Its main loop applies three hints.  First, we perform inversion on any derivation of equivalence between a source-level function value and some other value.  Second, we eliminate redundant equality hypotheses.  Finally, we look for opportunities to instantiate inductive hypotheses.

     We identify an IH by its syntactic form, noting the expression [E] that it applies to.  It is important to instantiate IHes in the right order, since existentially-quantified variables in the conclusion of one IH may need to be used in instantiating the universal quantifiers of a different IH.  Thus, we perform a quick check to [fail 1] if the IH we found applies to an expression that was evaluated after another expression [E'] whose IH we did not yet instantiate.  The flow of closure heaps through source-level evaluation is used to implement the check.

     If the hypothesis [H] is indeed the right IH to handle next, we use the [guess] tactic to guess values for its universal quantifiers and prove its hypotheses with [eauto].  This tactic is very similar to [inster] from Chapter 12.  It takes two arguments: the first is a value to use for any properly-typed universal quantifier, and the second is the hypothesis to instantiate.  The final inner [match] deduces if we are at the point of executing the body of a called function.  If so, we help [guess] by saying that the initial closure heap will be the current closure heap [cs] extended with the current continuation [k].  In all other cases, [guess] is smart enough to operate alone. *)

  induction 1; inversion 1; crush;
    repeat (match goal with
              | [ H : _ & _ |-- Source.VFun _ ~~ _ |- _ ] => inversion H; clear H
              | [ H1 : ?E = _, H2 : ?E = _ |- _ ] => rewrite H1 in H2; clear H1
              | [ H : forall G e2, exp_equiv G ?E e2 -> _ |- _ ] =>
                match goal with
                  | [ _ : Source.eval ?CS E _ _, _ : Source.eval _ ?E' ?CS _,
                      _ : forall G e2, exp_equiv G ?E' e2 -> _ |- _ ] => fail 1
                  | _ => match goal with
                           | [ k : val -> prog val, _ : _ & ?cs |-- _ ~~ _,
                               _ : context[VFun] |- _ ] =>
                             guess (k :: cs) H
                           | _ => guess tt H
                         end
                end
            end; crush); eauto 13.
Qed.

(** The final theorem follows easily from this lemma. *)

Theorem CpsExp_correct : forall E cs b,
  Source.Eval nil E cs (Source.VBool b)
  -> Wf E
  -> CPS.Eval nil (CpsExp E) (CPS.VBool b).
  Hint Constructors CPS.eval.

  unfold Source.Eval, CPS.Eval, CpsExp; intros ? ? ? H1 H2;
    generalize (cpsExp_correct H1 (H2 _ _) (s2 := nil)
      (fun _ _ pf => match pf with end) (Halt (var := _))); crush;
    match goal with
      | [ H : _ & _ |-- _ ~~ _ |- _ ] => inversion H
    end; crush.
Qed.
