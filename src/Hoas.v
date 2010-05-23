(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Eqdep String List.

Require Import Axioms Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Higher-Order Abstract Syntax}% *)

(** In many cases, detailed reasoning about variable binders and substitution is a small annoyance; in other cases, it becomes the dominant cost of proving a theorem formally.  No matter which of these possibilities prevails, it is clear that it would be very pragmatic to find a way to avoid reasoning about variable identity or freshness.  A well-established alternative to first-order encodings is %\textit{%#<i>#higher-order abstract syntax#</i>#%}%, or HOAS.  In mechanized theorem-proving, HOAS is most closely associated with the LF meta logic and the tools based on it, including Twelf.

In this chapter, we will see that HOAS cannot be implemented directly in Coq.  However, a few very similar encodings are possible and are in fact very effective in some important domains. *)


(** * Classic HOAS *)

(** The motto of HOAS is simple: represent object language binders using meta language binders.  Here, "object language" refers to the language being formalized, while the meta language is the language in which the formalization is done.  Our usual meta language, Coq's Gallina, contains the standard binding facilities of functional programming, making it a promising base for higher-order encodings.

   Recall the concrete encoding of basic untyped lambda calculus expressions. *)

Inductive uexp : Set :=
| UVar : string -> uexp
| UApp : uexp -> uexp -> uexp
| UAbs : string -> uexp -> uexp.

(** The explicit presence of variable names forces us to think about issues of freshness and variable capture.  The HOAS alternative would look like this. *)

Reset uexp.

(** [[
Inductive uexp : Set :=
| UApp : uexp -> uexp -> uexp
| UAbs : (uexp -> uexp) -> uexp.
 
  ]]

  We have avoided any mention of variables.  Instead, we encode the binding done by abstraction using the binding facilities associated with Gallina functions.  For instance, we might represent the term $\lambda x. \; x \; x$#<tt>\x. x x</tt># as [UAbs (fun x => UApp x x)].  Coq has built-in support for matching binders in anonymous [fun] expressions to their uses, so we avoid needing to implement our own binder-matching logic.

  This definition is not quite HOAS, because of the broad variety of functions that Coq would allow us to pass as arguments to [UAbs].  We can thus construct many [uexp]s that do not correspond to normal lambda terms.  These deviants are called %\textit{%#<i>#exotic terms#</i>#%}%.  In LF, functions may only be written in a very restrictive computational language, lacking, among other things, pattern matching and recursive function definitions.  Thus, thanks to a careful balancing act of design decisions, exotic terms are not possible with usual HOAS encodings in LF.

  Our definition of [uexp] has a more fundamental problem: it is invalid in Gallina.

  [[
Error: Non strictly positive occurrence of "uexp" in
 "(uexp -> uexp) -> uexp".
 
  ]]

  We have violated a rule that we considered before: an inductive type may not be defined in terms of functions over itself.  Way back in Chapter 3, we considered this example and the reasons why we should be glad that Coq rejects it.  Thus, we will need to use more cleverness to reap similar benefits.

  The root problem is that our expressions contain variables representing expressions of the same kind.  Many useful kinds of syntax involve no such cycles.  For instance, it is easy to use HOAS to encode standard first-order logic in Coq. *)

Inductive prop : Type :=
| Eq : forall T, T -> T -> prop
| Not : prop -> prop
| And : prop -> prop -> prop
| Or : prop -> prop -> prop
| Forall : forall T, (T -> prop) -> prop
| Exists : forall T, (T -> prop) -> prop.

Fixpoint propDenote (p : prop) : Prop :=
  match p with
    | Eq _ x y => x = y
    | Not p => ~ (propDenote p)
    | And p1 p2 => propDenote p1 /\ propDenote p2
    | Or p1 p2 => propDenote p1 \/ propDenote p2
    | Forall _ f => forall x, propDenote (f x)
    | Exists _ f => exists x, propDenote (f x)
  end.

(** Unfortunately, there are other recursive functions that we might like to write but cannot.  One simple example is a function to count the number of constructors used to build a [prop].  To look inside a [Forall] or [Exists], we need to look inside the quantifier's body, which is represented as a function.  In Gallina, as in most statically-typed functional languages, the only way to interact with a function is to call it.  We have no hope of doing that here; the domain of the function in question has an arbitary type [T], so [T] may even be uninhabited.  If we had a universal way of constructing values to look inside functions, we would have uncovered a consistency bug in Coq!

   We are still suffering from the possibility of writing exotic terms, such as this example: *)

Example true_prop := Eq 1 1.
Example false_prop := Not true_prop.
Example exotic_prop := Forall (fun b : bool => if b then true_prop else false_prop).

(** Thus, the idea of a uniform way of looking inside a binder to find another well-defined [prop] is hopelessly doomed.

   A clever HOAS variant called %\textit{%#<i>#weak HOAS#</i>#%}% manages to rule out exotic terms in Coq.  Here is a weak HOAS version of untyped lambda terms. *)

Parameter var : Set.

Inductive uexp : Set :=
| UVar : var -> uexp
| UApp : uexp -> uexp -> uexp
| UAbs : (var -> uexp) -> uexp.

(** We postulate the existence of some set [var] of variables, and variable nodes appear explicitly in our syntax.  A binder is represented as a function over %\textit{%#<i>#variables#</i>#%}%, rather than as a function over %\textit{%#<i>#expressions#</i>#%}%.  This breaks the cycle that led Coq to reject the literal HOAS definition.  It is easy to encode our previous example, $\lambda x. \; x \; x$#<tt>\x. x x</tt>#: *)

Example self_app := UAbs (fun x => UApp (UVar x) (UVar x)).

(** What about exotic terms?  The problems they caused earlier came from the fact that Gallina is expressive enough to allow us to perform case analysis on the types we used as the domains of binder functions.  With weak HOAS, we use an abstract type [var] as the domain.  Since we assume the existence of no functions for deconstructing [var]s, Coq's type soundness enforces that no Gallina term of type [uexp] can take different values depending on the value of a [var] available in the typing context, %\textit{%#<i>#except#</i>#%}% by incorporating those variables into a [uexp] value in a legal way.

   Weak HOAS retains the other disadvantage of our previous example: it is hard to write recursive functions that deconstruct terms.  As with the previous example, some functions %\textit{%#<i>#are#</i>#%}% implementable.  For instance, we can write a function to reverse the function and argument positions of every [UApp] node. *)

Fixpoint swap (e : uexp) : uexp :=
  match e with
    | UVar _ => e
    | UApp e1 e2 => UApp (swap e2) (swap e1)
    | UAbs e1 => UAbs (fun x => swap (e1 x))
  end.

(** However, it is still impossible to write a function to compute the size of an expression.  We would still need to manufacture a value of type [var] to peer under a binder, and that is impossible, because [var] is an abstract type. *)


(** * Parametric HOAS *)

(** In the context of Haskell, Washburn and Weirich introduced a technique called %\emph{%#<i>#parametric HOAS#</i>#%}%, or PHOAS.  By making a slight alteration in the spirit of weak HOAS, we arrive at an encoding that addresses all three of the complaints above: the encoding is legal in Coq, exotic terms are impossible, and it is possible to write any syntax-deconstructing function that we can write with first-order encodings.  The last of these advantages is not even present with HOAS in Twelf.  In a sense, we receive it in exchange for giving up a free implementation of capture-avoiding substitution.

   The first step is to change the weak HOAS type so that [var] is a variable inside a section, rather than a global parameter. *)

Reset uexp.

Section uexp.
  Variable var : Set.

  Inductive uexp : Set :=
  | UVar : var -> uexp
  | UApp : uexp -> uexp -> uexp
  | UAbs : (var -> uexp) -> uexp.
End uexp.

(** Next, we can encapsulate choices of [var] inside a polymorphic function type. *)

Definition Uexp := forall var, uexp var.

(** This type [Uexp] is our final, exotic-term-free representation of lambda terms.  Inside the body of a [Uexp] function, [var] values may not be deconstructed illegaly, for much the same reason as with weak HOAS.  We simply trade an abstract type for parametric polymorphism.

   Our running example $\lambda x. \; x \; x$#<tt>\x. x x</tt># is easily expressed: *)

Example self_app : Uexp := fun var => UAbs (var := var)
  (fun x : var => UApp (var := var) (UVar (var := var) x) (UVar (var := var) x)).

(** Including all mentions of [var] explicitly helps clarify what is happening here, but it is convenient to let Coq's local type inference fill in these occurrences for us. *)

Example self_app' : Uexp := fun _ => UAbs (fun x => UApp (UVar x) (UVar x)).

(** We can go further and apply the PHOAS technique to dependently-typed ASTs, where Gallina typing guarantees that only well-typed terms can be represented.  For the rest of this chapter, we consider the example of simply-typed lambda calculus with natural numbers and addition.  We start with a conventional definition of the type language. *)

Inductive type : Type :=
| Nat : type
| Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

(** Our definition of the expression type follows the definition for untyped lambda calculus, with one important change.  Now our section variable [var] is not just a type.  Rather, it is a %\textit{%#<i>#function#</i>#%}% returning types.  The idea is that a variable of object language type [t] is represented by a [var t].  Note how this enables us to avoid indexing the [exp] type with a representation of typing contexts. *)

Section exp.
  Variable var : type -> Type.

  Inductive exp : type -> Type :=
  | Const' : nat -> exp Nat
  | Plus' : exp Nat -> exp Nat -> exp Nat

  | Var : forall t, var t -> exp t
  | App' : forall dom ran, exp (dom --> ran) -> exp dom -> exp ran
  | Abs' : forall dom ran, (var dom -> exp ran) -> exp (dom --> ran).
End exp.

Implicit Arguments Const' [var].
Implicit Arguments Var [var t].
Implicit Arguments Abs' [var dom ran].

(** Our final representation type wraps [exp] as before. *)

Definition Exp t := forall var, exp var t.

(* begin thide *)

(** We can define some smart constructors to make it easier to build [Exp]s without using polymorphism explicitly. *)

Definition Const (n : nat) : Exp Nat :=
  fun _ => Const' n.
Definition Plus (E1 E2 : Exp Nat) : Exp Nat :=
  fun _ => Plus' (E1 _) (E2 _).
Definition App dom ran (F : Exp (dom --> ran)) (X : Exp dom) : Exp ran :=
  fun _ => App' (F _) (X _).

(** A case for function abstraction is not as natural, but we can implement one candidate in terms of a type family [Exp1], such that [Exp1 free result] represents an expression of type [result] with one free variable of type [free]. *)

Definition Exp1 t1 t2 := forall var, var t1 -> exp var t2.
Definition Abs dom ran (B : Exp1 dom ran) : Exp (dom --> ran) :=
  fun _ => Abs' (B _).
(* end thide *)

(* EX: Define appropriate shorthands, so that these definitions type-check. *)

(** Now it is easy to encode a number of example programs. *)

Example zero := Const 0.
Example one := Const 1.
Example one_again := Plus zero one.
Example ident : Exp (Nat --> Nat) := Abs (fun _ X => Var X).
Example app_ident := App ident one_again.
Example app : Exp ((Nat --> Nat) --> Nat --> Nat) := fun _ =>
  Abs' (fun f => Abs' (fun x => App' (Var f) (Var x))).
Example app_ident' := App (App app ident) one_again.

(* EX: Define a function to count the number of variable occurrences in an [Exp]. *)

(** We can write syntax-deconstructing functions, such as [CountVars], which counts how many [Var] nodes appear in an [Exp].  First, we write a version [countVars] for [exp]s.  The main trick is to specialize [countVars] to work over expressions where [var] is instantiated as [fun _ => unit].  That is, every variable is just a value of type [unit], such that variables carry no information.  The important thing is that we have a value [tt] of type [unit] available, to use in descending into binders. *)

(* begin thide *)
Fixpoint countVars t (e : exp (fun _ => unit) t) : nat :=
  match e with
    | Const' _ => 0
    | Plus' e1 e2 => countVars e1 + countVars e2
    | Var _ _ => 1
    | App' _ _ e1 e2 => countVars e1 + countVars e2
    | Abs' _ _ e' => countVars (e' tt)
  end.

(** We turn [countVars] into [CountVars] with explicit instantiation of a polymorphic [Exp] value [E].  We can write an underscore for the paramter to [E], because local type inference is able to infer the proper value. *)

Definition CountVars t (E : Exp t) : nat := countVars (E _).
(* end thide *)

(** A few evaluations establish that [CountVars] behaves plausibly. *)

Eval compute in CountVars zero.
(** %\vspace{-.15in}% [[
     = 0
     : nat
     ]] *)

Eval compute in CountVars one.
(** %\vspace{-.15in}% [[
     = 0
     : nat
     ]] *)

Eval compute in CountVars one_again.
(** %\vspace{-.15in}% [[
     = 0
     : nat
     ]] *)

Eval compute in CountVars ident.
(** %\vspace{-.15in}% [[
     = 1
     : nat
     ]] *)

Eval compute in CountVars app_ident.
(** %\vspace{-.15in}% [[
     = 1
     : nat
     ]] *)

Eval compute in CountVars app.
(** %\vspace{-.15in}% [[
     = 2
     : nat
     ]] *)

Eval compute in CountVars app_ident'.
(** %\vspace{-.15in}% [[
     = 3
     : nat
     ]] *)


(* EX: Define a function to count the number of occurrences of a single distinguished variable. *)

(** We might want to go further and count occurrences of a single distinguished free variable in an expression.  In this case, it is useful to instantiate [var] as [fun _ => bool].  We will represent the distinguished variable with [true] and all other variables with [false]. *)

(* begin thide *)
Fixpoint countOne t (e : exp (fun _ => bool) t) : nat :=
  match e with
    | Const' _ => 0
    | Plus' e1 e2 => countOne e1 + countOne e2
    | Var _ true => 1
    | Var _ false => 0
    | App' _ _ e1 e2 => countOne e1 + countOne e2
    | Abs' _ _ e' => countOne (e' false)
  end.

(** We wrap [countOne] into [CountOne], which we type using the [Exp1] definition from before.  [CountOne] operates on an expression [E] with a single free variable.  We apply an instantiated [E] to [true] to mark this variable as the one [countOne] should look for.  [countOne] itself is careful to instantiate all other variables with [false]. *)

Definition CountOne t1 t2 (E : Exp1 t1 t2) : nat :=
  countOne (E _ true).
(* end thide *)

(** We can check the behavior of [CountOne] on a few examples. *)

Example ident1 : Exp1 Nat Nat := fun _ X => Var X.
Example add_self : Exp1 Nat Nat := fun _ X => Plus' (Var X) (Var X).
Example app_zero : Exp1 (Nat --> Nat) Nat := fun _ X => App' (Var X) (Const' 0).
Example app_ident1 : Exp1 Nat Nat := fun _ X =>
  App' (Abs' (fun Y => Var Y)) (Var X).

Eval compute in CountOne ident1.
(** %\vspace{-.15in}% [[
     = 1
     : nat
     ]] *)

Eval compute in CountOne add_self.
(** %\vspace{-.15in}% [[
     = 2
     : nat
     ]] *)

Eval compute in CountOne app_zero.
(** %\vspace{-.15in}% [[
     = 1
     : nat
     ]] *)

Eval compute in CountOne app_ident1.
(** %\vspace{-.15in}% [[
     = 1
     : nat
     ]] *)


(* EX: Define a function to pretty-print [Exp]s as strings. *)

(** The PHOAS encoding turns out to be just as general as the first-order encodings we saw previously.  To provide a taste of that generality, we implement a translation into concrete syntax, rendered in human-readable strings.  This is as easy as representing variables as strings. *)

(* begin thide *)
Section ToString.
  Open Scope string_scope.

  Fixpoint natToString (n : nat) : string :=
    match n with
      | O => "O"
      | S n' => "S(" ++ natToString n' ++ ")"
    end.

  (** Function [toString] takes an extra argument [cur], which holds the last variable name assigned to a binder.  We build new variable names by extending [cur] with primes.  The function returns a pair of the next available variable name and of the actual expression rendering. *)

  Fixpoint toString t (e : exp (fun _ => string) t) (cur : string) : string * string :=
    match e with
      | Const' n => (cur, natToString n)
      | Plus' e1 e2 =>
        let (cur', s1) := toString e1 cur in
        let (cur'', s2) := toString e2 cur' in
        (cur'', "(" ++ s1 ++ ") + (" ++ s2 ++ ")")
      | Var _ s => (cur, s)
      | App' _ _ e1 e2 =>
        let (cur', s1) := toString e1 cur in
        let (cur'', s2) := toString e2 cur' in
        (cur'', "(" ++ s1 ++ ") (" ++ s2 ++ ")")
      | Abs' _ _ e' =>
        let (cur', s) := toString (e' cur) (cur ++ "'") in
        (cur', "(\" ++ cur ++ ", " ++ s ++ ")")
    end.

  Definition ToString t (E : Exp t) : string := snd (toString (E _) "x").
End ToString.
(* end thide *)

Eval compute in ToString zero.
(** %\vspace{-.15in}% [[
     = "O"%string
     : string
   ]] *)

Eval compute in ToString one.
(** %\vspace{-.15in}% [[
     = "S(O)"%string
     : string
   ]] *)

Eval compute in ToString one_again.
(** %\vspace{-.15in}% [[
     = "(O) + (S(O))"%string
     : string
   ]] *)

Eval compute in ToString ident.
(** %\vspace{-.15in}% [[
     = "(\x, x)"%string
     : string
   ]] *)

Eval compute in ToString app_ident.
(** %\vspace{-.15in}% [[
     = "((\x, x)) ((O) + (S(O)))"%string
     : string
   ]] *)

Eval compute in ToString app.
(** %\vspace{-.15in}% [[
     = "(\x, (\x', (x) (x')))"%string
     : string
   ]] *)

Eval compute in ToString app_ident'.
(** %\vspace{-.15in}% [[
     = "(((\x, (\x', (x) (x')))) ((\x'', x''))) ((O) + (S(O)))"%string
     : string
   ]] *)


(* EX: Define a substitution function. *)

(** Our final example is crucial to using PHOAS to encode standard operational semantics.  We define capture-avoiding substitution, in terms of a function [flatten] which takes in an expression that represents variables as expressions.  [flatten] replaces every node [Var e] with [e]. *)

(* begin thide *)
Section flatten.
  Variable var : type -> Type.

  Fixpoint flatten t (e : exp (exp var) t) : exp var t :=
    match e with
      | Const' n => Const' n
      | Plus' e1 e2 => Plus' (flatten e1) (flatten e2)
      | Var _ e' => e'
      | App' _ _ e1 e2 => App' (flatten e1) (flatten e2)
      | Abs' _ _ e' => Abs' (fun x => flatten (e' (Var x)))
    end.
End flatten.

(** Flattening turns out to implement the heart of substitution.  We apply [E2], which has one free variable, to [E1], replacing the occurrences of the free variable by copies of [E1].  [flatten] takes care of removing the extra [Var] applications around these copies. *)

Definition Subst t1 t2 (E1 : Exp t1) (E2 : Exp1 t1 t2) : Exp t2 := fun _ =>
  flatten (E2 _ (E1 _)).
(* end thide *)

Eval compute in Subst one ident1.
(** %\vspace{-.15in}% [[
     = fun var : type -> Type => Const' 1
     : Exp Nat
   ]] *)

Eval compute in Subst one add_self.
(** %\vspace{-.15in}% [[
     = fun var : type -> Type => Plus' (Const' 1) (Const' 1)
     : Exp Nat
   ]] *)

Eval compute in Subst ident app_zero.
(** %\vspace{-.15in}% [[
     = fun var : type -> Type =>
       App' (Abs' (fun X : var Nat => Var X)) (Const' 0)
     : Exp Nat
   ]] *)

Eval compute in Subst one app_ident1.
(** %\vspace{-.15in}% [[
     = fun var : type -> Type =>
       App' (Abs' (fun x : var Nat => Var x)) (Const' 1)
     : Exp Nat
   ]] *)


(** * A Type Soundness Proof *)

(** With [Subst] defined, there are few surprises encountered in defining a standard small-step, call-by-value semantics for our object language.  We begin by classifying a subset of expressions as values. *)

Inductive Val : forall t, Exp t -> Prop :=
| VConst : forall n, Val (Const n)
| VAbs : forall dom ran (B : Exp1 dom ran), Val (Abs B).

Hint Constructors Val.

(** Since this language is more complicated than the one we considered in the chapter on first-order encodings, we will use explicit evaluation contexts to define the semantics.  A value of type [Ctx t u] is a context that yields an expression of type [u] when filled by an expression of type [t].  We have one context for each position of the [App] and [Plus] constructors. *)

Inductive Ctx : type -> type -> Type :=
| AppCong1 : forall (dom ran : type),
  Exp dom -> Ctx (dom --> ran) ran
| AppCong2 : forall (dom ran : type),
  Exp (dom --> ran) -> Ctx dom ran
| PlusCong1 : Exp Nat -> Ctx Nat Nat
| PlusCong2 : Exp Nat -> Ctx Nat Nat.

(** A judgment characterizes when contexts are valid, enforcing the standard call-by-value restriction that certain positions must hold values. *)

Inductive isCtx : forall t1 t2, Ctx t1 t2 -> Prop :=
| IsApp1 : forall dom ran (X : Exp dom), isCtx (AppCong1 ran X)
| IsApp2 : forall dom ran (F : Exp (dom --> ran)), Val F -> isCtx (AppCong2 F)
| IsPlus1 : forall E2, isCtx (PlusCong1 E2)
| IsPlus2 : forall E1, Val E1 -> isCtx (PlusCong2 E1).

(** A simple definition implements plugging a context with a specific expression. *)

Definition plug t1 t2 (C : Ctx t1 t2) : Exp t1 -> Exp t2 :=
  match C with
    | AppCong1 _ _ X => fun F => App F X
    | AppCong2 _ _ F => fun X => App F X
    | PlusCong1 E2 => fun E1 => Plus E1 E2
    | PlusCong2 E1 => fun E2 => Plus E1 E2
  end.

Infix "@" := plug (no associativity, at level 60).

(** Finally, we have the step relation itself, which combines our ingredients in the standard way.  In the congruence rule, we introduce the extra variable [E1] and its associated equality to make the rule easier for [eauto] to apply. *)

Reserved Notation "E1 ==> E2" (no associativity, at level 90).

Inductive Step : forall t, Exp t -> Exp t -> Prop :=
| Beta : forall dom ran (B : Exp1 dom ran) (X : Exp dom),
  Val X
  -> App (Abs B) X ==> Subst X B
| Sum : forall n1 n2,
  Plus (Const n1) (Const n2) ==> Const (n1 + n2)
| Cong : forall t t' (C : Ctx t t') E E' E1,
  isCtx C
  -> E1 = C @ E
  -> E ==> E'
  -> E1 ==> C @ E'

  where "E1 ==> E2" := (Step E1 E2).

Hint Constructors isCtx Step.

(* EX: Prove type soundness. *)

(** To prove type soundness for this semantics, we need to overcome one crucial obstacle.  Standard proofs use induction on the structure of typing derivations.  Our encoding mixes typing derivations with expression syntax, so we want to induct over expression structure.  Our expressions are represented as functions, which do not, in general, admit induction in Coq.  However, because of our use of parametric polymorphism, we know that our expressions do, in fact, have inductive structure.  In particular, every closed value of [Exp] type must belong to the following relation. *)

(* begin thide *)
Inductive Closed : forall t, Exp t -> Prop :=
| CConst : forall n,
  Closed (Const n)
| CPlus : forall E1 E2,
  Closed E1
  -> Closed E2
  -> Closed (Plus E1 E2)
| CApp : forall dom ran (E1 : Exp (dom --> ran)) E2,
  Closed E1
  -> Closed E2
  -> Closed (App E1 E2)
| CAbs : forall dom ran (E1 : Exp1 dom ran),
  Closed (Abs E1).

(** How can we prove such a fact?  It probably cannot be established in Coq without axioms.  Rather, one would have to establish it metatheoretically, reasoning informally outside of Coq.  For now, we assert the fact as an axiom.  The later chapter on intensional transformations shows one approach to removing the need for an axiom. *)

Axiom closed : forall t (E : Exp t), Closed E.

(** The usual progress and preservation theorems are now very easy to prove.  In fact, preservation is implicit in our dependently-typed definition of [Step].  This is a huge win, because we avoid completely the theorem about substitution and typing that made up the bulk of each proof in the chapter on first-order encodings.  The progress theorem yields to a few lines of automation.

   We define a slight variant of [crush] which also looks for chances to use the theorem [inj_pair2] on hypotheses.  This theorem deals with an artifact of the way that [inversion] works on dependently-typed hypotheses. *)

Ltac my_crush' :=
  crush;
  repeat (match goal with
            | [ H : _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H
          end; crush).

Hint Extern 1 (_ = _ @ _) => simpl.

(** This is the point where we need to do induction over functions, in the form of expressions [E].  The judgment [Closed] provides the perfect framework; we induct over [Closed] derivations. *)

Lemma progress' : forall t (E : Exp t),
  Closed E
  -> Val E \/ exists E', E ==> E'.
  induction 1; crush;
    repeat match goal with
             | [ H : Val _ |- _ ] => inversion H; []; clear H; my_crush'
           end; eauto 6.
Qed.

(** Our final proof of progress makes one top-level use of the axiom [closed] that we asserted above. *)

Theorem progress : forall t (E : Exp t),
  Val E \/ exists E', E ==> E'.
  intros; apply progress'; apply closed.
Qed.
(* end thide *)


(** * Big-Step Semantics *)

(** Another standard exercise in operational semantics is proving the equivalence of small-step and big-step semantics.  We can carry out this exercise for our PHOAS lambda calculus.  Most of the steps are just as pleasant as in the previous section, but things get complicated near to the end.

   We must start by defining the big-step semantics itself.  The definition is completely standard. *)

Reserved Notation "E1 ===> E2" (no associativity, at level 90).

Inductive BigStep : forall t, Exp t -> Exp t -> Prop :=
| SConst : forall n,
  Const n ===> Const n
| SPlus : forall E1 E2 n1 n2,
  E1 ===> Const n1
  -> E2 ===> Const n2
  -> Plus E1 E2 ===> Const (n1 + n2)

| SApp : forall dom ran (E1 : Exp (dom --> ran)) E2 B V2 V,
  E1 ===> Abs B
  -> E2 ===> V2
  -> Subst V2 B ===> V
  -> App E1 E2 ===> V
| SAbs : forall dom ran (B : Exp1 dom ran),
  Abs B ===> Abs B

  where "E1 ===> E2" := (BigStep E1 E2).

Hint Constructors BigStep.

(* EX: Prove the equivalence of the small- and big-step semantics. *)

(** To prove a crucial intermediate lemma, we will want to name the transitive-reflexive closure of the small-step relation. *)

(* begin thide *)
Reserved Notation "E1 ==>* E2" (no associativity, at level 90).

Inductive MultiStep : forall t, Exp t -> Exp t -> Prop :=
| Done : forall t (E : Exp t), E ==>* E
| OneStep : forall t (E E' E'' : Exp t),
  E ==> E'
  -> E' ==>* E''
  -> E ==>* E''

  where "E1 ==>* E2" := (MultiStep E1 E2).

Hint Constructors MultiStep.

(** A few basic properties of evaluation and values admit easy proofs. *)

Theorem MultiStep_trans : forall t (E1 E2 E3 : Exp t),
  E1 ==>* E2
  -> E2 ==>* E3
  -> E1 ==>* E3.
  induction 1; eauto.
Qed.

Theorem Big_Val : forall t (E V : Exp t),
  E ===> V
  -> Val V.
  induction 1; crush.
Qed.

Theorem Val_Big : forall t (V : Exp t),
  Val V
  -> V ===> V.
  destruct 1; crush.
Qed.

Hint Resolve Big_Val Val_Big.

(** Another useful property deals with pushing multi-step evaluation inside of contexts. *)

Lemma Multi_Cong : forall t t' (C : Ctx t t'),
  isCtx C
  -> forall E E', E ==>* E'
    -> C @ E ==>* C @ E'.
  induction 2; crush; eauto.
Qed.

Lemma Multi_Cong' : forall t t' (C : Ctx t t') E1 E2 E E',
  isCtx C
  -> E1 = C @ E
  -> E2 = C @ E'
  -> E ==>* E'
  -> E1 ==>* E2.
  crush; apply Multi_Cong; auto.
Qed.

Hint Resolve Multi_Cong'.

(** Unrestricted use of transitivity of [==>*] can lead to very large [eauto] search spaces, which has very inconvenient efficiency consequences.  Instead, we define a special tactic [mtrans] that tries applying transitivity with a particular intermediate expression. *)

Ltac mtrans E :=
  match goal with
    | [ |- E ==>* _ ] => fail 1
    | _ => apply MultiStep_trans with E; [ solve [ eauto ] | eauto ]
  end.

(** With [mtrans], we can give a reasonably short proof of one direction of the equivalence between big-step and small-step semantics.  We include proof cases specific to rules of the big-step semantics, since leaving the details to [eauto] would lead to a very slow proof script.  The use of [solve] in [mtrans]'s definition keeps us from going down unfruitful paths. *)

Theorem Big_Multi : forall t (E V : Exp t),
  E ===> V
  -> E ==>* V.
  induction 1; crush; eauto;
    repeat match goal with
             | [ n1 : _, E2 : _ |- _ ] => mtrans (Plus (Const n1) E2)
             | [ n1 : _, n2 : _ |- _ ] => mtrans (Plus (Const n1) (Const n2))
             | [ B : _, E2 : _ |- _ ] => mtrans (App (Abs B) E2)
           end.
Qed.

(** We are almost ready to prove the other direction of the equivalence.  First, we wrap an earlier lemma in a form that will work better with [eauto]. *)

Lemma Big_Val' : forall t (V1 V2 : Exp t),
  Val V2
  -> V1 = V2
  -> V1 ===> V2.
  crush.
Qed.

Hint Resolve Big_Val'.

(** Now we build some quite involved tactic support for reasoning about equalities over PHOAS terms.  First, we will call [equate_conj F G] to determine the consequences of an equality [F = G].  When [F = f e_1 ... e_n] and [G = f e'_1 ... e'_n], [equate_conj] will return a conjunction [e_1 = e'_1 /\ ... /\ e_n = e'_n].  We hardcode a pattern for each value of [n] from 1 to 5. *)

Ltac equate_conj F G :=
  match constr:(F, G) with
    | (_ ?x1, _ ?x2) => constr:(x1 = x2)
    | (_ ?x1 ?y1, _ ?x2 ?y2) => constr:(x1 = x2 /\ y1 = y2)
    | (_ ?x1 ?y1 ?z1, _ ?x2 ?y2 ?z2) => constr:(x1 = x2 /\ y1 = y2 /\ z1 = z2)
    | (_ ?x1 ?y1 ?z1 ?u1, _ ?x2 ?y2 ?z2 ?u2) =>
      constr:(x1 = x2 /\ y1 = y2 /\ z1 = z2 /\ u1 = u2)
    | (_ ?x1 ?y1 ?z1 ?u1 ?v1, _ ?x2 ?y2 ?z2 ?u2 ?v2) =>
      constr:(x1 = x2 /\ y1 = y2 /\ z1 = z2 /\ u1 = u2 /\ v1 = v2)
  end.

(** The main tactic is [my_crush], which generalizes our earlier [my_crush'] by performing inversion on hypotheses that equate PHOAS terms.  Coq's built-in [inversion] is only designed to be useful on equalities over inductive types.  PHOAS terms are functions, so [inversion] is not very helpful on them.  To perform the equivalent of [discriminate], we instantiate the terms with [var] as [fun _ => unit] and then appeal to normal [discriminate].  This eliminates some contradictory cases.  To perform the equivalent of [injection], we must consider all possible [var] instantiations.  Some fairly intricate logic strings together these elements.  The details are not worth discussing, since our conclusion will be that one should avoid dealing with proofs of facts like this one. *)

Ltac my_crush :=
  my_crush';
  repeat (match goal with
            | [ H : ?F = ?G |- _ ] =>
              (let H' := fresh "H'" in
                assert (H' : F (fun _ => unit) = G (fun _ => unit)); [ congruence
                  | discriminate || injection H'; clear H' ];
                my_crush';
                repeat match goal with
                         | [ H : context[fun _ => unit] |- _ ] => clear H
                       end;
                match type of H with
                  | ?F = ?G =>
                    let ec := equate_conj F G in
                      let var := fresh "var" in
                        assert ec; [ intuition; unfold Exp; apply ext_eq; intro var;
                          assert (H' : F var = G var); try congruence;
                            match type of H' with
                              | ?X = ?Y =>
                                let X := eval hnf in X in
                                  let Y := eval hnf in Y in
                                    change (X = Y) in H'
                            end; injection H'; my_crush'; tauto
                          | intuition; subst ]
                end);
              clear H
          end; my_crush');
  my_crush'.

(** With that complicated tactic available, the proof of the main lemma is straightforward. *)

Lemma Multi_Big' : forall t (E E' : Exp t),
  E ==> E'
  -> forall E'', E' ===> E''
    -> E ===> E''.
  induction 1; crush; eauto;
    match goal with
      | [ H : _ ===> _ |- _ ] => inversion H; my_crush; eauto
    end;
    match goal with
      | [ H : isCtx _ |- _ ] => inversion H; my_crush; eauto
    end.
Qed.

Hint Resolve Multi_Big'.

(** The other direction of the overall equivalence follows as an easy corollary. *)

Theorem Multi_Big : forall t (E V : Exp t),
  E ==>* V
  -> Val V
  -> E ===> V.
  induction 1; crush; eauto.
Qed.
(* end thide *)

(** The lesson here is that working directly with PHOAS terms can easily lead to extremely intricate proofs.  It is usually a better idea to stick to inductive proofs about %\textit{%#<i>#instantiated#</i>#%}% PHOAS terms; in the case of this example, that means proofs about [exp] instead of [Exp].  Such results can usually be wrapped into results about [Exp] without further induction.  Different theorems demand different variants of this underlying advice, and we will consider several of them in the chapters to come. *)
