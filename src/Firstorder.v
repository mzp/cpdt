(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith String List.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\part{Formalizing Programming Languages and Compilers}

   \chapter{First-Order Abstract Syntax}% *)

(** Many people interested in interactive theorem-proving want to prove theorems about programming languages.  That domain also provides a good setting for demonstrating how to apply the ideas from the earlier parts of this book.  This part introduces some techniques for encoding the syntax and semantics of programming languages, along with some example proofs designed to be as practical as possible, rather than to illustrate basic Coq technique.

   To prove anything about a language, we must first formalize the language's syntax.  We have a broad design space to choose from, and it makes sense to start with the simplest options, so-called %\textit{%#<i>#first-order#</i>#%}% syntax encodings that do not use dependent types.  These encodings are first-order because they do not use Coq function types in a critical way.  In this chapter, we consider the most popular first-order encodings, using each to prove a basic type soundness theorem. *)


(** * Concrete Binding *)

(** The most obvious encoding of the syntax of programming languages follows usual context-free grammars literally.  We represent variables as strings and include a variable in our AST definition wherever a variable appears in the informal grammar.  Concrete binding turns out to involve a surprisingly large amount of menial bookkeeping, especially when we encode higher-order languages with nested binder scopes.  This section's example should give a flavor of what is required. *)

Module Concrete.

  (** We need our variable type and its decidable equality operation. *)

  Definition var := string.
  Definition var_eq := string_dec.

  (** We will formalize basic simply-typed lambda calculus.  The syntax of expressions and types follows what we would write in a context-free grammar. *)

  Inductive exp : Set :=
  | Const : bool -> exp
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : var -> exp -> exp.

  Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

  (** It is useful to define a syntax extension that lets us write function types in more standard notation. *)

  Infix "-->" := Arrow (right associativity, at level 60).

  (** Now we turn to a typing judgment.  We will need to define it in terms of typing contexts, which we represent as lists of pairs of variables and types. *)

  Definition ctx := list (var * type).

  (** The definitions of our judgments will be prettier if we write them using mixfix syntax.  To define a judgment for looking up the type of a variable in a context, we first %\textit{%#</i>#reserve#</i>#%}% a notation for the judgment.  Reserved notations enable mutually-recursive definition of a judgment and its notation; in this sense, the reservation is like a forward declaration in C. *)

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  (** Now we define the judgment itself, for variable typing, using a [where] clause to associate a notation definition. *)

  Inductive lookup : ctx -> var -> type -> Prop :=
  | First : forall x t G,
    (x, t) :: G |-v x : t
  | Next : forall x t x' t' G,
    x <> x'
    -> G |-v x : t
    -> (x', t') :: G |-v x : t

    where "G |-v x : t" := (lookup G x t).

  Hint Constructors lookup.

  (** The same technique applies to defining the main typing judgment.  We use an [at next level] clause to cause the argument [e] of the notation to be parsed at a low enough precedence level. *)

  Reserved Notation "G |-e e : t" (no associativity, at level 90, e at next level).

  Inductive hasType : ctx -> exp -> type -> Prop :=
  | TConst : forall G b,
    G |-e Const b : Bool
  | TVar : forall G v t,
    G |-v v : t
    -> G |-e Var v : t
  | TApp : forall G e1 e2 dom ran,
    G |-e e1 : dom --> ran
    -> G |-e e2 : dom
    -> G |-e App e1 e2 : ran
  | TAbs : forall G x e' dom ran,
    (x, dom) :: G |-e e' : ran
    -> G |-e Abs x e' : dom --> ran

    where "G |-e e : t" := (hasType G e t).

  Hint Constructors hasType.

  (** It is useful to know that variable lookup results are unchanged by adding extra bindings to the end of a context. *)

  Lemma weaken_lookup : forall x t G' G1,
    G1 |-v x : t
    -> G1 ++ G' |-v x : t.
    induction G1 as [ | [? ?] ? ]; crush;
      match goal with
        | [ H : _ |-v _ : _ |- _ ] => inversion H; crush
      end.
  Qed.

  Hint Resolve weaken_lookup.

  (** The same property extends to the full typing judgment. *)

  Theorem weaken_hasType' : forall G' G e t,
    G |-e e : t
    -> G ++ G' |-e e : t.
    induction 1; crush; eauto.
  Qed.

  Theorem weaken_hasType : forall e t,
    nil |-e e : t
    -> forall G', G' |-e e : t.
    intros; change G' with (nil ++ G');
      eapply weaken_hasType'; eauto.
  Qed.

  Hint Resolve weaken_hasType.

  (** Much of the inconvenience of first-order encodings comes from the need to treat capture-avoiding substitution explicitly.  We must start by defining a substitution function. *)

  Section subst.
    Variable x : var.
    Variable e1 : exp.

    (** We are substituting expression [e1] for every free occurrence of [x].  Note that this definition is specialized to the case where [e1] is closed; substitution is substantially more complicated otherwise, potentially involving explicit alpha-variation.  Luckily, our example of type safety for a call-by-value semantics only requires this restricted variety of substitution. *)

    Fixpoint subst (e2 : exp) : exp :=
      match e2 with
        | Const _ => e2
        | Var x' => if var_eq x' x then e1 else e2
        | App e1 e2 => App (subst e1) (subst e2)
        | Abs x' e' => Abs x' (if var_eq x' x then e' else subst e')
      end.

    (** We can prove a few theorems about substitution in well-typed terms, where we assume that [e1] is closed and has type [xt]. *)

    Variable xt : type.
    Hypothesis Ht' : nil |-e e1 : xt.

    (** It is helpful to establish a notation asserting the freshness of a particular variable in a context. *)

    Notation "x # G" := (forall t' : type, In (x, t') G -> False) (no associativity, at level 90).

    (** To prove type preservation, we will need lemmas proving consequences of variable lookup proofs. *)

    Lemma subst_lookup' : forall x' t,
      x <> x'
      -> forall G1, G1 ++ (x, xt) :: nil |-v x' : t
        -> G1 |-v x' : t.
      induction G1 as [ | [? ?] ? ]; crush;
        match goal with
          | [ H : _ |-v _ : _ |- _ ] => inversion H
        end; crush.
    Qed.

    Hint Resolve subst_lookup'.

    Lemma subst_lookup : forall x' t G1,
      x' # G1
      -> G1 ++ (x, xt) :: nil |-v x' : t
      -> t = xt.
      induction G1 as [ | [? ?] ? ]; crush; eauto;
        match goal with
          | [ H : _ |-v _ : _ |- _ ] => inversion H
        end; crush; (elimtype False; eauto;
          match goal with
            | [ H : nil |-v _ : _ |- _ ] => inversion H
          end)
        || match goal with
             | [ H : _ |- _ ] => apply H; crush; eauto
           end.
    Qed.

    Implicit Arguments subst_lookup [x' t G1].

    (** Another set of lemmas allows us to remove provably unused variables from the ends of typing contexts. *)

    Lemma shadow_lookup : forall v t t' G1,
      G1 |-v x : t'
      -> G1 ++ (x, xt) :: nil |-v v : t
      -> G1 |-v v : t.
      induction G1 as [ | [? ?] ? ]; crush;
        match goal with
          | [ H : nil |-v _ : _ |- _ ] => inversion H
          | [ H1 : _ |-v _ : _, H2 : _ |-v _ : _ |- _ ] =>
            inversion H1; crush; inversion H2; crush
        end.
    Qed.

    Lemma shadow_hasType' : forall G e t,
      G |-e e : t
      -> forall G1, G = G1 ++ (x, xt) :: nil
        -> forall t'', G1 |-v x : t''
          -> G1 |-e e : t.
      Hint Resolve shadow_lookup.

      induction 1; crush; eauto;
        match goal with
          | [ H : (?x0, _) :: _ ++ (?x, _) :: _ |-e _ : _ |- _ ] =>
            destruct (var_eq x0 x); subst; eauto
        end.
    Qed.

    Lemma shadow_hasType : forall G1 e t t'',
      G1 ++ (x, xt) :: nil |-e e : t
      -> G1 |-v x : t''
      -> G1 |-e e : t.
      intros; eapply shadow_hasType'; eauto.
    Qed.

    Hint Resolve shadow_hasType.

    (** Disjointness facts may be extended to larger contexts when the appropriate obligations are met. *)

    Lemma disjoint_cons : forall x x' t (G : ctx),
      x # G
      -> x' <> x
      -> x # (x', t) :: G.
      firstorder;
        match goal with
          | [ H : (_, _) = (_, _) |- _ ] => injection H
        end; crush.
    Qed.

    Hint Resolve disjoint_cons.

    (** Finally, we arrive at the main theorem about substitution: it preserves typing. *)

    Theorem subst_hasType : forall G e2 t,
      G |-e e2 : t
        -> forall G1, G = G1 ++ (x, xt) :: nil
          -> x # G1
          -> G1 |-e subst e2 : t.
      induction 1; crush;
        try match goal with
              | [ |- context[if ?E then _ else _] ] => destruct E
            end; crush; eauto 6;
        match goal with
          | [ H1 : x # _, H2 : _ |-v x : _ |- _ ] =>
            rewrite (subst_lookup H1 H2)
        end; crush.
    Qed.

    (** We wrap the last theorem into an easier-to-apply form specialized to closed expressions. *)

    Theorem subst_hasType_closed : forall e2 t,
      (x, xt) :: nil |-e e2 : t
      -> nil |-e subst e2 : t.
      intros; eapply subst_hasType; eauto.
    Qed.
  End subst.

  Hint Resolve subst_hasType_closed.

  (** A notation for substitution will make the operational semantics easier to read. *)

  Notation "[ x ~> e1 ] e2" := (subst x e1 e2) (no associativity, at level 80).

  (** To define a call-by-value small-step semantics, we rely on a standard judgment characterizing which expressions are values. *)

  Inductive val : exp -> Prop :=
  | VConst : forall b, val (Const b)
  | VAbs : forall x e, val (Abs x e).

  Hint Constructors val.

  (** Now the step relation is easy to define. *)

  Reserved Notation "e1 ==> e2" (no associativity, at level 90).

  Inductive step : exp -> exp -> Prop :=
  | Beta : forall x e1 e2,
    val e2
    -> App (Abs x e1) e2 ==> [x ~> e2] e1
  | Cong1 : forall e1 e2 e1',
    e1 ==> e1'
    -> App e1 e2 ==> App e1' e2
  | Cong2 : forall e1 e2 e2',
    val e1
    -> e2 ==> e2'
    -> App e1 e2 ==> App e1 e2'

    where "e1 ==> e2" := (step e1 e2).

  Hint Constructors step.

  (** The progress theorem says that any well-typed expression can take a step.  To deal with limitations of the [induction] tactic, we put most of the proof in a lemma whose statement uses the usual trick of introducing extra equality hypotheses. *)

  Lemma progress' : forall G e t, G |-e e : t
    -> G = nil
    -> val e \/ exists e', e ==> e'.
    induction 1; crush; eauto;
      try match goal with
            | [ H : _ |-e _ : _ --> _ |- _ ] => inversion H
          end;
      match goal with
        | [ H : _ |- _ ] => solve [ inversion H; crush; eauto ]
      end.
  Qed.

  Theorem progress : forall e t, nil |-e e : t
    -> val e \/ exists e', e ==> e'.
    intros; eapply progress'; eauto.
  Qed.

  (** A similar pattern works for the preservation theorem, which says that any step of execution preserves an expression's type. *)

  Lemma preservation' : forall G e t, G |-e e : t
    -> G = nil
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    induction 1; inversion 2; crush; eauto;
      match goal with
        | [ H : _ |-e Abs _ _ : _ |- _ ] => inversion H
      end; eauto.
  Qed.

  Theorem preservation : forall e t, nil |-e e : t
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    intros; eapply preservation'; eauto.
  Qed.

End Concrete.

(** This was a relatively simple example, giving only a taste of the proof burden associated with concrete syntax.  We were helped by the fact that, with call-by-value semantics, we only need to reason about substitution in closed expressions.  There was also no need to alpha-vary an expression. *)


(** * De Bruijn Indices *)

(** De Bruijn indices are much more popular than concrete syntax.  This technique provides a %\textit{%#<i>#canonical#</i>#%}% representation of syntax, where any two alpha-equivalent expressions have syntactically equal encodings, removing the need for explicit reasoning about alpha conversion.  Variables are represented as natural numbers, where variable [n] denotes a reference to the [n]th closest enclosing binder.  Because variable references in effect point to binders, there is no need to label binders, such as function abstraction, with variables. *)

Module DeBruijn.

  Definition var := nat.
  Definition var_eq := eq_nat_dec.

  Inductive exp : Set :=
  | Const : bool -> exp
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : exp -> exp.

  Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

  (** The definition of typing proceeds much the same as in the last section.  Since variables are numbers, contexts can be simple lists of types.  This makes it possible to write the lookup judgment without mentioning inequality of variables. *)

  Definition ctx := list type.

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  Inductive lookup : ctx -> var -> type -> Prop :=
  | First : forall t G,
    t :: G |-v O : t
  | Next : forall x t t' G,
    G |-v x : t
    -> t' :: G |-v S x : t

    where "G |-v x : t" := (lookup G x t).

  Hint Constructors lookup.

  Reserved Notation "G |-e e : t" (no associativity, at level 90, e at next level).

  Inductive hasType : ctx -> exp -> type -> Prop :=
  | TConst : forall G b,
    G |-e Const b : Bool
  | TVar : forall G v t,
    G |-v v : t
    -> G |-e Var v : t
  | TApp : forall G e1 e2 dom ran,
    G |-e e1 : dom --> ran
    -> G |-e e2 : dom
    -> G |-e App e1 e2 : ran
  | TAbs : forall G e' dom ran,
    dom :: G |-e e' : ran
    -> G |-e Abs e' : dom --> ran

    where "G |-e e : t" := (hasType G e t).

  (** In the [hasType] case for function abstraction, there is no need to choose a variable name.  We simply push the function domain type onto the context [G]. *)

  Hint Constructors hasType.

  (** We prove roughly the same weakening theorems as before. *)

  Lemma weaken_lookup : forall G' v t G,
    G |-v v : t
    -> G ++ G' |-v v : t.
    induction 1; crush.
  Qed.

  Hint Resolve weaken_lookup.

  Theorem weaken_hasType' : forall G' G e t,
    G |-e e : t
    -> G ++ G' |-e e : t.
    induction 1; crush; eauto.
  Qed.

  Theorem weaken_hasType : forall e t,
    nil |-e e : t
    -> forall G', G' |-e e : t.
    intros; change G' with (nil ++ G');
      eapply weaken_hasType'; eauto.
  Qed.

  Hint Resolve weaken_hasType.

  Section subst.
    Variable e1 : exp.

    (** Substitution is easier to define than with concrete syntax.  While our old definition needed to use two comparisons for equality of variables, the de Bruijn substitution only needs one comparison. *)

    Fixpoint subst (x : var) (e2 : exp) : exp :=
      match e2 with
        | Const _ => e2
        | Var x' => if var_eq x' x then e1 else e2
        | App e1 e2 => App (subst x e1) (subst x e2)
        | Abs e' => Abs (subst (S x) e')
      end.

    Variable xt : type.

    (** We prove similar theorems about inversion of variable lookup. *)

    Lemma subst_eq : forall t G1,
      G1 ++ xt :: nil |-v length G1 : t
      -> t = xt.
      induction G1; inversion 1; crush.
    Qed.

    Implicit Arguments subst_eq [t G1].

    Lemma subst_eq' : forall t G1 x,
      G1 ++ xt :: nil |-v x : t
      -> x <> length G1
      -> G1 |-v x : t.
      induction G1; inversion 1; crush;
        match goal with
          | [ H : nil |-v _ : _ |- _ ] => inversion H
        end.
    Qed.

    Hint Resolve subst_eq'.

    Lemma subst_neq : forall v t G1,
      G1 ++ xt :: nil |-v v : t
      -> v <> length G1
      -> G1 |-e Var v : t.
      induction G1; inversion 1; crush.
    Qed.

    Hint Resolve subst_neq.

    Hypothesis Ht' : nil |-e e1 : xt.

    (** The next lemma is included solely to guide [eauto], which will not apply computational equivalences automatically. *)

    Lemma hasType_push : forall dom G1 e' ran,
      dom :: G1 |-e subst (length (dom :: G1)) e' : ran
      -> dom :: G1 |-e subst (S (length G1)) e' : ran.
      trivial.
    Qed.

    Hint Resolve hasType_push.

    (** Finally, we are ready for the main theorem about substitution and typing. *)

    Theorem subst_hasType : forall G e2 t,
      G |-e e2 : t
        -> forall G1, G = G1 ++ xt :: nil
          -> G1 |-e subst (length G1) e2 : t.
      induction 1; crush;
        try match goal with
              | [ |- context[if ?E then _ else _] ] => destruct E
            end; crush; eauto 6;
        try match goal with
              | [ H : _ |-v _ : _ |- _ ] =>
                rewrite (subst_eq H)
            end; crush.
    Qed.

    Theorem subst_hasType_closed : forall e2 t,
      xt :: nil |-e e2 : t
      -> nil |-e subst O e2 : t.
      intros; change O with (length (@nil type)); eapply subst_hasType; eauto.
    Qed.
  End subst.

  Hint Resolve subst_hasType_closed.

  (** We define the operational semantics much as before. *)

  Notation "[ x ~> e1 ] e2" := (subst e1 x e2) (no associativity, at level 80).

  Inductive val : exp -> Prop :=
  | VConst : forall b, val (Const b)
  | VAbs : forall e, val (Abs e).

  Hint Constructors val.

  Reserved Notation "e1 ==> e2" (no associativity, at level 90).

  Inductive step : exp -> exp -> Prop :=
  | Beta : forall e1 e2,
    val e2
    -> App (Abs e1) e2 ==> [O ~> e2] e1
  | Cong1 : forall e1 e2 e1',
    e1 ==> e1'
    -> App e1 e2 ==> App e1' e2
  | Cong2 : forall e1 e2 e2',
    val e1
    -> e2 ==> e2'
    -> App e1 e2 ==> App e1 e2'

    where "e1 ==> e2" := (step e1 e2).

  Hint Constructors step.

  (** Since we have added the right hints, the progress and preservation theorem statements and proofs are exactly the same as in the concrete encoding example. *)

  Lemma progress' : forall G e t, G |-e e : t
    -> G = nil
    -> val e \/ exists e', e ==> e'.
    induction 1; crush; eauto;
      try match goal with
            | [ H : _ |-e _ : _ --> _ |- _ ] => inversion H
          end;
      repeat match goal with
               | [ H : _ |- _ ] => solve [ inversion H; crush; eauto ]
             end.
  Qed.

  Theorem progress : forall e t, nil |-e e : t
    -> val e \/ exists e', e ==> e'.
    intros; eapply progress'; eauto.
  Qed.

  Lemma preservation' : forall G e t, G |-e e : t
    -> G = nil
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    induction 1; inversion 2; crush; eauto;
      match goal with
        | [ H : _ |-e Abs _ : _ |- _ ] => inversion H
      end; eauto.
  Qed.

  Theorem preservation : forall e t, nil |-e e : t
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    intros; eapply preservation'; eauto.
  Qed.

End DeBruijn.


(** * Locally Nameless Syntax *)

(** The most popular Coq syntax encoding today is the %\textit{%#<i>#locally nameless#</i>#%}% style, which has been around for a while but was popularized recently by Aydemir et al., following a methodology summarized in their paper "Engineering Formal Metatheory."  #<a href="http://www.cis.upenn.edu/~plclub/oregon08/">#A specialized tutorial by that group#</a>#%\footnote{\url{http://www.cis.upenn.edu/~plclub/oregon08/}}% explains the approach, based on a library.  In this section, we will build up all of the necessary ingredients from scratch.

   The one-sentence summary of locally nameless encoding is that we represent free variables as concrete syntax does, and we represent bound variables with de Bruijn indices.  Many proofs involve reasoning about terms transplanted into different free variable contexts; concrete encoding of free variables means that, to perform such a transplanting, we need no fix-up operation to adjust de Bruijn indices.  At the same time, use of de Bruijn indices for local variables gives us canonical representations of expressions, with respect to the usual convention of alpha-equivalence.  This makes many operations, including substitution of open terms in open terms, easier to implement.

   The "Engineering Formal Metatheory" methodology involves a number of subtle design decisions, which we will describe as they appear in the latest version of our running example. *)

Module LocallyNameless.

  Definition free_var := string.
  Definition bound_var := nat.

  Inductive exp : Set :=
  | Const : bool -> exp
  | FreeVar : free_var -> exp
  | BoundVar : bound_var -> exp
  | App : exp -> exp -> exp
  | Abs : exp -> exp.

  (** Note the different constructors for free vs. bound variables, and note that the lack of a variable annotation on [Abs] nodes is inherited from the de Bruijn convention. *)

  Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

  (** As typing only depends on types of free variables, our contexts borrow their form from the concrete binding example.  *)

  Definition ctx := list (free_var * type).

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  Inductive lookup : ctx -> free_var -> type -> Prop :=
  | First : forall x t G,
    (x, t) :: G |-v x : t
  | Next : forall x t x' t' G,
    x <> x'
    -> G |-v x : t
    -> (x', t') :: G |-v x : t

    where "G |-v x : t" := (lookup G x t).

  Hint Constructors lookup.

  (** The first unusual operation we need is %\textit{%#<i>#opening#</i>#%}%, where we replace a particular bound variable with a particular free variable.  Whenever we "go under a binder," in the typing judgment or elsewhere, we choose a new free variable to replace the old bound variable of the binder.  Opening implements the replacement of one by the other.  It is like a specialized version of the substitution function we used for pure de Bruijn terms. *)

  Section open.
    Variable x : free_var.

    Fixpoint open (n : bound_var) (e : exp) : exp :=
      match e with
        | Const _ => e
        | FreeVar _ => e
        | BoundVar n' =>
          if eq_nat_dec n' n
            then FreeVar x
            else if le_lt_dec n' n
              then e
              else BoundVar (pred n')
        | App e1 e2 => App (open n e1) (open n e2)
        | Abs e1 => Abs (open (S n) e1)
      end.
  End open.

  (** We will also need to reason about an expression's set of free variables.  To keep things simple, we represent sets as lists that may contain duplicates.  Note how much easier this operation is to implement than over pure de Bruijn terms, since we do not need to maintain a separate numeric argument that keeps track of how deeply we have descended into the input expression. *)

  Fixpoint freeVars (e : exp) : list free_var :=
    match e with
      | Const _ => nil
      | FreeVar x => x :: nil
      | BoundVar _ => nil
      | App e1 e2 => freeVars e1 ++ freeVars e2
      | Abs e1 => freeVars e1
    end.

  (** It will be useful to have a well-formedness judgment for our terms.  This notion is called %\textit{%#<i>#local closure#</i>#%}%.  An expression may be declared to be closed, up to a particular maximum de Bruijn index. *)

  Inductive lclosed : nat -> exp -> Prop :=
  | CConst : forall n b, lclosed n (Const b)
  | CFreeVar : forall n v, lclosed n (FreeVar v)
  | CBoundVar : forall n v, v < n -> lclosed n (BoundVar v)
  | CApp : forall n e1 e2, lclosed n e1 -> lclosed n e2 -> lclosed n (App e1 e2)
  | CAbs : forall n e1, lclosed (S n) e1 -> lclosed n (Abs e1).

  Hint Constructors lclosed.

  (** Now we are ready to define the typing judgment. *)

  Reserved Notation "G |-e e : t" (no associativity, at level 90, e at next level).

  Inductive hasType : ctx -> exp -> type -> Prop :=
  | TConst : forall G b,
    G |-e Const b : Bool
  | TFreeVar : forall G v t,
    G |-v v : t
    -> G |-e FreeVar v : t
  | TApp : forall G e1 e2 dom ran,
    G |-e e1 : dom --> ran
    -> G |-e e2 : dom
    -> G |-e App e1 e2 : ran
  | TAbs : forall G e' dom ran L,
    (forall x, ~ In x L -> (x, dom) :: G |-e open x O e' : ran)
    -> G |-e Abs e' : dom --> ran

    where "G |-e e : t" := (hasType G e t).

  (** Compared to the previous versions, only the [TAbs] rule is surprising.  The rule uses %\textit{%#<i>#co-finite quantiifcation#</i>#%}%.  That is, the premise of the rule quantifies over all [x] values that are not members of a finite set [L].  A proof may choose any value of [L] when applying [TAbs].  An alternate, more intuitive version of the rule would fix [L] to be [freeVars e'].  It turns out that the greater flexibility of the rule above simplifies many proofs significantly.  This typing judgment may be proved equivalent to the more intuitive version, though we will not carry out the proof here.

     Specifially, what our version of [TAbs] says is that, to prove that [Abs e'] has a function type, we must prove that any opening of [e'] with a variable not in [L] has the proper type.  For each [x] choice, we extend the context [G] in the usual way. *)

  Hint Constructors hasType.

  (** We prove a standard weakening theorem for typing, adopting a more general form than in the previous sections. *)

  Lemma lookup_push : forall G G' x t x' t',
    (forall x t, G |-v x : t -> G' |-v x : t)
    -> (x, t) :: G |-v x' : t'
    -> (x, t) :: G' |-v x' : t'.
    inversion 2; crush.
  Qed.

  Hint Resolve lookup_push.

  Theorem weaken_hasType : forall G e t,
    G |-e e : t
    -> forall G', (forall x t, G |-v x : t -> G' |-v x : t)
      -> G' |-e e : t.
    induction 1; crush; eauto.
  Qed.

  Hint Resolve weaken_hasType.

  (** We define a simple extension of [crush] to apply in many of the lemmas that follow. *)

  Ltac ln := crush;
    repeat (match goal with
              | [ |- context[if ?E then _ else _] ] => destruct E
              | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
            end; crush); eauto.

  (** Two basic properties of local closure will be useful later. *)
  
  Lemma lclosed_S : forall x e n,
    lclosed n (open x n e)
    -> lclosed (S n) e.
    induction e; inversion 1; ln.
  Qed.

  Hint Resolve lclosed_S.

  Lemma lclosed_weaken : forall n e,
    lclosed n e
    -> forall n', n' >= n
      -> lclosed n' e.
    induction 1; crush.
  Qed.

  Hint Resolve lclosed_weaken.
  Hint Extern 1 (_ >= _) => omega.

  (** To prove some further properties, we need the ability to choose a variable that is disjoint from a particular finite set.  We implement a specific choice function [fresh]; its details do not matter, as all we need is the final theorem about it, [freshOk].  Concretely, to choose a variable disjoint from set [L], we sum the lengths of the variable names in [L] and choose a new variable name that is one longer than that sum.  This variable can be the string ["x"], followed by a number of primes equal to the sum. *)

  Open Scope string_scope.
  
  Fixpoint primes (n : nat) : string :=
    match n with
      | O => "x"
      | S n' => primes n' ++ "'"
    end.

  Fixpoint sumLengths (L : list free_var) : nat :=
    match L with
      | nil => O
      | x :: L' => String.length x + sumLengths L'
    end.

  Definition fresh (L : list free_var) := primes (sumLengths L).

  (** A few lemmas suffice to establish the correctness theorem [freshOk] for [fresh]. *)

  Theorem freshOk' : forall x L, String.length x > sumLengths L
    -> ~ In x L.
    induction L; crush.
  Qed.

  Lemma length_app : forall s2 s1,
    String.length (s1 ++ s2) = String.length s1 + String.length s2.
    induction s1; crush.
  Qed.

  Hint Rewrite length_app : cpdt.

  Lemma length_primes : forall n, String.length (primes n) = S n.
    induction n; crush.
  Qed.

  Hint Rewrite length_primes : cpdt.

  Theorem freshOk : forall L, ~ In (fresh L) L.
    intros; apply freshOk'; unfold fresh; crush.
  Qed.

  Hint Resolve freshOk.

  (** Now we can prove that well-typedness implies local closure.  [fresh] will be used for us automatically by [eauto] in the [Abs] case, driven by the presence of [freshOk] as a hint. *)

  Lemma hasType_lclosed : forall G e t,
    G |-e e : t
    -> lclosed O e.
    induction 1; eauto.
  Qed.

  (** An important consequence of local closure is that certain openings are idempotent. *)

  Lemma lclosed_open : forall n e, lclosed n e
    -> forall x, open x n e = e.
    induction 1; ln.
  Qed.

  Hint Resolve lclosed_open hasType_lclosed.

  Open Scope list_scope.

  (** We are now almost ready to get down to the details of substitution.  First, we prove six lemmas related to treating lists as sets. *)

  Lemma In_cons1 : forall T (x x' : T) ls,
    x = x'
    -> In x (x' :: ls).
    crush.
  Qed.

  Lemma In_cons2 : forall T (x x' : T) ls,
    In x ls
    -> In x (x' :: ls).
    crush.
  Qed.

  Lemma In_app1 : forall T (x : T) ls2 ls1,
    In x ls1
    -> In x (ls1 ++ ls2).
    induction ls1; crush.
  Qed.

  Lemma In_app2 : forall T (x : T) ls2 ls1,
    In x ls2
    -> In x (ls1 ++ ls2).
    induction ls1; crush.
  Qed.

  Lemma freshOk_app1 : forall L1 L2,
    ~ In (fresh (L1 ++ L2)) L1.
    intros; generalize (freshOk (L1 ++ L2)); crush.
  Qed.

  Lemma freshOk_app2 : forall L1 L2,
    ~ In (fresh (L1 ++ L2)) L2.
    intros; generalize (freshOk (L1 ++ L2)); crush.
  Qed.

  Hint Resolve In_cons1 In_cons2 In_app1 In_app2.

  (** Now we can define our simplest substitution function yet, thanks to the fact that we only subsitute for free variables, which are distinguished syntactically from bound variables. *)

  Section subst.
    Hint Resolve freshOk_app1 freshOk_app2.

    Variable x : free_var.
    Variable e1 : exp.

    Fixpoint subst (e2 : exp) : exp :=
      match e2 with
        | Const _ => e2
        | FreeVar x' => if string_dec x' x then e1 else e2
        | BoundVar _ => e2
        | App e1 e2 => App (subst e1) (subst e2)
        | Abs e' => Abs (subst e')
      end.

    Variable xt : type.

    (** It comes in handy to define disjointness of a variable and a context differently than in previous examples.  We use the standard list function [map], as well as the function [fst] for projecting the first element of a pair.  We write [@fst _ _] rather than just [fst] to ask that [fst]'s implicit arguments be instantiated with inferred values. *)

    Definition disj x (G : ctx) := In x (map (@fst _ _) G) -> False.
    Infix "#" := disj (no associativity, at level 90).

    Ltac disj := crush;
      match goal with
        | [ _ : _ :: _ = ?G0 ++ _ |- _ ] => destruct G0
      end; crush; eauto.

    (** Some basic properties of variable lookup will be needed on the road to our usual theorem connecting substitution and typing. *)

    Lemma lookup_disj' : forall t G1,
      G1 |-v x : t
      -> forall G, x # G
        -> G1 = G ++ (x, xt) :: nil
        -> t = xt.
      unfold disj; induction 1; disj.
    Qed.

    Lemma lookup_disj : forall t G,
      x # G
      -> G ++ (x, xt) :: nil |-v x : t
      -> t = xt.
      intros; eapply lookup_disj'; eauto.
    Qed.

    Lemma lookup_ne' : forall G1 v t,
      G1 |-v v : t
      -> forall G, G1 = G ++ (x, xt) :: nil
        -> v <> x
        -> G |-v v : t.
      induction 1; disj.
    Qed.

    Lemma lookup_ne : forall G v t,
      G ++ (x, xt) :: nil |-v v : t
      -> v <> x
      -> G |-v v : t.
      intros; eapply lookup_ne'; eauto.
    Qed.

    Hint Extern 1 (_ |-e _ : _) =>
      match goal with
        | [ H1 : _, H2 : _ |- _ ] => rewrite (lookup_disj H1 H2)
      end.
    Hint Resolve lookup_ne.

    Hint Extern 1 (@eq exp _ _) => f_equal.

    (** We need to know that substitution and opening commute under appropriate circumstances. *)

    Lemma open_subst : forall x0 e' n,
      lclosed n e1
      -> x <> x0
      -> open x0 n (subst e') = subst (open x0 n e').
      induction e'; ln.
    Qed.

    (** We state a corollary of the last result which will work more smoothly with [eauto]. *)

    Lemma hasType_open_subst : forall G x0 e t,
      G |-e subst (open x0 0 e) : t
      -> x <> x0
      -> lclosed 0 e1
      -> G |-e open x0 0 (subst e) : t.
      intros; rewrite open_subst; eauto.
    Qed.

    Hint Resolve hasType_open_subst.

    (** Another lemma establishes the validity of weakening variable lookup judgments with fresh variables. *)

    Lemma disj_push : forall x0 (t : type) G,
      x # G
      -> x <> x0
      -> x # (x0, t) :: G.
      unfold disj; crush.
    Qed.

    Hint Resolve disj_push.

    Lemma lookup_cons : forall x0 dom G x1 t,
      G |-v x1 : t
      -> ~ In x0 (map (@fst _ _) G)
      -> (x0, dom) :: G |-v x1 : t.
      induction 1; crush;
        match goal with
          | [ H : _ |-v _ : _ |- _ ] => inversion H
        end; crush.
    Qed.

    Hint Resolve lookup_cons.
    Hint Unfold disj.

    (** Finally, it is useful to state a version of the [TAbs] rule specialized to the choice of [L] that is useful in our main substitution proof. *)

    Lemma TAbs_specialized : forall G e' dom ran L x1,
      (forall x, ~ In x (x1 :: L ++ map (@fst _ _) G) -> (x, dom) :: G |-e open x O e' : ran)
      -> G |-e Abs e' : dom --> ran.
      eauto.
    Qed.

    (** Now we can prove the main inductive lemma in a manner similar to what worked for concrete binding. *)

    Lemma hasType_subst' : forall G1 e t,
      G1 |-e e : t
      -> forall G, G1 = G ++ (x, xt) :: nil
        -> x # G
        -> G |-e e1 : xt
        -> G |-e subst e : t.
      induction 1; ln;
        match goal with
          | [ L : list free_var, _ : ?x # _ |- _ ] =>
            apply TAbs_specialized with L x; eauto 20
        end.
    Qed.

    (** The main theorem about substitution of closed expressions follows easily. *)

    Theorem hasType_subst : forall e t,
      (x, xt) :: nil |-e e : t
      -> nil |-e e1 : xt
      -> nil |-e subst e : t.
      intros; eapply hasType_subst'; eauto.
    Qed.
  End subst.

  Hint Resolve hasType_subst.

  (** We can define the operational semantics in almost the same way as in previous examples. *)

  Notation "[ x ~> e1 ] e2" := (subst x e1 e2) (no associativity, at level 60).

  Inductive val : exp -> Prop :=
  | VConst : forall b, val (Const b)
  | VAbs : forall e, val (Abs e).

  Hint Constructors val.

  Reserved Notation "e1 ==> e2" (no associativity, at level 90).

  Inductive step : exp -> exp -> Prop :=
  | Beta : forall e1 e2 x,
    val e2
    -> ~ In x (freeVars e1)
    -> App (Abs e1) e2 ==> [x ~> e2] (open x O e1)
  | Cong1 : forall e1 e2 e1',
    e1 ==> e1'
    -> App e1 e2 ==> App e1' e2
  | Cong2 : forall e1 e2 e2',
    val e1
    -> e2 ==> e2'
    -> App e1 e2 ==> App e1 e2'

    where "e1 ==> e2" := (step e1 e2).

  Hint Constructors step.

  (** The only interesting change is that the [Beta] rule requires identifying a fresh variable [x] to use in opening the abstraction body.  We could have avoided this by implementing a more general [open] that allows substituting expressions for variables, not just variables for variables, but it simplifies the proofs to have just one general substitution function.

     Now we are ready to prove progress and preservation.  The same proof script from the last examples suffices to prove progress, though significantly different lemmas are applied for us by [eauto]. *)

  Lemma progress' : forall G e t, G |-e e : t
    -> G = nil
    -> val e \/ exists e', e ==> e'.
    induction 1; crush; eauto;
      try match goal with
            | [ H : _ |-e _ : _ --> _ |- _ ] => inversion H
          end;
      repeat match goal with
               | [ H : _ |- _ ] => solve [ inversion H; crush; eauto ]
             end.
  Qed.

  Theorem progress : forall e t, nil |-e e : t
    -> val e \/ exists e', e ==> e'.
    intros; eapply progress'; eauto.
  Qed.

  (** To establish preservation, it is useful to formalize a principle of sound alpha-variation.  In particular, when we open an expression with a particular variable and then immediately substitute for the same variable, we can replace that variable with any other that is not free in the body of the opened expression. *)

  Lemma alpha_open : forall x1 x2 e1 e2 n,
    ~ In x1 (freeVars e2)
    -> ~ In x2 (freeVars e2)
    -> [x1 ~> e1](open x1 n e2) = [x2 ~> e1](open x2 n e2).
    induction e2; ln.
  Qed.

  Hint Resolve freshOk_app1 freshOk_app2.

  (** Again it is useful to state a direct corollary which is easier to apply in proof search. *)

  Lemma hasType_alpha_open : forall G L e0 e2 x t,
    ~ In x (freeVars e0)
    -> G |-e [fresh (L ++ freeVars e0) ~> e2](open (fresh (L ++ freeVars e0)) 0 e0) : t
    -> G |-e [x ~> e2](open x 0 e0) : t.
    intros; rewrite (alpha_open x (fresh (L ++ freeVars e0))); auto.
  Qed.

  Hint Resolve hasType_alpha_open.

  (** Now the previous sections' preservation proof scripts finish the job. *)

  Lemma preservation' : forall G e t, G |-e e : t
    -> G = nil
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    induction 1; inversion 2; crush; eauto;
      match goal with
        | [ H : _ |-e Abs _ : _ |- _ ] => inversion H
      end; eauto.
  Qed.

  Theorem preservation : forall e t, nil |-e e : t
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    intros; eapply preservation'; eauto.
  Qed.

End LocallyNameless.
