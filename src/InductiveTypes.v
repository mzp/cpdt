(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import List.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\part{Basic Programming and Proving}

\chapter{Introducing Inductive Types}% *)

(** In a sense, CIC is built from just two relatively straightforward features: function types and inductive types.  From this modest foundation, we can prove effectively all of the theorems of math and carry out effectively all program verifications, with enough effort expended.  This chapter introduces induction and recursion for functional programming in Coq. *)


(** * Enumerations *)

(** Coq inductive types generalize the algebraic datatypes found in Haskell and ML.  Confusingly enough, inductive types also generalize generalized algebraic datatypes (GADTs), by adding the possibility for type dependency.  Even so, it is worth backing up from the examples of the last chapter and going over basic, algebraic datatype uses of inductive datatypes, because the chance to prove things about the values of these types adds new wrinkles beyond usual practice in Haskell and ML.

The singleton type [unit] is an inductive type: *)

Inductive unit : Set :=
  | tt.

(** This vernacular command defines a new inductive type [unit] whose only value is [tt], as we can see by checking the types of the two identifiers: *)

Check unit.
(** [unit : Set] *)

Check tt.
(** [tt : unit] *)

(** We can prove that [unit] is a genuine singleton type. *)

Theorem unit_singleton : forall x : unit, x = tt.

(** The important thing about an inductive type is, unsurprisingly, that you can do induction over its values, and induction is the key to proving this theorem.  We ask to proceed by induction on the variable [x]. *)

(* begin thide *)
  induction x.

(** The goal changes to:
[[
 tt = tt
]] *)

  (** ...which we can discharge trivially. *)

  reflexivity.
Qed.
(* end thide *)

(** It seems kind of odd to write a proof by induction with no inductive hypotheses.  We could have arrived at the same result by beginning the proof with: [[

  destruct x.

]]

%\noindent%...which corresponds to "proof by case analysis" in classical math.  For non-recursive inductive types, the two tactics will always have identical behavior.  Often case analysis is sufficient, even in proofs about recursive types, and it is nice to avoid introducing unneeded induction hypotheses.

What exactly %\textit{%#<i>#is#</i>#%}% the induction principle for [unit]?  We can ask Coq: *)

Check unit_ind.
(** [unit_ind : forall P : unit -> Prop, P tt -> forall u : unit, P u] *)

(** Every [Inductive] command defining a type [T] also defines an induction principle named [T_ind].  Coq follows the Curry-Howard correspondence and includes the ingredients of programming and proving in the same single syntactic class.  Thus, our type, operations over it, and principles for reasoning about it all live in the same language and are described by the same type system.  The key to telling what is a program and what is a proof lies in the distinction between the type [Prop], which appears in our induction principle; and the type [Set], which we have seen a few times already.

The convention goes like this: [Set] is the type of normal types, and the values of such types are programs.  [Prop] is the type of logical propositions, and the values of such types are proofs.  Thus, an induction principle has a type that shows us that it is a function for building proofs.

Specifically, [unit_ind] quantifies over a predicate [P] over [unit] values.  If we can present a proof that [P] holds of [tt], then we are rewarded with a proof that [P] holds for any value [u] of type [unit].  In our last proof, the predicate was [(fun u : unit => u = tt)].

%\medskip%

We can define an inductive type even simpler than [unit]: *)

Inductive Empty_set : Set := .

(** [Empty_set] has no elements.  We can prove fun theorems about it: *)

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
(* begin thide *)
  destruct 1.
Qed.
(* end thide *)

(** Because [Empty_set] has no elements, the fact of having an element of this type implies anything.  We use [destruct 1] instead of [destruct x] in the proof because unused quantified variables are relegated to being referred to by number.  (There is a good reason for this, related to the unity of quantifiers and implication.  An implication is just a quantification over a proof, where the quantified variable is never used.  It generally makes more sense to refer to implication hypotheses by number than by name, and Coq treats our quantifier over an unused variable as an implication in determining the proper behavior.)

We can see the induction principle that made this proof so easy: *)

Check Empty_set_ind.
(** [Empty_set_ind : forall (P : Empty_set -> Prop) (e : Empty_set), P e] *)

(** In other words, any predicate over values from the empty set holds vacuously of every such element.  In the last proof, we chose the predicate [(fun _ : Empty_set => 2 + 2 = 5)].

We can also apply this get-out-of-jail-free card programmatically.  Here is a lazy way of converting values of [Empty_set] to values of [unit]: *)

Definition e2u (e : Empty_set) : unit := match e with end.

(** We employ [match] pattern matching as in the last chapter.  Since we match on a value whose type has no constructors, there is no need to provide any branches.

%\medskip%

Moving up the ladder of complexity, we can define the booleans: *)

Inductive bool : Set :=
| true
| false.

(** We can use less vacuous pattern matching to define boolean negation. *)

Definition not (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

(** An alternative definition desugars to the above: *)

Definition not' (b : bool) : bool :=
  if b then false else true.

(** We might want to prove that [not] is its own inverse operation. *)

Theorem not_inverse : forall b : bool, not (not b) = b.
(* begin thide *)
  destruct b.

  (** After we case-analyze on [b], we are left with one subgoal for each constructor of [bool].

[[
2 subgoals
  
  ============================
   not (not true) = true
]]

[[
subgoal 2 is:
 not (not false) = false
 
]]

The first subgoal follows by Coq's rules of computation, so we can dispatch it easily: *)

  reflexivity.

(** Likewise for the second subgoal, so we can restart the proof and give a very compact justification. *)

Restart.
  destruct b; reflexivity.
Qed.
(* end thide *)

(** Another theorem about booleans illustrates another useful tactic. *)

Theorem not_ineq : forall b : bool, not b <> b.
(* begin thide *)
  destruct b; discriminate.
Qed.
(* end thide *)

(** [discriminate] is used to prove that two values of an inductive type are not equal, whenever the values are formed with different constructors.  In this case, the different constructors are [true] and [false].

At this point, it is probably not hard to guess what the underlying induction principle for [bool] is. *)

Check bool_ind.
(** [bool_ind : forall P : bool -> Prop, P true -> P false -> forall b : bool, P b] *)


(** * Simple Recursive Types *)

(** The natural numbers are the simplest common example of an inductive type that actually deserves the name. *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(** [O] is zero, and [S] is the successor function, so that [0] is syntactic sugar for [O], [1] for [S O], [2] for [S (S O)], and so on.

Pattern matching works as we demonstrated in the last chapter: *)

Definition isZero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** We can prove theorems by case analysis: *)

Theorem S_isZero : forall n : nat, isZero (pred (S (S n))) = false.
(* begin thide *)
  destruct n; reflexivity.
Qed.
(* end thide *)

(** We can also now get into genuine inductive theorems.  First, we will need a recursive function, to make things interesting. *)

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Recall that [Fixpoint] is Coq's mechanism for recursive function definitions.  Some theorems about [plus] can be proved without induction. *)

Theorem O_plus_n : forall n : nat, plus O n = n.
(* begin thide *)
  intro; reflexivity.
Qed.
(* end thide *)

(** Coq's computation rules automatically simplify the application of [plus], because unfolding the definition of [plus] gives us a [match] expression where the branch to be taken is obvious from syntax alone.  If we just reverse the order of the arguments, though, this no longer works, and we need induction. *)

Theorem n_plus_O : forall n : nat, plus n O = n.
(* begin thide *)
  induction n.

(** Our first subgoal is [plus O O = O], which %\textit{%#<i>#is#</i>#%}% trivial by computation. *)

  reflexivity.

(** Our second subgoal is more work and also demonstrates our first inductive hypothesis.

[[
  n : nat
  IHn : plus n O = n
  ============================
   plus (S n) O = S n
 
]]

We can start out by using computation to simplify the goal as far as we can. *)

  simpl.

(** Now the conclusion is [S (plus n O) = S n].  Using our inductive hypothesis: *)

  rewrite IHn.

(** ...we get a trivial conclusion [S n = S n]. *)

  reflexivity.

(** Not much really went on in this proof, so the [crush] tactic from the [Tactics] module can prove this theorem automatically. *)

Restart.
  induction n; crush.
Qed.
(* end thide *)

(** We can check out the induction principle at work here: *)

Check nat_ind.
(** %\vspace{-.15in}% [[
  nat_ind : forall P : nat -> Prop,
            P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
 
  ]]

Each of the two cases of our last proof came from the type of one of the arguments to [nat_ind].  We chose [P] to be [(fun n : nat => plus n O = n)].  The first proof case corresponded to [P O] and the second case to [(forall n : nat, P n -> P (S n))].  The free variable [n] and inductive hypothesis [IHn] came from the argument types given here.

Since [nat] has a constructor that takes an argument, we may sometimes need to know that that constructor is injective. *)

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
(* begin thide *)
  injection 1; trivial.
Qed.
(* end thide *)

(** [injection] refers to a premise by number, adding new equalities between the corresponding arguments of equated terms that are formed with the same constructor.  We end up needing to prove [n = m -> n = m], so it is unsurprising that a tactic named [trivial] is able to finish the proof.

There is also a very useful tactic called [congruence] that can prove this theorem immediately.  [congruence] generalizes [discriminate] and [injection], and it also adds reasoning about the general properties of equality, such as that a function returns equal results on equal arguments.  That is, [congruence] is a %\textit{%#<i>#complete decision procedure for the theory of equality and uninterpreted functions#</i>#%}%, plus some smarts about inductive types.

%\medskip%

We can define a type of lists of natural numbers. *)

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

(** Recursive definitions are straightforward extensions of what we have seen before. *)

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
    | NNil => O
    | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
    | NNil => ls2
    | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

(** Inductive theorem proving can again be automated quite effectively. *)

Theorem nlength_napp : forall ls1 ls2 : nat_list, nlength (napp ls1 ls2)
  = plus (nlength ls1) (nlength ls2).
(* begin thide *)
  induction ls1; crush.
Qed.
(* end thide *)

Check nat_list_ind.
(** %\vspace{-.15in}% [[
  nat_list_ind
     : forall P : nat_list -> Prop,
       P NNil ->
       (forall (n : nat) (n0 : nat_list), P n0 -> P (NCons n n0)) ->
       forall n : nat_list, P n
]]

%\medskip%

In general, we can implement any "tree" types as inductive types.  For example, here are binary trees of naturals. *)

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
    | NLeaf => S O
    | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
    | NLeaf => NNode tr2 O NLeaf
    | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
(* begin thide *)
  induction n1; crush.
Qed.
(* end thide *)

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2)
  = plus (nsize tr2) (nsize tr1).
(* begin thide *)
  Hint Rewrite n_plus_O plus_assoc : cpdt.

  induction tr1; crush.
Qed.
(* end thide *)

Check nat_btree_ind.
(** %\vspace{-.15in}% [[
  nat_btree_ind
     : forall P : nat_btree -> Prop,
       P NLeaf ->
       (forall n : nat_btree,
        P n -> forall (n0 : nat) (n1 : nat_btree), P n1 -> P (NNode n n0 n1)) ->
       forall n : nat_btree, P n
]] *)


(** * Parameterized Types *)

(** We can also define polymorphic inductive types, as with algebraic datatypes in Haskell and ML. *)

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
    | Nil => O
    | Cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
  end.

Theorem length_app : forall T (ls1 ls2 : list T), length (app ls1 ls2)
  = plus (length ls1) (length ls2).
(* begin thide *)
  induction ls1; crush.
Qed.
(* end thide *)

(** There is a useful shorthand for writing many definitions that share the same parameter, based on Coq's %\textit{%#<i>#section#</i>#%}% mechanism.  The following block of code is equivalent to the above: *)

(* begin hide *)
Reset list.
(* end hide *)

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
      | Nil => O
      | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall ls1 ls2 : list, length (app ls1 ls2)
    = plus (length ls1) (length ls2).
(* begin thide *)
    induction ls1; crush.
  Qed.
(* end thide *)
End list.

(* begin hide *)
Implicit Arguments Nil [T].
(* end hide *)

(** After we end the section, the [Variable]s we used are added as extra function parameters for each defined identifier, as needed.  We verify that this has happened using the [Print] command, a cousin of [Check] which shows the definition of a symbol, rather than just its type. *)

Print list.
(** %\vspace{-.15in}% [[
  Inductive list (T : Set) : Set :=
    Nil : list T | Cons : T -> list T -> list Tlist
 
]]

The final definition is the same as what we wrote manually before.  The other elements of the section are altered similarly, turning out exactly as they were before, though we managed to write their definitions more succinctly. *)

Check length.
(** %\vspace{-.15in}% [[
  length
     : forall T : Set, list T -> nat
]]

The parameter [T] is treated as a new argument to the induction principle, too. *)

Check list_ind.
(** %\vspace{-.15in}% [[
  list_ind
     : forall (T : Set) (P : list T -> Prop),
       P (Nil T) ->
       (forall (t : T) (l : list T), P l -> P (Cons t l)) ->
       forall l : list T, P l
]]

Thus, even though we just saw that [T] is added as an extra argument to the constructor [Cons], there is no quantifier for [T] in the type of the inductive case like there is for each of the other arguments. *)


(** * Mutually Inductive Types *)

(** We can define inductive types that refer to each other: *)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
    | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.

(** Everything is going roughly the same as in past examples, until we try to prove a theorem similar to those that came before. *)

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
(* begin thide *)
  induction el1; crush.

  (** One goal remains: [[

  n : nat
  o : odd_list
  el2 : even_list
  ============================
   S (olength (oapp o el2)) = S (plus (olength o) (elength el2))
   ]]

   We have no induction hypothesis, so we cannot prove this goal without starting another induction, which would reach a similar point, sending us into a futile infinite chain of inductions.  The problem is that Coq's generation of [T_ind] principles is incomplete.  We only get non-mutual induction principles generated by default. *)

Abort.
Check even_list_ind.
(** %\vspace{-.15in}% [[
  even_list_ind
     : forall P : even_list -> Prop,
       P ENil ->
       (forall (n : nat) (o : odd_list), P (ECons n o)) ->
       forall e : even_list, P e
 
]]

We see that no inductive hypotheses are included anywhere in the type.  To get them, we must ask for mutual principles as we need them, using the [Scheme] command. *)

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

Check even_list_mut.
(** %\vspace{-.15in}% [[
  even_list_mut
     : forall (P : even_list -> Prop) (P0 : odd_list -> Prop),
       P ENil ->
       (forall (n : nat) (o : odd_list), P0 o -> P (ECons n o)) ->
       (forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) ->
       forall e : even_list, P e
 
]]

This is the principle we wanted in the first place.  There is one more wrinkle left in using it: the [induction] tactic will not apply it for us automatically.  It will be helpful to look at how to prove one of our past examples without using [induction], so that we can then generalize the technique to mutual inductive types. *)

Theorem n_plus_O' : forall n : nat, plus n O = n.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

(** From this example, we can see that [induction] is not magic.  It only does some bookkeeping for us to make it easy to apply a theorem, which we can do directly with the [apply] tactic.  We apply not just an identifier but a partial application of it, specifying the predicate we mean to prove holds for all naturals.

This technique generalizes to our mutual example: *)

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).

  apply (even_list_mut
    (fun el1 : even_list => forall el2 : even_list,
      elength (eapp el1 el2) = plus (elength el1) (elength el2))
    (fun ol : odd_list => forall el : even_list,
      olength (oapp ol el) = plus (olength ol) (elength el))); crush.
Qed.
(* end thide *)

(** We simply need to specify two predicates, one for each of the mutually inductive types.  In general, it would not be a good idea to assume that a proof assistant could infer extra predicates, so this way of applying mutual induction is about as straightforward as we could hope for. *)


(** * Reflexive Types *)

(** A kind of inductive type called a %\textit{%#<i>#reflexive type#</i>#%}% is defined in terms of functions that have the type being defined as their range.  One very useful class of examples is in modeling variable binders.  For instance, here is a type for encoding the syntax of a subset of first-order logic: *)

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

(** Our kinds of formulas are equalities between naturals, conjunction, and universal quantification over natural numbers.  We avoid needing to include a notion of "variables" in our type, by using Coq functions to encode quantification.  For instance, here is the encoding of [forall x : nat, x = x]: *)

Example forall_refl : formula := Forall (fun x => Eq x x).

(** We can write recursive functions over reflexive types quite naturally.  Here is one translating our formulas into native Coq propositions. *)

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
    | Eq n1 n2 => n1 = n2
    | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

(** We can also encode a trivial formula transformation that swaps the order of equality and conjunction operands. *)

Fixpoint swapper (f : formula) : formula :=
  match f with
    | Eq n1 n2 => Eq n2 n1
    | And f1 f2 => And (swapper f2) (swapper f1)
    | Forall f' => Forall (fun n => swapper (f' n))
  end.

(** It is helpful to prove that this transformation does not make true formulas false. *)

Theorem swapper_preserves_truth : forall f, formulaDenote f -> formulaDenote (swapper f).
(* begin thide *)
  induction f; crush.
Qed.
(* end thide *)

(** We can take a look at the induction principle behind this proof. *)

Check formula_ind.
(** %\vspace{-.15in}% [[
  formula_ind
     : forall P : formula -> Prop,
       (forall n n0 : nat, P (Eq n n0)) ->
       (forall f0 : formula,
        P f0 -> forall f1 : formula, P f1 -> P (And f0 f1)) ->
       (forall f1 : nat -> formula,
        (forall n : nat, P (f1 n)) -> P (Forall f1)) ->
       forall f2 : formula, P f2
 
]]

Focusing on the [Forall] case, which comes third, we see that we are allowed to assume that the theorem holds %\textit{%#<i>#for any application of the argument function [f1]#</i>#%}%.  That is, Coq induction principles do not follow a simple rule that the textual representations of induction variables must get shorter in appeals to induction hypotheses.  Luckily for us, the people behind the metatheory of Coq have verified that this flexibility does not introduce unsoundness.

%\medskip%

Up to this point, we have seen how to encode in Coq more and more of what is possible with algebraic datatypes in Haskell and ML.  This may have given the inaccurate impression that inductive types are a strict extension of algebraic datatypes.  In fact, Coq must rule out some types allowed by Haskell and ML, for reasons of soundness.  Reflexive types provide our first good example of such a case.

Given our last example of an inductive type, many readers are probably eager to try encoding the syntax of lambda calculus.  Indeed, the function-based representation technique that we just used, called %\textit{%#<i>#higher-order abstract syntax (HOAS)#</i>#%}%, is the representation of choice for lambda calculi in Twelf and in many applications implemented in Haskell and ML.  Let us try to import that choice to Coq: *)

(** [[
Inductive term : Set :=
| App : term -> term -> term
| Abs : (term -> term) -> term.

Error: Non strictly positive occurrence of "term" in "(term -> term) -> term"
 
]]

We have run afoul of the %\textit{%#<i>#strict positivity requirement#</i>#%}% for inductive definitions, which says that the type being defined may not occur to the left of an arrow in the type of a constructor argument.  It is important that the type of a constructor is viewed in terms of a series of arguments and a result, since obviously we need recursive occurrences to the lefts of the outermost arrows if we are to have recursive occurrences at all.

Why must Coq enforce this restriction?  Imagine that our last definition had been accepted, allowing us to write this function:

[[
Definition uhoh (t : term) : term :=
  match t with
    | Abs f => f t
    | _ => t
  end.

]]

Using an informal idea of Coq's semantics, it is easy to verify that the application [uhoh (Abs uhoh)] will run forever.  This would be a mere curiosity in OCaml and Haskell, where non-termination is commonplace, though the fact that we have a non-terminating program without explicit recursive function definitions is unusual.

For Coq, however, this would be a disaster.  The possibility of writing such a function would destroy all our confidence that proving a theorem means anything.  Since Coq combines programs and proofs in one language, we would be able to prove every theorem with an infinite loop.

Nonetheless, the basic insight of HOAS is a very useful one, and there are ways to realize most benefits of HOAS in Coq.  We will study a particular technique of this kind in the later chapters on programming language syntax and semantics. *)


(** * An Interlude on Proof Terms *)

(** As we have emphasized a few times already, Coq proofs are actually programs, written in the same language we have been using in our examples all along.  We can get a first sense of what this means by taking a look at the definitions of some of the induction principles we have used. *)

Print unit_ind.
(** %\vspace{-.15in}% [[
  unit_ind = 
  fun P : unit -> Prop => unit_rect P
     : forall P : unit -> Prop, P tt -> forall u : unit, P u
 
]]

We see that this induction principle is defined in terms of a more general principle, [unit_rect]. *)

Check unit_rect.
(** %\vspace{-.15in}% [[
  unit_rect
     : forall P : unit -> Type, P tt -> forall u : unit, P u
 
]]

[unit_rect] gives [P] type [unit -> Type] instead of [unit -> Prop].  [Type] is another universe, like [Set] and [Prop].  In fact, it is a common supertype of both.  Later on, we will discuss exactly what the significances of the different universes are.  For now, it is just important that we can use [Type] as a sort of meta-universe that may turn out to be either [Set] or [Prop].  We can see the symmetry inherent in the subtyping relationship by printing the definition of another principle that was generated for [unit] automatically: *)

Print unit_rec.
(** %\vspace{-.15in}% [[
  unit_rec = 
  fun P : unit -> Set => unit_rect P
     : forall P : unit -> Set, P tt -> forall u : unit, P u
 
]]

This is identical to the definition for [unit_ind], except that we have substituted [Set] for [Prop].  For most inductive types [T], then, we get not just induction principles [T_ind], but also recursion principles [T_rec].  We can use [T_rec] to write recursive definitions without explicit [Fixpoint] recursion.  For instance, the following two definitions are equivalent: *)

Definition always_O (u : unit) : nat :=
  match u with
    | tt => O
  end.

Definition always_O' (u : unit) : nat :=
  unit_rec (fun _ : unit => nat) O u.

(** Going even further down the rabbit hole, [unit_rect] itself is not even a primitive.  It is a functional program that we can write manually. *)

Print unit_rect.
(** %\vspace{-.15in}% [[
  unit_rect = 
  fun (P : unit -> Type) (f : P tt) (u : unit) =>
  match u as u0 return (P u0) with
  | tt => f
  end
     : forall P : unit -> Type, P tt -> forall u : unit, P u
 
]]

The only new feature we see is an [as] clause for a [match], which is used in concert with the [return] clause that we saw in the introduction.  Since the type of the [match] is dependent on the value of the object being analyzed, we must give that object a name so that we can refer to it in the [return] clause.

To prove that [unit_rect] is nothing special, we can reimplement it manually. *)

Definition unit_rect' (P : unit -> Type) (f : P tt) (u : unit) :=
  match u with
    | tt => f
  end.

(** We rely on Coq's heuristics for inferring [match] annotations.

We can check the implementation of [nat_rect] as well: *)

Print nat_rect.
(** %\vspace{-.15in}% [[
  nat_rect = 
  fun (P : nat -> Type) (f : P O) (f0 : forall n : nat, P n -> P (S n)) =>
  fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
     | O => f
     | S n0 => f0 n0 (F n0)
     end
      : forall P : nat -> Type,
        P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
 ]]

 Now we have an actual recursive definition.  [fix] expressions are an anonymous form of [Fixpoint], just as [fun] expressions stand for anonymous non-recursive functions.  Beyond that, the syntax of [fix] mirrors that of [Fixpoint].  We can understand the definition of [nat_rect] better by reimplementing [nat_ind] using sections. *)

 Section nat_ind'.
   (** First, we have the property of natural numbers that we aim to prove. *)

   Variable P : nat -> Prop.

   (** Then we require a proof of the [O] case. *)

   Hypothesis O_case : P O.

   (** Next is a proof of the [S] case, which may assume an inductive hypothesis. *)

   Hypothesis S_case : forall n : nat, P n -> P (S n).

   (** Finally, we define a recursive function to tie the pieces together. *)

   Fixpoint nat_ind' (n : nat) : P n :=
     match n with
       | O => O_case
       | S n' => S_case (nat_ind' n')
     end.
 End nat_ind'.

 (** Closing the section adds the [Variable]s and [Hypothesis]es as new [fun]-bound arguments to [nat_ind'], and, modulo the use of [Prop] instead of [Type], we end up with the exact same definition that was generated automatically for [nat_rect].

 %\medskip%

 We can also examine the definition of [even_list_mut], which we generated with [Scheme] for a mutually-recursive type. *)

 Print even_list_mut.
 (** %\vspace{-.15in}% [[
   even_list_mut = 
   fun (P : even_list -> Prop) (P0 : odd_list -> Prop) 
     (f : P ENil) (f0 : forall (n : nat) (o : odd_list), P0 o -> P (ECons n o))
     (f1 : forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) =>
   fix F (e : even_list) : P e :=
     match e as e0 return (P e0) with
     | ENil => f
     | ECons n o => f0 n o (F0 o)
     end
   with F0 (o : odd_list) : P0 o :=
     match o as o0 return (P0 o0) with
     | OCons n e => f1 n e (F e)
     end
   for F
      : forall (P : even_list -> Prop) (P0 : odd_list -> Prop),
        P ENil ->
        (forall (n : nat) (o : odd_list), P0 o -> P (ECons n o)) ->
        (forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) ->
        forall e : even_list, P e

 ]]

 We see a mutually-recursive [fix], with the different functions separated by [with] in the same way that they would be separated by [and] in ML.  A final [for] clause identifies which of the mutually-recursive functions should be the final value of the [fix] expression.  Using this definition as a template, we can reimplement [even_list_mut] directly. *)

 Section even_list_mut'.
   (** First, we need the properties that we are proving. *)

   Variable Peven : even_list -> Prop.
   Variable Podd : odd_list -> Prop.

   (** Next, we need proofs of the three cases. *)

   Hypothesis ENil_case : Peven ENil.
   Hypothesis ECons_case : forall (n : nat) (o : odd_list), Podd o -> Peven (ECons n o).
   Hypothesis OCons_case : forall (n : nat) (e : even_list), Peven e -> Podd (OCons n e).

   (** Finally, we define the recursive functions. *)

   Fixpoint even_list_mut' (e : even_list) : Peven e :=
     match e with
       | ENil => ENil_case
       | ECons n o => ECons_case n (odd_list_mut' o)
     end
   with odd_list_mut' (o : odd_list) : Podd o :=
     match o with
       | OCons n e => OCons_case n (even_list_mut' e)
     end.
End even_list_mut'.

(** Even induction principles for reflexive types are easy to implement directly.  For our [formula] type, we can use a recursive definition much like those we wrote above. *)

Section formula_ind'.
  Variable P : formula -> Prop.
  Hypothesis Eq_case : forall n1 n2 : nat, P (Eq n1 n2).
  Hypothesis And_case : forall f1 f2 : formula,
    P f1 -> P f2 -> P (And f1 f2).
  Hypothesis Forall_case : forall f : nat -> formula,
    (forall n : nat, P (f n)) -> P (Forall f).

  Fixpoint formula_ind' (f : formula) : P f :=
    match f with
      | Eq n1 n2 => Eq_case n1 n2
      | And f1 f2 => And_case (formula_ind' f1) (formula_ind' f2)
      | Forall f' => Forall_case f' (fun n => formula_ind' (f' n))
    end.
End formula_ind'.


(** * Nested Inductive Types *)

(** Suppose we want to extend our earlier type of binary trees to trees with arbitrary finite branching.  We can use lists to give a simple definition. *)

Inductive nat_tree : Set :=
| NLeaf' : nat_tree
| NNode' : nat -> list nat_tree -> nat_tree.

(** This is an example of a %\textit{%#<i>#nested#</i>#%}% inductive type definition, because we use the type we are defining as an argument to a parametrized type family.  Coq will not allow all such definitions; it effectively pretends that we are defining [nat_tree] mutually with a version of [list] specialized to [nat_tree], checking that the resulting expanded definition satisfies the usual rules.  For instance, if we replaced [list] with a type family that used its parameter as a function argument, then the definition would be rejected as violating the positivity restriction.

Like we encountered for mutual inductive types, we find that the automatically-generated induction principle for [nat_tree] is too weak. *)

Check nat_tree_ind.
(** %\vspace{-.15in}% [[
  nat_tree_ind
     : forall P : nat_tree -> Prop,
       P NLeaf' ->
       (forall (n : nat) (l : list nat_tree), P (NNode' n l)) ->
       forall n : nat_tree, P n
 
]]

There is no command like [Scheme] that will implement an improved principle for us.  In general, it takes creativity to figure out how to incorporate nested uses to different type families.  Now that we know how to implement induction principles manually, we are in a position to apply just such creativity to this problem.

First, we will need an auxiliary definition, characterizing what it means for a property to hold of every element of a list. *)

Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | Nil => True
      | Cons h t => P h /\ All t
    end.
End All.

(** It will be useful to look at the definitions of [True] and [/\], since we will want to write manual proofs of them below. *)

Print True.
(** %\vspace{-.15in}% [[
  Inductive True : Prop :=  I : True
 
  ]]

That is, [True] is a proposition with exactly one proof, [I], which we may always supply trivially.

Finding the definition of [/\] takes a little more work.  Coq supports user registration of arbitrary parsing rules, and it is such a rule that is letting us write [/\] instead of an application of some inductive type family.  We can find the underlying inductive type with the [Locate] command. *)

Locate "/\".
(** %\vspace{-.15in}% [[
  Notation            Scope     
  "A /\ B" := and A B  : type_scope
                        (default interpretation)
]] *)

Print and.
(** %\vspace{-.15in}% [[
  Inductive and (A : Prop) (B : Prop) : Prop :=  conj : A -> B -> A /\ B
  For conj: Arguments A, B are implicit
  For and: Argument scopes are [type_scope type_scope]
  For conj: Argument scopes are [type_scope type_scope _ _]
 
]]

In addition to the definition of [and] itself, we get information on implicit arguments and parsing rules for [and] and its constructor [conj].  We will ignore the parsing information for now.  The implicit argument information tells us that we build a proof of a conjunction by calling the constructor [conj] on proofs of the conjuncts, with no need to include the types of those proofs as explicit arguments.

%\medskip%

Now we create a section for our induction principle, following the same basic plan as in the last section of this chapter. *)

Section nat_tree_ind'.
  Variable P : nat_tree -> Prop.

  Hypothesis NLeaf'_case : P NLeaf'.
  Hypothesis NNode'_case : forall (n : nat) (ls : list nat_tree),
    All P ls -> P (NNode' n ls).

  (** A first attempt at writing the induction principle itself follows the intuition that nested inductive type definitions are expanded into mutual inductive definitions.

  [[
  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NLeaf' => NLeaf'_case
      | NNode' n ls => NNode'_case n ls (list_nat_tree_ind ls)
    end

  with list_nat_tree_ind (ls : list nat_tree) : All P ls :=
    match ls with
      | Nil => I
      | Cons tr rest => conj (nat_tree_ind' tr) (list_nat_tree_ind rest)
    end.

  ]]

  Coq rejects this definition, saying "Recursive call to nat_tree_ind' has principal argument equal to "tr" instead of rest."  The term "nested inductive type" hints at the solution to the problem.  Just like true mutually-inductive types require mutually-recursive induction principles, nested types require nested recursion. *)

  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NLeaf' => NLeaf'_case
      | NNode' n ls => NNode'_case n ls
        ((fix list_nat_tree_ind (ls : list nat_tree) : All P ls :=
          match ls with
            | Nil => I
            | Cons tr rest => conj (nat_tree_ind' tr) (list_nat_tree_ind rest)
          end) ls)
    end.

  (** We include an anonymous [fix] version of [list_nat_tree_ind] that is literally %\textit{%#<i>#nested#</i>#%}% inside the definition of the recursive function corresponding to the inductive definition that had the nested use of [list]. *)

End nat_tree_ind'.

(** We can try our induction principle out by defining some recursive functions on [nat_tree]s and proving a theorem about them.  First, we define some helper functions that operate on lists. *)

Section map.
  Variables T T' : Set.
  Variable f : T -> T'.

  Fixpoint map (ls : list T) : list T' :=
    match ls with
      | Nil => Nil
      | Cons h t => Cons (f h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | Nil => O
    | Cons h t => plus h (sum t)
  end.

(** Now we can define a size function over our trees. *)

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
    | NLeaf' => S O
    | NNode' _ trs => S (sum (map ntsize trs))
  end.

(** Notice that Coq was smart enough to expand the definition of [map] to verify that we are using proper nested recursion, even through a use of a higher-order function. *)

Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
    | NLeaf' => NNode' O (Cons tr2 Nil)
    | NNode' n Nil => NNode' n (Cons tr2 Nil)
    | NNode' n (Cons tr trs) => NNode' n (Cons (ntsplice tr tr2) trs)
  end.

(** We have defined another arbitrary notion of tree splicing, similar to before, and we can prove an analogous theorem about its relationship with tree size.  We start with a useful lemma about addition. *)

(* begin thide *)
Lemma plus_S : forall n1 n2 : nat,
  plus n1 (S n2) = S (plus n1 n2).
  induction n1; crush.
Qed.
(* end thide *)

(** Now we begin the proof of the theorem, adding the lemma [plus_S] as a hint. *)

Theorem ntsize_ntsplice : forall tr1 tr2 : nat_tree, ntsize (ntsplice tr1 tr2)
  = plus (ntsize tr2) (ntsize tr1).
(* begin thide *)
  Hint Rewrite plus_S : cpdt.

  (** We know that the standard induction principle is insufficient for the task, so we need to provide a [using] clause for the [induction] tactic to specify our alternate principle. *)

  induction tr1 using nat_tree_ind'; crush.

  (** One subgoal remains: [[
  n : nat
  ls : list nat_tree
  H : All
        (fun tr1 : nat_tree =>
         forall tr2 : nat_tree,
         ntsize (ntsplice tr1 tr2) = plus (ntsize tr2) (ntsize tr1)) ls
  tr2 : nat_tree
  ============================
   ntsize
     match ls with
     | Nil => NNode' n (Cons tr2 Nil)
     | Cons tr trs => NNode' n (Cons (ntsplice tr tr2) trs)
     end = S (plus (ntsize tr2) (sum (map ntsize ls)))
 
     ]]

     After a few moments of squinting at this goal, it becomes apparent that we need to do a case analysis on the structure of [ls].  The rest is routine. *)

  destruct ls; crush.

  (** We can go further in automating the proof by exploiting the hint mechanism. *)

  Restart.
  Hint Extern 1 (ntsize (match ?LS with Nil => _ | Cons _ _ => _ end) = _) =>
    destruct LS; crush.
  induction tr1 using nat_tree_ind'; crush.
Qed.
(* end thide *)

(** We will go into great detail on hints in a later chapter, but the only important thing to note here is that we register a pattern that describes a conclusion we expect to encounter during the proof.  The pattern may contain unification variables, whose names are prefixed with question marks, and we may refer to those bound variables in a tactic that we ask to have run whenever the pattern matches.

The advantage of using the hint is not very clear here, because the original proof was so short.  However, the hint has fundamentally improved the readability of our proof.  Before, the proof referred to the local variable [ls], which has an automatically-generated name.  To a human reading the proof script without stepping through it interactively, it was not clear where [ls] came from.  The hint explains to the reader the process for choosing which variables to case analyze on, and the hint can continue working even if the rest of the proof structure changes significantly. *)


(** * Manual Proofs About Constructors *)

(** It can be useful to understand how tactics like [discriminate] and [injection] work, so it is worth stepping through a manual proof of each kind.  We will start with a proof fit for [discriminate]. *)

Theorem true_neq_false : true <> false.

(* begin thide *)
(** We begin with the tactic [red], which is short for "one step of reduction," to unfold the definition of logical negation. *)

  red.
(** [[
  ============================
   true = false -> False
 
]]

The negation is replaced with an implication of falsehood.  We use the tactic [intro H] to change the assumption of the implication into a hypothesis named [H]. *)

  intro H.
(** [[
  H : true = false
  ============================
   False
 
]]

This is the point in the proof where we apply some creativity.  We define a function whose utility will become clear soon. *)

  Definition f (b : bool) := if b then True else False.

(** It is worth recalling the difference between the lowercase and uppercase versions of truth and falsehood: [True] and [False] are logical propositions, while [true] and [false] are boolean values that we can case-analyze.  We have defined [f] such that our conclusion of [False] is computationally equivalent to [f false].  Thus, the [change] tactic will let us change the conclusion to [f false]. *)

  change (f false).
(** [[
  H : true = false
  ============================
   f false
 
]]

Now the righthand side of [H]'s equality appears in the conclusion, so we can rewrite, using the notation [<-] to request to replace the righthand side the equality with the lefthand side. *)

  rewrite <- H.
(** [[
  H : true = false
  ============================
   f true
 
]]

We are almost done.  Just how close we are to done is revealed by computational simplification. *)

  simpl.
(** [[
  H : true = false
  ============================
   True
 
]] *)

  trivial.
Qed.
(* end thide *)

(** I have no trivial automated version of this proof to suggest, beyond using [discriminate] or [congruence] in the first place.

%\medskip%

We can perform a similar manual proof of injectivity of the constructor [S].  I leave a walk-through of the details to curious readers who want to run the proof script interactively. *)

Theorem S_inj' : forall n m : nat, S n = S m -> n = m.
(* begin thide *)
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.
(* end thide *)


(** * Exercises *)

(** %\begin{enumerate}%#<ol>#

%\item%#<li># Define an inductive type [truth] with three constructors, [Yes], [No], and [Maybe].  [Yes] stands for certain truth, [No] for certain falsehood, and [Maybe] for an unknown situation.  Define "not," "and," and "or" for this replacement boolean algebra.  Prove that your implementation of "and" is commutative and distributes over your implementation of "or."#</li>#

%\item%#<li># Modify the first example language of Chapter 2 to include variables, where variables are represented with [nat].  Extend the syntax and semantics of expressions to accommodate the change.  Your new [expDenote] function should take as a new extra first argument a value of type [var -> nat], where [var] is a synonym for naturals-as-variables, and the function assigns a value to each variable.  Define a constant folding function which does a bottom-up pass over an expression, at each stage replacing every binary operation on constants with an equivalent constant.  Prove that constant folding preserves the meanings of expressions.#</li>#

%\item%#<li># Reimplement the second example language of Chapter 2 to use mutually-inductive types instead of dependent types.  That is, define two separate (non-dependent) inductive types [nat_exp] and [bool_exp] for expressions of the two different types, rather than a single indexed type.  To keep things simple, you may consider only the binary operators that take naturals as operands.  Add natural number variables to the language, as in the last exercise, and add an "if" expression form taking as arguments one boolean expression and two natural number expressions.  Define semantics and constant-folding functions for this new language.  Your constant folding should simplify not just binary operations (returning naturals or booleans) with known arguments, but also "if" expressions with known values for their test expressions but possibly undetermined "then" and "else" cases.  Prove that constant-folding a natural number expression preserves its meaning.#</li>#

%\item%#<li># Using a reflexive inductive definition, define a type [nat_tree] of infinitary trees, with natural numbers at their leaves and a countable infinity of new trees branching out of each internal node.  Define a function [increment] that increments the number in every leaf of a [nat_tree].  Define a function [leapfrog] over a natural [i] and a tree [nt].  [leapfrog] should recurse into the [i]th child of [nt], the [i+1]st child of that node, the [i+2]nd child of the next node, and so on, until reaching a leaf, in which case [leapfrog] should return the number at that leaf.  Prove that the result of any call to [leapfrog] is incremented by one by calling [increment] on the tree.#</li>#

%\item%#<li># Define a type of trees of trees of trees of (repeat to infinity).  That is, define an inductive type [trexp], whose members are either base cases containing natural numbers or binary trees of [trexp]s.  Base your definition on a parameterized binary tree type [btree] that you will also define, so that [trexp] is defined as a nested inductive type.  Define a function [total] that sums all of the naturals at the leaves of a [trexp].  Define a function [increment] that increments every leaf of a [trexp] by one.  Prove that, for all [tr], [total (increment tr) >= total tr].  On the way to finishing this proof, you will probably want to prove a lemma and add it as a hint using the syntax [Hint Resolve name_of_lemma.].#</li>#

%\item%#<li># Prove discrimination and injectivity theorems for the [nat_btree] type defined earlier in this chapter.  In particular, without using the tactics [discriminate], [injection], or [congruence], prove that no leaf equals any node, and prove that two equal nodes carry the same natural number.#</li>#

#</ol>#%\end{enumerate}% *)
