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


(** %\chapter{Infinite Data and Proofs}% *)

(** In lazy functional programming languages like Haskell, infinite data structures are everywhere.  Infinite lists and more exotic datatypes provide convenient abstractions for communication between parts of a program.  Achieving similar convenience without infinite lazy structures would, in many cases, require acrobatic inversions of control flow.

Laziness is easy to implement in Haskell, where all the definitions in a program may be thought of as mutually recursive.  In such an unconstrained setting, it is easy to implement an infinite loop when you really meant to build an infinite list, where any finite prefix of the list should be forceable in finite time.  Haskell programmers learn how to avoid such slip-ups.  In Coq, such a laissez-faire policy is not good enough.

We spent some time in the last chapter discussing the Curry-Howard isomorphism, where proofs are identified with functional programs.  In such a setting, infinite loops, intended or otherwise, are disastrous.  If Coq allowed the full breadth of definitions that Haskell did, we could code up an infinite loop and use it to prove any proposition vacuously.  That is, the addition of general recursion would make CIC %\textit{%#<i>#inconsistent#</i>#%}%.  For an arbitrary proposition [P], we could write:

[[
Fixpoint bad (u : unit) : P := bad u.
 
]]

This would leave us with [bad tt] as a proof of [P].

There are also algorithmic considerations that make universal termination very desirable.  We have seen how tactics like [reflexivity] compare terms up to equivalence under computational rules.  Calls to recursive, pattern-matching functions are simplified automatically, with no need for explicit proof steps.  It would be very hard to hold onto that kind of benefit if it became possible to write non-terminating programs; we would be running smack into the halting problem.

One solution is to use types to contain the possibility of non-termination.  For instance, we can create a "non-termination monad," inside which we must write all of our general-recursive programs.  This is a heavyweight solution, and so we would like to avoid it whenever possible.

Luckily, Coq has special support for a class of lazy data structures that happens to contain most examples found in Haskell.  That mechanism, %\textit{%#<i>#co-inductive types#</i>#%}%, is the subject of this chapter. *)


(** * Computing with Infinite Data *)

(** Let us begin with the most basic type of infinite data, %\textit{%#<i>#streams#</i>#%}%, or lazy lists. *)

Section stream.
  Variable A : Set.

  CoInductive stream : Set :=
  | Cons : A -> stream -> stream.
End stream.

(** The definition is surprisingly simple.  Starting from the definition of [list], we just need to change the keyword [Inductive] to [CoInductive].  We could have left a [Nil] constructor in our definition, but we will leave it out to force all of our streams to be infinite.

   How do we write down a stream constant?  Obviously simple application of constructors is not good enough, since we could only denote finite objects that way.  Rather, whereas recursive definitions were necessary to %\textit{%#<i>#use#</i>#%}% values of recursive inductive types effectively, here we find that we need %\textit{%#<i>#co-recursive definitions#</i>#%}% to %\textit{%#<i>#build#</i>#%}% values of co-inductive types effectively.

   We can define a stream consisting only of zeroes. *)

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

(** We can also define a stream that alternates between [true] and [false]. *)

CoFixpoint trues : stream bool := Cons true falses
with falses : stream bool := Cons false trues.

(** Co-inductive values are fair game as arguments to recursive functions, and we can use that fact to write a function to take a finite approximation of a stream. *)

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx t n'
      end
  end.

Eval simpl in approx zeroes 10.
(** %\vspace{-.15in}% [[
     = 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: nil
     : list nat
     ]] *)

Eval simpl in approx trues 10.
(** %\vspace{-.15in}% [[
     = true
       :: false
          :: true
             :: false
                :: true :: false :: true :: false :: true :: false :: nil
     : list bool
 
     ]]

     So far, it looks like co-inductive types might be a magic bullet, allowing us to import all of the Haskeller's usual tricks.  However, there are important restrictions that are dual to the restrictions on the use of inductive types.  Fixpoints %\textit{%#<i>#consume#</i>#%}% values of inductive types, with restrictions on which %\textit{%#<i>#arguments#</i>#%}% may be passed in recursive calls.  Dually, co-fixpoints %\textit{%#<i>#produce#</i>#%}% values of co-inductive types, with restrictions on what may be done with the %\textit{%#<i>#results#</i>#%}% of co-recursive calls.

The restriction for co-inductive types shows up as the %\textit{%#<i>#guardedness condition#</i>#%}%, and it can be broken into two parts.  First, consider this stream definition, which would be legal in Haskell.

[[
CoFixpoint looper : stream nat := looper.

Error:
Recursive definition of looper is ill-formed.
In environment
looper : stream nat

unguarded recursive call in "looper"
 
]]

The rule we have run afoul of here is that %\textit{%#<i>#every co-recursive call must be guarded by a constructor#</i>#%}%; that is, every co-recursive call must be a direct argument to a constructor of the co-inductive type we are generating.  It is a good thing that this rule is enforced.  If the definition of [looper] were accepted, our [approx] function would run forever when passed [looper], and we would have fallen into inconsistency.

The second rule of guardedness is easiest to see by first introducing a more complicated, but legal, co-fixpoint. *)

Section map.
  Variables A B : Set.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

(** This code is a literal copy of that for the list [map] function, with the [Nil] case removed and [Fixpoint] changed to [CoFixpoint].  Many other standard functions on lazy data structures can be implemented just as easily.  Some, like [filter], cannot be implemented.  Since the predicate passed to [filter] may reject every element of the stream, we cannot satisfy even the first guardedness condition.

   The second condition is subtler.  To illustrate it, we start off with another co-recursive function definition that %\textit{%#<i>#is#</i>#%}% legal.  The function [interleave] takes two streams and produces a new stream that alternates between their elements. *)

Section interleave.
  Variable A : Set.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
      | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

(** Now say we want to write a weird stuttering version of [map] that repeats elements in a particular way, based on interleaving. *)

Section map'.
  Variables A B : Set.
  Variable f : A -> B.
(* begin thide *)
  (** [[
  CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' s)) (Cons (f h) (map' s))
    end.
 
    ]]
    
    We get another error message about an unguarded recursive call.  This is because we are violating the second guardedness condition, which says that, not only must co-recursive calls be arguments to constructors, there must also %\textit{%#<i>#not be anything but [match]es and calls to constructors of the same co-inductive type#</i>#%}% wrapped around these immediate uses of co-recursive calls.  The actual implemented rule for guardedness is a little more lenient than what we have just stated, but you can count on the illegality of any exception that would enhance the expressive power of co-recursion.

     Why enforce a rule like this?  Imagine that, instead of [interleave], we had called some other, less well-behaved function on streams.  Perhaps this other function might be defined mutually with [map'].  It might deconstruct its first argument, retrieving [map' s] from within [Cons (f h) (map' s)].  Next it might try a [match] on this retrieved value, which amounts to deconstructing [map' s].  To figure out how this [match] turns out, we need to know the top-level structure of [map' s], but this is exactly what we started out trying to determine!  We run into a loop in the evaluation process, and we have reached a witness of inconsistency if we are evaluating [approx (map' s) 1] for any [s]. *)
(* end thide *)

End map'.


(** * Infinite Proofs *)

(** Let us say we want to give two different definitions of a stream of all ones, and then we want to prove that they are equivalent. *)

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.

(** The obvious statement of the equality is this: *)

Theorem ones_eq : ones = ones'.

  (** However, faced with the initial subgoal, it is not at all clear how this theorem can be proved.  In fact, it is unprovable.  The [eq] predicate that we use is fundamentally limited to equalities that can be demonstrated by finite, syntactic arguments.  To prove this equivalence, we will need to introduce a new relation. *)
(* begin thide *)

Abort.

(** Co-inductive datatypes make sense by analogy from Haskell.  What we need now is a %\textit{%#<i>#co-inductive proposition#</i>#%}%.  That is, we want to define a proposition whose proofs may be infinite, subject to the guardedness condition.  The idea of infinite proofs does not show up in usual mathematics, but it can be very useful (unsurprisingly) for reasoning about infinite data structures.  Besides examples from Haskell, infinite data and proofs will also turn out to be useful for modelling inherently infinite mathematical objects, like program executions.

We are ready for our first co-inductive predicate. *)

Section stream_eq.
  Variable A : Set.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2
    -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

(** We say that two streams are equal if and only if they have the same heads and their tails are equal.  We use the normal finite-syntactic equality for the heads, and we refer to our new equality recursively for the tails.

We can try restating the theorem with [stream_eq]. *)

Theorem ones_eq : stream_eq ones ones'.
  (** Coq does not support tactical co-inductive proofs as well as it supports tactical inductive proofs.  The usual starting point is the [cofix] tactic, which asks to structure this proof as a co-fixpoint. *)

  cofix.
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones ones'
 
   ]]

   It looks like this proof might be easier than we expected! *)

  assumption.
  (** [[
Proof completed.
 
]]

  Unfortunately, we are due for some disappointment in our victory lap.

  [[
Qed.

Error:
Recursive definition of ones_eq is ill-formed.

In environment
ones_eq : stream_eq ones ones'

unguarded recursive call in "ones_eq"
 
]]

Via the Curry-Howard correspondence, the same guardedness condition applies to our co-inductive proofs as to our co-inductive data structures.  We should be grateful that this proof is rejected, because, if it were not, the same proof structure could be used to prove any co-inductive theorem vacuously, by direct appeal to itself!

Thinking about how Coq would generate a proof term from the proof script above, we see that the problem is that we are violating the first part of the guardedness condition.  During our proofs, Coq can help us check whether we have yet gone wrong in this way.  We can run the command [Guarded] in any context to see if it is possible to finish the proof in a way that will yield a properly guarded proof term.

     [[
Guarded.

]]

     Running [Guarded] here gives us the same error message that we got when we tried to run [Qed].  In larger proofs, [Guarded] can be helpful in detecting problems %\textit{%#<i>#before#</i>#%}% we think we are ready to run [Qed].
     
     We need to start the co-induction by applying one of [stream_eq]'s constructors.  To do that, we need to know that both arguments to the predicate are [Cons]es.  Informally, this is trivial, but [simpl] is not able to help us. *)

  Undo.
  simpl.
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones ones'
 
   ]]

   It turns out that we are best served by proving an auxiliary lemma. *)

Abort.

(** First, we need to define a function that seems pointless on first glance. *)

Definition frob A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

(** Next, we need to prove a theorem that seems equally pointless. *)

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s; reflexivity.
Qed.

(** But, miraculously, this theorem turns out to be just what we needed. *)

Theorem ones_eq : stream_eq ones ones'.
  cofix.

  (** We can use the theorem to rewrite the two streams. *)

  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq (frob ones) (frob ones')
 
   ]]

   Now [simpl] is able to reduce the streams. *)

  simpl.
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq (Cons 1 ones)
     (Cons 1
        ((cofix map (s : stream nat) : stream nat :=
            match s with
            | Cons h t => Cons (S h) (map t)
            end) zeroes))
 
            ]]

  Since we have exposed the [Cons] structure of each stream, we can apply the constructor of [stream_eq]. *)

  constructor.
  (** [[
  ones_eq : stream_eq ones ones'
  ============================
   stream_eq ones
     ((cofix map (s : stream nat) : stream nat :=
         match s with
         | Cons h t => Cons (S h) (map t)
         end) zeroes)
 
         ]]

  Now, modulo unfolding of the definition of [map], we have matched our assumption. *)

  assumption.
Qed.

(** Why did this silly-looking trick help?  The answer has to do with the constraints placed on Coq's evaluation rules by the need for termination.  The [cofix]-related restriction that foiled our first attempt at using [simpl] is dual to a restriction for [fix].  In particular, an application of an anonymous [fix] only reduces when the top-level structure of the recursive argument is known.  Otherwise, we would be unfolding the recursive definition ad infinitum.

   Fixpoints only reduce when enough is known about the %\textit{%#<i>#definitions#</i>#%}% of their arguments.  Dually, co-fixpoints only reduce when enough is known about %\textit{%#<i>#how their results will be used#</i>#%}%.  In particular, a [cofix] is only expanded when it is the discriminee of a [match].  Rewriting with our superficially silly lemma wrapped new [match]es around the two [cofix]es, triggering reduction.

   If [cofix]es reduced haphazardly, it would be easy to run into infinite loops in evaluation, since we are, after all, building infinite objects.

   One common source of difficulty with co-inductive proofs is bad interaction with standard Coq automation machinery.  If we try to prove [ones_eq'] with automation, like we have in previous inductive proofs, we get an invalid proof. *)

Theorem ones_eq' : stream_eq ones ones'.
  cofix; crush.
  (** [[
  Guarded.

  ]] *)
Abort.
(* end thide *)

(** The standard [auto] machinery sees that our goal matches an assumption and so applies that assumption, even though this violates guardedness.  One usually starts a proof like this by [destruct]ing some parameter and running a custom tactic to figure out the first proof rule to apply for each case.  Alternatively, there are tricks that can be played with "hiding" the co-inductive hypothesis. *)


(** * Simple Modeling of Non-Terminating Programs *)

(** We close the chapter with a quick motivating example for more complex uses of co-inductive types.  We will define a co-inductive semantics for a simple assembly language and use that semantics to prove that assembly programs always run forever.  This basic technique can be combined with typing judgments for more advanced languages, where some ill-typed programs can go wrong, but no well-typed programs go wrong.

   We define suggestive synonyms for [nat], for cases where we use natural numbers as registers or program labels.  That is, we consider our idealized machine to have infinitely many registers and infinitely many code addresses. *)

Definition reg := nat.
Definition label := nat.

(** Our instructions are loading of a constant into a register, copying from one register to another, unconditional jump, and conditional jump based on whether the value in a register is not zero. *)

Inductive instr : Set :=
| Imm : reg -> nat -> instr
| Copy : reg -> reg -> instr
| Jmp : label -> instr
| Jnz : reg -> label -> instr.

(** We define a type [regs] of maps from registers to values.  To define a function [set] for setting a register's value in a map, we import the [Arith] module from Coq's standard library, and we use its function [eq_nat_dec] for comparing natural numbers. *)

Definition regs := reg -> nat.
Require Import Arith.
Definition set (rs : regs) (r : reg) (v : nat) : regs :=
  fun r' => if eq_nat_dec r r' then v else rs r'.

(** An inductive [exec] judgment captures the effect of an instruction on the program counter and register bank. *)

Inductive exec : label -> regs -> instr -> label -> regs -> Prop :=
| E_Imm : forall pc rs r n, exec pc rs (Imm r n) (S pc) (set rs r n)
| E_Copy : forall pc rs r1 r2, exec pc rs (Copy r1 r2) (S pc) (set rs r1 (rs r2))
| E_Jmp : forall pc rs pc', exec pc rs (Jmp pc') pc' rs
| E_JnzF : forall pc rs r pc', rs r = 0 -> exec pc rs (Jnz r pc') (S pc) rs
| E_JnzT : forall pc rs r pc' n, rs r = S n -> exec pc rs (Jnz r pc') pc' rs.

(** We prove that [exec] represents a total function.  In our proof script, we use a [match] tactic with a [context] pattern.  This particular example finds an occurrence of a pattern [Jnz ?r _] anywhere in the current subgoal's conclusion.  We use a Coq library tactic [case_eq] to do case analysis on whether the current value [rs r] of the register [r] is zero or not.  [case_eq] differs from [destruct] in saving an equality relating the old variable to the new form we deduce for it. *)

Lemma exec_total : forall pc rs i,
  exists pc', exists rs', exec pc rs i pc' rs'.
  Hint Constructors exec.

  destruct i; crush; eauto;
    match goal with
      | [ |- context[Jnz ?r _] ] => case_eq (rs r)
    end; eauto.
Qed.

(** We are ready to define a co-inductive judgment capturing the idea that a program runs forever.  We define the judgment in terms of a program [prog], represented as a function mapping each label to the instruction found there. *)

Section safe.
  Variable prog : label -> instr.

  CoInductive safe : label -> regs -> Prop :=
  | Step : forall pc r pc' r',
    exec pc r (prog pc) pc' r'
    -> safe pc' r'
    -> safe pc r.

  (** Now we can prove that any starting address and register bank lead to safe infinite execution.  Recall that proofs of existentially-quantified formulas are all built with a single constructor of the inductive type [ex].  This means that we can use [destruct] to "open up" such proofs.  In the proof below, we want to perform this opening up on an appropriate use of the [exec_total] lemma.  This lemma's conclusion begins with two existential quantifiers, so we want to tell [destruct] that it should not stop at the first quantifier.  We accomplish our goal by using an %\textit{%#<i>#intro pattern#</i>#%}% with [destruct].  Consult the Coq manual for the details of intro patterns; the specific pattern [[? [? ?]]] that we use here accomplishes our goal of destructing both quantifiers at once. *)
  
  Theorem always_safe : forall pc rs,
    safe pc rs.
    cofix; intros;
      destruct (exec_total pc rs (prog pc)) as [? [? ?]];
        econstructor; eauto.
  Qed.
End safe.

(** If we print the proof term that was generated, we can verify that the proof is structured as a [cofix], with each co-recursive call properly guarded. *)

Print always_safe.


(** * Exercises *)

(** %\begin{enumerate}%#<ol>#

%\item%#<li># %\begin{enumerate}%#<ol>#
  %\item%#<li># Define a co-inductive type of infinite trees carrying data of a fixed parameter type.  Each node should contain a data value and two child trees.#</li>#
  %\item%#<li># Define a function [everywhere] for building a tree with the same data value at every node.#</li>#
  %\item%#<li># Define a function [map] for building an output tree out of two input trees by traversing them in parallel and applying a two-argument function to their corresponding data values.#</li>#
  %\item%#<li># Define a tree [falses] where every node has the value [false].#</li>#
  %\item%#<li># Define a tree [true_false] where the root node has value [true], its children have value [false], all nodes at the next have the value [true], and so on, alternating boolean values from level to level.#</li>#
  %\item%#<li># Prove that [true_false] is equal to the result of mapping the boolean "or" function [orb] over [true_false] and [falses].  You can make [orb] available with [Require Import Bool.].  You may find the lemma [orb_false_r] from the same module helpful.  Your proof here should not be about the standard equality [=], but rather about some new equality relation that you define.#</li>#
#</ol>#%\end{enumerate}% #</li>#

#</ol>#%\end{enumerate}% *)
