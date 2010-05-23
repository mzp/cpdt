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


(** %\part{Programming with Dependent Types}

\chapter{Subset Types and Variations}% *)

(** So far, we have seen many examples of what we might call "classical program verification."  We write programs, write their specifications, and then prove that the programs satisfy their specifications.  The programs that we have written in Coq have been normal functional programs that we could just as well have written in Haskell or ML.  In this chapter, we start investigating uses of %\textit{%#<i>#dependent types#</i>#%}% to integrate programming, specification, and proving into a single phase. *)


(** * Introducing Subset Types *)

(** Let us consider several ways of implementing the natural number predecessor function.  We start by displaying the definition from the standard library: *)

Print pred.
(** %\vspace{-.15in}% [[
pred = fun n : nat => match n with
                      | 0 => 0
                      | S u => u
                      end
     : nat -> nat
 
]]

We can use a new command, [Extraction], to produce an OCaml version of this function. *)

Extraction pred.

(** %\begin{verbatim}
(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u
\end{verbatim}%

#<pre>
(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u
</pre># *)

(** Returning 0 as the predecessor of 0 can come across as somewhat of a hack.  In some situations, we might like to be sure that we never try to take the predecessor of 0.  We can enforce this by giving [pred] a stronger, dependent type. *)

Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

(** We expand the type of [pred] to include a %\textit{%#<i>#proof#</i>#%}% that its argument [n] is greater than 0.  When [n] is 0, we use the proof to derive a contradiction, which we can use to build a value of any type via a vacuous pattern match.  When [n] is a successor, we have no need for the proof and just return the answer.  The proof argument can be said to have a %\textit{%#<i>#dependent#</i>#%}% type, because its type depends on the %\textit{%#<i>#value#</i>#%}% of the argument [n].

One aspect in particular of the definition of [pred_strong1] may be surprising.  We took advantage of [Definition]'s syntactic sugar for defining function arguments in the case of [n], but we bound the proofs later with explicit [fun] expressions.  Let us see what happens if we write this function in the way that at first seems most natural.

[[
Definition pred_strong1' (n : nat) (pf : n > 0) : nat :=
  match n with
    | O => match zgtz pf with end
    | S n' => n'
  end.

Error: In environment
n : nat
pf : n > 0
The term "pf" has type "n > 0" while it is expected to have type 
"0 > 0"
 
]]

The term [zgtz pf] fails to type-check.  Somehow the type checker has failed to take into account information that follows from which [match] branch that term appears in.  The problem is that, by default, [match] does not let us use such implied information.  To get refined typing, we must always rely on [match] annotations, either written explicitly or inferred.

In this case, we must use a [return] annotation to declare the relationship between the %\textit{%#<i>#value#</i>#%}% of the [match] discriminee and the %\textit{%#<i>#type#</i>#%}% of the result.  There is no annotation that lets us declare a relationship between the discriminee and the type of a variable that is already in scope; hence, we delay the binding of [pf], so that we can use the [return] annotation to express the needed relationship.

We are lucky that Coq's heuristics infer the [return] clause (specifically, [return n > 0 -> nat]) for us in this case.  In general, however, the inference problem is undecidable.  The known undecidable problem of %\textit{%#<i>#higher-order unification#</i>#%}% reduces to the [match] type inference problem.  Over time, Coq is enhanced with more and more heuristics to get around this problem, but there must always exist [match]es whose types Coq cannot infer without annotations.

Let us now take a look at the OCaml code Coq generates for [pred_strong1]. *)

Extraction pred_strong1.

(** %\begin{verbatim}
(** val pred_strong1 : nat -> nat **)

let pred_strong1 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
\end{verbatim}%

#<pre>
(** val pred_strong1 : nat -> nat **)

let pred_strong1 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
</pre># *)

(** The proof argument has disappeared!  We get exactly the OCaml code we would have written manually.  This is our first demonstration of the main technically interesting feature of Coq program extraction: program components of type [Prop] are erased systematically.

We can reimplement our dependently-typed [pred] based on %\textit{%#<i>#subset types#</i>#%}%, defined in the standard library with the type family [sig]. *)

Print sig.
(** %\vspace{-.15in}% [[
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P
For sig: Argument A is implicit
For exist: Argument A is implicit
 
]]

[sig] is a Curry-Howard twin of [ex], except that [sig] is in [Type], while [ex] is in [Prop].  That means that [sig] values can survive extraction, while [ex] proofs will always be erased.  The actual details of extraction of [sig]s are more subtle, as we will see shortly.

We rewrite [pred_strong1], using some syntactic sugar for subset types. *)

Locate "{ _ : _ | _ }".
(** %\vspace{-.15in}% [[
Notation            Scope     
"{ x : A  |  P }" := sig (fun x : A => P)
                      : type_scope
                      (default interpretation)
 ]] *)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist O pf => match zgtz pf with end
    | exist (S n') _ => n'
  end.

Extraction pred_strong2.

(** %\begin{verbatim}
(** val pred_strong2 : nat -> nat **)

let pred_strong2 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
\end{verbatim}%

#<pre>
(** val pred_strong2 : nat -> nat **)

let pred_strong2 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
</pre>#

We arrive at the same OCaml code as was extracted from [pred_strong1], which may seem surprising at first.  The reason is that a value of [sig] is a pair of two pieces, a value and a proof about it.  Extraction erases the proof, which reduces the constructor [exist] of [sig] to taking just a single argument.  An optimization eliminates uses of datatypes with single constructors taking single arguments, and we arrive back where we started.

We can continue on in the process of refining [pred]'s type.  Let us change its result type to capture that the output is really the predecessor of the input. *)

Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
    | exist 0 pf => match zgtz pf with end
    | exist (S n') pf => exist _ n' (refl_equal _)
  end.

(** The function [proj1_sig] extracts the base value from a subset type.  Besides the use of that function, the only other new thing is the use of the [exist] constructor to build a new [sig] value, and the details of how to do that follow from the output of our earlier [Print] command.  It also turns out that we need to include an explicit [return] clause here, since Coq's heuristics are not smart enough to propagate the result type that we wrote earlier.

By now, the reader is probably ready to believe that the new [pred_strong] leads to the same OCaml code as we have seen several times so far, and Coq does not disappoint. *)

Extraction pred_strong3.

(** %\begin{verbatim}
(** val pred_strong3 : nat -> nat **)

let pred_strong3 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
\end{verbatim}%

#<pre>
(** val pred_strong3 : nat -> nat **)

let pred_strong3 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
</pre>#

We have managed to reach a type that is, in a formal sense, the most expressive possible for [pred].  Any other implementation of the same type must have the same input-output behavior.  However, there is still room for improvement in making this kind of code easier to write.  Here is a version that takes advantage of tactic-based theorem proving.  We switch back to passing a separate proof argument instead of using a subset type for the function's input, because this leads to cleaner code. *)

Definition pred_strong4 (n : nat) : n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end).

(* begin thide *)
  (** We build [pred_strong4] using tactic-based proving, beginning with a [Definition] command that ends in a period before a definition is given.  Such a command enters the interactive proving mode, with the type given for the new identifier as our proof goal.  We do most of the work with the [refine] tactic, to which we pass a partial "proof" of the type we are trying to prove.  There may be some pieces left to fill in, indicated by underscores.  Any underscore that Coq cannot reconstruct with type inference is added as a proof subgoal.  In this case, we have two subgoals:

     [[
2 subgoals
  
  n : nat
  _ : 0 > 0
  ============================
   False

subgoal 2 is:
 S n' = S n'
 
 ]]

We can see that the first subgoal comes from the second underscore passed to [False_rec], and the second subgoal comes from the second underscore passed to [exist].  In the first case, we see that, though we bound the proof variable with an underscore, it is still available in our proof context.  It is hard to refer to underscore-named variables in manual proofs, but automation makes short work of them.  Both subgoals are easy to discharge that way, so let us back up and ask to prove all subgoals automatically. *)

  Undo.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end); crush.
(* end thide *)
Defined.

(** We end the "proof" with [Defined] instead of [Qed], so that the definition we constructed remains visible.  This contrasts to the case of ending a proof with [Qed], where the details of the proof are hidden afterward.  Let us see what our proof script constructed. *)

Print pred_strong4.
(** %\vspace{-.15in}% [[
pred_strong4 = 
fun n : nat =>
match n as n0 return (n0 > 0 -> {m : nat | n0 = S m}) with
| 0 =>
    fun _ : 0 > 0 =>
    False_rec {m : nat | 0 = S m}
      (Bool.diff_false_true
         (Bool.absurd_eq_true false
            (Bool.diff_false_true
               (Bool.absurd_eq_true false (pred_strong4_subproof n _)))))
| S n' =>
    fun _ : S n' > 0 =>
    exist (fun m : nat => S n' = S m) n' (refl_equal (S n'))
end
     : forall n : nat, n > 0 -> {m : nat | n = S m}
 
]]

We see the code we entered, with some proofs filled in.  The first proof obligation, the second argument to [False_rec], is filled in with a nasty-looking proof term that we can be glad we did not enter by hand.  The second proof obligation is a simple reflexivity proof.

We are almost done with the ideal implementation of dependent predecessor.  We can use Coq's syntax extension facility to arrive at code with almost no complexity beyond a Haskell or ML program with a complete specification in a comment. *)

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_strong5 (n : nat) : n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end); crush.
Defined.

(** One other alternative is worth demonstrating.  Recent Coq versions include a facility called [Program] that streamlines this style of definition.  Here is a complete implementation using [Program]. *)

Obligation Tactic := crush.

Program Definition pred_strong6 (n : nat) (_ : n > 0) : {m : nat | n = S m} :=
  match n with
    | O => _
    | S n' => n'
  end.

(** Printing the resulting definition of [pred_strong6] yields a term very similar to what we built with [refine].  [Program] can save time in writing programs that use subset types.  Nonetheless, [refine] is often just as effective, and [refine] gives you more control over the form the final term takes, which can be useful when you want to prove additional theorems about your definition.  [Program] will sometimes insert type casts that can complicate theorem-proving. *)


(** * Decidable Proposition Types *)

(** There is another type in the standard library which captures the idea of program values that indicate which of two propositions is true. *)

Print sumbool.
(** %\vspace{-.15in}% [[
Inductive sumbool (A : Prop) (B : Prop) : Set :=
    left : A -> {A} + {B} | right : B -> {A} + {B}
For left: Argument A is implicit
For right: Argument B is implicit
 
]]

We can define some notations to make working with [sumbool] more convenient. *)

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

(** The [Reduce] notation is notable because it demonstrates how [if] is overloaded in Coq.  The [if] form actually works when the test expression has any two-constructor inductive type.  Moreover, in the [then] and [else] branches, the appropriate constructor arguments are bound.  This is important when working with [sumbool]s, when we want to have the proof stored in the test expression available when proving the proof obligations generated in the appropriate branch.

Now we can write [eq_nat_dec], which compares two natural numbers, returning either a proof of their equality or a proof of their inequality. *)

Definition eq_nat_dec (n m : nat) : {n = m} + {n <> m}.
  refine (fix f (n m : nat) : {n = m} + {n <> m} :=
    match n, m with
      | O, O => Yes
      | S n', S m' => Reduce (f n' m')
      | _, _ => No
    end); congruence.
Defined.

(** Our definition extracts to reasonable OCaml code. *)

Extraction eq_nat_dec.

(** %\begin{verbatim}
(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S n0 -> Right)
    | S n' -> (match m with
                 | O -> Right
                 | S m' -> eq_nat_dec n' m')
\end{verbatim}%

#<pre>
(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S n0 -> Right)
    | S n' -> (match m with
                 | O -> Right
                 | S m' -> eq_nat_dec n' m')
</pre>#

Proving this kind of decidable equality result is so common that Coq comes with a tactic for automating it. *)

Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
  decide equality.
Defined.

(** Curious readers can verify that the [decide equality] version extracts to the same OCaml code as our more manual version does.  That OCaml code had one undesirable property, which is that it uses %\texttt{%#<tt>#Left#</tt>#%}% and %\texttt{%#<tt>#Right#</tt>#%}% constructors instead of the boolean values built into OCaml.  We can fix this, by using Coq's facility for mapping Coq inductive types to OCaml variant types. *)

Extract Inductive sumbool => "bool" ["true" "false"].
Extraction eq_nat_dec'.

(** %\begin{verbatim}
(** val eq_nat_dec' : nat -> nat -> bool **)

let rec eq_nat_dec' n m0 =
  match n with
    | O -> (match m0 with
              | O -> true
              | S n0 -> false)
    | S n0 -> (match m0 with
                 | O -> false
                 | S n1 -> eq_nat_dec' n0 n1)
\end{verbatim}%

#<pre>
(** val eq_nat_dec' : nat -> nat -> bool **)

let rec eq_nat_dec' n m0 =
  match n with
    | O -> (match m0 with
              | O -> true
              | S n0 -> false)
    | S n0 -> (match m0 with
                 | O -> false
                 | S n1 -> eq_nat_dec' n0 n1)
</pre># *)

(** %\smallskip%

We can build "smart" versions of the usual boolean operators and put them to good use in certified programming.  For instance, here is a [sumbool] version of boolean "or." *)

(* begin thide *)
Notation "x || y" := (if x then Yes else Reduce y).

(** Let us use it for building a function that decides list membership.  We need to assume the existence of an equality decision procedure for the type of list elements. *)

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** The final function is easy to write using the techniques we have developed so far. *)

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + {~ In x ls}.
    refine (fix f (x : A) (ls : list A) : {In x ls} + {~ In x ls} :=
      match ls with
	| nil => No
	| x' :: ls' => A_eq_dec x x' || f x ls'
      end); crush.
  Qed.
End In_dec.

(** [In_dec] has a reasonable extraction to OCaml. *)

Extraction In_dec.
(* end thide *)

(** %\begin{verbatim}
(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec a_eq_dec x = function
  | Nil -> false
  | Cons (x', ls') ->
      (match a_eq_dec x x' with
         | true -> true
         | false -> in_dec a_eq_dec x ls')
\end{verbatim}%

#<pre>
(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec a_eq_dec x = function
  | Nil -> false
  | Cons (x', ls') ->
      (match a_eq_dec x x' with
         | true -> true
         | false -> in_dec a_eq_dec x ls')
</pre># *)


(** * Partial Subset Types *)

(** Our final implementation of dependent predecessor used a very specific argument type to ensure that execution could always complete normally.  Sometimes we want to allow execution to fail, and we want a more principled way of signaling that than returning a default value, as [pred] does for [0].  One approach is to define this type family [maybe], which is a version of [sig] that allows obligation-free failure. *)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

(** We can define some new notations, analogous to those we defined for subset types. *)

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[[ x ]]" := (Found _ x _).

(** Now our next version of [pred] is trivial to write. *)

Definition pred_strong7 (n : nat) : {{m | n = S m}}.
  refine (fun n =>
    match n with
      | O => ??
      | S n' => [[n']]
    end); trivial.
Defined.

(** Because we used [maybe], one valid implementation of the type we gave [pred_strong7] would return [??] in every case.  We can strengthen the type to rule out such vacuous implementations, and the type family [sumor] from the standard library provides the easiest starting point.  For type [A] and proposition [B], [A + {B}] desugars to [sumor A B], whose values are either values of [A] or proofs of [B]. *)

Print sumor.
(** %\vspace{-.15in}% [[
Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}
For inleft: Argument A is implicit
For inright: Argument B is implicit
]] *)

(** We add notations for easy use of the [sumor] constructors.  The second notation is specialized to [sumor]s whose [A] parameters are instantiated with regular subset types, since this is how we will use [sumor] below. *)

Notation "!!" := (inright _ _).
Notation "[[[ x ]]]" := (inleft _ [x]).

(** Now we are ready to give the final version of possibly-failing predecessor.  The [sumor]-based type that we use is maximally expressive; any implementation of the type has the same input-output behavior. *)

Definition pred_strong8 (n : nat) : {m : nat | n = S m} + {n = 0}.
  refine (fun n =>
    match n with
      | O => !!
      | S n' => [[[n']]]
    end); trivial.
Defined.


(** * Monadic Notations *)

(** We can treat [maybe] like a monad, in the same way that the Haskell [Maybe] type is interpreted as a failure monad.  Our [maybe] has the wrong type to be a literal monad, but a "bind"-like notation will still be helpful. *)

Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

(** The meaning of [x <- e1; e2] is: First run [e1].  If it fails to find an answer, then announce failure for our derived computation, too.  If [e1] %\textit{%#<i>#does#</i>#%}% find an answer, pass that answer on to [e2] to find the final result.  The variable [x] can be considered bound in [e2].

   This notation is very helpful for composing richly-typed procedures.  For instance, here is a very simple implementation of a function to take the predecessors of two naturals at once. *)

Definition doublePred (n1 n2 : nat) : {{p | n1 = S (fst p) /\ n2 = S (snd p)}}.
  refine (fun n1 n2 =>
    m1 <- pred_strong7 n1;
    m2 <- pred_strong7 n2;
    [[(m1, m2)]]); tauto.
Defined.

(** We can build a [sumor] version of the "bind" notation and use it to write a similarly straightforward version of this function. *)

(** printing <-- $\longleftarrow$ *)

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

(** printing * $\times$ *)

Definition doublePred' (n1 n2 : nat)
  : {p : nat * nat | n1 = S (fst p) /\ n2 = S (snd p)}
  + {n1 = 0 \/ n2 = 0}.
  refine (fun n1 n2 =>
    m1 <-- pred_strong8 n1;
    m2 <-- pred_strong8 n2;
    [[[(m1, m2)]]]); tauto.
Defined.


(** * A Type-Checking Example *)

(** We can apply these specification types to build a certified type-checker for a simple expression language. *)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

(** We define a simple language of types and its typing rules, in the style introduced in Chapter 4. *)

Inductive type : Set := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

(** It will be helpful to have a function for comparing two types.  We build one using [decide equality]. *)

(* begin thide *)
Definition eq_type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

(** Another notation complements the monadic notation for [maybe] that we defined earlier.  Sometimes we want to include "assertions" in our procedures.  That is, we want to run a decision procedure and fail if it fails; otherwise, we want to continue, with the proof that it produced made available to us.  This infix notation captures that idea, for a procedure that returns an arbitrary two-constructor type. *)

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).

(** With that notation defined, we can implement a [typeCheck] function, whose code is only more complex than what we would write in ML because it needs to include some extra type annotations.  Every [[[e]]] expression adds a [hasType] proof obligation, and [crush] makes short work of them when we add [hasType]'s constructors as hints. *)
(* end thide *)

Definition typeCheck (e : exp) : {{t | hasType e t}}.
(* begin thide *)
  Hint Constructors hasType.

  refine (fix F (e : exp) : {{t | hasType e t}} :=
    match e with
      | Nat _ => [[TNat]]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;;
        eq_type_dec t2 TNat;;
        [[TNat]]
      | Bool _ => [[TBool]]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [[TBool]]
    end); crush.
(* end thide *)
Defined.

(** Despite manipulating proofs, our type checker is easy to run. *)

Eval simpl in typeCheck (Nat 0).
(** %\vspace{-.15in}% [[
     = [[TNat]]
     : {{t | hasType (Nat 0) t}}
     ]] *)

Eval simpl in typeCheck (Plus (Nat 1) (Nat 2)).
(** %\vspace{-.15in}% [[
     = [[TNat]]
     : {{t | hasType (Plus (Nat 1) (Nat 2)) t}}
     ]] *)

Eval simpl in typeCheck (Plus (Nat 1) (Bool false)).
(** %\vspace{-.15in}% [[
     = ??
     : {{t | hasType (Plus (Nat 1) (Bool false)) t}}
     ]] *)

(** The type-checker also extracts to some reasonable OCaml code. *)

Extraction typeCheck.

(** %\begin{verbatim}
(** val typeCheck : exp -> type0 maybe **)

let rec typeCheck = function
  | Nat n -> Found TNat
  | Plus (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TNat with
                       | true ->
                           (match eq_type_dec t2 TNat with
                              | true -> Found TNat
                              | false -> Unknown)
                       | false -> Unknown)))
  | Bool b -> Found TBool
  | And (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TBool with
                       | true ->
                           (match eq_type_dec t2 TBool with
                              | true -> Found TBool
                              | false -> Unknown)
                       | false -> Unknown)))
\end{verbatim}%

#<pre>
(** val typeCheck : exp -> type0 maybe **)

let rec typeCheck = function
  | Nat n -> Found TNat
  | Plus (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TNat with
                       | true ->
                           (match eq_type_dec t2 TNat with
                              | true -> Found TNat
                              | false -> Unknown)
                       | false -> Unknown)))
  | Bool b -> Found TBool
  | And (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TBool with
                       | true ->
                           (match eq_type_dec t2 TBool with
                              | true -> Found TBool
                              | false -> Unknown)
                       | false -> Unknown)))
</pre># *)

(** %\smallskip%

We can adapt this implementation to use [sumor], so that we know our type-checker only fails on ill-typed inputs.  First, we define an analogue to the "assertion" notation. *)

(* begin thide *)
Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).

(** Next, we prove a helpful lemma, which states that a given expression can have at most one type. *)

Lemma hasType_det : forall e t1,
  hasType e t1
  -> forall t2,
    hasType e t2
    -> t1 = t2.
  induction 1; inversion 1; crush.
Qed.

(** Now we can define the type-checker.  Its type expresses that it only fails on untypable expressions. *)

(* end thide *)
Definition typeCheck' (e : exp) : {t : type | hasType e t} + {forall t, ~ hasType e t}.
(* begin thide *)
  Hint Constructors hasType.
  (** We register all of the typing rules as hints. *)

  Hint Resolve hasType_det.
  (** [hasType_det] will also be useful for proving proof obligations with contradictory contexts.  Since its statement includes [forall]-bound variables that do not appear in its conclusion, only [eauto] will apply this hint. *)

  (** Finally, the implementation of [typeCheck] can be transcribed literally, simply switching notations as needed. *)

  refine (fix F (e : exp) : {t : type | hasType e t} + {forall t, ~ hasType e t} :=
    match e with
      | Nat _ => [[[TNat]]]
      | Plus e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TNat;;;
        eq_type_dec t2 TNat;;;
        [[[TNat]]]
      | Bool _ => [[[TBool]]]
      | And e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TBool;;;
        eq_type_dec t2 TBool;;;
        [[[TBool]]]
    end); clear F; crush' tt hasType; eauto.

  (** We clear [F], the local name for the recursive function, to avoid strange proofs that refer to recursive calls that we never make.  The [crush] variant [crush'] helps us by performing automatic inversion on instances of the predicates specified in its second argument.  Once we throw in [eauto] to apply [hasType_det] for us, we have discharged all the subgoals. *)
(* end thide *)


Defined.

(** The short implementation here hides just how time-saving automation is.  Every use of one of the notations adds a proof obligation, giving us 12 in total.  Most of these obligations require multiple inversions and either uses of [hasType_det] or applications of [hasType] rules.

The results of simplifying calls to [typeCheck'] look deceptively similar to the results for [typeCheck], but now the types of the results provide more information. *)

Eval simpl in typeCheck' (Nat 0).
(** %\vspace{-.15in}% [[
     = [[[TNat]]]
     : {t : type | hasType (Nat 0) t} +
       {(forall t : type, ~ hasType (Nat 0) t)}
       ]] *)

Eval simpl in typeCheck' (Plus (Nat 1) (Nat 2)).
(** %\vspace{-.15in}% [[
     = [[[TNat]]]
     : {t : type | hasType (Plus (Nat 1) (Nat 2)) t} +
       {(forall t : type, ~ hasType (Plus (Nat 1) (Nat 2)) t)}
       ]] *)

Eval simpl in typeCheck' (Plus (Nat 1) (Bool false)).
(** %\vspace{-.15in}% [[
     = !!
     : {t : type | hasType (Plus (Nat 1) (Bool false)) t} +
       {(forall t : type, ~ hasType (Plus (Nat 1) (Bool false)) t)}
       ]] *)


(** * Exercises *)

(** All of the notations defined in this chapter, plus some extras, are available for import from the module [MoreSpecif] of the book source.

%\begin{enumerate}%#<ol>#
%\item%#<li># Write a function of type [forall n m : nat, {n <= m} + {n > m}].  That is, this function decides whether one natural is less than another, and its dependent type guarantees that its results are accurate.#</li>#

%\item%#<li># %\begin{enumerate}%#<ol>#
  %\item%#<li># Define [var], a type of propositional variables, as a synonym for [nat].#</li>#
  %\item%#<li># Define an inductive type [prop] of propositional logic formulas, consisting of variables, negation, and binary conjunction and disjunction.#</li>#
  %\item%#<li># Define a function [propDenote] from variable truth assignments and [prop]s to [Prop], based on the usual meanings of the connectives.  Represent truth assignments as functions from [var] to [bool].#</li>#
  %\item%#<li># Define a function [bool_true_dec] that checks whether a boolean is true, with a maximally expressive dependent type.  That is, the function should have type [forall b, {b = true} + {b = true -> False}]. #</li>#
  %\item%#<li># Define a function [decide] that determines whether a particular [prop] is true under a particular truth assignment.  That is, the function should have type [forall (truth : var -> bool) (p : prop), {propDenote truth p} + {~ propDenote truth p}].  This function is probably easiest to write in the usual tactical style, instead of programming with [refine].  [bool_true_dec] may come in handy as a hint.#</li>#
  %\item%#<li># Define a function [negate] that returns a simplified version of the negation of a [prop].  That is, the function should have type [forall p : prop, {p' : prop | forall truth, propDenote truth p <-> ~ propDenote truth p'}].  To simplify a variable, just negate it.  Simplify a negation by returning its argument.  Simplify conjunctions and disjunctions using De Morgan's laws, negating the arguments recursively and switching the kind of connective.  [decide] may be useful in some of the proof obligations, even if you do not use it in the computational part of [negate]'s definition.  Lemmas like [decide] allow us to compensate for the lack of a general Law of the Excluded Middle in CIC.#</li>#
#</ol>#%\end{enumerate}% #</li>#

%\item%#<li># Implement the DPLL satisfiability decision procedure for boolean formulas in conjunctive normal form, with a dependent type that guarantees its correctness.  An example of a reasonable type for this function would be [forall f : formula, {truth : tvals | formulaTrue truth f} + {forall truth, ~ formulaTrue truth f}].  Implement at least "the basic backtracking algorithm" as defined here:
  %\begin{center}\url{http://en.wikipedia.org/wiki/DPLL_algorithm}\end{center}%
  #<blockquote><a href="http://en.wikipedia.org/wiki/DPLL_algorithm">http://en.wikipedia.org/wiki/DPLL_algorithm</a></blockquote>#
It might also be instructive to implement the unit propagation and pure literal elimination optimizations described there or some other optimizations that have been used in modern SAT solvers.#</li>#
   
#</ol>#%\end{enumerate}% *)
