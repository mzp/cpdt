(* Copyright (c) 2008-2010, Adam Chlipala
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


(** %\chapter{Some Quick Examples}% *)


(** I will start off by jumping right in to a fully-worked set of examples, building certified compilers from increasingly complicated source languages to stack machines.  We will meet a few useful tactics and see how they can be used in manual proofs, and we will also see how easily these proofs can be automated instead.  I assume that you have installed Coq and Proof General.  The code in this book is tested with Coq version 8.2pl1, though parts may work with other versions.

As always, you can step through the source file %\texttt{%#<tt>#StackMachine.v#</tt>#%}% for this chapter interactively in Proof General.  Alternatively, to get a feel for the whole lifecycle of creating a Coq development, you can enter the pieces of source code in this chapter in a new %\texttt{%#<tt>#.v#</tt>#%}% file in an Emacs buffer.  If you do the latter, include two lines [Require Import List Tactics.] and [Set Implicit Arguments.] at the start of the file, to match some code hidden in this rendering of the chapter source, and be sure to run the Coq binary %\texttt{%#<tt>#coqtop#</tt>#%}% with the command-line argument %\texttt{%#<tt>#-I SRC#</tt>#%}%, where %\texttt{%#<tt>#SRC#</tt>#%}% is the path to a directory containing the source for this book.  In either case, you will need to run %\texttt{%#<tt>#make#</tt>#%}% in the root directory of the source distribution for the book before getting started.  If you have installed Proof General properly, it should start automatically when you visit a %\texttt{%#<tt>#.v#</tt>#%}% buffer in Emacs.

There are some minor headaches associated with getting Proof General to pass the proper command line arguments to the %\texttt{%#<tt>#coqtop#</tt>#%}% program.  The best way to add settings that will be shared by many source files is to add a custom variable setting to your %\texttt{%#<tt>#.emacs#</tt>#%}% file, like this:
%\begin{verbatim}%#<pre>#(custom-set-variables
  ...
  '(coq-prog-args '("-I" "/path/to/cpdt/src"))
  ...
)#</pre>#%\end{verbatim}%
The extra arguments demonstrated here are the proper choices for working with the code for this book.  The ellipses stand for other Emacs customization settings you may already have.  It can be helpful to save several alternate sets of flags in your %\texttt{%#<tt>#.emacs#</tt>#%}% file, with all but one commented out within the %\texttt{%#<tt>#custom-set-variables#</tt>#%}% block at any given time.

With Proof General, the portion of a buffer that Coq has processed is highlighted in some way, like being given a blue background.  You step through Coq source files by positioning the point at the position you want Coq to run to and pressing C-C C-RET.  This can be used both for normal step-by-step coding, by placing the point inside some command past the end of the highlighted region; and for undoing, by placing the point inside the highlighted region. *)


(** * Arithmetic Expressions Over Natural Numbers *)

(** We will begin with that staple of compiler textbooks, arithmetic expressions over a single type of numbers. *)

(** ** Source Language *)

(** We begin with the syntax of the source language. *)

Inductive binop : Set := Plus | Times.

(** Our first line of Coq code should be unsurprising to ML and Haskell programmers.  We define an algebraic datatype [binop] to stand for the binary operators of our source language.  There are just two wrinkles compared to ML and Haskell.  First, we use the keyword [Inductive], in place of %\texttt{%#<tt>#data#</tt>#%}%, %\texttt{%#<tt>#datatype#</tt>#%}%, or %\texttt{%#<tt>#type#</tt>#%}%.  This is not just a trivial surface syntax difference; inductive types in Coq are much more expressive than garden variety algebraic datatypes, essentially enabling us to encode all of mathematics, though we begin humbly in this chapter.  Second, there is the [: Set] fragment, which declares that we are defining a datatype that should be thought of as a constituent of programs.  Later, we will see other options for defining datatypes in the universe of proofs or in an infinite hierarchy of universes, encompassing both programs and proofs, that is useful in higher-order constructions. *)

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

(** Now we define the type of arithmetic expressions.  We write that a constant may be built from one argument, a natural number; and a binary operation may be built from a choice of operator and two operand expressions.

A note for readers following along in the PDF version: coqdoc supports pretty-printing of tokens in LaTeX or HTML.  Where you see a right arrow character, the source contains the ASCII text %\texttt{%#<tt>#->#</tt>#%}%.  Other examples of this substitution appearing in this chapter are a double right arrow for %\texttt{%#<tt>#=>#</tt>#%}% and the inverted 'A' symbol for %\texttt{%#<tt>#forall#</tt>#%}%.  When in doubt about the ASCII version of a symbol, you can consult the chapter source code.

%\medskip%

Now we are ready to say what these programs mean.  We will do this by writing an interpreter that can be thought of as a trivial operational or denotational semantics.  (If you are not familiar with these semantic techniques, no need to worry; we will stick to "common sense" constructions.) *)

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

(** The meaning of a binary operator is a binary function over naturals, defined with pattern-matching notation analogous to the %\texttt{%#<tt>#case#</tt>#%}% and %\texttt{%#<tt>#match#</tt>#%}% of ML and Haskell, and referring to the functions [plus] and [mult] from the Coq standard library.  The keyword [Definition] is Coq's all-purpose notation for binding a term of the programming language to a name, with some associated syntactic sugar, like the notation we see here for defining a function.  That sugar could be expanded to yield this definition:

[[
Definition binopDenote : binop -> nat -> nat -> nat := fun (b : binop) =>
  match b with
    | Plus => plus
    | Times => mult
  end.

]]

In this example, we could also omit all of the type annotations, arriving at:

[[
Definition binopDenote := fun b =>
  match b with
    | Plus => plus
    | Times => mult
  end.

]]

Languages like Haskell and ML have a convenient %\textit{%#<i>#principal typing#</i>#%}% property, which gives us strong guarantees about how effective type inference will be.  Unfortunately, Coq's type system is so expressive that any kind of "complete" type inference is impossible, and the task even seems to be hard heuristically in practice.  Nonetheless, Coq includes some very helpful heuristics, many of them copying the workings of Haskell and ML type-checkers for programs that fall in simple fragments of Coq's language.

This is as good a time as any to mention the preponderance of different languages associated with Coq.  The theoretical foundation of Coq is a formal system called the %\textit{%#<i>#Calculus of Inductive Constructions (CIC)#</i>#%}%, which is an extension of the older %\textit{%#<i>#Calculus of Constructions (CoC)#</i>#%}%.  CIC is quite a spartan foundation, which is helpful for proving metatheory but not so helpful for real development.  Still, it is nice to know that it has been proved that CIC enjoys properties like %\textit{%#<i>#strong normalization#</i>#%}%, meaning that every program (and, more importantly, every proof term) terminates; and %\textit{%#<i>#relative consistency#</i>#%}% with systems like versions of Zermelo Fraenkel set theory, which roughly means that you can believe that Coq proofs mean that the corresponding propositions are "really true," if you believe in set theory.

Coq is actually based on an extension of CIC called %\textit{%#<i>#Gallina#</i>#%}%.  The text after the [:=] and before the period in the last code example is a term of Gallina.  Gallina adds many useful features that are not compiled internally to more primitive CIC features.  The important metatheorems about CIC have not been extended to the full breadth of these features, but most Coq users do not seem to lose much sleep over this omission.

Commands like [Inductive] and [Definition] are part of %\textit{%#<i>#the vernacular#</i>#%}%, which includes all sorts of useful queries and requests to the Coq system.

Finally, there is %\textit{%#<i>#Ltac#</i>#%}%, Coq's domain-specific language for writing proofs and decision procedures. We will see some basic examples of Ltac later in this chapter, and much of this book is devoted to more involved Ltac examples.

%\medskip%

We can give a simple definition of the meaning of an expression: *)

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(** We declare explicitly that this is a recursive definition, using the keyword [Fixpoint].  The rest should be old hat for functional programmers. *)

(** It is convenient to be able to test definitions before starting to prove things about them.  We can verify that our semantics is sensible by evaluating some sample uses. *)

Eval simpl in expDenote (Const 42).
(** [= 42 : nat] *)

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
(** [= 4 : nat] *)

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= 28 : nat] *)

(** ** Target Language *)

(** We will compile our source programs onto a simple stack machine, whose syntax is: *)

Inductive instr : Set :=
| IConst : nat -> instr
| IBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(** An instruction either pushes a constant onto the stack or pops two arguments, applies a binary operator to them, and pushes the result onto the stack.  A program is a list of instructions, and a stack is a list of natural numbers.

We can give instructions meanings as functions from stacks to optional stacks, where running an instruction results in [None] in case of a stack underflow and results in [Some s'] when the result of execution is the new stack [s'].  [::] is the "list cons" operator from the Coq standard library. *)

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | IConst n => Some (n :: s)
    | IBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.

(** With [instrDenote] defined, it is easy to define a function [progDenote], which iterates application of [instrDenote] through a whole program.

   [[
Fixpoint progDenote (p : prog) (s : stack) {struct p} : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

  ]]

  There is one interesting difference compared to our previous example of a [Fixpoint].  This recursive function takes two arguments, [p] and [s].  It is critical for the soundness of Coq that every program terminate, so a shallow syntactic termination check is imposed on every recursive function definition.  One of the function parameters must be designated to decrease monotonically across recursive calls.  That is, every recursive call must use a version of that argument that has been pulled out of the current argument by some number of [match] expressions.  [expDenote] has only one argument, so we did not need to specify which of its arguments decreases.  For [progDenote], we resolve the ambiguity by writing [{struct p}] to indicate that argument [p] decreases structurally.

   Recent versions of Coq will also infer a termination argument, so that we may write simply: *)

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.


(** ** Translation *)

(** Our compiler itself is now unsurprising.  [++] is the list concatenation operator from the Coq standard library. *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => IConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ IBinop b :: nil
  end.


(** Before we set about proving that this compiler is correct, we can try a few test runs, using our sample programs from earlier. *)

Eval simpl in compile (Const 42).
(** [= IConst 42 :: nil : prog] *)

Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
(** [= IConst 2 :: IConst 2 :: IBinop Plus :: nil : prog] *)

Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= IConst 7 :: IConst 2 :: IConst 2 :: IBinop Plus :: IBinop Times :: nil : prog] *)

(** We can also run our compiled programs and check that they give the right results. *)

Eval simpl in progDenote (compile (Const 42)) nil.
(** [= Some (42 :: nil) : option stack] *)

Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
(** [= Some (4 :: nil) : option stack] *)

Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) nil.
(** [= Some (28 :: nil) : option stack] *)


(** ** Translation Correctness *)

(** We are ready to prove that our compiler is implemented correctly.  We can use a new vernacular command [Theorem] to start a correctness proof, in terms of the semantics we defined earlier: *)

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
(* begin hide *)
Abort.
(* end hide *)
(* begin thide *)

(** Though a pencil-and-paper proof might clock out at this point, writing "by a routine induction on [e]," it turns out not to make sense to attack this proof directly.  We need to use the standard trick of %\textit{%#<i>#strengthening the induction hypothesis#</i>#%}%.  We do that by proving an auxiliary lemma:
*)

Lemma compile_correct' : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

(** After the period in the [Lemma] command, we are in %\textit{%#<i>#the interactive proof-editing mode#</i>#%}%.  We find ourselves staring at this ominous screen of text:

[[
1 subgoal
  
 ============================
  forall (e : exp) (p : list instr) (s : stack),
   progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)  
 
]]

Coq seems to be restating the lemma for us.  What we are seeing is a limited case of a more general protocol for describing where we are in a proof.  We are told that we have a single subgoal.  In general, during a proof, we can have many pending subgoals, each of which is a logical proposition to prove.  Subgoals can be proved in any order, but it usually works best to prove them in the order that Coq chooses.

Next in the output, we see our single subgoal described in full detail.  There is a double-dashed line, above which would be our free variables and hypotheses, if we had any.  Below the line is the conclusion, which, in general, is to be proved from the hypotheses.

We manipulate the proof state by running commands called %\textit{%#<i>#tactics#</i>#%}%.  Let us start out by running one of the most important tactics:
*)

  induction e.

(** We declare that this proof will proceed by induction on the structure of the expression [e].  This swaps out our initial subgoal for two new subgoals, one for each case of the inductive proof:

[[
2 subgoals
  
 n : nat
 ============================
 forall (s : stack) (p : list instr),
   progDenote (compile (Const n) ++ p) s =
   progDenote p (expDenote (Const n) :: s)
]]
[[
 subgoal 2 is:
  forall (s : stack) (p : list instr),
    progDenote (compile (Binop b e1 e2) ++ p) s =
    progDenote p (expDenote (Binop b e1 e2) :: s)
 
]]

The first and current subgoal is displayed with the double-dashed line below free variables and hypotheses, while later subgoals are only summarized with their conclusions.  We see an example of a free variable in the first subgoal; [n] is a free variable of type [nat].  The conclusion is the original theorem statement where [e] has been replaced by [Const n].  In a similar manner, the second case has [e] replaced by a generalized invocation of the [Binop] expression constructor.  We can see that proving both cases corresponds to a standard proof by structural induction.

We begin the first case with another very common tactic.
*)

  intros.

(** The current subgoal changes to:
[[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote (compile (Const n) ++ p) s =
 progDenote p (expDenote (Const n) :: s)
 
]]

We see that [intros] changes [forall]-bound variables at the beginning of a goal into free variables.

To progress further, we need to use the definitions of some of the functions appearing in the goal.  The [unfold] tactic replaces an identifier with its definition.
*)

  unfold compile.
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
 progDenote ((IConst n :: nil) ++ p) s =
 progDenote p (expDenote (Const n) :: s)
 
]] *)

  unfold expDenote.
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
 progDenote ((IConst n :: nil) ++ p) s = progDenote p (n :: s)
 
]]

We only need to unfold the first occurrence of [progDenote] to prove the goal: *)

  unfold progDenote at 1.

(** [[

 n : nat
 s : stack
 p : list instr
 ============================
  (fix progDenote (p0 : prog) (s0 : stack) {struct p0} : 
    option stack :=
      match p0 with
      | nil => Some s0
      | i :: p' =>
          match instrDenote i s0 with
          | Some s' => progDenote p' s'
          | None => None (A:=stack)
          end
      end) ((IConst n :: nil) ++ p) s =
   progDenote p (n :: s)
 
]]

This last [unfold] has left us with an anonymous fixpoint version of [progDenote], which will generally happen when unfolding recursive definitions.  Fortunately, in this case, we can eliminate such complications right away, since the structure of the argument [(IConst n :: nil) ++ p] is known, allowing us to simplify the internal pattern match with the [simpl] tactic:
*)

  simpl.
(** [[
 n : nat
 s : stack
 p : list instr
 ============================
 (fix progDenote (p0 : prog) (s0 : stack) {struct p0} : 
  option stack :=
    match p0 with
    | nil => Some s0
    | i :: p' =>
        match instrDenote i s0 with
        | Some s' => progDenote p' s'
        | None => None (A:=stack)
        end
    end) p (n :: s) = progDenote p (n :: s)
 
]]

Now we can unexpand the definition of [progDenote]:
*)

  fold progDenote.

(** [[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote p (n :: s) = progDenote p (n :: s)
 
]]

It looks like we are at the end of this case, since we have a trivial equality.  Indeed, a single tactic finishes us off:
*)

  reflexivity.

(** On to the second inductive case:

[[
  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  ============================
   forall (s : stack) (p : list instr),
   progDenote (compile (Binop b e1 e2) ++ p) s =
   progDenote p (expDenote (Binop b e1 e2) :: s)
 
]]

We see our first example of hypotheses above the double-dashed line.  They are the inductive hypotheses [IHe1] and [IHe2] corresponding to the subterms [e1] and [e2], respectively.

We start out the same way as before, introducing new free variables and unfolding and folding the appropriate definitions.  The seemingly frivolous [unfold]/[fold] pairs are actually accomplishing useful work, because [unfold] will sometimes perform easy simplifications. *)

  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.

(** Now we arrive at a point where the tactics we have seen so far are insufficient.  No further definition unfoldings get us anywhere, so we will need to try something different.

[[
  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  s : stack
  p : list instr
  ============================
   progDenote ((compile e2 ++ compile e1 ++ IBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
 
]]

What we need is the associative law of list concatenation, available as a theorem [app_ass] in the standard library. *)

Check app_ass.
(** [[
app_ass
     : forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n
 
]]

We use it to perform a rewrite: *)

  rewrite app_ass.

(** changing the conclusion to:

[[
   progDenote (compile e2 ++ (compile e1 ++ IBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
 
]]

Now we can notice that the lefthand side of the equality matches the lefthand side of the second inductive hypothesis, so we can rewrite with that hypothesis, too: *)

  rewrite IHe2.
(** [[
   progDenote ((compile e1 ++ IBinop b :: nil) ++ p) (expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
 
]]

The same process lets us apply the remaining hypothesis. *)

  rewrite app_ass.
  rewrite IHe1.
(** [[
   progDenote ((IBinop b :: nil) ++ p) (expDenote e1 :: expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
 
]]

Now we can apply a similar sequence of tactics to that that ended the proof of the first case.
*)

  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.

(** And the proof is completed, as indicated by the message:

[[
Proof completed.

]]

And there lies our first proof.  Already, even for simple theorems like this, the final proof script is unstructured and not very enlightening to readers.  If we extend this approach to more serious theorems, we arrive at the unreadable proof scripts that are the favorite complaints of opponents of tactic-based proving.  Fortunately, Coq has rich support for scripted automation, and we can take advantage of such a scripted tactic (defined elsewhere) to make short work of this lemma.  We abort the old proof attempt and start again.
*)

Abort.

Lemma compile_correct' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

(** We need only to state the basic inductive proof scheme and call a tactic that automates the tedious reasoning in between.  In contrast to the period tactic terminator from our last proof, the semicolon tactic separator supports structured, compositional proofs.  The tactic [t1; t2] has the effect of running [t1] and then running [t2] on each remaining subgoal.  The semicolon is one of the most fundamental building blocks of effective proof automation.  The period terminator is very useful for exploratory proving, where you need to see intermediate proof states, but final proofs of any serious complexity should have just one period, terminating a single compound tactic that probably uses semicolons.

The [crush] tactic comes from the library associated with this book and is not part of the Coq standard library.  The book's library contains a number of other tactics that are especially helpful in highly-automated proofs.

The proof of our main theorem is now easy.  We prove it with four period-terminated tactics, though separating them with semicolons would work as well; the version here is easier to step through. *)

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros.
(** [[
  e : exp
  ============================
   progDenote (compile e) nil = Some (expDenote e :: nil)
 
]]

At this point, we want to massage the lefthand side to match the statement of [compile_correct'].  A theorem from the standard library is useful: *)

Check app_nil_end.
(** [[
app_nil_end
     : forall (A : Type) (l : list A), l = l ++ nil
]] *)

  rewrite (app_nil_end (compile e)).

(** This time, we explicitly specify the value of the variable [l] from the theorem statement, since multiple expressions of list type appear in the conclusion.  [rewrite] might choose the wrong place to rewrite if we did not specify which we want.

[[
  e : exp
  ============================
   progDenote (compile e ++ nil) nil = Some (expDenote e :: nil)
 
]]

Now we can apply the lemma. *)

  rewrite compile_correct'.
(** [[
  e : exp
  ============================
   progDenote nil (expDenote e :: nil) = Some (expDenote e :: nil)
 
]]

We are almost done.  The lefthand and righthand sides can be seen to match by simple symbolic evaluation.  That means we are in luck, because Coq identifies any pair of terms as equal whenever they normalize to the same result by symbolic evaluation.  By the definition of [progDenote], that is the case here, but we do not need to worry about such details.  A simple invocation of [reflexivity] does the normalization and checks that the two results are syntactically equal. *)

  reflexivity.
Qed.
(* end thide *)


(** * Typed Expressions *)

(** In this section, we will build on the initial example by adding additional expression forms that depend on static typing of terms for safety. *)

(** ** Source Language *)

(** We define a trivial language of types to classify our expressions: *)

Inductive type : Set := Nat | Bool.

(** Now we define an expanded set of binary operators. *)

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

(** The definition of [tbinop] is different from [binop] in an important way.  Where we declared that [binop] has type [Set], here we declare that [tbinop] has type [type -> type -> type -> Set].  We define [tbinop] as an %\textit{%#<i>#indexed type family#</i>#%}%.  Indexed inductive types are at the heart of Coq's expressive power; almost everything else of interest is defined in terms of them.

ML and Haskell have indexed algebraic datatypes.  For instance, their list types are indexed by the type of data that the list carries.  However, compared to Coq, ML and Haskell 98 place two important restrictions on datatype definitions.

First, the indices of the range of each data constructor must be type variables bound at the top level of the datatype definition.  There is no way to do what we did here, where we, for instance, say that [TPlus] is a constructor building a [tbinop] whose indices are all fixed at [Nat].  %\textit{%#<i>#Generalized algebraic datatypes (GADTs)#</i>#%}% are a popular feature in GHC Haskell and other languages that removes this first restriction.

The second restriction is not lifted by GADTs.  In ML and Haskell, indices of types must be types and may not be %\textit{%#<i>#expressions#</i>#%}%.  In Coq, types may be indexed by arbitrary Gallina terms.  Type indices can live in the same universe as programs, and we can compute with them just like regular programs.  Haskell supports a hobbled form of computation in type indices based on multi-parameter type classes, and recent extensions like type functions bring Haskell programming even closer to "real" functional programming with types, but, without dependent typing, there must always be a gap between how one programs with types and how one programs normally.
*)

(** We can define a similar type family for typed expressions. *)

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall arg1 arg2 res, tbinop arg1 arg2 res -> texp arg1 -> texp arg2 -> texp res.

(** Thanks to our use of dependent types, every well-typed [texp] represents a well-typed source expression, by construction.  This turns out to be very convenient for many things we might want to do with expressions.  For instance, it is easy to adapt our interpreter approach to defining semantics.  We start by defining a function mapping the types of our languages into Coq types: *)

Definition typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(** It can take a few moments to come to terms with the fact that [Set], the type of types of programs, is itself a first-class type, and that we can write functions that return [Set]s.  Past that wrinkle, the definition of [typeDenote] is trivial, relying on the [nat] and [bool] types from the Coq standard library.

We need to define a few auxiliary functions, implementing our boolean binary operators that do not appear with the right types in the standard library.  They are entirely standard and ML-like, with the one caveat being that the Coq [nat] type uses a unary representation, where [O] is zero and [S n] is the successor of [n].
*)

Definition eq_bool (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | false, false => true
    | _, _ => false
  end.

Fixpoint eq_nat (n1 n2 : nat) : bool :=
  match n1, n2 with
    | O, O => true
    | S n1', S n2' => eq_nat n1' n2'
    | _, _ => false
  end.

Fixpoint lt (n1 n2 : nat) : bool :=
  match n1, n2 with
    | O, S _ => true
    | S n1', S n2' => lt n1' n2'
    | _, _ => false
  end.

(** Now we can interpret binary operators: *)

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b in (tbinop arg1 arg2 res)
    return (typeDenote arg1 -> typeDenote arg2 -> typeDenote res) with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => eq_nat
    | TEq Bool => eq_bool
    | TLt => lt
  end.

(** This function has just a few differences from the denotation functions we saw earlier.  First, [tbinop] is an indexed type, so its indices become additional arguments to [tbinopDenote].  Second, we need to perform a genuine %\textit{%#<i>#dependent pattern match#</i>#%}% to come up with a definition of this function that type-checks.  In each branch of the [match], we need to use branch-specific information about the indices to [tbinop].  General type inference that takes such information into account is undecidable, so it is often necessary to write annotations, like we see above on the line with [match].

The [in] annotation restates the type of the term being case-analyzed.  Though we use the same names for the indices as we use in the type of the original argument binder, these are actually fresh variables, and they are %\textit{%#<i>#binding occurrences#</i>#%}%.  Their scope is the [return] clause.  That is, [arg1], [arg2], and [res] are new bound variables bound only within the return clause [typeDenote arg1 -> typeDenote arg2 -> typeDenote res].  By being explicit about the functional relationship between the type indices and the match result, we regain decidable type inference.

In fact, recent Coq versions use some heuristics that can save us the trouble of writing [match] annotations, and those heuristics get the job done in this case.  We can get away with writing just: *)

(* begin hide *)
Reset tbinopDenote.
(* end hide *)
Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => eq_nat
    | TEq Bool => eq_bool
    | TLt => lt
  end.

(**
The same tricks suffice to define an expression denotation function in an unsurprising way:
*)

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

(** We can evaluate a few example programs to convince ourselves that this semantics is correct. *)

Eval simpl in texpDenote (TNConst 42).
(** [= 42 : typeDenote Nat] *)

Eval simpl in texpDenote (TBConst true).
(** [= true : typeDenote Bool] *)

Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
(** [= 28 : typeDenote Nat] *)

Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
(** [= false : typeDenote Bool] *)

Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
(** [= true : typeDenote Bool] *)


(** ** Target Language *)

(** Now we want to define a suitable stack machine target for compilation.  In the example of the untyped language, stack machine programs could encounter stack underflows and "get stuck."  This was unfortunate, since we had to deal with this complication even though we proved that our compiler never produced underflowing programs.  We could have used dependent types to force all stack machine programs to be underflow-free.

For our new languages, besides underflow, we also have the problem of stack slots with naturals instead of bools or vice versa.  This time, we will use indexed typed families to avoid the need to reason about potential failures.

We start by defining stack types, which classify sets of possible stacks. *)

Definition tstack := list type.

(** Any stack classified by a [tstack] must have exactly as many elements, and each stack element must have the type found in the same position of the stack type.

We can define instructions in terms of stack types, where every instruction's type tells us what initial stack type it expects and what final stack type it will produce. *)

Inductive tinstr : tstack -> tstack -> Set :=
| TINConst : forall s, nat -> tinstr s (Nat :: s)
| TIBConst : forall s, bool -> tinstr s (Bool :: s)
| TIBinop : forall arg1 arg2 res s,
  tbinop arg1 arg2 res
  -> tinstr (arg1 :: arg2 :: s) (res :: s).

(** Stack machine programs must be a similar inductive family, since, if we again used the [list] type family, we would not be able to guarantee that intermediate stack types match within a program. *)

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

(** Now, to define the semantics of our new target language, we need a representation for stacks at runtime.  We will again take advantage of type information to define types of value stacks that, by construction, contain the right number and types of elements. *)

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

(** This is another [Set]-valued function.  This time it is recursive, which is perfectly valid, since [Set] is not treated specially in determining which functions may be written.  We say that the value stack of an empty stack type is any value of type [unit], which has just a single value, [tt].  A nonempty stack type leads to a value stack that is a pair, whose first element has the proper type and whose second element follows the representation for the remainder of the stack type.  We write [%type] so that Coq knows to interpret [*] as Cartesian product rather than multiplication.

This idea of programming with types can take a while to internalize, but it enables a very simple definition of instruction denotation.  Our definition is like what you might expect from a Lisp-like version of ML that ignored type information.  Nonetheless, the fact that [tinstrDenote] passes the type-checker guarantees that our stack machine programs can never go wrong. *)

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TINConst _ n => fun s => (n, s)
    | TIBConst _ b => fun s => (b, s)
    | TIBinop _ _ _ _ b => fun s =>
      match s with
        (arg1, (arg2, s')) => ((tbinopDenote b) arg1 arg2, s')
      end
  end.

(** Why do we choose to use an anonymous function to bind the initial stack in every case of the [match]?  Consider this well-intentioned but invalid alternative version:

[[
Definition tinstrDenote ts ts' (i : tinstr ts ts') (s : vstack ts) : vstack ts' :=
  match i with
    | TINConst _ n => (n, s)
    | TIBConst _ b => (b, s)
    | TIBinop _ _ _ _ b =>
      match s with
        (arg1, (arg2, s')) => ((tbinopDenote b) arg1 arg2, s')
      end
  end.

]]

The Coq type-checker complains that:

[[
The term "(n, s)" has type "(nat * vstack ts)%type"
 while it is expected to have type "vstack ?119".

]]

The text [?119] stands for a unification variable.  We can try to help Coq figure out the value of this variable with an explicit annotation on our [match] expression.

[[
Definition tinstrDenote ts ts' (i : tinstr ts ts') (s : vstack ts) : vstack ts' :=
  match i in tinstr ts ts' return vstack ts' with
    | TINConst _ n => (n, s)
    | TIBConst _ b => (b, s)
    | TIBinop _ _ _ _ b =>
      match s with
        (arg1, (arg2, s')) => ((tbinopDenote b) arg1 arg2, s')
      end
  end.

]]

Now the error message changes.

[[
The term "(n, s)" has type "(nat * vstack ts)%type"
 while it is expected to have type "vstack (Nat :: t)".

]]

Recall from our earlier discussion of [match] annotations that we write the annotations to express to the type-checker the relationship between the type indices of the case object and the result type of the [match].  Coq chooses to assign to the wildcard [_] after [TINConst] the name [t], and the type error is telling us that the type checker cannot prove that [t] is the same as [ts].  By moving [s] out of the [match], we lose the ability to express, with [in] and [return] clauses, the relationship between the shared index [ts] of [s] and [i].

There %\textit{%#<i>#are#</i>#%}% reasonably general ways of getting around this problem without pushing binders inside [match]es.  However, the alternatives are significantly more involved, and the technique we use here is almost certainly the best choice, whenever it applies.

*)

(** We finish the semantics with a straightforward definition of program denotation. *)

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.


(** ** Translation *)

(** To define our compilation, it is useful to have an auxiliary function for concatenating two stack machine programs. *)

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

(** With that function in place, the compilation is defined very similarly to how it was before, modulo the use of dependent typing. *)

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TINConst _ n) (TNil _)
    | TBConst b => TCons (TIBConst _ b) (TNil _)
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
      (tconcat (tcompile e1 _) (TCons (TIBinop _ b) (TNil _)))
  end.

(** One interesting feature of the definition is the underscores appearing to the right of [=>] arrows.  Haskell and ML programmers are quite familiar with compilers that infer type parameters to polymorphic values.  In Coq, it is possible to go even further and ask the system to infer arbitrary terms, by writing underscores in place of specific values.  You may have noticed that we have been calling functions without specifying all of their arguments.  For instance, the recursive calls here to [tcompile] omit the [t] argument.  Coq's %\textit{%#<i>#implicit argument#</i>#%}% mechanism automatically inserts underscores for arguments that it will probably be able to infer.  Inference of such values is far from complete, though; generally, it only works in cases similar to those encountered with polymorphic type instantiation in Haskell and ML.

The underscores here are being filled in with stack types.  That is, the Coq type inferencer is, in a sense, inferring something about the flow of control in the translated programs.  We can take a look at exactly which values are filled in: *)

Print tcompile.
(** [[
tcompile = 
fix tcompile (t : type) (e : texp t) (ts : tstack) {struct e} :
  tprog ts (t :: ts) :=
  match e in (texp t0) return (tprog ts (t0 :: ts)) with
  | TNConst n => TCons (TINConst ts n) (TNil (Nat :: ts))
  | TBConst b => TCons (TIBConst ts b) (TNil (Bool :: ts))
  | TBinop arg1 arg2 res b e1 e2 =>
      tconcat (tcompile arg2 e2 ts)
        (tconcat (tcompile arg1 e1 (arg2 :: ts))
           (TCons (TIBinop ts b) (TNil (res :: ts))))
  end
     : forall t : type, texp t -> forall ts : tstack, tprog ts (t :: ts)
]] *)


(** We can check that the compiler generates programs that behave appropriately on our sample programs from above: *)

Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.
(** [= (42, tt) : vstack (Nat :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.
(** [= (true, tt) : vstack (Bool :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) nil) tt.
(** [= (28, tt) : vstack (Nat :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) nil) tt.
(** [= (false, tt) : vstack (Bool :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) nil) tt.
(** [= (true, tt) : vstack (Bool :: nil)] *)


(** ** Translation Correctness *)

(** We can state a correctness theorem similar to the last one. *)

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
(* begin hide *)
Abort.
(* end hide *)
(* begin thide *)

(** Again, we need to strengthen the theorem statement so that the induction will go through.  This time, I will develop an alternative approach to this kind of proof, stating the key lemma as: *)

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).

(** While lemma [compile_correct'] quantified over a program that is the "continuation" for the expression we are considering, here we avoid drawing in any extra syntactic elements.  In addition to the source expression and its type, we also quantify over an initial stack type and a stack compatible with it.  Running the compilation of the program starting from that stack, we should arrive at a stack that differs only in having the program's denotation pushed onto it.

   Let us try to prove this theorem in the same way that we settled on in the last section. *)

  induction e; crush.

(** We are left with this unproved conclusion:

[[
tprogDenote
     (tconcat (tcompile e2 ts)
        (tconcat (tcompile e1 (arg2 :: ts))
           (TCons (TIBinop ts t) (TNil (res :: ts))))) s =
   (tbinopDenote t (texpDenote e1) (texpDenote e2), s)
 
]]

We need an analogue to the [app_ass] theorem that we used to rewrite the goal in the last section.  We can abort this proof and prove such a lemma about [tconcat].
*)

Abort.

Lemma tconcat_correct : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'')
  (s : vstack ts),
  tprogDenote (tconcat p p') s
  = tprogDenote p' (tprogDenote p s).
  induction p; crush.
Qed.

(** This one goes through completely automatically.

Some code behind the scenes registers [app_ass] for use by [crush].  We must register [tconcat_correct] similarly to get the same effect: *)

Hint Rewrite tconcat_correct : cpdt.

(** We ask that the lemma be used for left-to-right rewriting, and we ask for the hint to be added to the hint database called [cpdt], which is the database used by [crush].  Now we are ready to return to [tcompile_correct'], proving it automatically this time. *)

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
  induction e; crush.
Qed.

(** We can register this main lemma as another hint, allowing us to prove the final theorem trivially. *)

Hint Rewrite tcompile_correct' : cpdt.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.
(* end thide *)
