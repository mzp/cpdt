(* Copyright (c) 2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Proving in the Large}% *)

(** It is somewhat unfortunate that the term "theorem-proving" looks so much like the word "theory."  Most researchers and practitioners in software assume that mechanized theorem-proving is profoundly impractical.  Indeed, until recently, most advances in theorem-proving for higher-order logics have been largely theoretical.  However, starting around the beginning of the 21st century, there was a surge in the use of proof assistants in serious verification efforts.  That line of work is still quite new, but I believe it is not too soon to distill some lessons on how to work effectively with large formal proofs.

   Thus, this chapter gives some tips for structuring and maintaining large Coq developments. *)


(** * Ltac Anti-Patterns *)

(** In this book, I have been following an unusual style, where proofs are not considered finished until they are "fully automated," in a certain sense.  SEach such theorem is proved by a single tactic.  Since Ltac is a Turing-complete programming language, it is not hard to squeeze arbitrary heuristics into single tactics, using operators like the semicolon to combine steps.  In contrast, most Ltac proofs "in the wild" consist of many steps, performed by individual tactics followed by periods.  Is it really worth drawing a distinction between proof steps terminated by semicolons and steps terminated by periods?

   I argue that this is, in fact, a very important distinction, with serious consequences for a majority of important verification domains.  The more uninteresting drudge work a proof domain involves, the more important it is to work to prove theorems with single tactics.  From an automation standpoint, single-tactic proofs can be extremely effective, and automation becomes more and more critical as proofs are populated by more uninteresting detail.  In this section, I will give some examples of the consequences of more common proof styles.

   As a running example, consider a basic language of arithmetic expressions, an interpreter for it, and a transformation that scales up every constant in an expression. *)

Inductive exp : Set :=
| Const : nat -> exp
| Plus : exp -> exp -> exp.

Fixpoint eval (e : exp) : nat :=
  match e with
    | Const n => n
    | Plus e1 e2 => eval e1 + eval e2
  end.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
  end.

(** We can write a very manual proof that [double] really doubles an expression's value. *)

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e.

  trivial.

  simpl.
  rewrite IHe1.
  rewrite IHe2.
  rewrite mult_plus_distr_l.
  trivial.
Qed.

(** We use spaces to separate the two inductive cases.  The second case mentions automatically-generated hypothesis names explicitly.  As a result, innocuous changes to the theorem statement can invalidate the proof. *)

Reset eval_times.

Theorem eval_double : forall k x,
  eval (times k x) = k * eval x.
  induction x.

  trivial.

  simpl.
(** [[
  rewrite IHe1.

Error: The reference IHe1 was not found in the current environment.
 
  ]]

  The inductive hypotheses are named [IHx1] and [IHx2] now, not [IHe1] and [IHe2]. *)

Abort.

(** We might decide to use a more explicit invocation of [induction] to give explicit binders for all of the names that we will reference later in the proof. *)

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 ].

  trivial.

  simpl.
  rewrite IHe1.
  rewrite IHe2.
  rewrite mult_plus_distr_l.
  trivial.
Qed.

(** We pass [induction] an %\textit{%#<i>#intro pattern#</i>#%}%, using a [|] character to separate out instructions for the different inductive cases.  Within a case, we write [?] to ask Coq to generate a name automatically, and we write an explicit name to assign that name to the corresponding new variable.  It is apparent that, to use intro patterns to avoid proof brittleness, one needs to keep track of the seemingly unimportant facts of the orders in which variables are introduced.  Thus, the script keeps working if we replace [e] by [x], but it has become more cluttered.  Arguably, neither proof is particularly easy to follow.

   That category of complaint has to do with understanding proofs as static artifacts.  As with programming in general, with serious projects, it tends to be much more important to be able to support evolution of proofs as specifications change.  Unstructured proofs like the above examples can be very hard to update in concert with theorem statements.  For instance, consider how the last proof script plays out when we modify [times] to introduce a bug. *)

Reset times.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (1 + k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
  end.

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 ].

  trivial.

  simpl.
(** [[
  rewrite IHe1.

Error: The reference IHe1 was not found in the current environment.
 
  ]] *)

Abort.

(** Can you spot what went wrong, without stepping through the script step-by-step?  The problem is that [trivial] never fails.  Originally, [trivial] had been succeeding in proving an equality that follows by reflexivity.  Our change to [times] leads to a case where that equality is no longer true.  [trivial] happily leaves the false equality in place, and we continue on to the span of tactics intended for the second inductive case.  Unfortunately, those tactics end up being applied to the %\textit{%#<i>#first#</i>#%}% case instead.

   The problem with [trivial] could be "solved" by writing [solve [trivial]] instead, so that an error is signaled early on if something unexpected happens.  However, the root problem is that the syntax of a tactic invocation does not imply how many subgoals it produces.  Much more confusing instances of this problem are possible.  For example, if a lemma [L] is modified to take an extra hypothesis, then uses of [apply L] will general more subgoals than before.  Old unstructured proof scripts will become hopelessly jumbled, with tactics applied to inappropriate subgoals.  Because of the lack of structure, there is usually relatively little to be gleaned from knowledge of the precise point in a proof script where an error is raised. *)

Reset times.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
  end.

(** Many real developments try to make essentially unstructured proofs look structured by applying careful indentation conventions, idempotent case-marker tactics included soley to serve as documentation, and so on.  All of these strategies suffer from the same kind of failure of abstraction that was just demonstrated.  I like to say that if you find yourself caring about indentation in a proof script, it is a sign that the script is structured poorly.

   We can rewrite the current proof with a single tactic. *)

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 ]; [
    trivial
    | simpl; rewrite IHe1; rewrite IHe2; rewrite mult_plus_distr_l; trivial ].
Qed.

(** This is an improvement in robustness of the script.  We no longer need to worry about tactics from one case being applied to a different case.  Still, the proof script is not especially readable.  Probably most readers would not find it helpful in explaining why the theorem is true.

   The situation gets worse in considering extensions to the theorem we want to prove.  Let us add multiplication nodes to our [exp] type and see how the proof fares. *)

Reset exp.

Inductive exp : Set :=
| Const : nat -> exp
| Plus : exp -> exp -> exp
| Mult : exp -> exp -> exp.

Fixpoint eval (e : exp) : nat :=
  match e with
    | Const n => n
    | Plus e1 e2 => eval e1 + eval e2
    | Mult e1 e2 => eval e1 * eval e2
  end.

Fixpoint times (k : nat) (e : exp) : exp :=
  match e with
    | Const n => Const (k * n)
    | Plus e1 e2 => Plus (times k e1) (times k e2)
    | Mult e1 e2 => Mult (times k e1) e2
  end.

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
(** [[
  induction e as [ | ? IHe1 ? IHe2 ]; [
    trivial
    | simpl; rewrite IHe1; rewrite IHe2; rewrite mult_plus_distr_l; trivial ].

Error: Expects a disjunctive pattern with 3 branches.

  ]] *)

Abort.

(** Unsurprisingly, the old proof fails, because it explicitly says that there are two inductive cases.  To update the script, we must, at a minimum, remember the order in which the inductive cases are generated, so that we can insert the new case in the appropriate place.  Even then, it will be painful to add the case, because we cannot walk through proof steps interactively when they occur inside an explicit set of cases. *)

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e as [ | ? IHe1 ? IHe2 | ? IHe1 ? IHe2 ]; [
    trivial
    | simpl; rewrite IHe1; rewrite IHe2; rewrite mult_plus_distr_l; trivial
    | simpl; rewrite IHe1; rewrite mult_assoc; trivial ].
Qed.

(** Now we are in a position to see how much nicer is the style of proof that we have followed in most of this book. *)

Reset eval_times.

Hint Rewrite mult_plus_distr_l : cpdt.

Theorem eval_times : forall k e,
  eval (times k e) = k * eval e.
  induction e; crush.
Qed.

(** This style is motivated by a hard truth: one person's manual proof script is almost always mostly inscrutable to most everyone else.  I claim that step-by-step formal proofs are a poor way of conveying information.  Thus, we had might as well cut out the steps and automate as much as possible.

   What about the illustrative value of proofs?  Most informal proofs are read to convey the big ideas of proofs.  How can reading [induction e; crush] convey any big ideas?  My position is that any ideas that standard automation can find are not very big after all, and the %\textit{%#<i>#real#</i>#%}% big ideas should be expressed through lemmas that are added as hints.

   An example should help illustrate what I mean.  Consider this function, which rewrites an expression using associativity of addition and multiplication. *)

Fixpoint reassoc (e : exp) : exp :=
  match e with
    | Const _ => e
    | Plus e1 e2 =>
      let e1' := reassoc e1 in
      let e2' := reassoc e2 in
        match e2' with
          | Plus e21 e22 => Plus (Plus e1' e21) e22
          | _ => Plus e1' e2'
        end
    | Mult e1 e2 =>
      let e1' := reassoc e1 in
      let e2' := reassoc e2 in
        match e2' with
          | Mult e21 e22 => Mult (Mult e1' e21) e22
          | _ => Mult e1' e2'
        end
  end.

Theorem reassoc_correct : forall e, eval (reassoc e) = eval e.
  induction e; crush;
    match goal with
      | [ |- context[match ?E with Const _ => _ | Plus _ _ => _ | Mult _ _ => _ end] ] =>
        destruct E; crush
    end.

  (** One subgoal remains:
     [[
  IHe2 : eval e3 * eval e4 = eval e2
  ============================
   eval e1 * eval e3 * eval e4 = eval e1 * eval e2
 
   ]]

   [crush] does not know how to finish this goal.  We could finish the proof manually. *)

  rewrite <- IHe2; crush.

  (** However, the proof would be easier to understand and maintain if we separated this insight into a separate lemma. *)

Abort.

Lemma rewr : forall a b c d, b * c = d -> a * b * c = a * d.
  crush.
Qed.

Hint Resolve rewr.

Theorem reassoc_correct : forall e, eval (reassoc e) = eval e.
  induction e; crush;
    match goal with
      | [ |- context[match ?E with Const _ => _ | Plus _ _ => _ | Mult _ _ => _ end] ] =>
        destruct E; crush
    end.
Qed.

(** In the limit, a complicated inductive proof might rely on one hint for each inductive case.  The lemma for each hint could restate the associated case.  Compared to manual proof scripts, we arrive at more readable results.  Scripts no longer need to depend on the order in which cases are generated.  The lemmas are easier to digest separately than are fragments of tactic code, since lemma statements include complete proof contexts.  Such contexts can only be extracted from monolithic manual proofs by stepping through scripts interactively.

   The more common situation is that a large induction has several easy cases that automation makes short work of.  In the remaining cases, automation performs some standard simplification.  Among these cases, some may require quite involved proofs; such a case may deserve a hint lemma of its own, where the lemma statement may copy the simplified version of the case.  Alternatively, the proof script for the main theorem may be extended with some automation code targeted at the specific case.  Even such targeted scripting is more desirable than manual proving, because it may be read and understood without knowledge of a proof's hierarchical structure, case ordering, or name binding structure. *)


(** * Debugging and Maintaining Automation *)

(** Fully-automated proofs are desirable because they open up possibilities for automatic adaptation to changes of specification.  A well-engineered script within a narrow domain can survive many changes to the formulation of the problem it solves.  Still, as we are working with higher-order logic, most theorems fall within no obvious decidable theories.  It is inevitable that most long-lived automated proofs will need updating.

   Before we are ready to update our proofs, we need to write them in the first place.  While fully-automated scripts are most robust to changes of specification, it is hard to write every new proof directly in that form.  Instead, it is useful to begin a theorem with exploratory proving and then gradually refine it into a suitable automated form.

   Consider this theorem from Chapter 7, which we begin by proving in a mostly manual way, invoking [crush] after each steop to discharge any low-hanging fruit.  Our manual effort involves choosing which expressions to case-analyze on. *)

(* begin hide *)
Require Import MoreDep.
(* end hide *)

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
  induction e; crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (cfold e2); crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (cfold e2); crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (cfold e2); crush.

  dep_destruct (cfold e1); crush.
  dep_destruct (expDenote e1); crush.

  dep_destruct (cfold e); crush.

  dep_destruct (cfold e); crush.
Qed.

(** In this complete proof, it is hard to avoid noticing a pattern.  We rework the proof, abstracting over the patterns we find. *)

Reset cfold_correct.

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
  induction e; crush.

  (** The expression we want to destruct here turns out to be the discriminee of a [match], and we can easily enough write a tactic that destructs all such expressions. *)

  Ltac t :=
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | Plus _ _ => _
                               | Eq _ _ => _ | BConst _ => _ | And _ _ => _
                               | If _ _ _ _ => _ | Pair _ _ _ _ => _
                               | Fst _ _ _ => _ | Snd _ _ _ => _ end] ] =>
                dep_destruct E
            end; crush).

  t.

  (** This tactic invocation discharges the whole case.  It does the same on the next two cases, but it gets stuck on the fourth case. *)

  t.

  t.

  t.

  (** The subgoal's conclusion is:
     [[
    ============================
   (if expDenote e1 then expDenote (cfold e2) else expDenote (cfold e3)) =
   expDenote (if expDenote e1 then cfold e2 else cfold e3)
 
   ]]

   We need to expand our [t] tactic to handle this case. *)

  Ltac t' :=
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | Plus _ _ => _
                               | Eq _ _ => _ | BConst _ => _ | And _ _ => _
                               | If _ _ _ _ => _ | Pair _ _ _ _ => _
                               | Fst _ _ _ => _ | Snd _ _ _ => _ end] ] =>
                dep_destruct E
              | [ |- (if ?E then _ else _) = _ ] => destruct E
            end; crush).

  t'.

  (** Now the goal is discharged, but [t'] has no effect on the next subgoal. *)

  t'.

  (** A final revision of [t] finishes the proof. *)

  Ltac t'' :=
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | Plus _ _ => _
                               | Eq _ _ => _ | BConst _ => _ | And _ _ => _
                               | If _ _ _ _ => _ | Pair _ _ _ _ => _
                               | Fst _ _ _ => _ | Snd _ _ _ => _ end] ] =>
                dep_destruct E
              | [ |- (if ?E then _ else _) = _ ] => destruct E
              | [ |- context[match pairOut ?E with Some _ => _
                               | None => _ end] ] =>
                dep_destruct E
            end; crush).

  t''.

  t''.
Qed.

(** We can take the final tactic and move it into the initial part of the proof script, arriving at a nicely-automated proof. *)

Reset t.

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
  induction e; crush;
    repeat (match goal with
              | [ |- context[match ?E with NConst _ => _ | Plus _ _ => _
                               | Eq _ _ => _ | BConst _ => _ | And _ _ => _
                               | If _ _ _ _ => _ | Pair _ _ _ _ => _
                               | Fst _ _ _ => _ | Snd _ _ _ => _ end] ] =>
                dep_destruct E
              | [ |- (if ?E then _ else _) = _ ] => destruct E
              | [ |- context[match pairOut ?E with Some _ => _
                               | None => _ end] ] =>
                dep_destruct E
            end; crush).
Qed.

(** Even after we put together nice automated proofs, we must deal with specification changes that can invalidate them.  It is not generally possible to step through single-tactic proofs interactively.  There is a command [Debug On] that lets us step through points in tactic execution, but the debugger tends to make counterintuitive choices of which points we would like to stop at, and per-point output is quite verbose, so most Coq users do not find this debugging mode very helpful.  How are we to understand what has broken in a script that used to work?

   An example helps demonstrate a useful approach.  Consider what would have happened in our proof of [reassoc_correct] if we had first added an unfortunate rewriting hint. *)

Reset reassoc_correct.

Theorem confounder : forall e1 e2 e3,
  eval e1 * eval e2 * eval e3 = eval e1 * (eval e2 + 1 - 1) * eval e3.
  crush.
Qed.

Hint Rewrite confounder : cpdt.

Theorem reassoc_correct : forall e, eval (reassoc e) = eval e.
  induction e; crush;
    match goal with
      | [ |- context[match ?E with Const _ => _ | Plus _ _ => _ | Mult _ _ => _ end] ] =>
        destruct E; crush
    end.

  (** One subgoal remains:
     
     [[
  ============================
   eval e1 * (eval e3 + 1 - 1) * eval e4 = eval e1 * eval e2
 
   ]]

   The poorly-chosen rewrite rule fired, changing the goal to a form where another hint no longer applies.  Imagine that we are in the middle of a large development with many hints.  How would we diagnose the problem?  First, we might not be sure which case of the inductive proof has gone wrong.  It is useful to separate out our automation procedure and apply it manually. *)

  Restart.

  Ltac t := crush; match goal with
                     | [ |- context[match ?E with Const _ => _ | Plus _ _ => _
                                      | Mult _ _ => _ end] ] =>
                       destruct E; crush
                   end.

  induction e.

  (** Since we see the subgoals before any simplification occurs, it is clear that this is the case for constants.  [t] makes short work of it. *)
  
  t.

  (** The next subgoal, for addition, is also discharged without trouble. *)

  t.

  (** The final subgoal is for multiplication, and it is here that we get stuck in the proof state summarized above. *)

  t.

  (** What is [t] doing to get us to this point?  The [info] command can help us answer this kind of question. *)

  (** remove printing * *)
  Undo.
  info t.
  (** [[
 == simpl in *; intuition; subst; autorewrite with cpdt in *; 
    simpl in *; intuition; subst; autorewrite with cpdt in *; 
    simpl in *; intuition; subst; destruct (reassoc e2).
    simpl in *; intuition.
    
    simpl in *; intuition.
    
    simpl in *; intuition; subst; autorewrite with cpdt in *;
       refine (eq_ind_r
                 (fun n : nat =>
                  n * (eval e3 + 1 - 1) * eval e4 = eval e1 * eval e2) _ IHe1);
       autorewrite with cpdt in *; simpl in *; intuition; 
    subst; autorewrite with cpdt in *; simpl in *; 
    intuition; subst.
 
    ]]

    A detailed trace of [t]'s execution appears.  Since we are using the very general [crush] tactic, many of these steps have no effect and only occur as instances of a more general strategy.  We can copy-and-paste the details to see where things go wrong. *)

  Undo.

  (** We arbitrarily split the script into chunks.  The first few seem not to do any harm. *)

  simpl in *; intuition; subst; autorewrite with cpdt in *.
  simpl in *; intuition; subst; autorewrite with cpdt in *.
  simpl in *; intuition; subst; destruct (reassoc e2).
  simpl in *; intuition.
  simpl in *; intuition.

  (** The next step is revealed as the culprit, bringing us to the final unproved subgoal. *)

  simpl in *; intuition; subst; autorewrite with cpdt in *.

  (** We can split the steps further to assign blame. *)

  Undo.

  simpl in *.
  intuition.
  subst.
  autorewrite with cpdt in *.

  (** It was the final of these four tactics that made the rewrite.  We can find out exactly what happened.  The [info] command presents hierarchical views of proof steps, and we can zoom down to a lower level of detail by applying [info] to one of the steps that appeared in the original trace. *)

  Undo.

  info autorewrite with cpdt in *.
  (** [[
 == refine (eq_ind_r (fun n : nat => n = eval e1 * eval e2) _
              (confounder (reassoc e1) e3 e4)).
 
      ]]

      The way a rewrite is displayed is somewhat baroque, but we can see that theorem [confounder] is the final culprit.  At this point, we could remove that hint, prove an alternate version of the key lemma [rewr], or come up with some other remedy.  Fixing this kind of problem tends to be relatively easy once the problem is revealed. *)

Abort.

(** printing * $\times$ *)

(** Sometimes a change to a development has undesirable performance consequences, even if it does not prevent any old proof scripts from completing.  If the performance consequences are severe enough, the proof scripts can be considered broken for practical purposes.

   Here is one example of a performance surprise. *)

Section slow.
  Hint Resolve trans_eq.

  (** The central element of the problem is the addition of transitivity as a hint.  With transitivity available, it is easy for proof search to wind up exploring exponential search spaces.  We also add a few other arbitrary variables and hypotheses, designed to lead to trouble later. *)

  Variable A : Set.
  Variables P Q R S : A -> A -> Prop.
  Variable f : A -> A.

  Hypothesis H1 : forall x y, P x y -> Q x y -> R x y -> f x = f y.
  Hypothesis H2 : forall x y, S x y -> R x y.

  (** We prove a simple lemma very quickly, using the [Time] command to measure exactly how quickly. *)

  Lemma slow : forall x y, P x y -> Q x y -> S x y -> f x = f y.
    Time eauto 6.
    (** [[
Finished transaction in 0. secs (0.068004u,0.s)
]] *)

  Qed.

  (** Now we add a different hypothesis, which is innocent enough; in fact, it is even provable as a theorem. *)

  Hypothesis H3 : forall x y, x = y -> f x = f y.

  Lemma slow' : forall x y, P x y -> Q x y -> S x y -> f x = f y.
    Time eauto 6.
    (** [[
Finished transaction in 2. secs (1.264079u,0.s)
 
      ]]

      Why has the search time gone up so much?  The [info] command is not much help, since it only shows the result of search, not all of the paths that turned out to be worthless. *)

    Restart.
    info eauto 6.
    (** [[
 == intro x; intro y; intro H; intro H0; intro H4;
       simple eapply trans_eq.
    simple apply refl_equal.
    
    simple eapply trans_eq.
    simple apply refl_equal.
    
    simple eapply trans_eq.
    simple apply refl_equal.
    
    simple apply H1.
    eexact H.
    
    eexact H0.
    
    simple apply H2; eexact H4.
 
    ]]

    This output does not tell us why proof search takes so long, but it does provide a clue that would be useful if we had forgotten that we added transitivity as a hint.  The [eauto] tactic is applying depth-first search, and the proof script where the real action is ends up buried inside a chain of pointless invocations of transitivity, where each invocation uses reflexivity to discharge one subgoal.  Each increment to the depth argument to [eauto] adds another silly use of transitivity.  This wasted proof effort only adds linear time overhead, as long as proof search never makes false steps.  No false steps were made before we added the new hypothesis, but somehow the addition made possible a new faulty path.  To understand which paths we enabled, we can use the [debug] command. *)

    Restart.
    debug eauto 6.

    (** The output is a large proof tree.  The beginning of the tree is enough to reveal what is happening:

       [[
1 depth=6 
1.1 depth=6 intro
1.1.1 depth=6 intro
1.1.1.1 depth=6 intro
1.1.1.1.1 depth=6 intro
1.1.1.1.1.1 depth=6 intro
1.1.1.1.1.1.1 depth=5 apply H3
1.1.1.1.1.1.1.1 depth=4 eapply trans_eq
1.1.1.1.1.1.1.1.1 depth=4 apply refl_equal
1.1.1.1.1.1.1.1.1.1 depth=3 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1 depth=3 apply refl_equal
1.1.1.1.1.1.1.1.1.1.1.1 depth=2 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1 depth=2 apply refl_equal
1.1.1.1.1.1.1.1.1.1.1.1.1.1 depth=1 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 depth=1 apply refl_equal
1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 depth=1 apply sym_eq ; trivial
1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.1.1.3 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2 depth=2 apply sym_eq ; trivial
1.1.1.1.1.1.1.1.1.1.1.1.2.1 depth=1 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2.1.1 depth=1 apply refl_equal
1.1.1.1.1.1.1.1.1.1.1.1.2.1.1.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2.1.2 depth=1 apply sym_eq ; trivial
1.1.1.1.1.1.1.1.1.1.1.1.2.1.2.1 depth=0 eapply trans_eq
1.1.1.1.1.1.1.1.1.1.1.1.2.1.3 depth=0 eapply trans_eq
 
       ]]

       The first choice [eauto] makes is to apply [H3], since [H3] has the fewest hypotheses of all of the hypotheses and hints that match.  However, it turns out that the single hypothesis generated is unprovable.  That does not stop [eauto] from trying to prove it with an exponentially-sized tree of applications of transitivity, reflexivity, and symmetry of equality.  It is the children of the initial [apply H3] that account for all of the noticeable time in proof execution.  In a more realistic development, we might use this output of [info] to realize that adding transitivity as a hint was a bad idea. *)

  Qed.
End slow.

(** It is also easy to end up with a proof script that uses too much memory.  As tactics run, they avoid generating proof terms, since serious proof search will consider many possible avenues, and we do not want to built proof terms for subproofs that end up unused.  Instead, tactic execution maintains %\textit{%#<i>#thunks#</i>#%}% (suspended computations, represented with closures), such that a tactic's proof-producing thunk is only executed when we run [Qed].  These thunks can use up large amounts of space, such that a proof script exhausts available memory, even when we know that we could have used much less memory by forcing some thunks earlier.

   The [abstract] tactical helps us force thunks by proving some subgoals as their own lemmas.  For instance, a proof [induction x; crush] can in many cases be made to use significantly less peak memory by changing it to [induction x; abstract crush].  The main limitation of [abstract] is that it can only be applied to subgoals that are proved completely, with no undetermined unification variables remaining.  Still, many large automated proofs can realize vast memory savings via [abstract]. *)


(** * Modules *)

(** Last chapter's examples of proof by reflection demonstrate opportunities for implementing abstract proof strategies with stronger formal guarantees than can be had with Ltac scripting.  Coq's %\textit{%#<i>#module system#</i>#%}% provides another tool for more rigorous development of generic theorems.  This feature is inspired by the module systems found in Standard ML and Objective Caml, and the discussion that follows assumes familiarity with the basics of one of those systems.

   ML modules facilitate the grouping of abstract types with operations over those types.  Moreover, there is support for %\textit{%#<i>#functors#</i>#%}%, which are functions from modules to modules.  A canonical example of a functor is one that builds a data structure implementation from a module that describes a domain of keys and its associated comparison operations.

   When we add modules to a base language with dependent types, it becomes possible to use modules and functors to formalize kinds of reasoning that are common in algebra.  For instance, this module signature captures the essence of the algebraic structure known as a group.  A group consists of a carrier set [G], an associative binary operation [f], a left identity element [e] for [f], and an operation [i] that is a left inverse for [f]. *)

Module Type GROUP.
  Parameter G : Set.
  Parameter f : G -> G -> G.
  Parameter e : G.
  Parameter i : G -> G.

  Axiom assoc : forall a b c, f (f a b) c = f a (f b c).
  Axiom ident : forall a, f e a = a.
  Axiom inverse : forall a, f (i a) a = e.
End GROUP.

(** Many useful theorems hold of arbitrary groups.  We capture some such theorem statements in another module signature. *)

Module Type GROUP_THEOREMS.
  Declare Module M : GROUP.

  Axiom ident' : forall a, M.f a M.e = a.

  Axiom inverse' : forall a, M.f a (M.i a) = M.e.

  Axiom unique_ident : forall e', (forall a, M.f e' a = a) -> e' = M.e.
End GROUP_THEOREMS.

(** We implement generic proofs of these theorems with a functor, whose input is an arbitrary group [M].  The proofs are completely manual, since it would take some effort to build suitable generic automation; rather, these theorems can serve as a basis for an automated procedure for simplifying group expressions, along the lines of the procedure for monoids from the last chapter.  We take the proofs from the Wikipedia page on elementary group theory. *)

Module Group (M : GROUP) : GROUP_THEOREMS with Module M := M.
  Module M := M.

  Import M.

  Theorem inverse' : forall a, f a (i a) = e.
    intro.
    rewrite <- (ident (f a (i a))).
    rewrite <- (inverse (f a (i a))) at 1.
    rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc (i a) a (i a)).
    rewrite inverse.
    rewrite ident.
    apply inverse.
  Qed.

  Theorem ident' : forall a, f a e = a.
    intro.
    rewrite <- (inverse a).
    rewrite <- assoc.
    rewrite inverse'.
    apply ident.
  Qed.

  Theorem unique_ident : forall e', (forall a, M.f e' a = a) -> e' = M.e.
    intros.
    rewrite <- (H e).
    symmetry.
    apply ident'.
  Qed.
End Group.

(** We can show that the integers with [+] form a group. *)

Require Import ZArith.
Open Scope Z_scope.

Module Int.
  Definition G := Z.
  Definition f x y := x + y.
  Definition e := 0.
  Definition i x := -x.

  Theorem assoc : forall a b c, f (f a b) c = f a (f b c).
    unfold f; crush.
  Qed.
  Theorem ident : forall a, f e a = a.
    unfold f, e; crush.
  Qed.
  Theorem inverse : forall a, f (i a) a = e.
    unfold f, i, e; crush.
  Qed.
End Int.

(** Next, we can produce integer-specific versions of the generic group theorems. *)

Module IntTheorems := Group(Int).

Check IntTheorems.unique_ident.
(** %\vspace{-.15in}% [[
  IntTheorems.unique_ident
     : forall e' : Int.G, (forall a : Int.G, Int.f e' a = a) -> e' = Int.e
     ]] *)

Theorem unique_ident : forall e', (forall a, e' + a = a) -> e' = 0.
  exact IntTheorems.unique_ident.
Qed.

(** As in ML, the module system provides an effective way to structure large developments.  Unlike in ML, Coq modules add no expressiveness; we can implement any module as an inhabitant of a dependent record type.  It is the second-class nature of modules that makes them easier to use than dependent records in many case.  Because modules may only be used in quite restricted ways, it is easier to support convenient module coding through special commands and editing modes, as the above example demonstrates.  An isomorphic implementation with records would have suffered from lack of such conveniences as module subtyping and importation of the fields of a module. *)


(** * Build Processes *)

(** As in software development, large Coq projects are much more manageable when split across multiple files and when decomposed into libraries.  Coq and Proof General provide very good support for these activities.

   Consider a library that we will name [Lib], housed in directory %\texttt{%#<tt>#LIB#</tt>#%}% and split between files %\texttt{%#<tt>#A.v#</tt>#%}%, %\texttt{%#<tt>#B.v#</tt>#%}%, and %\texttt{%#<tt>#C.v#</tt>#%}%.  A simple Makefile will compile the library, relying on the standard Coq tool %\texttt{%#<tt>#coq_makefile#</tt>#%}% to do the hard work.

<<
MODULES := A B C
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
        make -f Makefile.coq

Makefile.coq: Makefile $(VS)
        coq_makefile -R . Lib $(VS) -o Makefile.coq

clean:: Makefile.coq
        make -f Makefile.coq clean
        rm -f Makefile.coq
>>

   The Makefile begins by defining a variable %\texttt{%#<tt>#VS#</tt>#%}% holding the list of filenames to be included in the project.  The primary target is %\texttt{%#<tt>#coq#</tt>#%}%, which depends on the construction of an auxiliary Makefile called %\texttt{%#<tt>#Makefile.coq#</tt>#%}%.  Another rule explains how to build that file.  We call %\texttt{%#<tt>#coq_makefile#</tt>#%}%, using the %\texttt{%#<tt>#-R#</tt>#%}% flag to specify that files in the current directory should be considered to belong to the library [Lib].  This Makefile will build a compiled version of each module, such that %\texttt{%#<tt>#X.v#</tt>#%}% is compiled into %\texttt{%#<tt>#X.vo#</tt>#%}%.

   Now code in %\texttt{%#<tt>#B.v#</tt>#%}% may refer to definitions in %\texttt{%#<tt>#A.v#</tt>#%}% after running

   [[
Require Import Lib.A.

   ]]

   Library [Lib] is presented as a module, containing a submodule [A], which contains the definitions from %\texttt{%#<tt>#A.v#</tt>#%}%.  These are genuine modules in the sense of Coq's module system, and they may be passed to functors and so on.

   [Require Import] is a convenient combination of two more primitive commands.  [Require] finds the %\texttt{%#<tt>#.vo#</tt>#%}% file containing the named module, ensuring that the module is loaded into memory.  [Import] loads all top-level definitions of the named module into the current namespace, and it may be used with local modules that do not have corresponding %\texttt{%#<tt>#.vo#</tt>#%}% files.  Another command, [Load], is for inserting the contents of a named file verbatim.  It is generally better to use the module-based commands, since they avoid rerunning proof scripts, and they facilitate reorganization of directory structure without the need to change code.

   Now we would like to use our library from a different development, called [Client] and found in directory %\texttt{%#<tt>#CLIENT#</tt>#%}%, which has its own Makefile.

<<
MODULES := D E
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
        make -f Makefile.coq

Makefile.coq: Makefile $(VS)
        coq_makefile -R LIB Lib -R . Client $(VS) -o Makefile.coq

clean:: Makefile.coq
        make -f Makefile.coq clean
        rm -f Makefile.coq
>>

   We change the %\texttt{%#<tt>#coq_makefile#</tt>#%}% call to indicate where the library [Lib] is found.  Now %\texttt{%#<tt>#D.v#</tt>#%}% and %\texttt{%#<tt>#E.v#</tt>#%}% can refer to definitions from [Lib] module [A] after running

   [[
Require Import Lib.A.

   ]]

   and %\texttt{%#<tt>#E.v#</tt>#%}% can refer to definitions from %\texttt{%#<tt>#D.v#</tt>#%}% by running

   [[
Require Import Client.D.

   ]]

   It can be useful to split a library into several files, but it is also inconvenient for client code to import library modules individually.  We can get the best of both worlds by, for example, adding an extra source file %\texttt{%#<tt>#Lib.v#</tt>#%}% to [Lib]'s directory and Makefile.

   [[
Require Export Lib.A Lib.B Lib.C.

   ]]

   Now client code can import all definitions from all of [Lib]'s modules simply by running

   [[
Require Import Lib.

   ]]

   The two Makefiles above share a lot of code, so, in practice, it is useful to define a common Makefile that is included by multiple library-specific Makefiles.

   %\medskip%

   The remaining ingredient is the proper way of editing library code files in Proof General.  Recall this snippet of %\texttt{%#<tt>#.emacs#</tt>#%}% code from Chapter 2, which tells Proof General where to find the library associated with this book.

<<
(custom-set-variables
  ...
  '(coq-prog-args '("-I" "/path/to/cpdt/src"))
  ...
)
>>

   To do interactive editing of our current example, we just need to change the flags to point to the right places.

<<
(custom-set-variables
  ...
; '(coq-prog-args '("-I" "/path/to/cpdt/src"))
  '(coq-prog-args '("-R" "LIB" "Lib" "-R" "CLIENT" "Client"))
  ...
)
>>

   When working on multiple projects, it is useful to leave multiple versions of this setting in your %\texttt{%#<tt>#.emacs#</tt>#%}% file, commenting out all but one of them at any moment in time.  To switch between projects, change the commenting structure and restart Emacs. *)
