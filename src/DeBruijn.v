(* Copyright (c) 2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Set Implicit Arguments.

Require Import Eqdep.

Require Import DepList Tactics.
(* end hide *)

(** remove printing * *)
(** printing || $\mid\mid$ *)

(** %\chapter{Dependent De Bruijn Indices}% *)

(** The previous chapter introduced the most common form of de Bruijn indices, without essential use of dependent types.  In earlier chapters, we used dependent de Bruijn indices to illustrate tricks for working with dependent types.  This chapter presents one complete case study with dependent de Bruijn indices, focusing on producing the most maintainable proof possible of a classic theorem about lambda calculus.

   The proof that follows does not provide a complete guide to all kinds of formalization with de Bruijn indices.  Rather, it is intended as an example of some simple design patterns that can make proving standard theorems much easier.

   We will prove commutativity of capture-avoiding substitution for basic untyped lambda calculus:

   %$$x_1 \neq x_2 \Rightarrow [e_1/x_1][e_2/x_2]e = [e_2/x_2][[e_2/x_2]e_1/x_1]e$$%
   #<tt>x1 <> x2 => [e1/x1][e2/x2]e = [e2/x2][[e2/x2]e1/x1]e</tt>#
   *)

(** * Defining Syntax and Its Associated Operations *) 

(** Our definition of expression syntax should be unsurprising.  An expression of type [exp n] may refer to [n] different free variables. *)

Inductive exp : nat -> Type :=
| Var : forall n, fin n -> exp n
| App : forall n, exp n -> exp n -> exp n
| Abs : forall n, exp (S n) -> exp n.

(** The classic implementation of substitution in de Bruijn terms requires an auxiliary operation, %\emph{%lifting%}%, which increments the indices of all free variables in an expression.  We need to lift whenever we %``%#"#go under a binder.#"#%''%  It is useful to write an auxiliary function [liftVar] that lifts a variable; that is, [liftVar x y] will return [y + 1] if [y >= x], and it will return [y] otherwise.  This simple description uses numbers rather than our dependent [fin] family, so the actual specification is more involved.

   Combining a number of dependent types tricks, we wind up with this concrete realization. *)

Fixpoint liftVar n (x : fin n) : fin (pred n) -> fin n :=
  match x with
    | First _ => fun y => Next y
    | Next _ x' => fun y =>
      match y in fin n' return fin n' -> (fin (pred n') -> fin n')
        -> fin (S n') with
        | First _ => fun x' _ => First
        | Next _ y' => fun _ fx' => Next (fx' y')
      end x' (liftVar x')
  end.

(** Now it is easy to implement the main lifting operation. *)

Fixpoint lift n (e : exp n) : fin (S n) -> exp (S n) :=
  match e with
    | Var _ f' => fun f => Var (liftVar f f')
    | App _ e1 e2 => fun f => App (lift e1 f) (lift e2 f)
    | Abs _ e1 => fun f => Abs (lift e1 (Next f))
  end.

(** To define substitution itself, we will need to apply some explicit type casts, based on equalities between types.  A single equality will suffice for all of our casts.  Its statement is somewhat strange: it quantifies over a variable [f] of type [fin n], but then never mentions [f].  Rather, quantifying over [f] is useful because [fin] is a dependent type that is inhabited or not depending on its index.  The body of the theorem, [S (pred n) = n], is true only for [n] $> 0$, but we can prove it by contradiction when [n = 0], because we have around a value [f] of the uninhabited type [fin 0]. *)

Theorem nzf : forall n (f : fin n), S (pred n) = n.
  destruct 1; trivial.
Qed.

(** Now we define a notation to streamline our cast expressions.  The code [[f return n, r for e]] denotes a cast of expression [e] whose type can be obtained by substituting some number [n1] for [n] in [r].  [f] should be a proof that [n1 = n2], for any [n2].  In that case, the type of the cast expression is [r] with [n2] substituted for [n]. *)

Notation "[ f 'return' n , r 'for' e ]" :=
  match f in _ = n return r with
    | refl_equal => e
  end.

(** This notation is useful in defining a variable substitution operation.  The idea is that [substVar x y] returns [None] if [x = y]; otherwise, it returns a %``%#"#squished#"#%''% version of [y] with a smaller [fin] index, reflecting that variable [x] has been substituted away.  Without dependent types, this would be a simple definition.  With dependency, it is reasonably intricate, and our main task in automating proofs about it will be hiding that intricacy. *)

Fixpoint substVar n (x : fin n) : fin n -> option (fin (pred n)) :=
  match x with
    | First _ => fun y =>
      match y in fin n' return option (fin (pred n')) with
        | First _ => None
        | Next _ f' => Some f'
      end
    | Next _ x' => fun y =>
      match y in fin n'
        return fin (pred n') -> (fin (pred n') -> option (fin (pred (pred n'))))
          -> option (fin (pred n')) with
        | First _ => fun x' _ => Some [nzf x' return n, fin n for First]
        | Next _ y' => fun _ fx' =>
          match fx' y' with
            | None => None
            | Some f => Some [nzf y' return n, fin n for Next f]
          end
      end x' (substVar x')
  end.

(** It is now easy to define our final substitution function.  The abstraction case involves two casts, where one uses the [sym_eq] function to convert a proof of [n1 = n2] into a proof of [n2 = n1]. *)

Fixpoint subst n (e : exp n) : fin n -> exp (pred n) -> exp (pred n) :=
  match e with
    | Var _ f' => fun f v => match substVar f f' with
                               | None => v
                               | Some f'' => Var f''
                             end
    | App _ e1 e2 => fun f v => App (subst e1 f v) (subst e2 f v)
    | Abs _ e1 => fun f v => Abs [sym_eq (nzf f) return n, exp n for
      subst e1 (Next f) [nzf f return n, exp n for lift v First]]
  end.

(** Our final commutativity theorem is about [subst], but our proofs will rely on a few more auxiliary definitions.  First, we will want an operation [more] that increments the index of a [fin] while preserving its interpretation as a number. *)

Fixpoint more n (f : fin n) : fin (S n) :=
  match f with
    | First _ => First
    | Next _ f' => Next (more f')
  end.

(** Second, we will want a kind of inverse to [liftVar]. *)

Fixpoint unliftVar n (f : fin n) : fin (pred n) -> fin (pred n) :=
  match f with
    | First _ => fun g => [nzf g return n, fin n for First]
    | Next _ f' => fun g =>
      match g in fin n'
        return fin n' -> (fin (pred n') -> fin (pred n')) -> fin n' with
        | First _ => fun f' _ => f'
        | Next _ g' => fun _ unlift => Next (unlift g')
      end f' (unliftVar f')
  end.


(** * Custom Tactics *)

(* begin hide *)
Ltac simp := repeat progress (crush; try discriminate;
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => rewrite (UIP_refl _ _ pf)
           | [ _ : context[match ?pf with refl_equal => _ end] |- _ ] => rewrite (UIP_refl _ _ pf) in *

           | [ H : Next _ = Next _ |- _ ] => injection H; clear H
           | [ H : ?E = _, H' : ?E = _ |- _ ] => rewrite H in H'
           | [ H : ?P |- _ ] => rewrite H in *; [match P with
                                                   | forall x, _ => clear H
                                                   | _ => idtac
                                                 end]
         end).
(* end hide *)

(** Less than a page of tactic code will be sufficient to automate our proof of commuativity.  We start by defining a workhorse simplification tactic [simp], which extends [crush] in a few ways.

  [[
Ltac simp := repeat progress (crush; try discriminate;
 
  ]]

  We enter an inner loop of applying hints specific to our domain.

  [[
  repeat match goal with
 
  ]]

  Our first two hints find places where equality proofs are pattern-matched on.  The first hint matches pattern-matches in the conclusion, while the second hint matches pattern-matches in hypotheses.  In each case, we apply the library theorem [UIP_refl], which says that any proof of a fact like [e = e] is itself equal to [refl_equal].  Rewriting with this fact enables reduction of the pattern-match that we found.

  [[
           | [ |- context[match ?pf with refl_equal => _ end] ] =>
           rewrite (UIP_refl _ _ pf)
           | [ _ : context[match ?pf with refl_equal => _ end] |- _ ] =>
           rewrite (UIP_refl _ _ pf) in *
 
  ]]

  The next hint finds an opportunity to invert a [fin] equality hypothesis.

  [[
           | [ H : Next _ = Next _ |- _ ] => injection H; clear H
 
  ]]

  If we have two equality hypotheses that share a lefthand side, we can use one to rewrite the other, bringing the hypotheses' righthand sides together in a single equation.

  [[
           | [ H : ?E = _, H' : ?E = _ |- _ ] => rewrite H in H'
 
  ]]

  Finally, we would like automatic use of quantified equality hypotheses to perform rewriting.  We pattern-match a hypothesis [H] asserting proposition [P].  We try to use [H] to perform rewriting everywhere in our goal.  The rewrite succeeds if it generates no additional hypotheses, and, to prevent infinite loops in proof search, we clear [H] if it begins with universal quantification.

  [[
           | [ H : ?P |- _ ] => rewrite H in *; [match P with
                                                   | forall x, _ => clear H
                                                   | _ => idtac
                                                 end]
         end).
 
  ]]

  In implementing another level of automation, it will be useful to mark which free variables we generated with tactics, as opposed to which were present in the original theorem statement.  We use a dummy marker predicate [Generated] to record that information.  A tactic [not_generated] fails if and only if its argument is a generated variable, and a tactic [generate] records that its argument is generated. *)

Definition Generated n (_ : fin n) := True.

Ltac not_generated x :=
  match goal with
    | [ _ : Generated x |- _ ] => fail 1
    | _ => idtac
  end.

Ltac generate x := assert (Generated x); [ constructor | ].

(** A tactic [destructG] performs case analysis on [fin] values.  The built-in case analysis tactics are not smart enough to handle all situations, and we also want to mark new variables as generated, to avoid infinite loops of case analysis.  Our [destructG] tactic will only proceed if its argument is not generated. *)

Theorem fin_inv : forall n (f : fin (S n)), f = First \/ exists f', f = Next f'.
  intros; dep_destruct f; eauto.
Qed.

Ltac destructG E :=
  not_generated E; let x := fresh "x" in
    (destruct (fin_inv E) as [ | [x]] || destruct E as [ | ? x]);
    [ | generate x ].

(* begin hide *)
Ltac dester := simp;
  repeat (match goal with
            | [ x : fin _, H : _ = _, IH : forall f : fin _, _ |- _ ] =>
              generalize (IH x); clear IH; intro IH; rewrite H in IH
            | [ x : fin _, y : fin _, H : _ = _, IH : forall (f : fin _) (g : fin _), _ |- _ ] =>
              generalize (IH x y); clear IH; intro IH; rewrite H in IH
            | [ |- context[match ?E with First _ => _ | Next _ _ => _ end] ] => destructG E
            | [ _ : context[match ?E with First _ => _ | Next _ _ => _ end] |- _ ] => destructG E
            | [ |- context[more ?E] ] => destructG E
            | [ x : fin ?n |- _ ] =>
              match goal with
                | [ |- context[nzf x] ] =>
                  destruct n; [ inversion x | ]
              end
            | [ x : fin (pred ?n), y : fin ?n |- _ ] =>
              match goal with
                | [ |- context[nzf x] ] =>
                  destruct n; [ inversion y | ]
              end
            | [ |- context[match ?E with None => _ | Some _ => _ end] ] =>
              match E with
                | match _ with None => _ | Some _ => _ end => fail 1
                | _ => case_eq E; firstorder
              end
          end; simp); eauto.
(* end hide *)

(** Our most powerful workhorse tactic will be [dester], which incorporates all of [simp]'s simplifications and adds heuristics for automatic case analysis and automatic quantifier instantiation.

   [[
Ltac dester := simp;
  repeat (match goal with
 
   ]]

   The first hint expresses our main insight into quantifier instantiation.  We identify a hypothesis [IH] that begins with quantification over [fin] values.  We also identify a free [fin] variable [x] and an arbitrary equality hypothesis [H].  Given these, we try instantiating [IH] with [x].  We know we chose correctly if the instantiated proposition includes an opportunity to rewrite using [H].

   [[
            | [ x : fin _, H : _ = _, IH : forall f : fin _, _ |- _ ] =>
              generalize (IH x); clear IH; intro IH; rewrite H in IH
 
   ]]

   This basic idea suffices for all of our explicit quantifier instantiation.  We add one more variant that handles cases where an opportunity for rewriting is only exposed if two different quantifiers are instantiated at once.

   [[
            | [ x : fin _, y : fin _, H : _ = _,
                IH : forall (f : fin _) (g : fin _), _ |- _ ] =>
              generalize (IH x y); clear IH; intro IH; rewrite H in IH
 
   ]]

   We want to case-analyze on any [fin] expression that is the discriminee of a [match] expression or an argument to [more].

   [[
            | [ |- context[match ?E with First _ => _ | Next _ _ => _ end] ] =>
              destructG E
            | [ _ : context[match ?E with First _ => _ | Next _ _ => _ end] |- _ ] =>
              destructG E
            | [ |- context[more ?E] ] => destructG E
 
   ]]

   Recall that [simp] will simplify equality proof terms of facts like [e = e].  The proofs in question will either be of [n = S (pred n)] or [S (pred n) = n], for some [n].  These equations do not have syntactically equal sides.  We can get to the point where they %\emph{%#<i>#do#</i>#%}% have equal sides by performing case analysis on [n].  Whenever we do so, the [n = 0] case will be contradictory, allowing us to discharge it by finding a free variable of type [fin 0] and performing inversion on it.  In the [n = S n'] case, the sides of these equalities will simplify to equal values, as needed.  The next two hints identify [n] values that are good candidates for such case analysis.

   [[
            | [ x : fin ?n |- _ ] =>
              match goal with
                | [ |- context[nzf x] ] =>
                  destruct n; [ inversion x | ]
              end
            | [ x : fin (pred ?n), y : fin ?n |- _ ] =>
              match goal with
                | [ |- context[nzf x] ] =>
                  destruct n; [ inversion y | ]
              end
 
   ]]

   Finally, we find [match] discriminees of [option] type, enforcing that we do not destruct any discriminees that are themselves [match] expressions.  Crucially, we do these case analyses with [case_eq] instead of [destruct].  The former adds equality hypotheses to record the relationships between old variables and their new deduced forms.  These equalities will be used by our quantifier instantiation heuristic.

   [[
            | [ |- context[match ?E with None => _ | Some _ => _ end] ] =>
              match E with
                | match _ with None => _ | Some _ => _ end => fail 1
                | _ => case_eq E; firstorder
              end
 
   ]]

   Each iteration of the loop ends by calling [simp] again, and, after no more progress can be made, we finish by calling [eauto].
   
   [[
          end; simp); eauto.
 
   ]] *)


(** * Theorems *)

(** We are now ready to prove our main theorem, by way of a progression of lemmas.

   The first pair of lemmas characterizes the interaction of substitution and lifting at the variable level. *)

Lemma substVar_unliftVar : forall n (f0 : fin n) f g,
  match substVar f0 f, substVar (liftVar f0 g) f with
    | Some f1, Some f2 => exists f', substVar g f1 = Some f'
      /\ substVar (unliftVar f0 g) f2 = Some f'
    | Some f1, None => substVar g f1 = None
    | None, Some f2 => substVar (unliftVar f0 g) f2 = None
    | None, None => False
  end.
  induction f0; dester.
Qed.

Lemma substVar_liftVar : forall n (f0 : fin n) f,
  substVar f0 (liftVar f0 f) = Some f.
  induction f0; dester.
Qed.

(** Next, we define a notion of %``%#"#greater-than-or-equal#"#%''% for [fin] values, prove an inversion theorem for it, and add that theorem as a hint. *)

Inductive fin_ge : forall n1, fin n1 -> forall n2, fin n2 -> Prop :=
| GeO : forall n1 (f1 : fin n1) n2,
  fin_ge f1 (First : fin (S n2))
| GeS : forall n1 (f1 : fin n1) n2 (f2 : fin n2),
  fin_ge f1 f2
  -> fin_ge (Next f1) (Next f2).

Hint Constructors fin_ge.

Lemma fin_ge_inv' : forall n1 n2 (f1 : fin n1) (f2 : fin n2),
  fin_ge f1 f2
  -> match f1, f2 with
       | Next _ f1', Next _ f2' => fin_ge f1' f2'
       | _, _ => True
     end.
  destruct 1; dester.
Qed.

Lemma fin_ge_inv : forall n1 n2 (f1 : fin n1) (f2 : fin n2),
  fin_ge (Next f1) (Next f2)
  -> fin_ge f1 f2.
  intros; generalize (fin_ge_inv' (f1 := Next f1) (f2 := Next f2)); dester.
Qed.

Hint Resolve fin_ge_inv.

(** A congruence lemma for the [fin] constructor [Next] is similarly useful. *)

Lemma Next_cong : forall n (f1 f2 : fin n),
  f1 = f2
  -> Next f1 = Next f2.
  dester.
Qed.

Hint Resolve Next_cong.

(** We prove a crucial lemma about [liftVar] in terms of [fin_ge]. *)

Lemma liftVar_more : forall n (f : fin n) (f0 : fin (S n)) g,
  fin_ge g f0
  -> match liftVar f0 f in fin n'
       return fin n' -> (fin (pred n') -> fin n') -> fin (S n') with
       | First n0 => fun _ _ => First
       | Next n0 y' => fun _ fx' => Next (fx' y')
     end g (liftVar g) = liftVar (more f0) (liftVar g f).
  induction f; inversion 1; dester.
Qed.

Hint Resolve liftVar_more.

(** We suggest a particular way of changing the form of a goal, so that other hints are able to match. *)

Hint Extern 1 (_ = lift _ (Next (more ?f))) =>
  change (Next (more f)) with (more (Next f)).

(** We suggest applying the [f_equal] tactic to simplify equalities over expressions.  For instance, this would reduce a goal [App f1 x1 = App f2 x2] to two goals [f1 = f2] and [x1 = x2]. *)

Hint Extern 1 (eq (A := exp _) _ _) => f_equal.

(** Our consideration of lifting in isolation finishes with another hint lemma.  The auxiliary lemma with a strengthened induction hypothesis is where we put [fin_ge] to use, and we do not need to mention that predicate again afteward. *)

Lemma double_lift' : forall n (e : exp n) f g,
  fin_ge g f
  -> lift (lift e f) (Next g) = lift (lift e g) (more f).
  induction e; dester.
Qed.

Lemma double_lift : forall n (e : exp n) g,
  lift (lift e First) (Next g) = lift (lift e g) First.
  intros; apply double_lift'; dester.
Qed.

Hint Resolve double_lift.

(** Now we characterize the interaction of substitution and lifting on variables.  We start with a more general form [substVar_lift'] of the final lemma [substVar_lift], with the latter proved as a direct corollary of the former. *)

Lemma substVar_lift' : forall n (f0 : fin n) f g,
  substVar [nzf f0 return n, fin (S n) for
    liftVar (more g) [sym_eq (nzf f0) return n, fin n for f0]]
  (liftVar (liftVar (Next f0) [nzf f0 return n, fin n for g]) f)
  = match substVar f0 f with
      | Some f'' => Some [nzf f0 return n, fin n for liftVar g f'']
      | None => None
    end.
  induction f0; dester.
Qed.

Lemma substVar_lift : forall n (f0 f g : fin (S n)),
  substVar (liftVar (more g) f0) (liftVar (liftVar (Next f0) g) f)
  = match substVar f0 f with
      | Some f'' => Some (liftVar g f'')
      | None => None
    end.
  intros; generalize (substVar_lift' f0 f g); dester.
Qed.

(** We follow a similar decomposition for the expression-level theorem about substitution and lifting. *)

Lemma lift_subst' : forall n (e1 : exp n) f g e2,
  lift (subst e1 f e2) g
  = [sym_eq (nzf f) return n, exp n for
    subst
      (lift e1 (liftVar (Next f) [nzf f return n, fin n for g]))
      [nzf f return n, fin (S n) for
        liftVar (more g) [sym_eq (nzf f) return n, fin n for f]]
      [nzf f return n, exp n for lift e2 g]].
  induction e1; generalize substVar_lift; dester.
Qed.

Lemma lift_subst : forall n g (e2 : exp (S n)) e3,
  subst (lift e2 First) (Next g) (lift e3 First) = lift (n := n) (subst e2 g e3) First.
  intros; generalize (lift_subst' e2 g First e3); dester.
Qed.

Hint Resolve lift_subst.

(** Our last auxiliary lemma characterizes a situation where substitution can undo the effects of lifting. *)

Lemma undo_lift' : forall n (e1 : exp n) e2 f,
  subst (lift e1 f) f e2 = e1.
  induction e1; generalize substVar_liftVar; dester.
Qed.

Lemma undo_lift : forall n e2 e3 (f0 : fin (S (S n))) g,
  e3 = subst (lift e3 (unliftVar f0 g)) (unliftVar f0 g)
    (subst (n := S n) e2 g e3).
  generalize undo_lift'; dester.
Qed.

Hint Resolve undo_lift.

(** Finally, we arrive at the substitution commutativity theorem. *)

Lemma subst_comm' : forall n (e1 : exp n) f g e2 e3,
  subst (subst e1 f e2) g e3
  = subst
  (subst e1 (liftVar f g) [nzf g return n, exp n for
    lift e3 [sym_eq (nzf g) return n, fin n for unliftVar f g]])
  (unliftVar f g)
  (subst e2 g e3).
  induction e1; generalize (substVar_unliftVar (n := n)); dester.
Qed.

Theorem subst_comm : forall (e1 : exp 2) e2 e3,
  subst (subst e1 First e2) First e3
  = subst (subst e1 (Next First) (lift e3 First)) First (subst e2 First e3).
  intros; generalize (subst_comm' e1 First First e2 e3); dester.
Qed.

(** The final theorem is specialized to the case of substituting in an expression with exactly two free variables, which yields a statement that is readable enough, as statements about de Bruijn indices go.
   
   This proof script is resilient to specification changes.  It is easy to add new constructors to the language being treated.  The proofs adapt automatically to the addition of any constructor whose subterms each involve zero or one new bound variables.  That is, to add such a constructor, we only need to add it to the definition of [exp] and add (quite obvious) cases for it in the definitions of [lift] and [subst]. *)
