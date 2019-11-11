Require Import List Lia.
Require Import String.
Import ListNotations Nat.
Open Scope string.
Open Scope nat_scope.

Inductive formula {Pi} :=
  Bot | Top | V (p:Pi) | Not (a:formula) |
  And (a b:formula) | Or (a b:formula) |
  To (a b:formula) | Equiv (a b:formula).

Definition app {X} {Y} (f:X->Y) (x:option X) : option Y :=
  match x with
    None => None
  | Some x => Some (f x)
  end.

Notation "F ∨ G" := (Or F G)(at level 71).
Notation "F ∧ G" := (And F G)(at level 71).
Notation "F → G" := (To F G)(at level 71).
Notation "F ↔ G" := (Equiv F G)(at level 71).
Notation "¬ F" := (Not F)(at level 70).


Definition StringVar := @V string.
Coercion StringVar : string >-> formula.

Definition testFormula :=
  "P" ∨ (¬"Q" → (¬ "P" ∧ Top)).
(* Compute (negvar testFormula). *)


Fixpoint subst {Pi} (F G:@formula Pi) p :=
  match F, p with
    _, [] => Some G
  | (Not F), 1::p => app Not (subst F G p)
  | (And F1 F2), 1::p => app (fun f => And f F2) (subst F1 G p)
  | (And F1 F2), 2::p => app (And F1) (subst F2 G p)
  | (Or F1 F2), 1::p => app (fun f => Or f F2) (subst F1 G p)
  | (Or F1 F2), 2::p => app (Or F1) (subst F2 G p)
  | (To F1 F2), 1::p => app (fun f => To f F2) (subst F1 G p)
  | (To F1 F2), 2::p => app (To F1) (subst F2 G p)
  | (Equiv F1 F2), 1::p => app (fun f => Equiv f F2) (subst F1 G p)
  | (Equiv F1 F2), 2::p => app (Equiv F1) (subst F2 G p)
  | _, _ => None
  end.

Inductive polarity := TT | FF | NN.

Definition negPol p :=
  match p with
    TT => FF
  | FF => TT
  | NN => NN
  end.

Fixpoint pol {Pi} (F:@formula Pi) p :=
  match F,p with
    _, [] => Some TT
  | (Not F), 1::p => app negPol (pol F p)
  | (And F1 F2), 1::p => pol F1 p
  | (And F1 F2), 2::p => pol F2 p
  | (Or F1 F2), 1::p => pol F1 p
  | (Or F1 F2), 2::p => pol F2 p
  | (To F1 F2), 1::p => app negPol (pol F1 p)
  | (To F1 F2), 2::p => pol F2 p
  | (Equiv F1 F2), 1::p => Some NN
  | (Equiv F1 F2), 2::p => Some NN
  | _,_ => None
  end.

Definition bool2nat (b:bool) := if b then 1 else 0.

Coercion bool2nat : bool >-> nat.

Fixpoint eval {Pi} (A:Pi->bool) (F:@formula Pi) : nat :=
  match F with
    Bot => 0
  | Top => 1
  | V p => A p
  | Not F => 1-eval A F
  | And F G => min (eval A F) (eval A G)
  | Or F G => max (eval A F) (eval A G)
  | To F G => max (1-eval A F) (eval A G)
  | Equiv F G => if eval A F =? eval A G then 1 else 0
  end.


Lemma polEmpty {Pi} (H:@formula Pi) : pol H [] = Some TT.
Proof.
  destruct H;reflexivity.
Qed.

Lemma substEmpty {Pi} (H F:@formula Pi) : subst H F [] = Some F.
Proof.
  destruct H;reflexivity.
Qed.

Lemma appInv {X Y} (f:X->Y) x b: app f x = Some b <-> exists a, x=Some a /\ b=f a.
Proof.
  unfold app.
  split.
  - intros H. destruct x.
    + exists x;split;congruence.
    + congruence.
  - intros (a&H0&H1). now subst.
Qed.

Goal forall Pi A (F G H:@formula Pi) p, forall hf hg, subst H F p = Some hf -> subst H G p = Some hg ->
    (pol H p = Some TT -> eval A F <= eval A G -> eval A hf <= eval A hg) /\
    (pol H p = Some FF -> eval A F >= eval A G -> eval A hf <= eval A hg).
Proof.
  intros Pi A F G H p.
  induction p in F, G, H |- *.
  - intros. rewrite polEmpty. split;intros.
    + rewrite substEmpty in H0, H1.
      injection H0 as <-;injection H1 as <-.
      exact H3.
    + congruence.
  - intros hf hg Ef Eg.
    destruct H as [ | | |H'|H1 H2|H1 H2|H1 H2|H1 H2] eqn:H0;
      destruct a as [|[|[|]]];cbn in *;try congruence.
    all: rewrite appInv in Ef,Eg;
      destruct Ef as (af&Ef0&->);
      destruct Eg as (ag&Eg0&->).

    (* ~ *)
    + destruct pol as [[]|] eqn:Hp;cbn;split;intros;try congruence.
      all: destruct (IHp G F H' ag af Eg0 Ef0).
      1: specialize (H3 Hp H2).
      2: specialize (H4 Hp H2).
      all: destruct (eval A af), (eval A ag);repeat constructor;
        now apply PeanoNat.Nat.nle_succ_0 in H3.

    (* /\ *)
    (* second case is like first case but with H2 in IH *)
    + destruct (IHp F G H1 af ag Ef0 Eg0).
      destruct pol as [[]|];split;intros;try congruence;cbn.
      * specialize (H3 H5 H6).
        now apply PeanoNat.Nat.min_le_compat.
      * specialize (H4 H5 H6).
        now apply PeanoNat.Nat.min_le_compat.
    + destruct (IHp F G H2 af ag Ef0 Eg0).
      destruct pol as [[]|];split;intros;try congruence;cbn.
      * specialize (H3 H5 H6).
        now apply PeanoNat.Nat.min_le_compat.
      * specialize (H4 H5 H6).
        now apply PeanoNat.Nat.min_le_compat.

    (* \/ *)
    (* /\ but with max instead of min *)
    + destruct (IHp F G H1 af ag Ef0 Eg0).
      destruct pol as [[]|];split;intros;try congruence;cbn.
      * specialize (H3 H5 H6).
        now apply PeanoNat.Nat.max_le_compat.
      * specialize (H4 H5 H6).
        now apply PeanoNat.Nat.max_le_compat.
    + destruct (IHp F G H2 af ag Ef0 Eg0).
      destruct pol as [[]|];split;intros;try congruence;cbn.
      * specialize (H3 H5 H6).
        now apply PeanoNat.Nat.max_le_compat.
      * specialize (H4 H5 H6).
        now apply PeanoNat.Nat.max_le_compat.

    (* -> *)
    (* first case is ~ \/ *)
    (* first case is \/ *)
    + destruct (IHp G F H1 ag af Eg0 Ef0).
      destruct pol as [[]|];split;intros [=] ?.
      1: apply H3 in H6;trivial.
      2: apply H4 in H6;trivial.
      all: cbn;
      apply PeanoNat.Nat.max_le_compat;
      destruct (eval A af), (eval A ag);lia.
    + destruct (IHp F G H2 af ag Ef0 Eg0).
      destruct pol as [[]|];split;intros [=] ?.
      1: apply H3 in H6;trivial.
      2: apply H4 in H6;trivial.
      all: now cbn;apply PeanoNat.Nat.max_le_compat.

    (* <-> no case applicable *)
    + split;intros [=].
    + split;intros [=].
Qed.





Fixpoint negvar {Pi} (F:@formula Pi) :=
  match F with
    V p => Not (V p)
  | Not f => Not (negvar f)
  | And f1 f2 => And (negvar f1) (negvar f2)
  | Or f1 f2 => Or (negvar f1) (negvar f2)
  | To f1 f2 => To (negvar f1) (negvar f2)
  | Equiv f1 f2 => Equiv (negvar f1) (negvar f2)
  | _ => F
  end.

Definition satisfiable {Pi} (F:@formula Pi) : Prop :=
  exists A, eval A F = 1.

Lemma negvarEval: forall X (F:@formula X) A, eval A F = eval (fun a => negb (A a)) (negvar F).
Proof.
  intros Pi F A.
  induction F;cbn;trivial;intros.
  all: try(now destruct (eval A F1), (eval A F2);rewrite <- IHF1, <- IHF2).
  - now destruct A.
  - now destruct eval;rewrite <- IHF.
Qed.

Goal forall X (F:@formula X), satisfiable F -> satisfiable (negvar F).
Proof.
  intros Pi F [A H].
  exists (fun a => negb (A a)).
  now rewrite <- negvarEval.
Qed.








Lemma evalDestruct {Pi} (A:Pi->bool) F: eval A F = 0 \/ eval A F = 1.
Proof.
  induction F;cbn.
  all: try (destruct IHF1 as [->| ->], IHF2 as [-> | ->];cbn;tauto).
  - now left.
  - now right.
  - destruct A;tauto.
  - destruct eval;tauto.
Qed.

Lemma evalInd {Pi} (A:Pi->bool) F (p:nat->Prop): (eval A F = 0 -> p 0) -> (eval A F = 1 -> p 1) -> forall b, eval A F = b -> p b.
Proof.
  intros.
  destruct (evalDestruct A F);subst;rewrite H2;eauto.
Qed.

