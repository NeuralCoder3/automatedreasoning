Load properties.

Lemma polDef Pi A: forall (F G H:@formula Pi) p, forall hf hg, subst H F p = Some hf -> subst H G p = Some hg ->
    (pol H p = Some TT -> eval A F <= eval A G -> eval A hf <= eval A hg) /\
    (pol H p = Some FF -> eval A F >= eval A G -> eval A hf <= eval A hg).
Proof.
  intros F G H p.
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
