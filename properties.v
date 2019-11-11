Load functions.

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
