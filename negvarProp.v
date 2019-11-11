Load properties.

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
