Load properties.

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

