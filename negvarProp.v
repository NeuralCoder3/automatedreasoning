Load properties.

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
  unfold sat.
  now rewrite <- negvarEval.
Qed.

