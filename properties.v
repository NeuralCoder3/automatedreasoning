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


