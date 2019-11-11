Lemma eqSet (X:Type) (A B:X->Prop) :
  (forall x, B x <-> False) <->
  (forall x, ((A x /\ ~ B x) \/ (B x /\ ~ A x)) <-> A x).
Proof.
  split.
  - intros H x. split.
    + intros [[]|[]].
      * exact H0.
      * destruct(H x).
        destruct (H2 H0).
    + intros H0.
      assert(~B x).
      {
        intros H1. destruct (H x).
        now apply H2.
      }
      left.
      now split.
  - intros H x.
    split;intros H0.
    + specialize (H x).
      assert(~A x).
      {
        intros H1.
        destruct H.
        specialize (H2 H1) as [[]|[]].
        - now apply H3.
        - now apply H3.
      }
      apply H1.
      apply H.
      right. now split.
    + destruct H0.
Qed.

Goal forall (X:Type) (A:X->Prop) (f:X->X->X),
    (forall x y, exists z, f x z = y) -> forall x y, exists z, f x (f y z)=x.
Proof.
  intros.
  destruct (H x x) as [].
  destruct (H y x0) as [].
  exists x1.
  now rewrite H1, H0.
Qed.

