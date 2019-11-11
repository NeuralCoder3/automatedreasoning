Load basic.

Definition app {X} {Y} (f:X->Y) (x:option X) : option Y :=
  match x with
    None => None
  | Some x => Some (f x)
  end.

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

Definition satisfiable {Pi} (F:@formula Pi) : Prop :=
  exists A, eval A F = 1.
