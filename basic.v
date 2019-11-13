Require Import List Lia.
Require Import String.
Import ListNotations Nat.
Open Scope string.
Open Scope nat_scope.

Ltac inv H := inversion H; subst; clear H.

Inductive formula {Pi} :=
  Bot | Top | V (p:Pi) | Not (a:formula) |
  And (a b:formula) | Or (a b:formula) |
  To (a b:formula) | Equiv (a b:formula).

Notation "F ∨ G" := (Or F G)(at level 71).
Notation "F ∧ G" := (And F G)(at level 71).
Notation "F → G" := (To F G)(at level 71).
Notation "F ↔ G" := (Equiv F G)(at level 71).
Notation "¬ F" := (Not F)(at level 70).
Notation "x ∈ xs" := (xs x)(at level 80, only parsing).
Notation "T 'set'" := (T -> Prop)(at level 80, only parsing).

Definition StringVar := @V string.
Coercion StringVar : string >-> formula.

Definition bool2nat (b:bool) := if b then 1 else 0.
Coercion bool2nat : bool >-> nat.

Inductive polarity := TT | FF | NN.

