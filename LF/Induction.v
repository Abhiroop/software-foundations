From LF Require Export Basics.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
intros n. induction n  as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
intros n. induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros n.
intros m.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.