From LF Require Export Basics.

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
intros.
induction n as [|n' IHn'].
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

Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof.
intros.
induction n.
- reflexivity.
- simpl. rewrite -> IHn. reflexivity.
Qed.


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros.
induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros.
induction n.
- simpl. rewrite add_0_r. reflexivity.
- simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros.
induction n.
- simpl. reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
induction n. 
- simpl. reflexivity.
- simpl. rewrite IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
induction n.
- simpl. reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

(*
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
*)

Lemma bool_id : forall b : bool, negb (negb b) = b.
Proof.
intros b. destruct b.
- reflexivity.
- reflexivity.
Qed.

Theorem even_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
induction n.
- simpl. reflexivity.
- rewrite IHn. simpl.
rewrite bool_id. reflexivity.
Qed.


Theorem mult_0_plus' : forall n m : nat,
  mult (n + 0 + 0) m = mult n m.
Proof.
intros n m.
assert (H: n + 0 + 0 = n).
  { rewrite add_comm. simpl. rewrite add_comm. simpl. reflexivity.  }
rewrite H. reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
intros n m p q.
assert (H : n + m = m + n).
  { rewrite add_comm. reflexivity. }
rewrite H. reflexivity.
Qed.

(* not allowed to use induction *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros n m p.
rewrite add_assoc. rewrite add_assoc.
assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
rewrite H. reflexivity.
Qed.

Lemma mul_simpl: forall m n : nat, 
  m * S n = m * (1 + n).
Proof.
intros m n.
simpl.
reflexivity.
Qed.


Lemma mul_add_distr : forall m k : nat,
   m * (1 + k) = m * 1 + m * k.
Proof.
intros m k.
rewrite mult_n_1.
induction m.
- simpl. reflexivity.
- simpl. rewrite mul_simpl. rewrite IHm. 
  rewrite add_assoc. rewrite add_assoc.
  assert (H : k + m = m + k).
    { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat, m * n  = n * m.
Proof.
intros m n. 
induction n.
- simpl. rewrite mul_0_r. reflexivity.
- simpl. rewrite mul_add_distr. rewrite mult_n_1. rewrite IHn. reflexivity.
Qed.

Check leb.

Lemma plus_0_l : forall n : nat,
  0 + n = n.
Proof. reflexivity. Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
intros n m p.
intros H.
induction p.
- repeat rewrite plus_0_l. rewrite H. reflexivity.
- simpl. rewrite IHp. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
intros.
destruct b.
destruct c.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
repeat rewrite add_assoc.
replace (n + m) with (m + n).
- reflexivity.
- rewrite add_comm. reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).


Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z 
  | B0 x => B1 x
  | B1 x => B0 (incr x)
  end.

Compute (incr (B0 Z)).
Compute (incr Z).
Compute (incr (B1 Z)).
Compute (incr (B0 (B1 Z))). 
Compute (incr (B1 (B1 Z))).
Compute (incr (B0 (B0 (B1 Z)))).


Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 x => double (bin_to_nat x)
  | B1 x => S (double (bin_to_nat x))
  end.

Compute (bin_to_nat (B0 Z)).
Compute (bin_to_nat Z).
Compute (bin_to_nat (B1 Z)).
Compute (bin_to_nat (B0 (B1 Z))). 
Compute (bin_to_nat (B1 (B1 Z))).
Compute (bin_to_nat (B0 (B0 (B1 Z)))).

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
intros.
simpl.
induction b.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. rewrite IHb. simpl. reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
intros.
induction n.
- reflexivity.
- simpl. rewrite bin_to_nat_pres_incr. rewrite IHn. reflexivity.
Qed.


