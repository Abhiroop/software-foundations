Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday monday)).

Example test_next_weekday:
  (next_weekday (next_weekday monday)) = wednesday.
  Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Compute (andb true true).
Compute (andb true false).
Compute (andb false true).
Compute (andb false false).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.


Notation "x && y" := (andb x y).

Infix "&&" := andb.
Infix "||" := orb.

Definition negb' (b: bool) : bool :=
  if b then false
  else true.   

Example test_orb5: true || true || false = true.
Proof. simpl. reflexivity. Qed.



Definition nandb (x:bool) (y:bool) : bool :=
  negb (x && y).



Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  b1 && b2 && b3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check negb.
Check (negb true).


Module Playground1.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n:nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End Playground1.

Check (S (S O)).

Check (S (S (S O))).

Compute (pred (O)).

Definition minusTwo (n:nat) : nat :=
  pred (pred n).

Check minusTwo.

Compute (minusTwo (S (S (S (S O))))).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module Playground2.

Fixpoint plus (n m:nat) : nat :=
  match m with
  | O => n
  | S m' => plus (S n) m'
  end.

Compute (plus 3 3).

Fixpoint mult (n m:nat) : nat :=
  match m with
  | O => O
  | S m' => plus n (mult n m')
  end.

Compute (mult 3 4).

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p' => mult base (exp base p')
  end.

Example test_exp1: (exp 5 2) = 25.
Proof. simpl. reflexivity. Qed.



Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => (S O)
  | (S n') => mult n (factorial n')
  end.


 

Example test_factorial1: (factorial 5) = 120.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).


Fixpoint beq_nat (n m:nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => beq_nat n' m'
  end.

Example test_beq_nat1: (beq_nat 3 3) = true.
Proof. simpl. reflexivity. Qed.

Example test_beq_nat2: (beq_nat 4 3) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m:nat) : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n', S m' => leb n' m'
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.


Notation "x =? y" := (beq_nat x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Definition blt_nat (n m : nat) : bool :=
  negb (leb m n).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_l: forall n : nat, O + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l: forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_O_l: forall n : nat, O * n = O.
Proof.
  intros n. reflexivity. Qed.

Theorem plud_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
intros n m.
intros H.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros n m o.
intros H1.
intros H2.
rewrite H1.
rewrite <- H2.
reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
intros p q.
rewrite <- mult_n_O.
rewrite <- mult_n_O.
reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
intros p.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
intros b.
destruct b eqn:E.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Theorem andb_commutative: forall a b: bool,
  a && b = b && a.
Proof.
  intros a b. destruct a eqn:Ea.
    - destruct b eqn:Eb.
      + reflexivity.
      + reflexivity.
    - destruct b eqn:Eb.
      + reflexivity.
      + reflexivity.
  Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c.
destruct b eqn:Eb.
- simpl. intros H. rewrite H. reflexivity.
- simpl. destruct c eqn:Ec.
  + reflexivity.
  + intros H2. rewrite H2. reflexivity.
Qed.

Theorem andb_true_elim2_alternate : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c.
destruct b.
- simpl. intros H. rewrite H. reflexivity.
- simpl. intros H2. rewrite <- H2. destruct c.
  + rewrite H2. reflexivity.
  + reflexivity.
Qed.




(*
Theorem andb_true_elim2_another : forall b c: bool,
   (b && c) = true -> c = true.
Proof.
  intros [] [].
  intros H.
  - reflexivity.
  - simpl. intros. rewrite -> H. reflexivity.
  - simpl. intros. reflexivity.
  - simpl. intros. rewrite -> H. reflexivity.
Qed.
*)

Theorem plus_1_neq_0: forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros[|n].
  - reflexivity.
  - reflexivity.
 Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
intros [] [].
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
intros [|n']. (*intros n. destruct n.*)
- reflexivity.
- reflexivity.
Qed.


Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.



(* Fixpoint break_termination_checker (n:nat) : nat := 
  mult (break_termination_checker n) 0.  *)


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
intros f. 
intros H.
intros b.
rewrite H. rewrite H. reflexivity.
Qed.


Theorem negation_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
intros f.
intros H.
intros b.
rewrite H. rewrite H. 
destruct b.
- reflexivity.
- reflexivity.
Qed.


Theorem negation_fn_applied_twice' :
  forall (f : bool -> bool), (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
intros.
destruct b.
- rewrite H. rewrite H. reflexivity.
- rewrite H. rewrite H. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
intros b c.
destruct b.
destruct c.
- simpl. reflexivity.
- simpl. intros H. rewrite H. reflexivity.
- simpl. destruct c.
  + intros H. rewrite H. reflexivity.
  + reflexivity.
Qed.


Theorem andb_eq_orb' :
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
intros b c.
destruct b.
- destruct c.
  + reflexivity.
  + simpl. intros H. rewrite H. reflexivity.
- destruct c.
  + simpl. intros H. rewrite H. reflexivity.
  + reflexivity.
Qed.


Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Set :=
  | Eq : comparison (* "equal" *)
  | Lt : comparison (* "less than" *)
  | Gt : comparison. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.


Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
intros l.
destruct l.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.


Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
    match (letter_comparison l1 l2) with
    | Eq => modifier_comparison m1 m2
    | c  => c
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. reflexivity. Qed.

Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. reflexivity. Qed.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. reflexivity. Qed.

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Note that you can't go lower than F *)
  end.

Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

Theorem lower_letter_lowers:
 forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
intros.
destruct l.
- reflexivity.
- reflexivity.  
- reflexivity.
- reflexivity.
- simpl. rewrite <- H. simpl. reflexivity.
Qed.

Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade l1 m1 =>
    match m1 with
    | Plus => Grade l1 Natural
    | Natural => Grade l1 Minus
    | Minus =>
      match l1 with
      | F => Grade F Minus
      | _ => Grade (lower_letter l1) Plus
      end
    end
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. reflexivity. Qed.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
intros.
destruct g.
rewrite <- H.
destruct m.
- destruct l.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
- destruct l.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
- destruct l.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

End LateDays.