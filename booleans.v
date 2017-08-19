Module NatPlayground.

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

Example test_orb1: (orb true false) = true.
Proof. 
reflexivity. 
Qed.



Definition nandb (b1:bool) (b2:bool) : bool :=
(*  (negb (andb b1 b2)).*)
  match b1 with
  | true => 
     (match b2 with
     | true => false
     | false => true
     end)
  | false => 
     (match b2 with
     | true => true
     | false => true
     end)
  end.
Example test_nandb1: (nandb true false) = true.
 reflexivity.
 Qed.
Example test_nandb2: (nandb false false) = true.
 reflexivity.
 Qed.
Example test_nandb4: (nandb true true) = false.
 reflexivity.
 Qed.

Example test_nandb3: (nandb false true) = true.
 reflexivity.
 Qed.


Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
   (andb (andb b1 b2) b3).


Example test_andb31: (andb3 true true true) = true.
   reflexivity.
   Qed.
Example test_andb32: (andb3 false true true) = false.
   reflexivity.
   Qed.
Example test_andb33: (andb3 true false true) = false.
   reflexivity.
   Qed.
Example test_andb34: (andb3 true true false) = false.
   reflexivity.
   Qed.

Check true.

Check andb3.



Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Inductive nat' : Type :=
   | stop : nat'
   | tick : nat' -> nat'.


Definition pred ( n : nat ) :=
   match n with
   | O => O
   | S n1 => n1
   end.


Example simple_pred: (pred O) = O.
Proof.
reflexivity.
Qed.


Example simple_pred1: (pred (S O)) = O.
Proof.
reflexivity.
Qed.


Fixpoint evenb (n:nat) : bool :=
   match n with
   | O => true
   | S O => false
   | S (S n') => evenb n'
   end.

Example simple_even1: (evenb (S (S O))) = true.
Proof.
reflexivity.
Qed.


Example simple_even2: (evenb (S O)) = false.
Proof.
reflexivity.
Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Example simple_plus1: (plus (S (S O)) (S (S (S O)))) = (S (S (S (S (S O))))).
Proof.
 reflexivity.
Qed.

Fixpoint mult (n : nat) (m : nat) : nat :=
  match n with
  | O => O
  | S n' =>  (plus m (mult n' m))
  end.

Example simple_mult1: (mult (S (S O)) (S (S (S O)))) = (S (S (S (S (S (S O)))))).
Proof.
 simpl.
 reflexivity.
Qed.

End NatPlayground.

Fixpoint factorial (n:nat) : nat :=
   match n with
   | O => S O
   | S n' => (mult n (factorial n'))
   end.

Example test_factorial1: (factorial 3) = 6.
Proof.
reflexivity.
Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
reflexivity.
Qed.


Theorem plus_zero_l : forall x : nat , 0 + x = x.
Proof.
reflexivity.
Qed.

Theorem plus_zero_2 : forall x y : nat, x = y -> x + 0 = y + 0.
Proof.
intros x y.
intros H.
rewrite <- H.
reflexivity.
Qed.
(*
Theorem plus_zero_3 : forall x y : nat, x - y = 0 -> x + 0 =  y + 0.
Proof.
intros x y.
intros H.
rewrite -> H.
reflexivity.
Qed.*)


Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
   intros n m o.
   intros H1.
   rewrite <- H1.
   intros H2.
   rewrite <- H2.
   simpl.
   reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
   intros m n.
   intros H1.
   rewrite -> H1.
   reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.



Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
    { 
      simpl.
      reflexivity. }
    { reflexivity. }
  Qed.


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros x.
  intros l.
  simpl.
  rewrite x.
  rewrite x.
  trivial.
Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
   intros b c.
   destruct b.
     { simpl. intros k. rewrite k. reflexivity.  }
     { simpl. intros k. rewrite k. reflexivity.  }

Qed.

Extraction Language Scheme. 
Extraction "boolean.scm"  factorial.
