(* Exercises from chapter 2 *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn' ].
  - reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
   intros n m.
   induction n as [| n' IHn' ].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm2 : forall n m : nat,
  S (n + m) = (S n) + m.
Proof.
   intros n m.
   induction n as [| n' IHn' ].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn' ].
  { simpl.  
    induction m as [| m' IHm' ].
    - simpl. reflexivity.
    - simpl. rewrite <- IHm'. reflexivity.
   }
  {
   rewrite <- plus_n_Sm.   
   rewrite <- IHn'.
 rewrite -> plus_n_Sm2.   
   reflexivity.
}
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn' ].
  { simpl. reflexivity. }
  { rewrite <- plus_n_Sm2. 
    rewrite IHn'. 
    rewrite -> plus_n_Sm2. 
    rewrite -> plus_n_Sm2. 
    reflexivity. }
Qed.


Fixpoint double (n:nat) : nat :=
   match n with
   | O => O
   | S n' => S (S (double(n')))
   end.

Compute double 2.

Lemma double_plus: forall n, double(n) = n + n .
Proof.
intros n.
induction n as [| n' IHn' ].
{ simpl. reflexivity. }
{ simpl. rewrite <- plus_n_Sm. 
  rewrite <- IHn'. simpl. reflexivity. }
Qed.



Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Check negb.
Compute negb true.

Lemma doubleneg: forall b: bool, negb(negb(b)) = b.
Proof.
intros b.
destruct b.
- reflexivity.
- reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
intros n.
induction n as [| n' IHn'].
{ reflexivity. }
{ rewrite -> IHn'. 
   simpl.
   rewrite doubleneg.
   reflexivity.
}
Qed.



Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
   intros n m p.
   assert(H1: n + (m + p) = (n + m) + p). {
     rewrite <- plus_assoc.
     reflexivity.
   }
   rewrite H1.

   assert(H2: n + m = m + n). {
     rewrite <- plus_comm.
     reflexivity.
   }
   rewrite H2.
   assert(H3: m + (n + p) = (m + n) + p). {
     rewrite -> plus_assoc.
     reflexivity.
   }

   rewrite -> H3.
   reflexivity.
   
Qed.



(*  Exercise 3 *)

(* Prerequisites taken from section 2 *)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.


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

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* Exercise 3 Theorems *)

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intros n.
  induction n as [|n' IHn']. 
  {
     simpl.
     reflexivity.
  }
  { 
     simpl.
     rewrite <- IHn'.
     reflexivity.
  }
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
   destruct b .
   - reflexivity.
   - reflexivity.
Qed.

Lemma leb_suc : forall n m : nat,
   leb n m = true -> leb (S n) (S m) =  true.
Proof.
  intros n m.
  simpl.

  intros H1.  
  rewrite H1.
  reflexivity.
Qed.


Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
   intros n m p.

   intros H1.
   induction p as [| p' IHp'].
   - simpl. rewrite H1. reflexivity.
   - simpl. rewrite IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
   reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite plus_comm.
  simpl.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true. 
Proof.
  intros b c.
  destruct b.
  { simpl.
    destruct c. 
    { simpl. reflexivity. }
    {  simpl. reflexivity. }
  }
  { 
        destruct c. 
    { simpl. reflexivity. }
    {  simpl. reflexivity. }
}
Qed.

Lemma mult_zero : forall n : nat, n * 0 = 0.
Proof.
intros n.
simpl.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.



Lemma mult_plus1 : forall n m : nat, n * (S m) = (n * m) + n.
Proof.
intros n m.
simpl.
induction n as [|n' IHn'].
{
   simpl.
   reflexivity.
}
{
   induction m as [|m' IHm'].
   {
      simpl.
      rewrite IHn'.
      rewrite mult_zero.
      simpl.
      reflexivity.
   }
   {
       simpl.
       rewrite IHn'. 
       rewrite plus_n_Sm.
       assert(H1: S(n' * S m' + n') = n' * S m' + S n'). {
          rewrite plus_n_Sm.
          reflexivity.
       }
       rewrite H1.
       rewrite plus_assoc.
       reflexivity.
   }
}
Qed.

(*
Theorem mult_comm : forall n m : nat, n * m = m * n.
Proof.
   intros n m.
   induction n as [| n' IHn' ].
   {
      simpl.
      induction m as [|m' IHm'].
      {
        simpl.
        reflexivity.
      }
      {
        simpl.
        rewrite  <- IHm'.
        reflexivity.
      }
   }
   {
      induction m as [|m' IHm'].
      {
         simpl.
         rewrite IHn'.
         simpl.
         reflexivity.
      } 
      {
         simpl.
         rewrite plus_comm.
         rewrite IHn'.
         rewrite mult_plus1.


         rewrite plus_comm.
         reflexivity.
      }
   }

Qed.
*)


Lemma plus_order1 : forall n m p : nat, n + m + p = n + (m + p).
Proof.
  intros n m p.
  rewrite <- plus_assoc.
  reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  simpl.
  induction p as [| p' IHp' ].
  {
     simpl. 
     rewrite mult_zero.
     rewrite mult_zero.
     rewrite mult_zero.
     reflexivity.
  }
  {
     rewrite  mult_plus1.
     rewrite IHp'.
     rewrite mult_plus1.
     rewrite mult_plus1.
     rewrite <- plus_order1.
     rewrite <- plus_order1.
     assert(H1: n * p' + n + m * p' = n * p' + m * p' + n  ). {
       rewrite <- plus_assoc.
       rewrite <- plus_assoc.
       assert(H11: m * p' + n = n + m * p').
       {
          rewrite plus_comm.
          reflexivity.
       }
       rewrite H11.
       reflexivity.
     }
     rewrite H1.
     reflexivity.
  }
Qed.

Theorem mult_assoc : ∀n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.