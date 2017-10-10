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

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.

  induction n as [| n' IHn' ].
  {
     simpl. reflexivity.
  }
  {
    simpl. 
    rewrite -> mult_plus_distr_r.
    rewrite IHn'.
    reflexivity.
  }
Qed.


Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [|n' HIn'].
  - simpl. reflexivity.
  - simpl. rewrite HIn'. reflexivity.
Qed.



Lemma plus_suc1 : forall n m  : nat, 
    S (n + m ) =   n +  S m .
Proof.
   intros n m.
   induction n as [|n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite IHn'. reflexivity.

Qed.

Theorem plus_swapComplex' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n  m p.
  induction n as [|n' IHn].
  {
    simpl.
    reflexivity.
  }
  {
   simpl.
   rewrite IHn.
   replace (S n' + p) with (S (n' + p)).
   replace (m + S (n' + p)) with (S (m + n' + p)).
   rewrite plus_assoc.
   reflexivity.

   replace (m + n' + p) with (m + (n' + p)).
   rewrite plus_suc1.
   reflexivity.
  
   rewrite plus_assoc.
   reflexivity.

   replace (S n' + p) with (p + S n') .
   rewrite plus_comm.
   rewrite -> plus_suc1.
   reflexivity.
  
   rewrite <- plus_suc1.
   assert  (H1: S n' + p = p + S n') .
   { 
      rewrite plus_comm.  
      reflexivity.
       
   }
   rewrite H1.

   rewrite plus_suc1.
   reflexivity.
  }
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
   intros n m p.

   rewrite plus_assoc.
   replace (m + (n + p)) with ((m + n) + p).
   replace (m + n) with (n + m).
   reflexivity.
   rewrite plus_comm.
   reflexivity.
   rewrite plus_assoc.
   reflexivity.
Qed.

(*
 Exercise 3 stars  binary_commute
*)

Inductive bin : Type :=
  | Zero : bin
  | Twice : bin -> bin
  | OneMoreTwice : bin -> bin.


Definition normalizing(n : bin) :=
  match n with
       | Zero => Zero
       | another => Twice another
  end.



(* *)
Fixpoint normalize(n : bin) :=
   match n with
   | Twice other => 
       normalizing(normalize(other))
       (*
       match normalize(other) with
       | Zero => Zero
       | another => Twice another
       end*)
   | Zero => Zero
   | OneMoreTwice n' =>
      OneMoreTwice (normalize n')
   end.

Lemma normalizing_norm : forall b : bin,
   normalizing (normalize b) = normalize (Twice  b).
Proof.
   intros b.
   induction b.
   {
     simpl.
     reflexivity.
   }
   {
     simpl.
     reflexivity.
   }
   {
      simpl.
      reflexivity.
   }
Qed.

Lemma normalizing_norm_reverse : forall b : bin,
    normalize (normalizing b) = normalize (Twice  b).
Proof.
   intros b.
   induction b.
   - reflexivity.
   - simpl. reflexivity.
   - reflexivity.
Qed.


Fixpoint incr (number : bin) : bin :=
   match number with
   | Zero => OneMoreTwice Zero
   | Twice t => OneMoreTwice t
   | OneMoreTwice t => Twice (incr t)
end.

Fixpoint bin_to_nat(x : bin) : nat :=
   match x with
   | Zero => O
   | OneMoreTwice t' => 1 + 2*(bin_to_nat(t'))
   | Twice b' =>  2 * (bin_to_nat(b'))
end.




Lemma plus_zero: forall x : nat, x + 0 = x.
Proof.
  intros x.
  rewrite plus_comm.
  simpl.
  reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin, 
   bin_to_nat(incr b) = S (bin_to_nat(b)).
Proof.
  intros b.
  induction b .
  {  simpl. reflexivity. }
  { simpl. rewrite plus_zero. simpl. reflexivity. }
  {  
     simpl.
     rewrite plus_zero.
     rewrite IHb.
     rewrite plus_suc1.
     simpl.
     replace (bin_to_nat b + 0) with (bin_to_nat b).
     reflexivity.
     rewrite plus_zero.
     reflexivity.
  }
Qed.

Fixpoint nat_to_bin(x : nat) : bin :=
   match x with
   | O => Zero
   | S t' => incr(nat_to_bin(t'))
end.


Theorem bin_to_nat_reverse : forall n : nat, 
    bin_to_nat(nat_to_bin(n)) = n.
Proof.
   intros n.
   induction n.
   {
      simpl.
      reflexivity.
   }
   {   
      simpl.
      rewrite bin_to_nat_pres_incr.
      rewrite IHn.
      reflexivity.
   }
Qed.


Compute (normalize(OneMoreTwice (Twice Zero))).


Fixpoint bin_plus (n:bin) (m:bin) : bin :=
   match n with
   | Zero => m
   | Twice n' => (bin_plus n' (bin_plus n' m))
   | OneMoreTwice n' => (incr(bin_plus n' (bin_plus n' m)))
   end.

Fixpoint bin_plus_norm (n:bin) (m:bin) : bin :=
   match n with
   | Zero => normalize(m)
   | Twice n' => normalize(bin_plus n' (bin_plus n' m))
   | OneMoreTwice n' => normalize(incr(bin_plus n' (bin_plus n' m)))
   end.

Compute bin_to_nat(bin_plus (nat_to_bin 3) (nat_to_bin 4)).
Compute (bin_plus Zero Zero).
Compute (bin_plus (Twice Zero) (Twice (Twice Zero))).

(*
Lemma idem_norm_2 : forall b : bin,
       normalize (Twice b) = normalize (Twice (normalize b)).
Proof.
   intros b.
   induction b.
   {
     simpl.
     reflexivity.
   }
   { 
    
      simpl.
      rewrite  normalizing_norm_reverse.
      rewrite <- IHb.
      rewrite  normalizing_norm.
      reflexivity.
    }
    {
      simpl. 
    }
Abort.
*)


Lemma normalize_idem: forall b : bin,
    normalize( b) = normalize((normalize b)).
Proof.
   intros b.
   induction b as [|b' IHb'|].
   { simpl. reflexivity. }
   {
     simpl.
     rewrite  normalizing_norm_reverse .
     rewrite  normalizing_norm .
     simpl.
     rewrite <- IHb'.
     reflexivity.
   }
   {
      simpl.
      rewrite <- IHb.
      reflexivity.
   }
   
     
Qed.


Definition double_bin (n : bin)  : bin :=
   match n with
   | Zero => Zero
   | Twice n' => Twice (Twice n')
   | OneMoreTwice n' => Twice (OneMoreTwice n')
   end.


Lemma twice_double : forall b : bin , 
       bin_to_nat(b) + bin_to_nat(b) = bin_to_nat(double_bin(b)).
Proof.
  intros b.
  induction b.
  { simpl. reflexivity. }
  {  simpl. 
     rewrite plus_zero.
     rewrite plus_zero.
     reflexivity.
   } 
   {
      simpl.
      rewrite plus_zero.
      rewrite plus_zero.
      reflexivity.

   }
Qed.

Lemma twice_double2 : forall b : bin , 
      nat_to_bin( bin_to_nat(b) + bin_to_nat(b) ) = nat_to_bin(bin_to_nat(double_bin(b))).
Proof.
  intros b.
  induction b.
  { simpl. reflexivity. }
  {  simpl. 
     rewrite plus_zero.
     rewrite plus_zero.
     reflexivity.
   } 
   {
      simpl.
      rewrite plus_zero.
      rewrite plus_zero.
      reflexivity.

   }
Qed.

Lemma idem_norm : forall b : bin,
    normalize(b) = normalize(normalize b).
Proof.
   intros b.
   induction b.
   {
      simpl.
      reflexivity.
   }
   {
      simpl.
   }
Abort.


Compute (nat_to_bin(bin_to_nat  (Twice Zero))).
(*
Theorem nat_to_bin_plus_reverse : forall b : bin, 
    (nat_to_bin((bin_to_nat  b) + (bin_to_nat  b))) = 
    (bin_plus b b).
Proof.
   intros b.
   induction b.
   {
      simpl.
      reflexivity.
   }
   {
      simpl.
      rewrite plus_zero.
   }
   {
   }
Abort.
*)

Compute (normalize (incr (OneMoreTwice (Twice (Twice Zero))))).
Compute  (incr (normalize (OneMoreTwice (Twice (Twice Zero))))).

Compute  (nat_to_bin 15).

Lemma incr_normalize : forall b : bin, 
    incr (normalize b) = normalize(incr  b).
Proof.
   intros b.
   induction b.
   {
     simpl.
     reflexivity.
   }
   {
     simpl.
     destruct (normalize b).
     {
          simpl.
          reflexivity.
     }
     {
       simpl.
       reflexivity.
     }
     {
        simpl.
        reflexivity.
     }
   } 
   {
     simpl.
     destruct b.
     {
       simpl.
       reflexivity.
     }
     {
       rewrite IHb.
       simpl.

       reflexivity.
     }
     {
       rewrite <- IHb.
      simpl.
      reflexivity.
     }
      
   }
   

Qed.

Compute (incr(OneMoreTwice Zero)).
Compute (normalize (OneMoreTwice (Twice (Twice (Twice Zero))))).

Theorem nat_to_bin_norm : forall n : nat, 
    (nat_to_bin n) = normalize((nat_to_bin n)).
Proof.
   intros n.
   induction n as [| n' IHn].
   {
     simpl.
     reflexivity.
   }
   {
     simpl.
     rewrite  <- incr_normalize.

     assert(H1: incr(nat_to_bin n') = 
                    incr (normalize (nat_to_bin n'))). { 
        rewrite <- IHn.
        reflexivity.
     }
     rewrite H1.
     reflexivity.

   }

Qed.

(*
Lemma bin_plus_assoc : forall a b c : bin,
      (bin_plus a (bin_plus b c)) = (bin_plus (bin_plus a b) c).
Proof.
   intros a b c.
   induction a.
   {
     simpl.
     reflexivity.
   }
   {
     simpl.
     rewrite IHa.
*)

Lemma twice_bin_plus: forall b : bin, 
    (bin_plus b b) = normalize(Twice b).
Proof.
   intros b.
   induction b as [| b' IHb1 |].
   { simpl.
     reflexivity.
   }
   { simpl.
     replace (bin_plus (Twice b') (Twice b') ) with (normalize(bin_plus b' (bin_plus b' (Twice b')))).
   }
Abort.

Lemma replace_suc : forall n : nat, 
       S (n + n) = n + S n.
Proof.
   intros n.
   induction n.
   { simpl. reflexivity. }
   { simpl.
     replace (S (S n)) with (1 + (S n)).
     replace (n + (1 + (S n))) with (1 + (n + (S n))).
     simpl.
     reflexivity.
     rewrite  plus_assoc.
     rewrite  plus_assoc.
     replace (n + 1) with (1 + n).
     reflexivity.
     rewrite plus_comm.
     reflexivity.
     simpl.
     reflexivity.
   }
Qed.

Lemma plus_one_nat_to_bin : forall n : nat,
  nat_to_bin ( S (n + n)) = (OneMoreTwice (nat_to_bin n)).
Proof.
   intros n.
   induction n.
   {
     simpl.
     reflexivity.
   }
   {
     simpl.
     replace  (n + S n) with (S (n + n)).
     rewrite IHn.
     destruct (nat_to_bin n).
     {
        simpl.
        reflexivity.
     }
     {
        simpl.
        reflexivity. 
     }
     {
         simpl.
         reflexivity.
     }
     {
       simpl.
       rewrite replace_suc.
       reflexivity.
}
   }
Qed.

(*
Lemma bin_plus_normalizing_relation : forall a  : bin,
    (bin_plus a a) = (normalizing (normalize a)).
Proof.
   intros a.
   induction a.
   {
      simpl.
      reflexivity.
   }
   {  
      simpl.
      destruct a.
      - simpl.
 
Qed.
*)
(*
Lemma bin_plus_zero1 : forall a  : bin,
    (bin_plus a Zero) = (normalize a).
Proof.
   intros a.
   induction a.
   { simpl. reflexivity. }
   { simpl. 
     rewrite  IHa.
     rewrite <- IHa.
     simpl. 
     destruct a.
     - simpl. reflexivity.
     -  simpl.
 
*)


Lemma incr_twice : forall b: bin,
    (incr (Twice b)) = OneMoreTwice b.
Proof.
   intros b.
   destruct b.
   - simpl. reflexivity.
   -  simpl. reflexivity.
   - simpl. reflexivity.
Qed.

Lemma incr_bin_plus_relation1 : forall a : bin,
     (incr a) = (bin_plus  (OneMoreTwice Zero) a).
Proof.
   destruct a.
   - simpl. reflexivity.
   - simpl. reflexivity. 
   - simpl. reflexivity.
Qed.

Lemma incr_bin_plus_relation_omt1 : forall a b : bin,
    (bin_plus  (OneMoreTwice a) b) = (incr (bin_plus (Twice a) b)) .
Proof.
   intros a b.
   induction a.
   - simpl. reflexivity.
   -  simpl. reflexivity.
   - simpl. reflexivity.
Qed.

Lemma bin_plus_twice : forall a b : bin,
     (bin_plus  (Twice a) b) = (bin_plus a (bin_plus  a b)).
Proof.
   intros a b.
   destruct a.
   {
      simpl.
      reflexivity.
   }
   {
      simpl.
      reflexivity.
   }
   {
     simpl.
     reflexivity. 
   }
Qed.


(*
Lemma bin_plus_comm : forall a b : bin,
   (bin_plus a b) = (bin_plus b a).
Proof.
   intros a b.
   induction a.
   {
     simpl.
   }

Lemma bin_plus_assoc : forall a b c : bin,
      (bin_plus a (bin_plus b c)) = (bin_plus (bin_plus a b) c).
Proof.
    intros a b c.
    induction a.
    {
     simpl.
     reflexivity.
    }
    {
       rewrite bin_plus_twice.
       rewrite bin_plus_twice.
       rewrite  IHa.
       simpl.
       rewrite bin_plus_twice.
       simpl.
       rewrite   IHa.


Lemma bin_plus_incr : forall a b : bin,
    (bin_plus (incr a) b) = (incr (bin_plus a b)).
Proof.
   intros a b.
   induction a.
   { simpl. reflexivity. }
   { simpl. reflexivity. }
   {
     simpl.
     rewrite incr_bin_plus_relation1.
rewrite IHa.

(* POR AQUI *) 
       rewrite incr_bin_plus_relation_omt1.
       rewrite bin_plus_twice.
       rewrite <- incr_bin_plus_relation_omt1.
       rewrite  bin_plus_incr.
       
        simpl.
       rewrite  incr_bin_plus_relation1.
       rewrite <- incr_twice.
       rewrite <- incr_twice.
       simpl.

       rewrite  <- incr_bin_plus_relation1.
       simpl.
       rewrite <- incr_twice.

    
   }

Lemma double_nat_to_bin_reverse : forall b : nat,
    (nat_to_bin(b + b)) = (bin_plus (nat_to_bin(b)) (nat_to_bin(b))).
Proof.
   intros n.
   induction n. 
   {
      simpl.
      reflexivity.
   }
   {
     simpl.
     rewrite <- replace_suc.
     rewrite plus_one_nat_to_bin.
     simpl.
     destruct (nat_to_bin n).
     - simpl. reflexivity.
     - simpl.
   }
Abort.
*)

Lemma nomalizing_incr : forall b : bin,
     (normalizing (incr b)) = (Twice (incr b)).
Proof.
   intros b.
   destruct b.
   - simpl. reflexivity.
   - simpl. reflexivity.
   - simpl. reflexivity.
Qed.

Lemma nat_to_bin_incr : forall n : nat,
    (nat_to_bin (S n)) = incr (nat_to_bin n).
Proof.
   intros n.
   simpl.
   reflexivity.
Qed.

Lemma one_more_twice_double_incr : forall b : bin,
    (incr (incr (OneMoreTwice b))) = (OneMoreTwice (incr b)).
Proof.
    intros b.
    simpl.
    reflexivity.
Qed.

Lemma nat_to_bin_one_more_twice : forall n : nat,
    (nat_to_bin (n + S n)) = OneMoreTwice (nat_to_bin n).
Proof.
  intros n.
  induction n.
  {
     simpl. reflexivity.
  }
  {
     rewrite <- replace_suc.
     rewrite nat_to_bin_incr.
     rewrite nat_to_bin_incr.
     simpl.
     rewrite IHn.
     simpl.
     reflexivity.


  }
Qed.

Lemma one_more_twice_nat_to_bin_2 : forall n : nat,
   (OneMoreTwice (nat_to_bin n)) = incr (nat_to_bin (n + n)).
Proof.
   intros n.
   induction n.
   { 
      simpl.
      reflexivity.
   }
   {
     simpl.
     rewrite <- one_more_twice_double_incr .
     rewrite nat_to_bin_one_more_twice .
     reflexivity.
   }

Qed.

Theorem nat_to_bin_reverse : forall b : bin, 
    (nat_to_bin(bin_to_nat  b)) = normalize(b).
Proof.
   intros b.
   induction b as [|b' IHb |].
   { 
      simpl.
      reflexivity.
   }
   {
    
     simpl.
     rewrite plus_zero.

     rewrite <- IHb.
     destruct (bin_to_nat b').
     { simpl. reflexivity. }
     { simpl.  
       rewrite nomalizing_incr.
       rewrite nat_to_bin_one_more_twice.
       simpl.
       reflexivity.
     }
   }
   {
      simpl.
      rewrite plus_zero.
      rewrite <- IHb.
      rewrite one_more_twice_nat_to_bin_2.
      reflexivity.
   }
   
Qed.


Print nat_to_bin_reverse.
