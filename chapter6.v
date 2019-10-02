(*  Exercises for chapter 6 Logical Connectives *)



Require  Common.


Import Common.Common.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  reflexivity.
  reflexivity.
Qed.

Lemma and_intro : forall (A B : Prop),
    A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_excercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m.
  induction n.
  {
    simpl.
    simpl.
    intros H.
    split.
    reflexivity.
    apply H.
  }
  {
    simpl.
    intros H.
    inversion H.
  }
Qed.


Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [H1 H2].
  apply H2.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
    
Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.


(* DISJUNCTION *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B.
  intros HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(*
Lemma mult_times_one : forall n : nat,
    1 * n  = n.
Proof.
  intros n.
  simpl.
  *)


Lemma mult_times_zero : forall n : nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_zero : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite  IHn. reflexivity.
Qed.    

Lemma plus_prefix1 :
  forall a b c, a + b = a + c -> b = c.
Proof.
  intros a b c.
  intros H.
  induction a.
  - simpl in H. apply H.
  - inversion H. apply IHa.  apply H1.
Qed.

Lemma zero_suc_1 :
  forall m : nat, m + m = m -> m = 0.
Proof.
  intros m .
  assert (H : m = m + 0).
  rewrite plus_zero.
  reflexivity.
  
  rewrite  H.
  assert (H2 : m + 0 + (m + 0) = m + m).
  rewrite plus_zero. reflexivity.
  rewrite  H2.
  intros H3.
  apply plus_prefix1 in H3.
  rewrite H3.
  reflexivity.
Qed.
   

Lemma mult_plus_zero1 :
  forall n,
      n = 0 -> n + n = 0.
Proof.
  intros n H.
  rewrite -> H.
  simpl.
  reflexivity.
Qed.

Lemma mult_plus_zero2 :
  forall n,
      n + n = 0 -> n = 0.
Proof.
  intros n H.
  induction n.
  - reflexivity.
  - inversion H.
Qed.



Lemma mult_plus_zero2multi :
  forall n m,
      n + n = 0 -> ( m * n ) = 0.
Proof.
  intros n m.

  intros H.
  assert (H2: n = 0).
  apply mult_plus_zero2 in H.
  apply H.
  
  rewrite  H2.
  apply mult_times_zero.
Qed.

Lemma and_example_2 :
  forall n m,
    n = 0 /\ m = 0 -> n + m = 0 .
Proof.
  intros n m.
  intros H.
  destruct H as [Hn Hm].
  rewrite  Hn. rewrite  Hm.
  simpl.
  reflexivity.
Qed.


Lemma mult_succ :
  forall n m,
    (S n) * m = 0 -> m = 0.
Proof.
  intros n m.

  intros H.

  simpl in H.


  apply and_excercise in H.

  apply H.
Qed.




    

Lemma mult_eq_0 :
  forall n m, n * m  = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.

  destruct n.
  - simpl. left. reflexivity.
  - apply mult_succ in H. right. apply H.
Qed.

Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q.
  intros [Hl | Hr].
  - right. apply Hl.
  - left . apply Hr.
Qed.

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem not_Fals :
  ~ False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.


Theorem contrapositive : forall (P Q :Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.  
  intros H2.
  intros P2.
  apply H2.
  apply H.
  apply P2.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros [H1 H2].
  apply H2.
  apply H1.
Qed.


Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB.
Qed.

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma not_true_iff_false : forall b,
    b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros  H.
    rewrite H.
    intros H'.
    inversion H'.
Qed.

Theorem iff_refl : forall P : Prop,
    P <-> P.
Proof.
  intros P .
  split.
  intros P'.
  apply P'.
  intros P'.
  apply P'.
Qed.


Theorem iff_trans : forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros H1.
  intros H2.
  split.
  intros P'.
  apply H2.
  apply H1.
  apply P'.
  intros R'.
  apply H1.
  apply H2.
  apply R'.
 
Qed.



Lemma or_not1 : forall P Q : Prop,
    ~P /\ (P \/ Q) -> Q.
Proof.
  intros P Q.
  intros [H1 [H21|H22]].
  unfold not in H1.
  
  exfalso.
  apply H1.
  apply H21.
  apply H22.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  intros [H12 | H13].
  - split.
    left.
    apply H12.
    left.
    apply H12.
  - destruct H13 as [H41 H42].
    split.
    right.
    apply H41.
    right.
    apply H42.
  - intros [[H511|H512] [H521|H522]].
    left.
    apply H511.
    left.
    apply H511.
    left.
    apply H521.
    right.
    split.
    apply H512.
    apply H522.
Qed.

Fact not_implies_our_not : forall (P:Prop),
    ~ P -> (forall(Q:Prop), P -> Q).
Proof. 
  intros P Hp2 Q HP.
  unfold not in Hp2.
  exfalso.
  apply Hp2.
  apply HP.
Qed.

Theorem transitive_impl : forall (P Q R : Prop),
    ((P -> Q) /\ (Q -> R)) -> (P -> R).
Proof.
  intros P Q R [H1 H2] H3.
  assert Q.
  apply H1.
  apply H3.
  apply H2.
  apply H.
Qed.

Theorem contrapositive' : forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2.
  unfold not in H2.
  unfold not.
  intros P2.
  apply H2.
  apply H1.
  apply P2.
Qed.  

Theorem not_both_true_and_false' : forall P : Prop,
    ~(P /\ ~P).
Proof.
   intros P.  
   unfold not.    

   intros [H2 H3].
   apply H3.
   apply H2.
Qed.


Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P.
  intros FA.
  unfold not.
  intros  [x Hx].
  apply Hx.
  apply FA.
Qed.


Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  intros [x1 [Hx1|Hx2]].
  left.
  exists x1.  
  apply Hx1.

  right.
  exists x1.
  apply Hx2.

  intros  [[x H31]|[x H32]].
  exists x.
  left.

  apply H31.

  exists x.

  right.

  apply H32.
Qed.


Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1;2;3;4;5].
Proof.
   simpl.
   right.
   right.
   right.
   left.
   reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n.
  intros [H1 | [H2|H3]].
  exists 1. rewrite <- H1. simpl. reflexivity.
  exists 2. simpl.  rewrite H2. reflexivity.
  inversion H3.
Qed.

Lemma In_map :
  forall(A B :Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x .
  induction l as [].
  - simpl. intros H. inversion H.
  - simpl. intros [H1|H2]. left. rewrite H1. reflexivity.
    right. apply IHl. apply H2.
Qed.


Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l)  <-> exists x, f x = y /\ In x l .
Proof.
  intros A B f l y.
  split.
  
  induction l.
  - simpl. intros H. inversion H.
  - simpl. intros [H1|H2]. exists x. split. apply H1. left. reflexivity.
    apply IHl in H2. 
    destruct H2 as [x' [X1' X2']].
    exists x'.
    split.
    apply X1'.
    right.
    apply X2'.
  -
    

  
    
  intros [x [X1 X2]].
  rewrite <- X1.
  apply In_map.
  apply X2.


Qed.



Lemma append_null : forall  A (l : list A) , 
  l ++ [ ] = l.
Proof.
  intros A l.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma or_assoc : forall P K V:Prop,
    (P \/ K) \/ V <-> P \/ (K \/ V).
Proof.
  intros P K V.
  split.
  intros [[H1|H2]|H3].
  left.
  apply H1.
  right.
  left.
  apply H2.
  right.
  right.
  apply H3.
  intros [H1|[H2|H3]].
  left.
  left.
  apply H1.
  left.
  right.
  apply H2.
  right.
  
  apply H3.  
  
Qed.  


Require Import Coq.Setoids.Setoid.

Lemma app_empty : forall (A : Type) (l : list A) ,
    l ++ [] = l.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma in_app_if_1 : forall A l l' (a:A),
    In a l -> In a (l ++ l').
Proof.  
  intros A l l' a.
  intros H1.
  induction l.  
  simpl in H1.
  inversion H1.

  simpl.
  simpl in H1.
  destruct H1 as [H3|H4].
  left.
  apply H3.
  right.
  apply IHl.
  apply H4.
Qed.
   
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  intros H.
  induction l.
  induction l'.

  simpl in H.
  inversion H.
  simpl in H.
  simpl.
  right.
  apply H.
  simpl.
  simpl in H.
  destruct H.
  left. left.
  apply H.
  simpl in H.
  apply or_assoc.
  right.
  apply IHl.
  apply H.


  intros [H1|H2].
  destruct l.
  simpl in H1.
  inversion H1.
  simpl.
  simpl in H1.
  destruct H1.
  left.
  apply H.
  right.
  induction l.
  simpl in H.
  inversion H.
  simpl.
  simpl in H.
  destruct H.
  left.
  apply H.
  right.
  apply IHl.
  apply H.
  induction l.
  simpl.
  apply H2.
  simpl.
  right.
  apply IHl.
Qed.


Fixpoint All { T : Type } (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => (P x') /\ (All P l')
  end.

Compute (All (fun x => In x [1;2;3]) [3;2;1;1]).
Compute All (fun x => In x [1;2;3]) [3;24;1;1].

Lemma  All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  intros H.
  induction l.
  simpl.
  reflexivity.
  simpl.
  split.
  apply H.
  simpl.
  left.
  reflexivity.
  apply IHl.
  intros H3.
  intros H4.
  apply H.
  simpl.
  right.
  apply H4.

  intros H5.
  intros x.
  induction l.
  simpl.
  intros H6.
  inversion H6.
  simpl.
  intros [H7|H8].
  simpl in H5.
  destruct H5.
  rewrite <- H7.
  apply H.
  apply IHl.
  simpl in H5.
  destruct H5.
  apply H0.

  apply H8.
Qed.


Definition combine_odd_even (Podd Peven : nat -> Prop) :
  nat -> Prop :=
  (fun x => if (oddb x) then (Podd x) else (Peven x)).

Check combine_odd_even.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.

Proof.
  intros Podd Peven n.
  intros H1 H2.
  induction n.
  unfold combine_odd_even.
  unfold oddb.           
  simpl.              
  apply H2.
  unfold oddb.
  unfold evenb.
  simpl.
  reflexivity.

  unfold combine_odd_even.
  destruct (S n) eqn: H4.
  simpl.
  apply H2.
  unfold oddb.
  simpl.
  reflexivity.

  destruct (oddb (S n0)).
  apply H1.
  reflexivity.
  apply H2.
  reflexivity.
Qed.


Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n  .
  unfold combine_odd_even.
  destruct (oddb n) eqn: H1.
  intros H2 H3.
  simpl in H3.
  apply H2.
  intros H3 H4.
  inversion H4.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd  Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
       oddb n = false ->
       Peven n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (oddb n) eqn: H1.
  intros H2 H3.
  simpl in H3.
  inversion H3.
  intros H2 H3.
  
  apply H2.
  
  
Qed.  


Check combine_odd_even_elim_even.

Lemma proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros  P Q [HP HQ].
  apply HP.
Qed.



Example lemma_application_ex :
  forall {n : nat} { ns : list nat },
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
    as [m [Hm _]].
  assert (H3 : m * 0 = 0).
  induction m.
  reflexivity.
  simpl.
  simpl in Hm.
  apply IHm.
  apply Hm.
  rewrite <- Hm .
  rewrite H3.
  reflexivity.
Qed.


Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Check rev_append.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].


Axiom function_extensionality : forall {X Y : Type}
                                       {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.
(*
Lemma tr_rev_append : forall {X : Type} (x:X) (l : list X), tr_rev (x::l)  =  tr_rev l 

 *)(*

Lemma rev_append_prop : forall { X : Type } (x:X) (l : list X),
    rev_append l [x] = rev_append (l ++ [x]) [].
Proof.
  intros X x l.
  simpl.
  induction l.
  - simpl. reflexivity.
  - simpl.
    *)
Lemma rev_append_append : forall { X : Type } (x:X) (l : list X) (l2 : list X),
    rev_append l l2 = (rev_append l []) ++ l2.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl.  simpl. rewrite IHl.  intros l2. rewrite IHl. simpl. rewrite  <- app_assoc. simpl. reflexivity.
Qed. 

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply function_extensionality.
  intros x.
  induction x.
  {  simpl.  unfold tr_rev. simpl. reflexivity. }
  { simpl. unfold tr_rev. simpl. rewrite <- IHx. unfold tr_rev.
    simpl. rewrite rev_append_append. reflexivity.  apply x. }

Qed.

Fixpoint double (n:nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

         


Theorem evenb_double : forall k, evenb( double k)  = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem evenb_exist_double : forall n k,
    (n = double k) -> (evenb n) = true.
Proof.
  intros n k.
  intros H.
  rewrite H.
  apply evenb_double.
Qed.


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

Theorem evenb_double_conv : forall n,
    exists k, n = if evenb n then double k
                  else S (double k).
Proof.
 (* intros n.*)
  induction n.
  - simpl. exists 0. simpl. reflexivity.
  -  rewrite evenb_S. destruct (evenb n). simpl. inversion IHn.  exists x.  rewrite H. reflexivity.
     simpl.
     inversion IHn.
     rewrite  H.
     exists (S x).
     simpl.
     induction x.
     { simpl. reflexivity. }
     { simpl. reflexivity. }

Qed.

Lemma andb_true_iff : forall b1 b2 : bool,
    andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
    split.
    intros H.
    split.
    unfold andb in H.
    destruct b1 eqn: Hq.
    reflexivity.
    inversion H.
    unfold andb in H.
    destruct b1.
    apply H.
    inversion H.
    intros [H2 H3].
    rewrite H2.
    rewrite H3.
    simpl.
    reflexivity.
Qed.


Lemma orb_true_iff : forall b1 b2,
    orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  unfold orb.
  intros H1.
  destruct b1.
  left.
  reflexivity.
  right.
  rewrite H1.
  reflexivity.
  intros [H22|H23].
  rewrite H22.
  simpl.
  reflexivity.
  rewrite H23.
  destruct b1.
  - reflexivity.
  - simpl. reflexivity.
Qed.


Theorem diff_false : forall x : nat,
    ~(~(x = x)).
Proof.
  unfold not.
  intros x  H.
  apply H.
  trivial.
Qed.


Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. (* m H.*)
  induction n.
  {
    intros m H.
    destruct m.
    - reflexivity.
    - inversion H.
  }
  { 
    simpl.
    destruct m.
    {
      simpl. 
      intros H. 
      inversion H.
    }
    {
      simpl. 
      intros H.
      apply f_equal.

      apply IHn.
      apply H.

    }

  }
Qed.

Theorem beq_same : forall x : nat,
    beq_nat x x = true.
Proof.
  intros x.
  induction x.
  - simpl. reflexivity.
  - simpl. apply IHx.
Qed.  

Theorem beq_nat_false_iff : forall x y : nat,
    beq_nat x y = false <-> x <> y.
Proof.
  intros x y.
  unfold not.
  split.
  
  intros H3.
  intros H1.
  rewrite H1 in H3.
  rewrite  beq_same in H3. 
  inversion H3.
  intros H1.
  destruct (beq_nat x y) eqn: Ht1.
  apply beq_nat_true in Ht1.
  destruct H1.
  apply Ht1.
  reflexivity.
Qed.
 
Theorem restricted_excluded_middle : forall P b,
       (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

       

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match l1 with
  | (X::Rest1) =>
    match l2 with
    | (Y::Rest2) => andb (beq X Y) (beq_list beq Rest1 Rest2)
    | [] => false
    end
  | [] =>
    match l2 with
        | [] => true
        | _ => false
     end    
  end.



Fixpoint beq_list2 {A : Type} (beq : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match (l1,l2) with
  | ((X::Rest1),(Y::Rest2)) 
    => andb (beq X Y) (beq_list2 beq Rest1 Rest2)
  | ([],[]) => true
  | _ => false           
  end.


Compute beq_list beq_nat [1;2;3;4] [1;2;3;4].


Compute beq_list beq_nat [1;2;3;4] [1;2;3].

Compute beq_list beq_nat [1;2;3;4] [1;2;33;4].


Lemma list_equality :
  forall A (l1 l2 : list A),
    l1 = l2 -> (l1 = [] /\ l2 = []) \/ (exists a l, l1 = (a::l) /\ l2 = (a::l)). 
Proof.
  intros A l1 l2 H.
  induction l1.
  induction l2.
  left.
  split.
  reflexivity.
  reflexivity.
  inversion H.
  right.  
exists x.  
exists l1.  
split.
reflexivity.
rewrite H.
reflexivity.
Qed.

Lemma list_equality2 :
  forall A (l1 l2 : list A),
     ((l1 = [] /\ l2 = []) \/ (exists a l, l1 = (a::l) /\ l2 = (a::l))) -> l1 = l2 . 
Proof.
  intros A l1 l2.
  intros [[H1 H2]|H3].
  rewrite H1. rewrite H2.
  reflexivity.
  destruct H3.
  destruct H.
  generalize dependent H.
  intros [H5 H6].
  rewrite H5.
  rewrite H6.
  reflexivity.
Qed.

(*
Lemma list_bequality2 :
  forall A (beq : A -> A -> bool)   (l1 l2 : list A),
     ((l1 = [] /\ l2 = []) \/ (exists a l, (beq_list beq l1  (a::l) = true) /\ (beq_list beq l2  (a::l)) = true)) -> beq_list beq l1  l2 = true. 
Proof.
  
Qed.
 *)

Lemma beq_ref :
  forall A (beq : A -> A -> bool)  x, (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
              beq x x = true.
Proof.
  intros A beq x.
  intros H.
  apply H.
  reflexivity.
Qed.

Lemma list_beqlist_ref :
  forall A (beq : A -> A -> bool)   (l1  : list A),
     (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
     beq_list beq l1 l1 = true .
Proof.
  intros A beq l1 H.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite beq_ref.
  simpl.
  apply IHl1.
  apply H.
Qed.


  
Lemma list_bequality2_1 :
  forall A (beq : A -> A -> bool)   (l1 l2 : list A),
     (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
     beq_list beq l1  l2 = true -> ((l1 = [] /\ l2 = []) \/ (exists a l, (beq_list beq l1  (a::l) = true) /\ (beq_list beq l2  (a::l)) = true)). 
Proof.
  intros A beq l1 l2 Hb.
  induction l1.
  induction l2.
  simpl.
  left.
  split.
  reflexivity.
  reflexivity.
  simpl.
  intros H.
  inversion H.
  simpl.
  destruct l2.
  intros HC.
  inversion HC.
  intros HK.
  right.
  exists a.
  exists l2.
  split.
  apply HK.
  simpl.
  rewrite beq_ref.
  simpl.
  apply list_beqlist_ref.
  apply Hb.
    apply Hb.
Qed.



Lemma empty_beq :
    forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l2, beq_list beq [ ] l2 = true <-> [] = l2.
Proof.
  intros A beq H1.
  intros l2.
  destruct l2.
  simpl.
  split.
  reflexivity.
  reflexivity.
  simpl.
  split.
  intros Ht1.
  inversion Ht1.
  intros Ht2.
  inversion Ht2.
Qed.

Definition my_head {A : Type} (l : list A) (default: A) :=
  match l with
  | (t :: Rest) => t
  | _ => default
  end.

Lemma head1_eq :
  forall A (beq : A -> A -> bool) (D : A),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2 a b, beq_list2 beq (a::l1) (b::l2) = true ->
        a = b.
Proof.
  intros A beq D H l1 l2 a b.
  simpl.
  unfold andb.
  destruct (beq a b) eqn: HX1.
  apply H in HX1.
  intros H1.
  apply HX1.
  intros HC.
  inversion HC.
Qed.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H1.
  split.
  generalize dependent l2.
  induction l1.
  simpl.
  destruct l2.
  reflexivity.
  intros HC.
  inversion HC.
  simpl.
  destruct l2.
  intros HC.
  inversion HC.
  destruct (beq x a) eqn: Hbeq.
  apply H1 in Hbeq.
  simpl.
  rewrite Hbeq.
  assert (HR : l1 = l2 -> a :: l1 = a :: l2).
  intro HEq.
  rewrite HEq.
  reflexivity.
  intros Haa.
  apply HR.
  apply IHl1.
  apply Haa.
  simpl.
  intros HC2.
  inversion HC2.
  intros HP.
  rewrite HP.
    apply list_beqlist_ref.
    apply H1.
Qed.

Fixpoint forallb { X : Type } (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  split.
  induction l.
  simpl.
  trivial.
  simpl.
  intro H.
  split.
  destruct (test x) eqn: HTst.
  reflexivity.
  simpl in H.
  inversion H.
  apply IHl.
  destruct (forallb test l) eqn:  HC.
  reflexivity.
  destruct (test x) eqn: HC2.
  simpl in H.
  inversion H.
  simpl in H.
  inversion H.
  induction l.
  simpl.
  reflexivity.
  simpl.
  intros [H1 H2].
  rewrite H1.
  simpl.
  apply IHl.
  apply H2.
Qed.


Definition excluded_middle := forall P : Prop,
    P \/ ~P.


Theorem not_exists_dist :
  excluded_middle ->
  forall ( X: Type) (P : X -> Prop),
  ~(exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.

  intros X.

  intros H2.

  intros H1.

  intros HT1.
  intros x.
  assert (HN: H1 x \/ ~ (H1 x)).
  apply X.
  generalize dependent HN.
  intros [HK1|HK2].
  apply HK1.

  assert (exists y : H2, ~ H1 y).
  exists x.
  apply HK2.

  unfold not in HT1.
  unfold not in H.
  apply HT1 in H.
  inversion H.  
Qed.

(*
Theorem implassoc : forall P Q V : Prop,
    ((P -> Q) -> V) <-> (P -> (Q -> V)).
Proof.
  intros P Q V.
  split.
  intros H1.
  intros P1 Q1.
  apply H1.
  intros H11.
  apply Q1.

  intros H1.
  intros H11.
  apply H1.
*)
Definition peirce := forall P Q : Prop,
                              ((P -> Q) -> P) -> P.

Theorem equiv :
  excluded_middle <-> peirce.
Proof.
   split.
   unfold peirce.
   unfold excluded_middle.
   
   intros Ex.
   intros P Q.
   intros HT.
   assert (HK: P \/ ~P).
   apply Ex.
   generalize dependent HK.
   intros [H1|H2].
   apply H1.
   apply HT.
   intros HK.    
   apply H2 in HT.
   inversion HT.
   intros HN.
   generalize dependent HT.
   apply H2 in HN.
   inversion HN.

   unfold excluded_middle.
   unfold peirce.

   intros HT1.

   intros P.
   left.
(*   assert (HK1 : forall Q : Prop, (( P -> Q) -> P) -> P).*)
   apply HT1 with (Q := P).

   intros H1.
     
