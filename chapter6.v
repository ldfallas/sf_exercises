(*  Exercises for chapter 6 Logical Connectives *)



Require  Common.



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