(*  Exercises for chapter 7 Inductively Defined Propositions *)



Require  Common.


Import Common.Common.


Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition double(x : nat) := x + x.

Theorem plus_succ_1 : forall (x y : nat),
    S (y + x) = y + S x.
Proof.
  intros x y  .
  induction y.
  simpl.
  reflexivity.
  simpl.
  rewrite IHy.
  reflexivity.
Qed.

Theorem plus_conv : forall (x y : nat),
    x + y = y + x.
Proof.
  induction x.
  induction y.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHy.
  simpl.
  reflexivity.
  simpl.
  intros y.
  rewrite IHx.
  simpl.
  rewrite plus_succ_1.
  reflexivity.
Qed.

Theorem ev_double : forall n,
    ev (double n).
Proof.
   intros n.
   induction n.
   unfold double.
   simpl.
   apply ev_0.
   unfold double.
   unfold double in IHn.
   replace (S n + S n) with (S (S (n + n))).
   apply ev_SS.
   apply IHn.
   simpl.
   rewrite plus_succ_1.
   reflexivity.
Qed.


Compute pred 1.

Theorem ev_minus2 : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  simpl.
  apply ev_0.
  simpl.
  apply E'.
Qed.

Theorem SSSSev_even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n.
  intros H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  simpl.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.


Lemma dist_sum1 : forall n k : nat,
    S (n + k) = (S n) + k.
Proof.
  intros n k.
  simpl.  
  reflexivity.
Qed.

Lemma dist_sum2 : forall n k : nat,
    S (n + k) =  n + (S k).
Proof.
  intros n k.
  induction n .
  induction k.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  rewrite <- dist_sum1.
  rewrite IHn.
  simpl.
  reflexivity.
Qed.


Lemma plus_comm : forall a b : nat,
    a + b = b + a.
Proof.
  intros a b.
  induction a.
  induction b.
  reflexivity.
  simpl.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  destruct b.
  simpl.
  reflexivity.
  simpl in IHb.
  rewrite IHb.
  reflexivity.
  rewrite <- dist_sum1.
  rewrite IHa.
  simpl.
  rewrite dist_sum2.
  reflexivity.
Qed.

Lemma ev_even_firsttry : forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n H1.
  inversion H1 as [| n' E'].
  exists 0.
  reflexivity.

  assert (I : (exists k', n' = double k') ->
              (exists k, S (S n') = double k)).
  { intros [k' Hk'].   rewrite Hk'. exists (S k'). unfold double.
    rewrite dist_sum1. rewrite dist_sum2. simpl. reflexivity. }
  apply I.
  (*????????*)
  (* this is just an exploration, the solution is in the following
     theorem  *)
Admitted.

Lemma ev_even : forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - exists 0. unfold double. simpl. reflexivity.
  - destruct IH as [k' Hk'].
    rewrite Hk'.
    exists(S k').
    unfold double.
    rewrite <- dist_sum2.
    replace (S k' + k') with (k' + S k').
    rewrite <- dist_sum2.

    reflexivity.
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem ev_even_iff : forall n,
    ev n <-> exists k, n = double k.
Proof.
  intros n.
  split.
  apply ev_even.
  intros [k Hk].
  rewrite Hk.
  apply ev_double.
Qed.


Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).  Proof.  intros n m.  intros H1.  intros H2.  induction H1.  induction H2.  simpl.  apply ev_0.  simpl.  apply ev_SS.  apply H2.  simpl.  apply ev_SS.  apply IHev.  Qed.


Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  intros H1.
  induction H1.
  apply ev_0.
  apply ev_SS.
  apply ev_0.
  apply ev_sum.
  apply IHev'1.
  apply IHev'2.
  (* Second *)
  intros H2.
  induction H2.
  apply ev'_0.
  replace (S (S n)) with (n + 2).
  apply ev'_sum.
  apply IHev.
  apply ev'_2.
  apply plus_comm.
Qed.




Theorem ev_ev__ev : forall n m,
    ev (n+m) -> ev n ->  ev m.
Proof.
  intros n m.
  intros H.
  intros H2.
  induction H2.
  unfold plus in H.
  apply H.
  simpl in H.
  apply IHev.
  inversion H.  
  apply H1.
Qed.

Check ev_sum.


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



Theorem ev_plus_plus : forall n m p,
    ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p.
  intros H1 H2.
  assert (H : ev((n+m) + (n + p))).
  
  apply ev_sum.
  apply H1.
  apply H2.
  replace (n + m + (n + p)) with ((n + n) + (m + p)) in H.
  apply ev_ev__ev with (m := (m+p)) in H.
  apply H.
  replace (n + n + (m + p) + (m + p)) with (n + n + ((m + p) + (m + p))).
  apply ev_sum with (n := n+n) .
  apply ev_double.
  apply ev_double.
  rewrite plus_assoc.
  reflexivity.
  rewrite plus_assoc.

  rewrite <-plus_assoc.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  replace (m + (n + p)) with (n + (m + p)).
  reflexivity.
  rewrite plus_assoc.
  rewrite plus_assoc.
  replace (m + n) with (n + m).
  reflexivity.
  rewrite plus_comm.
  reflexivity.
Qed.

Inductive le : nat -> nat -> Prop :=
    | le_n : forall n, le n n
    | le_S : forall n m, (le n m) -> (le n (S m)).


Theorem test_le_2 :
  le 3 6.
Proof.
  apply le_S.
  apply le_S.  
  apply le_S.
  apply le_n.  
Qed.

Lemma le_zero : forall m, (le 0 m).
Proof.
  intros m.
  induction m.
  apply le_n.
  apply le_S.
  apply IHm.
Qed.

     
Lemma le_trans : forall m n o, (le m n) -> (le n o) -> (le m o).
Proof.
   intros m n o.
   intros H1 H2.
   induction H2.

   apply H1.
   apply le_S.
   apply IHle.
   apply H1.
Qed.

Lemma le_suc : forall m n, (le (S m) n) -> (le m n).
Proof.
   intros m n.
   intros H1.
   assert (HLT: (le m (S m))).
   apply le_S.      
   apply le_n.
   apply le_trans with (n := (S m)).
   apply le_S.
   apply le_n.
   apply H1.
Qed.

Theorem zero_le_n : forall n,
    le 0 n.
Proof.
  apply le_zero.
Qed.

Theorem n_le_m___Sn_le_Sm : forall n m,
    (le n m) -> (le (S n) (S m)).
Proof.
  intros n m.
  intros H.
  induction H.
  apply le_n.  
  apply le_S.
  apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
    le (S n) (S m) -> (le n m).
Proof.
  intros n m.
  intros H.

  inversion H.
  apply le_n.
  apply le_suc.
  apply H2.
Qed.

Theorem plus_zero_nn : forall a ,
     a = (a + 0).
Proof.
  intros a.
  replace (a + 0) with (0 + a).
  simpl.
  reflexivity.
  apply plus_comm.
Qed.  

Theorem le_plus_l : forall a b,
    (le a (a + b)).
Proof.
  intros a b.
  induction b.
  replace (a + 0) with a.
  apply le_n.

  apply plus_zero_nn.
  replace (a + S b) with (S (a + b)).
  apply le_S.

  apply IHb.
  simpl.
  replace (a + S b) with (1 + (a + b)).
  simpl.
  reflexivity.
  rewrite plus_comm.
  
  replace (S b) with (b + 1).
  rewrite  plus_assoc.
  reflexivity.
  rewrite plus_comm.
  simpl.
  reflexivity.
Qed.

Definition lt (n m:nat) := le (S n) m.

Theorem plus_lt : forall n_1 n_2 m,
    (lt (n_1 + n_2) m) ->
    (lt n_1  m) /\ (lt n_2  m).
Proof.
  intros n_1 n_2 m.
  intros H1.
  split.
  unfold lt.
  unfold lt in H1.
  replace (S (n_1 + n_2)) with ((S n_1) + n_2) in H1.
  assert (HP:(le (S n_1) ((S n_1) + n_2))).
  apply le_plus_l.
  apply le_trans with (n:=(S n_1 + n_2)).
  apply le_plus_l.
  apply H1.

  replace (S (n_1 + n_2)) with (1 + (n_1 + n_2) ).
  rewrite plus_assoc.
  simpl.
  reflexivity.
  
  simpl.

  reflexivity.
  

  (* Now the right side of the `and`  *)

  unfold lt.
  unfold lt in H1.
  replace (S (n_1 + n_2)) with ( n_1 + (S n_2)) in H1.
  assert (HP:(le (S n_2) (n_1 + (S n_2)))).
  rewrite plus_comm.  
  apply le_plus_l.
  apply le_trans with (n:=( n_1 + S n_2)).
  rewrite plus_comm.
  apply le_plus_l.
  apply H1.

  replace  (S n_2) with (n_2 + 1).
  
  rewrite plus_assoc.
  rewrite plus_comm.
  simpl.

  reflexivity.
  rewrite plus_comm.
  simpl.
  reflexivity.
Qed.  

Theorem lt_S : forall n m,
    (lt n  m) ->
    (lt n  (S m)).
Proof.
  intros n m.
  unfold lt.
  intros H.
  induction H.
  apply le_S.
  apply le_n.
  apply le_S.
  apply IHle.
Qed.


(*

 Theorem leb_trans : forall n m,
      leb n m = true -> leb n (S m) = true.
Proof.
  intros  n m H.
  induction  n.
  reflexivity.    
  simpl.  
    
Theorem leb_complete : forall m n,
    leb n m = true -> (le n m). 
Proof.
  intros m n H.
  induction n.
  apply le_zero.
  assert (H2: leb n m = true).
  simpl in H.
  destruct m.
  inversion H.

  simpl.
  *)
