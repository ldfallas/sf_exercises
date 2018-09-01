(*  Exercises for chapter 5 Tactics *)



Require  Common.

(* Very important novice mistake,
   we need an import for the .vo file and
   one import for the module define in this file
   for this case both are named 'Common'*)

(* REMEMBER
   In order to import the definitions we must
   first compile the imported module using:

     coqc Common.v

   This is going to generate a .vo file which
   is required to do the `Require`
 *)

Import Common.Common.


Theorem silly1 : forall (n m o p : nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem silly1_2 : forall (n m o p : nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.

Qed.


Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. 

(*  rewrite eq1.
  rewrite eq2.  --- error
*)
Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros e1 e2.
  apply e1.
  apply e2.
Qed.


Theorem silly3_firsttry : forall (n : nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n h.
  simpl.
  symmetry.
  apply h. 

Qed.


Theorem rev_exercise1 : forall (l l'  : list nat),
    l = rev l' ->
    l' = rev l.
Proof.
  intros a b c.
  symmetry.
  rewrite c.
  apply rev_involutive.
Qed.


Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.


Example trans_eq_example' : forall(a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise : forall( n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  symmetry.

  apply trans_eq with (m := m).
  symmetry. apply eq1.
  symmetry. apply eq2.
Qed.

Example inversion_ex3 :forall (X:Type) (x y z: X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros x y z l j h1 h2 h3.
  inversion h3.
  reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
    beq_nat 0 n = true -> n = 0.
Proof.
  intros n.  
  destruct n as [| n'].
  reflexivity.
  simpl.
  intros H.
  inversion H.
Qed.

Theorem inversion_ex4 : forall (n : nat),
    S n = 0 ->
    2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.


Example inversion_ex6 : forall ( X : Type)
                               ( x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros X x y z l j h1.
  inversion h1.
Qed.




(* Some utility definitions 
   to help me understand `inversion` 
 *)

Inductive my_func :=
| PrintFunc
| ExitFunc.

Inductive my_flag :=
| ActiveFlag
| InactiveFlag.


Inductive my_stat :=
| MyCall : my_func -> my_stat
| MyBlock : (list my_stat) -> my_stat
| MyConditional : my_flag -> my_stat -> my_stat -> my_stat.

Check MyBlock [(MyCall PrintFunc);
                 (MyConditional
                    ActiveFlag
                    (MyCall PrintFunc)
                    (MyCall ExitFunc)
              )].
                              

Theorem invoked_tested : forall (x y : my_func) (f : my_flag) (e : my_stat),
    (MyConditional ActiveFlag  (MyCall x) e) = (MyConditional ActiveFlag (MyCall y) e) -> x = y.
Proof.
  intros x y f e H1.
  inversion H1.
  reflexivity.
Qed.

Inductive my_option {X:Type} : Type :=
| my_some : X -> my_option
| my_none : my_option.

Fixpoint invoked_function (stat : my_stat) : (my_option ) :=
  match stat with
  | MyCall func => my_some func
  | MyBlock _ => my_none (* Don't know if you can create 
                            mutually recursive function *)
  | MyConditional ActiveFlag then_stat _ => invoked_function then_stat| MyConditional InactiveFlag _ else_stat  => invoked_function else_stat
  end.


Theorem invoked_active : forall (x : my_flag) (s1 s2 : my_stat),
    x = ActiveFlag ->
       invoked_function (MyConditional x s1 s2) = invoked_function  s1.
Proof.
  intros x s1 s2 H1.
(*  
  rewrite H1.
  simpl.
  reflexivity. *)
  inversion H1.
  reflexivity.
Qed.


Theorem silly3 : forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.


Theorem plus_n_n_eq_zero : forall n : nat,
    n + n = 0 -> n = 0.
Proof.
  intros n.
  induction n.
  {
    simpl.
    intros H1.
    reflexivity.
  }
  {
    intros H1.
    inversion H1.
    
  }
Qed.  


Theorem plus_n_n_injective1 : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n.
  induction n as [| n' ].
  {
    simpl .
    intros m H.
    symmetry.
    rewrite H.
    destruct m.
    - reflexivity.
    - inversion H.
  }
  {
    intros m H2.

    induction m.
    {
      inversion H2.

    }
    {
      inversion H2.
      rewrite <- plus_n_Sm in H0.
      rewrite <- plus_n_Sm in H0.
      inversion H0.

      apply IHn' in H1.
      rewrite H1.

      reflexivity.
    }
  }
Qed.


Definition double(x : nat) := x + x.

Compute double(10).

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y : A),
    x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
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

(* need to go back to "Varying the Induction Hypothesis"  *)
Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
    length l = n -> nth_error l n = None.
Proof.
  intros n t l h1.
  generalize dependent n.
  induction l.
  {
    simpl.
    reflexivity.
  }
  {
    intros n h2.
    simpl in h2.
    symmetry in h2.
    rewrite h2.
    simpl.
    rewrite IHl.
    reflexivity.
    reflexivity.
}
Qed.


(* **********************  *)


Definition square n := n * n.

Compute square 2.

(* destruct on compounds *)

(*
Theorem  combine_split : forall X Y (l : list (X * Y)) l1 l2,
     split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  intros X Y l l1 l2.
  intros P.

  induction l.
  {
    simpl.
    inversion P.
    simpl.
    reflexivity.
  }
  {
    inversion P.

    apply IHl.
    rewrite <- H0.
    rewrite <-   P in H0.
  }
  
  

  simpl in P.
   
Qed.
 p
 *)

Theorem  combine_parts : forall X Y (l : list (X * Y)) l1 l2 (v : (X * Y)) (x1 : X) (y1 : Y),
    (v :: l) = combine (x1 :: l1) (y1 :: l2) ->
    (v :: l) = (x1 , y1) :: (combine l1 l2).
Proof.
  intros xt yt lt l1t l2t vt x1t y1t.
  simpl.
  intros H.
  apply H.

Qed.

Theorem  combine_parts2 : forall X Y (l : list (X * Y)) l1 l2 (v : (X * Y)) (x1 : X) (y1 : Y),
    (v :: l) = (x1 , y1) :: (combine l1 l2) ->
    (v :: l) = combine (x1 :: l1) (y1 :: l2) .

Proof.
  intros xt yt lt l1t l2t vt x1t y1t.
  simpl.
  intros H.
  apply H.

Qed.



Compute split [(1,2)].
Compute split ([] : list(nat * nat)).
Compute combine ([] : list(nat)) ([] : list( nat)).

(*
Lemma split_empty : forall X Y (l : list (X * Y)) o,
    split l = ([], o) -> l = [].
Proof.
  intros X Y l o.
  
 
  induction l.
 
  { reflexivity. }
  { intros H. inversion H.
    re
  simpl.

  

  
Qed.
*)

Definition left { X Y :Type } (t : (X*Y)) :=
  match t with
  | (x, _) => x
  end.

Definition right { X Y :Type } (t : (X*Y)) :=
  match t with
  | (_, x) => x
  end.

Lemma split_parts2 : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1 ,l2) -> l2 = right (split l).
Proof.
  intros X Y l l1 l2 H .
  rewrite H.

  reflexivity.
Qed.

Lemma split_cons : forall X Y (l : list (X * Y))  (x : (X*Y)),
    split (((left x), (right x)) :: l) = (((left x)::(left (split l))), ((right x)::(right (split l)))).
Proof.
  intros X Y l x.
  simpl.

  destruct (split l).
  - simpl. reflexivity.
Qed.


Lemma split_parts : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1 ,l2) -> l1 = left (split l).
Proof.
  intros X Y l l1 l2.
  induction l.
  {
    simpl.
    intros H.
    inversion H.
    reflexivity.
  }
  {
    intros H.
    rewrite H.
    simpl.
    reflexivity.
  }  
Qed.
(*
Theorem combine_uni : forall X Y (l : list (X * Y)) (x : X) (y : Y),
    combine (left (split l)) (right (split l)) = l.
Proof.
  intros X Y l x y.
  induction l.
  { simpl.
    reflexivity.
  }
  {
    destruct  (x0 :: l).
    - simpl. reflexivity.
    - simpl.
    unfold combine.
    unfold right.
    unfold left.
     simpl.    
  }
  
 *)

Lemma pairs_left_right : forall X Y (x : (X*Y)),
    x = (left x, right x).
Proof.
  intros X Y x.
  destruct x.
  - simpl. reflexivity.
Qed.

    

Theorem  combine_split : forall X Y (l : list (X * Y)) l1 l2,
     split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  intros X Y l l1 l2.
  generalize dependent l1.
  generalize dependent l2.

  induction l.
  {
    simpl.
    intros H H2 H3.
    inversion H3.
    simpl.
    reflexivity.
  }
  {
    intros l2 l1.
    intros H.
    assert(HRight : l2 = right (split (x::l))).
    {
      apply split_parts2  in H.
      apply H.
    }
    assert(HLeft : l1 = left (split (x::l))).
    {
      apply split_parts  in H.
      apply H.
    }

    rewrite HRight.
    rewrite HLeft.

    assert (HLR : x = ((left x),(right x))).
    {
      simpl.
      destruct x.
      - simpl. reflexivity.
    }

    rewrite HLR.
    rewrite split_cons.

    simpl.

    rewrite IHl.
    reflexivity.


    rewrite <-  pairs_left_right.

    reflexivity.

    }
Qed.

Theorem i_f : forall ( f: bool -> bool) ( x  y: bool),
    x = y -> f x = f y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.  

Theorem bool_fn_applied_thrice :
  forall(f : bool -> bool) ( b : bool ) ,
  f( f ( f b)) = f b.
Proof.
  intros.

  destruct b eqn:H1.
  destruct (f true) eqn:H2.
  rewrite H2.
  rewrite H2.
  reflexivity.
  destruct (f false) eqn:H3.
  rewrite H2.
  reflexivity.
  rewrite H3.
  reflexivity.
  destruct (f false) eqn:H4.
  destruct (f true) eqn:H5.
  rewrite H5.
  reflexivity.
  rewrite H4.
  reflexivity.
  rewrite H4.
  rewrite H4.
  reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
    beq_nat n m = beq_nat m n.
Proof.
  induction n .
  {
    intros m.
    induction m.
    {
      reflexivity.
    }
    {
      simpl.
      reflexivity.
    }
  }
  {
    intros m.
    induction m.
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      apply IHn.
    }
    

  }
Qed.

Theorem beq_nat_trans : forall n m p,
    beq_nat n m = true ->
    beq_nat m p = true ->
    beq_nat n p = true.
Proof.
  intros n m p H H2.

  rewrite beq_nat_sym in H.
  assert (H3 : n = m).
  apply beq_nat_true.
  rewrite beq_nat_sym in H.
  rewrite <- H.
  reflexivity.
  rewrite H3.
  apply H2.
Qed.

Compute length [1;2;3].

Definition split_combine_statement : Prop :=
  forall X Y (l1 : list(X)) (l2 : list(Y)),
     length l1 = length l2 ->
     split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y .
  induction l1.
  {
    intros l2.
    simpl.
    destruct l2.
    - simpl. reflexivity.
    - simpl. intros H2. inversion H2.   
   }
  {
    intros l2.
    intros H2.
    simpl in H2.

    destruct l2.
    - simpl. inversion H2.
    - simpl in H2. simpl. rewrite IHl1. reflexivity.
      inversion H2.
      reflexivity.

  }
  
Qed.

(*
Lemma filter_append : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf l3 l4 : list X),
    filter test (app l3 app([x] l4))  = x :: lf -> test x = true.
Proof.
Qed.
*)

Theorem filter_excercise : forall (X : Type) (test : X -> bool)
                                  (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l lf.


  induction l.
  {
    simpl.

    intros  H.
    inversion H.
  }
  {
    simpl.
    intros H4.
    assert ((test x0 = true) -> (x0 = x)).
    intros H3.
    rewrite H3 in H4.
    inversion H4.
    reflexivity.

    destruct (test x0) eqn: HD.
    {
      simpl in  H.
      inversion H4.
      rewrite <- H1.
      rewrite HD.
      reflexivity.
    }    
    {

      inversion H4.

      apply IHl.
      apply H1.
    }
  }
    
Qed.


Theorem filter_excercise_2 : forall (X : Type) (test : X -> bool)
                                  (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l lf.


  induction l.
  {
    simpl.

    intros  H.
    inversion H.
  }
  {
    simpl.
    intros H4.

    destruct (test x0) eqn: HD.
    {
      inversion H4.
      rewrite <- H0.
      rewrite HD.
      reflexivity.
    }    
    {
      inversion H4.
      apply IHl.
      apply H0.
    }
  }
    
Qed.



Fixpoint forallb  { X  :Type } (f : X -> bool) (l : list X) :=
  match l with
  | (x::r) => andb (f x) (forallb f r)
  | _ => true
  end.

Compute (forallb oddb [1;2;3]).
Compute (forallb oddb [11;23;3]).
Compute (forallb negb [false;false]).

Fixpoint existsb  { X  :Type } (f : X -> bool) (l : list X) :=
  match l with
  | (x::r) => orb (f x) (existsb f r)
  | _ => false
  end.

Compute (existsb  (beq_nat 5)  [1;2;3]).
Compute (existsb (andb true) [true;true;false]).
Compute (existsb oddb [1;0;0;0;0;3] ).

Definition existsb' { X  :Type } (f : X -> bool) (l : list X) :=
  negb (forallb (fun k => negb (f k)) l). 


Compute (existsb'  (beq_nat 5)  [1;2;3]).
Compute (existsb' (andb true) [true;true;false]).
Compute (existsb' oddb [1;0;0;0;0;3] ).

Theorem existsb_existsb' : forall (X : Type) (l : list X) (f : X -> bool),
    existsb' f l = existsb f l.
Proof.
  intros X l f.
  induction l.
  {
    simpl.
    unfold existsb'.
    unfold forallb.
    simpl.
    reflexivity.    
  }
  {

    unfold existsb'.
(*    unfold existsb.*)
    destruct (f x) eqn: H2.
    { simpl.
      rewrite H2.
      simpl.
      reflexivity.
    }
    {
      simpl.
      rewrite H2.
      simpl.
      unfold existsb' in IHl.
      apply IHl.
      
    }
    
     
  }
  
Qed.  




