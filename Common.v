Module Common.

  Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

  (*
  Inductive list {X : Type} : Type :=
  | nil : list 
  | cons :  X -> list  -> list .
*)


  Fixpoint evenb (n:nat) : bool :=
     match n with
     | O => true
     | S O => false
     | S (S num) => evenb num
   end.

  Definition oddb (n:nat) : bool :=
     negb (evenb n).

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

Fixpoint app {X : Type} (l1 l2 : list X)
  : (list X) :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app t l2)
  end.


Fixpoint rev {X:Type} (l:(list X)) : (list X)  :=
  match l with
  | nil _   =>  nil  X
  | cons _ h t => app (rev t) (cons X h (nil X))
  end.


  Notation "x :: l" := (cons _ x l)
                     (at level 60, right associativity).
  Notation "[ ]" := (nil _).
  Notation "[ x ; .. ; y ]" := (cons _ x .. (cons _ y (nil _) ) ..).
  Notation "x ++ y" := (app x y)
                         (right associativity, at level 60).

  Check app [1;2] [3;4].

Lemma concat_append : forall X : Type, forall e : X, forall l : list X,
   cons _ e l = [e] ++ l.
Proof.
  intros X e l.
  simpl.
  reflexivity.
Qed.

Theorem app_nil_r : forall (X:Type), forall l:(list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.


Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| l' IHl' ].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHIHl'.
    reflexivity.
  }

Qed.


Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1.
  {
    simpl.
    rewrite app_nil_r.
    reflexivity.
  }
  {
    simpl.
    rewrite IHl1.
    simpl.
    rewrite app_assoc.
    reflexivity.
  }

Qed.



Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  induction l.
  { reflexivity. }
  { rewrite <- IHl.
    rewrite concat_append.
    rewrite rev_app_distr.
    rewrite IHl.
    rewrite rev_app_distr.
    rewrite IHl.
    simpl.
    reflexivity.
    }


Qed.


(* Common numeric functions *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
   intros n m.
   induction n as [| n' IHn' ].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.


(* Taken from chapter 2 *)
Theorem plus_n_Sm2 : forall n m : nat,
  S (n + m) = (S n) + m.
Proof.
   intros n m.
   induction n as [| n' IHn' ].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.


Fixpoint nth_error {X : Type} (l : list X) (n : nat)
  : option X :=
  match l with
  | [] => None
  | a :: l' => if (beq_nat n 0) then Some a else nth_error l' (pred n)
  end.


Fixpoint length {X : Type } (l : list X) : nat :=
  match l with
  | [] => 0
  | h :: t => S (length t)
  end.


Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split { X Y : Type } (l : list (X*Y) )
  : (list X) * (list Y) :=
  match l with
  |  nil _ => (nil _, nil _)
  |  ((x,y) :: rest) =>  match (split rest) with
                         |  (x2,y2) => ((x::x2), (y::y2))
                         end

  end.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then  h :: (filter test t)
               else filter test t
  end.


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


Fixpoint map {X Y:Type} (f : X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.



End Common.
  
