Module Poly.

  

  Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X  -> list X .

  Inductive list' {X : Type} : Type :=
  | nil' : list' 
  | cons' : X -> list'  -> list' .

  
  Definition head { X : Type } (l:list' ) (default : X) :=
    match l with
    | nil' => default
    | (cons' t _) => t
    end.
  


  Check nil.
  
  (*  Compute (cons nat  1  (nil nat)).*)
  Compute (cons' 1 (cons' 2 nil')).

  Compute (cons' true (cons' false nil')).
  Check (cons' true (cons' false nil')).

  Compute (head (cons' true (cons' false nil')) false).
  Check (head (cons' true (cons' false nil')) false).

  Compute (head (cons' 1 (cons' 2 nil')) (0)).
  Check (head (cons' 1 (cons' 2 nil')) 0).
  Check 1.
  Check (1 + 2).
  Check (head nil' nil').


  (* Taken from the chapter 4 *)

  Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons _ h (app t l2)
  end.

  Check app.

  Fixpoint app' {X : Type} (l1 l2 : list' )
             : (@list' X)  :=
  match l1 with
  | nil'  => l2
  | cons'  h t => cons'  h (app' t l2)
  end.

  Check app'.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil _ => nil _
  | cons _ h t => app (rev t) (cons _ h (nil _))
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons _ 1 (cons _ 2 ( nil _))) = (cons _ 2 (cons _ 1 (nil _))).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons _ true (nil _)) = cons _ true (nil _).
Proof. reflexivity. Qed.

Example test_length1: length (cons _ 1 (cons _ 2 (cons _ 3 (nil _)))) = 3.
Proof. reflexivity. Qed.

Notation "x :: y" := (cons _ x y)
                     (at level 60, right associativity).
Notation "[ ]" := (nil _).
Notation "[ x ; .. ; y ]" := (cons _ x .. (cons _ y []) ..).
Notation "x ++ y" := (app  x y)
                     (at level 60, right associativity).


Check (1 :: nil _).
Check [1;2;3].
Check ([1;2;3] ++ [4;5;6]).


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

Lemma app_length : forall(X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHl1.
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

Lemma concat_append : forall X : Type, forall e : X, forall l : list X,
   cons _ e l = [e] ++ l.
Proof.
  intros X e l.
  simpl.
  reflexivity.
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

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _ .

Notation "( x , y )" := (pair x y).

Check ( 1, true ).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X*Y) : X :=
  match p with
  | (x, y) => x
  end.


Definition snd {X Y : Type} (p : X*Y) : Y :=
  match p with
  | (_, y) => y
  end.


Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.  

Check @combine.
Compute (combine [1;2] [false;false;true;true]).


Fixpoint split { X Y : Type } (l : list (X*Y) )
  : (list X) * (list Y) :=
  match l with
  |  nil _ => (nil _, nil _)
  |  ((x,y) :: rest) =>  match (split rest) with
                         |  (x2,y2) => ((x::x2), (y::y2))
                         end
                           
  end.
  


Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity.
Qed.



(* OPTIONS *)

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

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


Fixpoint nth_error {X : Type} (l : list X) (n : nat)
  : option X :=
  match l with
  | [] => None
  | a :: l' => if (beq_nat n 0) then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [true] 1 = None.      
Proof. reflexivity. Qed.


Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  |  cons _ x _ => Some x
  |  nil _ => None
  end.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof.
  reflexivity.
Qed.



Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then  h :: (filter test t)
               else filter test t
  end.

Fixpoint evenb (n:nat) : bool :=
   match n with
   | O => true
   | S O => false
   | S (S num) => evenb num
   end.

Definition oddb (n:nat) : bool :=
   negb (evenb n).


Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
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


Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (evenb x) (negb (leb x 7))) l.

  
Example test_filter_even_gt7_1 :
      filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
  reflexivity.
Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof.
  reflexivity.
Qed.

Definition partition {X : Type}
           (test : X -> bool)
           (l : list X)
          : list X * list X :=
  ((filter test l), (filter (fun e => negb (test e)) l)).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
  reflexivity.
Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
  reflexivity.
Qed.


(* From the book  *)

Fixpoint map {X Y:Type} (f : X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.


(* Exercise map_ref *) 


Lemma  map_append_relation : forall (X Y : Type)
                                     (f : X -> Y)
                                     (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2.
  induction l1.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHl1.
    reflexivity.
  }
  
Qed.

  
    

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  {
    simpl.
    reflexivity.    
  }
  {

    simpl.
    rewrite map_append_relation.
    rewrite IHl.
    simpl.
    reflexivity.
  }
   
Qed.

  
Fixpoint flat_map {X Y : Type} (f: X -> list Y) (l: list X)
  : (list Y) :=
  match l with
  | [] => []
  | h :: r => (f h) ++ (flat_map f r)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
  reflexivity.
Qed.


(* From the book *)
Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
  : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.


Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l: list X) (b:Y)
  : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.

Check fold andb.



Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof.
  reflexivity.
Qed.

(* I'm cheating in the following exercise since
  the book hasn't touched the `unfold` tactic *)

Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  intros X l.
  induction l .
  {
    reflexivity.
  }
  {
    simpl.
    unfold fold_length.
    simpl.
    rewrite <- IHl.
    unfold fold_length.
    reflexivity.
  }  
Qed.

Theorem fold_length_correct_2 : forall X (l : list X),
    fold_length l = length l.
Proof.
  intros X l.
  induction l .
  {
    reflexivity.
  }
  {
    simpl.
    replace (fold_length (x :: l)) with (S (fold_length l)).
    rewrite <- IHl.
    reflexivity.

    induction l.
    {
      reflexivity.
    }
    {
      simpl.
      reflexivity.
    }
    
  }  
Qed.


Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold  (fun e n => (f e):: n) l [].


Compute (fold_map (fun x => x + x) [1;2;3;4]).
           
Theorem fold_and_map_same : forall ( X Y : Type ) (l : list X) (f : X -> Y),
    fold_map f l = map f l.
Proof.
  intros X Y l f.
  induction l.
  {
    reflexivity.
  }
  {
    
    simpl.
    unfold fold_map.
    simpl.
    rewrite <- IHl.
    unfold fold_map.
    reflexivity.
  }
  
Qed.


Theorem fold_and_map_same_2 : forall ( X Y : Type ) (l : list X) (f : X -> Y),
    fold_map f l = map f l.
Proof.
  intros X Y l f.
  induction l.
  {
    reflexivity.
  }
  {
    
    simpl.
    rewrite <- IHl.
    reflexivity.
  }
  
Qed.


(* Exercise currying*)

Definition prod_curry { X Y  Z : Type }
           (f : X *  Y -> Z) (x : X) (y : Y) : Z := f (x,y).

Definition prod_uncurry { X Y Z : Type }
          (f : X -> Y -> Z) (p : X * Y) : Z :=
    ((f (fst p)) (snd p)).



Example test_map2: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2_exercise: map ( plus 3 ) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.


Check prod_curry.
Check prod_uncurry.                                                      
Theorem uncurry_curry : forall (X Y Z : Type)
                               (f : X -> Y -> Z)
                               x y ,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  simpl.

  unfold prod_uncurry.
  simpl.
  unfold prod_curry.
  simpl.
  reflexivity.
Qed.

Lemma pair_destructed : forall (X Y : Type) (p : X * Y),
     (fst p, snd p) = p.
Proof.
  destruct p.
  simpl.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z)
                               (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  simpl.
  unfold prod_curry.
  unfold prod_uncurry.
  simpl.
  rewrite pair_destructed.
   reflexivity.
Qed.

  

End Poly.

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.


Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : nat :=
  fun (X : Type) (f : X -> X) (x : X) => (f (f (f x))).


Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.


Definition succ (n : nat) : nat :=
   fun (X : Type) (f : X -> X) (x : X) => f (n X f x).


Example succ_1 : succ zero = one.
Proof. 
reflexivity.
Qed.

Example succ_2 : succ one = two.
Proof. 
reflexivity.
Qed.

Example succ_3 : succ two = three.
Proof.
reflexivity.
Qed.


Definition plus (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof.
reflexivity.
Qed.

Example plus_2 : plus two three = plus three two.
Proof.
reflexivity.
Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof.
reflexivity.
Qed.

Definition mult (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => n X  (m X f ) x.

Example mult_1 : mult one one = one.
Proof.
reflexivity.
Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof.
  reflexivity.
Qed.

Example mult_3 : mult two three = plus three three.
Proof.
   reflexivity.
Qed.



Definition exp  (n m : nat) : nat :=
  fun (X: Type) (f : X -> X) (x : X) =>
    ((m (X -> X) (fun x1 => n X x1)) (one X f) ) x.
(*    m (X -> X) (fun y => ((mult n y) f)) (one f).*)

(*    fun (X : Type) (f : X -> X) (x : X) => zero (fun x => x) one.*)
(*
      two (X -> X) (fun x => mult x two) two.
    fun (X : Type) (f : X -> X) (x : X) => n X (fun w => mult m w) x.*)

Check exp.
Compute exp three zero.

Example exp_31 : exp three zero = one.
Proof.
  simpl.
  reflexivity.
Qed.


Example exp_1 : exp two two = plus two two.
Proof.
   reflexivity.
Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof.
   reflexivity.
Qed.

Example exp_3 : exp three zero = one.
Proof.
  reflexivity.
Qed.
End Church.
