(* 
   Exercises, examples and experiments related to the 
  "Lists working with structured data" chapter.
*)



Module NatList  .


Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.
  
Inductive natprod : Type := 
| pair : nat -> nat -> natprod.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Compute (pair 1 2).

Definition fst (p : natprod) :=
  match p with
  | pair x _ => x
  end.

Definition snd (p : natprod) :=
  match p with
  | pair _ x => x
  end.

Definition swap_pair (p : natprod) :=
  match p with
  | pair  x y => pair y x
  end.

Compute (fst (pair 3 2)).


Notation "( x , y )" := (pair x y).

Theorem surjective_pairing : forall n m : nat,
    (n, m) = ((fst (n, m)), (snd (n, m))).
Proof.
  simpl.
  reflexivity.
Qed.  

(* Ex 1*)

Theorem snd_fst_is_swap : forall p : natprod,
    (snd p, fst p) = swap_pair p.
Proof.
   intros p.
   destruct p as [n m].
   - simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall p : natprod,
    fst (swap_pair p) = snd p.
Proof.
   intros p.
   destruct p as [n m].
   - simpl. reflexivity.
Qed.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Check cons 1  mylist.


Fixpoint nonzeros (l:natlist) : (natlist ) :=
  match l with
  | nil => nil
  | (cons 0 rest) => (nonzeros rest)
  | (cons x rest) => x :: (nonzeros rest)
  end.

Compute (nonzeros [1;0;4;0;3;4;0;5]).


Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
   simpl.
   reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
   match n with
   | O => true
   | S O => false
   | S (S num) => evenb num
   end.

Compute negb (evenb 1).

Definition oddb (n:nat) : bool :=
   negb (evenb n).


Fixpoint oddmembers (l:natlist) : (natlist) :=
  match l with
  | nil => nil
  | (cons first rest) => 
       match (oddb first) with
       | true => first :: (oddmembers rest)
       | false => (oddmembers rest)  
       end
  end.
  

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
    simpl.
    reflexivity.
Qed.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.


Definition countoddmembers (l:natlist) : nat :=
    length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
   simpl.
  reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
   reflexivity.
Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
   reflexivity.
Qed.


Fixpoint alternate (l1 l2 : natlist) : (natlist) :=
   match l1 with
   | (cons el1 restl1) =>
        match l2 with
        | (cons el2 restl2) =>
            (cons el1 (cons el2 (alternate restl1 restl2)))
        | nil => l1
        end
   | nil => l2
   end.

Example test_alternate1:
    (alternate [1;3;5] [2;4]) = [1;2;3;4;5].
Proof.
   reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
   reflexivity.
Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
   simpl.
   reflexivity.
Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
   reflexivity.
Qed.



Definition bag := natlist.

(* taken from chapter 1 : Number *)

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

Fixpoint count (v:nat) (s:bag) : nat := 
   match s with
   | x::rest => 
       match (beq_nat v x) with
       | true => 1 + (count v rest)
       | false => (count v rest)
       end
   | nil => 0
   end.


Compute (count 1 [3;4;1;2;34;1;3;4]).

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
   reflexivity.
Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof.
   reflexivity.
Qed.

Fixpoint app (l1 l2 : natlist) : natlist := 
   match l1 with
   | nil => l2
   | (h :: t) => h :: (app t l2)
   end.
Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).



Definition sum (l1 l2 : bag) : bag  :=
   app l1 l2.


Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
   reflexivity.
Qed.

Definition add (v:nat) (s:bag) : bag := 
  cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
   reflexivity.
Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
   reflexivity.
Qed.

Definition member (v:nat) (s:bag) : bool :=
   negb (beq_nat (count v s) 0).

Example test_member1: member 1 [1;4;1] = true.
Proof.
    reflexivity.
Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof.
    reflexivity.
Qed.


Fixpoint remove_one (v:nat) (s:bag) : bag :=
   match s with
   | nil => nil
   | (h :: t) => 
          match (beq_nat h v) with
          | true => t
          | false => h :: (remove_one v t)
          end
   end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof.
   reflexivity.
Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof.
   reflexivity.
Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof.
   reflexivity.
Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof.
   reflexivity.
Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
   match s with
   | nil => nil
   | (h :: t) => 
          match (beq_nat h v) with
          | true => (remove_all v t)
          | false => h :: (remove_all v t)
          end
   end.


Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof.
  reflexivity.
Qed.

  
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof.
  reflexivity.
Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof.
  reflexivity.
Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof.
  reflexivity.
Qed.


Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | (first :: rest) =>
    match (member first s2) with
    | true => subset rest (remove_one first s2)
    | false => false
    end
  | nil => true
  end.



Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof.
  reflexivity.
Qed.

  
  
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof.
  reflexivity.
Qed.


(* Exercise bag_theorem seems open ended! *)

Theorem bag_theorem : forall  l : natlist,
    count 5 (add 5 l) = 1 + (count 5 l).
Proof.
  intros l.
  simpl.
  induction l as [| n l' IHl'].
  {
    reflexivity.
  }
  {
    reflexivity.
    
    }
Qed.


Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => (rev t) ++ [h]
  end.

Compute (rev [1;2;3]).



Theorem length_append : forall l1 l2 : natlist,
    length( l1 ++ l2 ) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l' IHl'].
  {
    reflexivity.
  }
  {
    simpl.
    rewrite <- IHl'.
    reflexivity.
  }
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


Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  {
    reflexivity.
  }
  {

    simpl.
    rewrite  length_append.
    rewrite IHl'.
    rewrite plus_comm.
    simpl.
    reflexivity.
  }
Qed.  


Compute (app [1;2;3] [4;5;6]).


Check (1 :: [2] ++ []).

                       
Theorem app_nil_r : forall l : natlist,
  (l ++ []) = l.
Proof.
  intros l.

  induction l as [| n l' IHl'].
  {
    reflexivity.
  }
  {
    simpl.    
    rewrite   IHl'.
    reflexivity.
  }
Qed.


Theorem app_assoc : forall l1 l2 l3 : natlist,
    l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros l1 l2 l3.
  simpl.
  induction l1 as [|n l1' IHl1'].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite <- IHl1'.
    reflexivity.
  }
Qed.


Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.

  intros l1 l2.
  simpl.
  induction l1 as [|n l IHl'].
  {
    rewrite app_nil_r.
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHl'.
    rewrite app_assoc.
    reflexivity.

  }
Qed.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [|n l' IHl'].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite  IHl'.

    reflexivity.
    
  }
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.



Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  {
    simpl.
    (*rewrite app_nil_r.
    rewrite app_nil_r.*)
    reflexivity.
  }
  {

    
    destruct n.
    - simpl. rewrite IHl1'. reflexivity.
    - simpl. rewrite  IHl1'. reflexivity.
  }
  
Qed.


Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | first1::rest1 =>
    match l2 with
    | first2::rest2 =>
      match (beq_nat first1 first2) with
      | true => beq_natlist rest1 rest2
      | false => false
      end
    | [] => false
    end
  | [] => match l2 with
          | [] => true
          | _ => false
          end
  end.

   

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof.
  reflexivity.
Qed.


Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof.
  reflexivity.
Qed.


Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof.
  reflexivity.
Qed.

Theorem beq_reflex : forall n : nat ,
    beq_nat n n = true.
Proof.
  intros n.
  induction n.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHn.
    reflexivity.
  }
Qed. 

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l.

  induction l.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite beq_reflex.
    rewrite IHl.
    reflexivity.
  }
Qed.

(*From chapter 1*)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.


Theorem count_member_nonzero : forall(s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros l.
  destruct l.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }


Qed.

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Compute leb 1 2.
Compute leb 1 1.
Compute leb 2 1.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.

induction s.
{
  reflexivity.
}
{
  destruct n.
  {
    simpl.
    rewrite ble_n_Sn.
    reflexivity.
  }
  {
    simpl.
    rewrite IHs.
    reflexivity.
  }
}

Qed.


Theorem rev_injective  : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2  .

  replace (l1 = l2) with ((rev (rev l1)) = l2).
  intros h1.
  rewrite h1.
  rewrite rev_involutive.
  reflexivity.

  rewrite rev_involutive.
  reflexivity.
Qed.

(* Taken from the book *)


Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | (fst::rest) => Some fst
  end.

Example test_hd_error1 : hd_error [] = None.
Proof.
  reflexivity.
Qed.


Example test_hd_error2 : hd_error [1] = Some 1.
Proof.
  reflexivity.
Qed.


Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof.
  reflexivity.
Qed.


Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
  
Qed.



(****** Partial maps ***********)

Inductive id : Type :=
| Id : nat -> id.


Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Lemma beq_nat_reflex : forall x, beq_nat x x = true.
Proof.
  intros x.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.


Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  destruct x.
  -  simpl. rewrite beq_nat_reflex. reflexivity.

Qed.

End NatList.

Module PartialMap.
Import NatList.
(*Export NatList.*)

Inductive partial_map : Type :=
| empty : partial_map
| record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map)
           (x : id) (value : nat) : partial_map :=
  record x value d.

Compute (update empty (Id 1) 100).


Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' =>  if beq_id x y
                      then Some v
                      else find x d'
end.

Compute (find (Id 1) (update empty (Id 1) 100)).
Compute (find (Id 2) (update empty (Id 1) 100)).


Theorem update_eq :
  forall(d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem update_neq :
  forall(d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros fr.
  simpl.
  rewrite fr.
  reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(*Zero???Compute (Baz2 Baz1).*)

End PartialMap.


