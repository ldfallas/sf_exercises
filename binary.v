(*
0   Zero
1   OneMoreTwice Zero
10  Twice OneMoreTwice Zero

11  OneMoreTwice OneMoreTwice Zero
100 Twice Twice OneMoreTwice Zero
101 OneMoreTwice Twice OneMoreTwice Zero
110 Twice OneMoreTwice OneMoreTwice Zero
111 OneMoreTwice OneMoreTwice OneMoreTwice Zero
1000 Twice Twice Twice OneMoreTwice Zero
1001 OneMoreTwice Twice Twice OneMoreTwice Zero
1010 Twice OneMoreTwice Twice OneMoreTwice Zero
1011 OneMoreTwice OneMoreTwice Twice OneMoreTwice Zero
1100 Twice Twice OneMoreTwice OneMoreTwice Zero
1101 OneMoreTwice Twice OneMoreTwice OneMoreTwice Zero
1110 Twice OneMoreTwice OneMoreTwice OneMoreTwice Zero
1111 OneMoreTwice OneMoreTwice OneMoreTwice OneMoreTwice Zero
100000 Twice Twice Twice Twice Twice OneMoreTwice Zero

*)

Inductive bin : Type :=
  | Zero : bin
  | Twice : bin -> bin
  | OneMoreTwice : bin -> bin.


Fixpoint incr (number : bin) : bin :=
   match number with
   | Zero => OneMoreTwice Zero
   | Twice t => OneMoreTwice t
   | OneMoreTwice t => Twice (incr t)
end.

Compute incr(incr(incr(incr( Zero)))).

Fixpoint bin_to_nat(x : bin) : nat :=
   match x with
   | Zero => O
   | OneMoreTwice t' => 1 + 2*(bin_to_nat(t'))
   | Twice b' =>  2 * (bin_to_nat(b'))
end.


Fixpoint nat_to_bin(x : nat) : bin :=
   match x with
   | O => Zero
   | S t' => incr(nat_to_bin(t'))
end.

Compute( bin_to_nat(incr(nat_to_bin(15)))).

Example test_bin_incr1: incr(Zero) = OneMoreTwice Zero.
Proof.
simpl.
reflexivity.
Qed.


Example test_bin_incr2: incr(OneMoreTwice Zero) = Twice (OneMoreTwice Zero).
Proof.
simpl.
reflexivity.
Qed.

Example test_bin_incr3: forall t : bin, incr(Twice t) = OneMoreTwice t.
Proof.
simpl.
reflexivity.
Qed.

Example pluszero_prop: forall n: nat, n + 0 = n.
Proof.
intros n.
induction n as [| n' IHn' ].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.


(*
Example plus_multi: forall n: nat 
Proof.
intros n.
induction n as [| n' IHn' ].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Abort.
*)
(*
Example btn_plus : forall t: bin, nat_to_bin(bin_to_nat(t) + bin_to_nat(t)) = Twice t.
Proof.
intros t.
induction t as [| t' IHt' |].
- simpl. reflexivity.
Qed.*)

Example test_bin_incr4: forall t : bin, nat_to_bin(bin_to_nat(t)) = t.
Proof.
intros t.
induction t as [| t' IHt' |].
- simpl. reflexivity.
- simpl. rewrite -> pluszero_prop. simpl. rewrite <- IHt'. 
Abort.

Lemma double_incr: forall x y:nat, (S x) + (S y) = (S (S (x + y))).
Proof.
intros x y.
simpl.
induction x as [| x' IHx'].
- simpl. reflexivity.
- simpl. rewrite <- IHx'. reflexivity.
Qed.


Example test_incr1: forall t: bin, (S (bin_to_nat t)) =  (bin_to_nat (incr t)).
Proof.
simpl.
intros t.
induction t as [| n' IHn' |].
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl. rewrite <- double_incr. rewrite -> pluszero_prop.  rewrite -> pluszero_prop.  
  rewrite <- IHt. simpl. reflexivity. }
Qed.


(*
  QUE FAAAAAACIL!!!!!

  It looks that you cannot prove the converse
*)
Example conversion_is_reversible_from_nat: forall n : nat, bin_to_nat(nat_to_bin(n)) = n.
Proof.
intros n.
induction n as [| n' IHn' ].
- simpl. reflexivity.
- simpl. rewrite <- test_incr1. simpl. rewrite -> IHn'. reflexivity.
Qed.



