Inductive nat :=
| Z : nat
| S : nat -> nat.

Fixpoint nat_add (a : nat) (b : nat) : nat :=
match a with
    | Z => b
    | S a => S (nat_add a b)
end.

Theorem zero_is_right_add_neutral :
    forall (n : nat), nat_add n Z = n.
Proof.
    induction n.
    + simpl. reflexivity.
    + simpl.
      rewrite -> IHn.
      reflexivity.
Qed.  

Theorem zero_is_left_add_neutral :
    forall (n : nat), nat_add Z n = n.
Proof.
    trivial.
Qed.

Theorem add_one :
    forall (n m : nat), S (nat_add n m) = nat_add n (S m).
Proof.
    induction n.
    + intros m.
      trivial.
    + intros m.
      simpl. 
      rewrite -> IHn.
      trivial.
Qed.

Theorem nat_add_is_commutative :
forall (n m : nat), nat_add n m = nat_add m n.
Proof.
    induction n.
    + intros m.
      rewrite -> zero_is_right_add_neutral.
      trivial.
    + intros m.
      rewrite <- add_one.
      simpl.
      rewrite -> IHn.
      trivial.
Qed.           

      
Theorem zero_is_add_neutral : 
    forall (n : nat), nat_add Z n = n /\ nat_add n Z = n.
Proof.
    intros n.
    split.
    + trivial.
    + rewrite -> nat_add_is_commutative.
      trivial.
Qed.

