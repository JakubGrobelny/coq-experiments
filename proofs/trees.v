Require Import PeanoNat.
Local Open Scope nat_scope.

Inductive BTree (A : Type) :=
| Leaf : BTree A
| Node : BTree A -> A -> BTree A -> BTree A.

Arguments Leaf {A}.
Arguments Node {A} l v r.

Check BTree_ind.

Fixpoint mirror (A : Type) (tree : BTree A) : BTree A :=
match tree with
    | Leaf       => Leaf
    | Node l v r => Node (mirror A r) v (mirror A l)
end.

Arguments mirror {A}.

Theorem double_mirror : 
    forall (A : Type) (tree : BTree A), mirror (mirror tree) = tree.
Proof.
    intros A.
    induction tree.
    + simpl. reflexivity.
    + simpl.
      rewrite -> IHtree1.
      rewrite -> IHtree2.
      reflexivity.
Qed.

Fixpoint height (A : Type) (tree : BTree A) : nat :=
match tree with
    | Leaf       => 0
    | Node l _ r => 1 + height A l + height A r
end.

Arguments height {A}.

Theorem mirror_preserves_height :
    forall (A : Type) (tree : BTree A), height (mirror tree) = height tree.
Proof.
    intros A.
    induction tree.
    + simpl. reflexivity.
    + simpl.
      rewrite -> IHtree1.
      rewrite -> IHtree2.
      rewrite Nat.add_comm.
      reflexivity.
Qed.

