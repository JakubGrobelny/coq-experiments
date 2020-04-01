Inductive list (A: Type) :=
| Null : list A
| Cons : A -> list A -> list A.

Arguments Null [A].
Arguments Cons [A] x xs.

Fixpoint append (A : Type) (xs : list A) (ys : list A) : list A :=
    match xs with
    | Null => ys
    | Cons x xs => Cons x (append A xs ys)
    end.

Arguments append [A].

Fixpoint map (A B : Type) (f : A -> B) (xs : list A) : list B :=
    match xs with
    | Null => Null
    | Cons x xs => Cons (f x) (map A B f xs)
    end.

Arguments map [A] [B].

Check list_ind.

Theorem map_append : forall (A B : Type) (f : A -> B) (xs ys : list A),
    append (map f xs) (map f ys) = map f (append xs ys).
Proof.
    intros A B f.
    induction xs.
    + intros ys.
      replace (map f Null) 
        with (@Null B) 
        by auto.
      replace (append Null ys) 
        with ys 
        by auto.
      replace (append Null (map f ys)) 
        with (map f ys) 
        by auto.
      reflexivity.
    + intros ys.
      replace (map f (Cons a xs)) 
        with (Cons (f a) (map f xs)) 
        by auto.
      replace (append (Cons (f a) (map f xs)) (map f ys)) 
        with (Cons (f a) (append (map f xs) (map f ys))) 
        by auto.
      replace (append (Cons a xs) ys)
        with (Cons a (append xs ys)) 
        by auto.
      replace (map f (Cons a (append xs ys)))
        with (Cons (f a) (map f (append xs ys))) 
        by auto.
      rewrite IHxs.
      reflexivity.
Qed.

Fixpoint length (A : Type) (xs : list A) : nat :=
    match xs with
    | Null => 0
    | Cons _ xs => 1 + length A xs
end.

Arguments length [A].

Theorem append_length : forall (A : Type) (xs ys : list A),
    length xs + length ys = length (append xs ys).
Proof.
    intros A.
    induction xs.
    + intros ys.
      simpl (length Null).
      simpl (append Null ys).
      simpl (0 + length ys).
      reflexivity.
    + intros ys.
      simpl (length (Cons a xs)).
      simpl (append (Cons a xs) ys).
      simpl (length (Cons a (append xs ys))).
      simpl (S (length xs) + length ys).
      rewrite IHxs.
      reflexivity.
Qed.


      





      
       
    

    

    
    
    
    