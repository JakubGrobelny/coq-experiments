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

Check (forall xs ,length xs > 0).

Theorem empty_list_length_ngtz : forall (A : Type), ~ @length A Null > 0.
Proof.
    intros A.
    simpl (length Null).
    unfold not.
    intros H.
    inversion H.
Qed.
    
Definition list_head (A : Type) (xs : list A) : length xs > 0 -> A :=
    match xs with
    | Cons x _ => fun _ => x
    | Null => fun pf => match empty_list_length_ngtz A pf with end
end.

Arguments list_head [A].

Definition list_tail (A : Type) (xs : list A) : length xs > 0 -> list A :=
    match xs with
    | Cons _ xs => fun _ => xs
    | Null => fun pf => match empty_list_length_ngtz A pf with end
end.

Arguments list_tail [A].

Fixpoint reverse_aux (A : Type) (xs : list A) (acc : list A) : list A :=
    match xs with 
    | Null => acc
    | Cons x xs => reverse_aux A xs (Cons x acc)
end.

Arguments reverse_aux [A].

Definition reverse (A : Type) (xs : list A) : list A := 
    reverse_aux xs Null.

Arguments reverse [A].

Definition singleton (A : Type) (x : A) : list A := Cons x Null.

Arguments singleton [A].

Fixpoint app_reverse (A : Type) (xs : list A) : list A :=
    match xs with
    | Null => Null
    | Cons x xs => append (app_reverse A xs) (singleton x)
end.

Arguments app_reverse [A].

Theorem append_assoc : forall (A : Type) (zs ys xs : list A),
    append xs (append ys zs) = append (append xs ys) zs.
Proof.
    intros A zs ys.
    induction xs.
    + simpl.
      reflexivity.
    + simpl append.
      rewrite IHxs.
      reflexivity.
Qed.

Theorem append_null_right : forall (A : Type) (xs : list A),
    append xs Null = xs.
Proof.
    intros A.
    induction xs.
    + simpl (append Null Null).
      reflexivity.
    + simpl (append (Cons a xs) Null).
      rewrite IHxs.
      reflexivity.
Qed.

Theorem reverse_append : forall (A : Type) (ys xs : list A),
    app_reverse (append xs ys) = append (app_reverse ys) (app_reverse xs).
Proof.
    intros A ys.
    induction xs.
    + simpl (append Null ys).
      simpl (app_reverse Null).
      simpl (append (app_reverse ys) Null).
      rewrite append_null_right.
      reflexivity.
    + replace (app_reverse (append (Cons a xs) ys))
        with (app_reverse (Cons a (append xs ys)))
        by auto.
      simpl app_reverse.
      rewrite append_assoc.
      rewrite IHxs.
      reflexivity.
Qed.
  
Theorem append_singleton : forall (A : Type) (a : A) (xs : list A),
    append (singleton a) xs = Cons a xs.
Proof.
    intros A a xs.
    simpl.
    reflexivity.
Qed.

Theorem reverse_singleton : 
    forall (A : Type) (a : A), app_reverse (singleton a) = singleton a.
Proof.
    intros A a.
    simpl.
    reflexivity.
Qed.

Theorem double_reverse_app : forall (A : Type) (xs : list A),
    app_reverse (app_reverse xs) = xs.
Proof.
    intros A.
    induction xs.
    + simpl.
      reflexivity.
    + replace (app_reverse (Cons a xs))
        with (append (app_reverse xs) (app_reverse (singleton a)))
        by auto.
      rewrite reverse_append.
      simpl app_reverse.
      rewrite append_singleton.
      rewrite IHxs.
      reflexivity.
Qed.

Theorem eq_sym : forall (a b : Prop), a = b -> b = a.
Proof.  
    intros.
    symmetry.
    assumption.
Qed.

Theorem append_length' : forall (A : Type) (xs ys : list A),
    length (append xs ys) = length xs + length ys.
Proof.
    symmetry.
    rewrite append_length.
    reflexivity.
Qed.
    
Theorem append_singleton_length : forall (A : Type) (a : A) (xs : list A),
    length (append xs (singleton a)) = length xs + 1.
Proof.
    intros A a xs.
    rewrite append_length'.
    unfold singleton.
    simpl length.
    reflexivity.
Qed. 

Theorem addition_zero_neutral : forall (a : nat), a + 0 = a.
Proof.
    induction a.
    + simpl plus.
      reflexivity.
    + simpl plus.
      rewrite IHa.
      reflexivity.
Qed.

Theorem addition_assoc : forall (a b : nat), a + b = b + a.
Proof.
    intros a.
    induction b.
    + simpl plus.
      rewrite addition_zero_neutral.
      reflexivity.
    + simpl plus.
      replace (a + S b) with (S (a + b)) by auto.
      rewrite IHb.
      reflexivity.
Qed.
      

Theorem reverse_preserves_length : forall (A : Type) (xs : list A),
    length (app_reverse xs) = length xs.
Proof.
    intros A.
    induction xs.
    + simpl app_reverse.
      reflexivity.
    + simpl app_reverse.
      rewrite append_singleton_length.
      simpl length.
      rewrite addition_assoc.
      rewrite IHxs.
      reflexivity.
Qed.    

Theorem rev_acc_step : forall (A : Type) (xs acc : list A) (a : A),
    reverse_aux (Cons a xs) acc = reverse_aux xs (Cons a acc).
Proof.
    intros A xs acc a.
    simpl reverse_aux.
    reflexivity.
Qed.

Theorem rev_acc_step_back : forall (A : Type) (xs acc : list A) (a : A),
    reverse_aux xs (Cons a acc) = reverse_aux (Cons a xs) acc.
Proof.
    symmetry.
    rewrite rev_acc_step.
    reflexivity.
Qed.

(* Theorem reverse_step : forall (A : Type) (x : A) (xs : list A),
    reverse_aux xs (Cons x Null) = append (reverse_aux xs Null) (Cons x Null).
Proof.
    intros A x.
    induction xs.
    + simpl.
      reflexivity.
    + repalce (append )  
       *)


(* Theorem reverse_eqv : 
    forall (A : Type) (xs : list A), reverse_aux xs Null = app_reverse xs.
Proof.
    intros A.
    induction xs.
    + simpl. reflexivity.
    + simpl app_reverse.
      simpl reverse_aux. *)



(* Theorem reveres_aux_cons : forall (A : Type) (x : A) (xs acc : list A),
    Cons x (reverse_aux xs acc) = reverse_aux xs (Cons x acc).
Proof.
    intros A x.
    induction xs.
    + simpl. reflexivity.
    + simpl.
      intros acc.
 *)

    
(* Theorem reverse_cons : forall (A : Type) (x : A) (xs : list A), 
    reverse (Cons x xs) = append xs (singleton x).
Proof.
    intros A x.
    induction xs.
        + simpl (append Null (singleton x)).
          unfold singleton.
          simpl (reverse (Cons x Null)).
          reflexivity.
        + simpl append.
          replace (append xs (singleton x)) 
            with (reverse (Cons x xs)) 
            by auto.
          simpl reverse.
          induction xs.
          simpl reverse_aux.
          reflexivity.
 *)
