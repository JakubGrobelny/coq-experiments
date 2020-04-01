Class Functor (F : Type -> Type) : Type := 
{ fmap : forall (A B : Type), F A -> (A -> B) -> F B
}.

Class Applicative (F : Type -> Type) : Type :=
{ ap   : forall (A B : Type), F (A -> B) -> F A -> F B;
  pure : forall (A : Type), A -> F A 
}.

Class Monad (M : Type -> Type) : Type :=
{ mreturn : forall (A : Type), A -> M A;
  bind    : forall (A B : Type), M A -> (A -> M B) -> M B
}.  

Set Implicit Arguments.
Print Implicit fmap.

Instance applicative_functor (F : Type -> Type) `{Applicative F} : Functor F :=
{  fmap _ _ x f := ap _ _ (pure _ f) x
}.

Instance monad_applicative (M : Type -> Type) `{Monad M} : Applicative M :=
{  pure := mreturn;
   ap _ _ f a := bind _ _ f (fun xf => bind _ _ a (fun xa => mreturn _ (xf xa)))
}.

Instance monad_functor (M : Type -> Type) `{Monad M} : Functor M :=
{ fmap _ _ x f := bind _ _ x (fun x => mreturn _ (f x))
}.

