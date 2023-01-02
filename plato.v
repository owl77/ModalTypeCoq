
Parameter encodes : forall (T: Type) ( t :T) (p : T -> Prop), Prop.
Parameter exemplifies : forall (T: Type) ( t :T) (p : T -> Prop), Prop.

Definition part (T : Type) ( a : T) ( b : T):= exists p: T -> Prop, exemplifies T a p /\ encodes T b p.

(** a participates of b, that is some participle emanation of b is a part of a   *) 

Parameter enc : forall (T : Type) (p : T -> Prop), T.

Axiom enc_ax : forall (T :Type) (p : T -> Prop), encodes T (enc T p) p.


Axiom log : forall (T : Type) (p : T -> Prop) (p' : T -> Prop) (a :T), (encodes T a p /\ (forall x:T, p x -> p' x)) -> encodes T a p'.


Parameter One Being : forall T : Type, (T -> Prop).

Definition one (T: Type) :=    enc T (One T).

Definition being (T: Type) :=  enc T (Being T).


Axiom henon : forall (T : Type) (a : T), exemplifies T a (One T) /\ exemplifies T a (Being T).


