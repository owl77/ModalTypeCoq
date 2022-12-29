(** * Muskens' Higher Order Modal Logic *)

Parameters S  I  P_S : Set.

Parameter Elem : S -> P_S -> Prop.

Definition Cont (s : P_S) ( t: P_S) := forall (x: S),   Elem x s -> Elem x t.

Definition Char ( s: P_S ) :=  fun ( x : S) =>  Elem x s.

Parameter CSet : (S -> Prop) -> P_S.

Definition Ex_eq (s : P_S) (t : P_S) := forall (x : S), Elem x s <-> Elem x t.

Axiom char_equiv : forall (s : P_S),    Ex_eq (CSet (Char s)) s.

Axiom cset_equiv : forall (c : S -> Prop), forall (x :S),  c x <->   Char (CSet c) x.

Definition Cl (s : P_S) :=   CSet (fun (x : S) => not ((Char s) x ) ).

Definition Lim (I : Set) (D: I -> P_S) :=  CSet ( fun (x :S) => forall ( i : I),  Elem x (D i) ).

Definition MType (T : Type) := T -> P_S. 

Definition Inv_r ( r : S -> P_S) := fun (x :S) =>  CSet ( fun (z :S) =>  Elem x (r z)).

Definition O := CSet (fun (x :S) => False).

Definition S_S := CSet (fun (x :S) => True).

Definition Top := fun (x :S) => S_S.

Definition Bot := fun (x :S) => O.

Definition mod (r : S -> P_S) ( p : P_S ) :=  CSet ( fun (x: S) => exists ( y :S),  and (Elem y (r x)) ((Char p) y) 
).
 
Definition dot (a : S) := Lim (S -> P_S) ( fun (r : S -> P_S) =>  mod r (   (Inv_r r) a )     ).
           
Definition Imp (a : P_S) (b : P_S) :=   CSet ( fun (x : S) =>  not (and (Elem x a) (not (Elem x b) )    )).

Definition MEq (T : Set) ( x : T)( y :T) := Lim ( T -> P_S) ( fun (z : T -> P_S) =>  Imp ( z x) ( z y)   ).
 
Definition sq (r : S -> P_S) ( p : P_S ) := Cl (mod r (Cl p) ).

Definition Loz ( p : P_S ) :=  mod Top p.

Definition Sq  ( p : P_S ) := sq Top p.



