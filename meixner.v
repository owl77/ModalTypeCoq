

Definition Unique (X: Set) ( p : X -> Prop) :=   exists x : X, and (p x) (forall  y : X,  p y -> (x = y)).

Axiom the : forall (X: Set) (p : X -> Prop),  Unique X p -> X.

Axiom the_def : forall (X: Set) (p : X -> Prop) (e :Unique X p),  p ( (the X p) e ).

Theorem  uni : forall ( X: Set) (p : X -> Prop) (e : Unique X p) ( y : X), p y -> y = the X p e.
Proof.
(intros **).
(pose proof the_def).
(pose proof (the_def X p e)).
(pose proof (H0 X p e)).
instantiate.
(destruct e).
(destruct a).
(pose proof
  (e
     (the X p
        (ex_intro (fun x : X => p x /\ (forall y : X, p y -> x = y)) x
           (conj p0 e))))).
(pose proof (e y)).
(pose proof (H4 H)).
(pose proof (H3 H2)).
(induction H5).
exact H6.
Qed.



