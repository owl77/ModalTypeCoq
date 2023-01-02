

Definition Unique (X: Type) ( p : X -> Prop) :=   exists x : X, and (p x) (forall  y : X, ( p y -> (x = y))).

Axiom the : forall (X: Type) (p : X -> Prop),  Unique X p -> X.

Axiom the_def : forall (X: Type) (p : X -> Prop) (e :Unique X p),  p ( (the X p) e ).

Theorem  uni : forall ( X: Type) (p : X -> Prop) (e : Unique X p) ( y : X), p y -> y = the X p e.
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

Axiom M : Type.
Axiom P : M -> M -> Prop.
Axiom P_trans : forall (x: M) (y : M) (z : M),  and (P x y) (P y z) -> P x z.
Axiom P_id : forall x: M, P x x.
Axiom P_asym : forall ( x : M) (y : M), and (P x y) (P y x) ->  x = y.

Axiom P_sup : forall  p : M -> Prop, exists  z : M,  (forall x : M, (p x -> P x z)) /\  forall y : M, ((forall w : M, p w -> P w y) -> P z y).

Definition Min (x : M) := forall z : M, P z x.

Definition QA (t : M) := forall x : M, P x t -> x = t \/ Min x.

Axiom P_qa : forall (x : M) (y : M), (forall z : M, (QA z /\ P z x) -> P z y) -> P x y.

Definition sup (p : M -> Prop) := fun (z : M) =>  (forall x : M, (p x -> P x z)) /\  forall y : M, ((forall x : M, p x -> P x y) -> P z y).

Theorem con: forall p: M-> Prop, Unique M (sup p). 
Proof.
intro.
(unfold sup).
(unfold Unique).
(pose proof (P_sup p)).
(destruct H).
(cut
  (forall y : M,
   (forall x1 : M, p x1 -> P x1 y) /\
   (forall y0 : M, (forall x1 : M, p x1 -> P x1 y0) -> P y y0) -> 
   x = y)).
 intro.
 (pose proof (Logic.conj H H0)).
 (pose proof
   (Logic.ex_intro
      (fun x : M =>
       ((forall x0 : M, p x0 -> P x0 x) /\
        (forall y : M, (forall w : M, p w -> P w y) -> P x y)) /\
       (forall y : M,
        (forall x1 : M, p x1 -> P x1 y) /\
        (forall y0 : M, (forall x1 : M, p x1 -> P x1 y0) -> P y y0) -> 
        x = y)) x H1)).
 exact H2.
 intro.
 (destruct H).
 intro.
 (destruct H1).
 (pose proof (H2 x)).
 (pose proof (H3 H)).
 (pose proof (H0 y)).
 (pose proof (H5 H1)).
 (pose proof (P_asym x y)).
 (pose proof (Logic.conj H6 H4)).
 (pose proof (H7 H8)).
 exact H9.
Qed.

Definition Sup (p: M -> Prop) :=  (the M) (sup p) (con p).

Theorem sup_M : forall p: M -> Prop, (sup p) (Sup p).
Proof.
intro.
(unfold Sup).
(pose proof (the_def M (sup p))).
(pose proof (H (con p))).
exact H0.
Qed.



 

                                                                                                                                                                                                     
