

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


Axiom P_min : forall (x: M) (p : M -> Prop), ( P x (Sup p) /\ not (Min x)) -> exists k :M,
(P k x /\ not (Min k) /\ exists z:M, P k z /\ p z  ).

Parameter w : M.

Definition T ( t : M) := forall y : M, P y t.

Definition QC (t : M) := forall y : M,  P t y -> ( y = t \/ T y ).

Axiom P_w : QC w.


Definition top := Sup (fun (x : M) => True).


Theorem t_un : Unique M (fun (x : M) =>  forall y: M, P y x).
Proof.
(unfold Unique).
(cut
  ((forall y : M, P y top) /\
   (forall y : M, (forall y0 : M, P y0 y) -> top = y))).
 intro.
 (pose proof
   (Logic.ex_intro
      (fun x : M =>
       (forall y : M, P y x) /\
       (forall y : M, (forall y0 : M, P y0 y) -> x = y)) top H)).
 exact H0.

 (pose proof (sup_M (fun _ : M => True))).

 (unfold sup).
 (unfold sup).

 (unfold sup in H).
 (unfold top).
 (destruct H).
 split.
  intro.
  (pose proof (H y)).
  (pose I).
  (pose proof (H1 t)).
  exact H2.

  intro.
  intro.
  (pose proof (H y)).
  (pose proof (H2 I)).
  (pose proof (H0 y)).
  (cut (forall y0 : M, True -> P y0 y)).
   (intros **).
   (intros **).
   (pose proof (H4 H5)).
   (pose proof (Logic.conj H6 H3)).
   (pose proof (P_asym (Sup (fun _ : M => True)) y)).
   (pose proof (H8 H7)).
   exact H9.

   intro.
   intro.
   (pose proof (H1 y0)).
   exact H6.
Qed.


Definition top2 := the M (fun (x : M) =>  forall y: M, P y x) t_un.
 

Axiom wt : not (top2 = w).

(**  Do the same for bottom and k *)

 
Definition A (x : M) := not (exists y : M, (not (y = x) /\ P y x )).


Fixpoint Ah (n : nat) : M -> Prop := 
 match n with
  | 0 =>   A
  | S n => fun (x : M) => ( forall y : M, P y x -> (y = x \/ (Ah n) y) )
  end.   

Definition Ae ( n : nat) : M -> Prop :=
 match n with
  | 0 =>  Ah 0
  | S n => fun (x : M) => ( ((Ah (S n)) x) /\ not ((Ah n) x) )
 end.

Axiom hier : forall n : nat, exists x : M, (Ae n) x.
                                                                                                                                                                                                     
