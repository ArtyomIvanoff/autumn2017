Require Import Notations.
Require Import Logic.
Require Import Relations.

Arguments clos_refl_trans_1n {A} R x _.
Arguments clos_trans {A} R x _.
Arguments union {A} R1 R2 x y.

Module Type DynLogic.
  Parameters atomProg state : Set.
  Parameter meanFunc : atomProg -> relation state.
End DynLogic.

Section Compose.
  Variable T : Type.
  Variables R1 R2 : relation T.
  Inductive composeRelSt : relation T :=
  | comp_intro (x y z : T) : R1 x y -> R2 y z -> composeRelSt x z.
End Compose.
Arguments composeRelSt {T} R1 R2 _ _.

Module PDL (Import D : DynLogic).
 Definition assertion := state -> Prop.

 Definition impl (A B : assertion) : assertion := (fun x => (A x -> B x)).
 
 Inductive prog : Type :=
 | Elem : atomProg -> prog
 | Sequence : prog -> prog -> prog
 | Choice : prog -> prog -> prog
 | Iteration : prog -> prog
 | Test : assertion -> prog.
 
 Fixpoint progSemantics  (p : prog) : relation state :=
 match p with
 | Elem ap => meanFunc ap
 | Sequence p1 p2 => composeRelSt (progSemantics p1) (progSemantics p2)
 | Choice p1 p2 => union (progSemantics p1) (progSemantics p2) 
 | Iteration p => clos_refl_trans_1n (progSemantics p) 
 | Test A => eq
 end.
  
 Definition box (pr : prog) (A : assertion) : assertion := 
   fun st => (forall st', progSemantics pr st st' -> A st').
 
 Definition skip := Test (fun _ => True).
 Definition fail := Test (fun _ => False).

 Notation "p1 ; p2" := (Sequence p1 p2) (at level 60, right associativity).
 Notation "p1 'U' p2" := (Choice p1 p2) (at level 55, right associativity).
 Notation "p *" := (Iteration p) (at level 50, left associativity).
 Notation "A ?" := (Test A) (at level 50, left associativity).
 Notation "[ p ] A" := (box p A) (at level 70, right associativity).

 Notation "A -> B" := (impl A B) (at level 80, right associativity).

 Theorem axiom_I : forall (p : prog) (A B : assertion) (st : state),
    ([p](A -> B) -> ([p]A -> [p]B)) st.
 Proof.
 Admitted.
 
 Definition and (A B : assertion) : assertion := (fun x => (A x /\ B x)).
 Notation "A /\ B" := (and A B) (at level 80, right associativity).

 Theorem axiom_II : forall (p : prog) (A B : assertion) (st : state),
 ([p](A/\B)) st <-> (([p]A) st)/\(([p]B) st).
 Proof.
 Admitted.

 Theorem axiom_III : forall (p p': prog) (A : assertion) (st : state),
  ([p U p']A) st <-> (([p]A) st)/\(([p']A) st). 
 Proof.
 Admitted.

 Theorem axion_IV : forall (p p': prog) (A : assertion) (st : state),
 ([p; p']A) st <-> ([p]([p']A)) st.
 Proof.
 Admitted.

 Theorem axiom_V : forall (A B : assertion) (st : state),
 ([A?]B) st <-> (A -> B) st.
 Proof.
 Admitted.

 Theorem axiom_VI : forall (p : prog) (A : assertion) (st : state),
 (and A ([p]([Iteration p]A))) st <-> ([Iteration p]A) st.
 Proof.
 Admitted.

 Theorem axiom_VII : forall (p : prog) (A : assertion) (st : state),
 (and A ([Iteration p](A -> [p]A)) -> [Iteration p]A) st. 
 Proof.
 Admitted.


End PDL.