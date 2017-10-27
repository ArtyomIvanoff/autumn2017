Require Import Notations.
Require Import Logic.
Require Import Relations.
Require Import Coq.Setoids.Setoid.

Arguments clos_refl_trans_1n {A} R x _.
Arguments clos_trans {A} R x _.
Arguments union {A} R1 R2 x y.

Module Type DynLogic.
  Parameters atomProg state : Set.
  Parameter meanFunc : atomProg -> relation state.
End DynLogic.

Section Compose.
  Variables U V T : Type.
  Variable R1 : U -> V -> Prop.
  Variable R2 : V -> T -> Prop.
  Inductive composeRel : U -> T -> Prop :=
  | comp_intro (x : U) (z : T) : (exists y, R1 x y /\ R2 y z) -> composeRel x z.
End Compose.

Arguments composeRel {U} {V} {T} R1 R2 _ _.

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
 | Sequence p1 p2 => composeRel (progSemantics p1) (progSemantics p2)
 | Choice p1 p2 => union (progSemantics p1) (progSemantics p2) 
 | Iteration p => clos_refl_trans_1n (progSemantics p) 
 | Test A => (fun st st' => st=st' /\ A st)
 end.
  
 Definition box (pr : prog) (A : assertion) : assertion := 
   fun st => (forall st', progSemantics pr st st' -> A st').
 
 Definition trueA : assertion := (fun _ => True).
 Definition falseA : assertion := (fun _ => False).
 Definition skip := Test trueA.
 Definition fail := Test falseA.

 Notation "p1 ; p2" := (Sequence p1 p2) (at level 60, right associativity).
 Notation "p1 'U' p2" := (Choice p1 p2) (at level 55, right associativity).
 Notation "p *" := (Iteration p) (at level 50, left associativity).
 Notation "A ?" := (Test A) (at level 50, left associativity).
 Notation "[ p ] A" := (box p A) (at level 70, right associativity).

 Notation "A ]-> B" := (impl A B) (at level 80, right associativity).

 Theorem axiom_I : forall (p : prog) (A B : assertion) (st : state),
    ([p](A ]-> B) ]-> ([p]A ]-> [p]B)) st.
 Proof.
 intros p A B st. unfold impl. intros HI HA. unfold box in *.
 intros st' H. apply HI. apply H. apply HA. apply H.
 Qed.
 
 Definition andA (A B : assertion) : assertion := (fun x => (A x /\ B x)).
 Notation "A /| B" := (andA A B) (at level 75, right associativity).

 Theorem axiom_II : forall (p : prog) (A B : assertion) (st : state),
 ([p](A/|B)) st <-> (([p]A) st)/\(([p]B) st).
 Proof.
 intros p A B st. split.
 * intros H. split; unfold box in *; intros st' H1;
   apply H in H1; destruct H1 as [H1' H1'']; assumption.
 * intros [HA HB]. unfold box in *. intros st' H. split.
   now apply HA in H. now apply HB in H.
 Qed.

 Theorem axiom_III : forall (p p': prog) (A : assertion) (st : state),
  ([p U p']A) st <-> (([p]A) st)/\(([p']A) st). 
 Proof.
 intros p p' A st. split.
 * intros H. unfold box in *. split;
   intros st' H1; specialize H with st';
   simpl in H; apply H; unfold union; [now left | now right].
 * intros [H H']. unfold box in *. intros st' H1. simpl in H1.
   unfold union in H1. destruct H1 as [H1|H1]. 
   now apply H in H1. now apply H' in H1.
 Qed.  
 
 Theorem axiom_IV : forall (p p': prog) (A : assertion) (st : state),
 ([p; p']A) st <-> ([p]([p']A)) st.
 Proof.
 intros p p' A st. split.
 * unfold box in *. intros H st'' H1 st3 H2. apply H.
   simpl in *. apply comp_intro. exists st''. split; assumption.  
 * unfold box in *. intros H st' H1. simpl in H1. 
   inversion H1. subst. destruct H0 as [y [H' H'']].
   apply H with (st':=y); assumption.
Qed.

 Theorem axiom_V : forall (A B : assertion) (st : state),
 ([A?]B) st <-> (A ]-> B) st.
 Proof.
 intros A B st. split.
 * unfold box in *. intros H. unfold impl. intros HA. apply H.
   simpl. split; [reflexivity|assumption].
 * unfold box in *. intros H st' HT. unfold impl in H. simpl in HT.
   destruct HT as [H1 H2].  rewrite <- H1. now apply H.
 Qed.

 Theorem axiom_VI : forall (p : prog) (A : assertion) (st : state),
 (A /| ([p]([Iteration p]A))) st <-> ([Iteration p]A) st.
 Proof.
 intros p A st. split.
 * unfold andA. intros [HA HI]. apply <- (axiom_IV p (Iteration p) A st) in HI .
   unfold box in *. simpl in *. intros st' H. inversion H. subst. apply HA.
   apply HI. apply comp_intro. exists y. split. apply H0. apply H1.
 * intros H. unfold andA. split.
   + unfold box in H. apply H. simpl. apply rt1n_refl.
   + unfold box at 1. intros. unfold box in *.
     intros st'' H1. apply H. simpl in *.
     apply Relation_Operators.rt1n_trans with (y:=st'). apply H0. apply H1.
 Qed.

 Theorem axiom_VII : forall (p : prog) (A : assertion) (st : state),
 ((A /|([Iteration p](A ]-> [p]A))) ]-> [Iteration p]A) st. 
 Proof.
 intros p A st. unfold box in *. simpl in *.  
 unfold impl. intros H. destruct H as [HA HI].
 intros st' H. rewrite <- clos_rt_rt1n_iff in *. 
 apply clos_refl_trans_ind_left with (R:=(progSemantics p)) (x:=st).
 apply HA. intros y z Hyz Hy Hpyz. rewrite clos_rt_rt1n_iff in Hyz.
 apply HI with (st':=y) (st'0:=z) in Hyz. apply Hyz. apply Hy. apply Hpyz.
 assumption.
 Qed.

 Definition diamond (p : prog) (A : assertion) : assertion :=
  fun st => ~(box p (fun st' => ~(A st')) st).

 Notation "< p > A" := (diamond p A) (at level 70, right associativity).
 
 Definition orA (A B : assertion) : assertion := (fun x => (A x \/ B x)).
 Notation "A \| B" := (orA A B) (at level 75, right associativity).

 Theorem theorem_I : forall (p : prog) (A B : assertion) (st : state),
 (diamond p (A\|B)) st <-> ((diamond p A) \| (diamond p B)) st.
 Proof.
 Admitted.

 Theorem theorem_II : forall (p : prog) (A B : assertion) (st : state),
 ((diamond p A)/|([p] B) ]-> (diamond p (A /| B))) st.
 Proof.
 intros p A B st. unfold impl. intros H.
 Admitted.

 Theorem theorem_III : forall (p : prog) (A B : assertion) (st : state),
 (diamond p (A/|B)) st <-> ((diamond p A) /| (diamond p B)) st.
 Proof.
 Admitted.

 Theorem theorem_IV : forall (p : prog) (A B : assertion) (st : state),
 ([p](A\|B)) st <-> (([p]A) st)\/(([p]B) st).
 Proof.
 Admitted.

 Theorem theorem_V : forall (p : prog) (st : state),
 (diamond p falseA) st <-> falseA st.
 Proof.
 Admitted.

 Theorem theorem_VI : forall (p : prog) (A : assertion) (st : state),
 ([p] A) st <->  ~(diamond p (fun st' => ~(A st')) st).
 Proof.
 Admitted.
End PDL.