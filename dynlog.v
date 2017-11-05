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
  Definition composeRel (x : U) (z : T) : Prop :=
    exists y, R1 x y /\ R2 y z.
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

 Notation "A ->> B" := (impl A B) (at level 80, right associativity).

 Definition assertImpl (A B : assertion) := forall st, A st -> B st.
 Definition assertEquiv (A B : assertion) := assertImpl A B /\ assertImpl B A.
 Definition valid (A : assertion) := forall st, A st.

 Infix "|=" := assertImpl (at level 85, no associativity).
 Infix "=|=" := assertEquiv (at level 90, no associativity).
 Notation "||= A" := (valid A) (at level 90).

 (** See Axiom System 5.5, p.173 *)
 Theorem axiom_II : forall (p : prog) (A B : assertion),
    [p](A ->> B) |= ([p]A ->> [p]B).
 Proof.
 intros p A B. unfold impl. intros st HA. unfold box in *.
 intros H st' H1. apply HA. apply H1. apply H. apply H1.
 Qed.
 
 Definition andA (A B : assertion) : assertion := (fun x => (A x /\ B x)).
 Notation "A /| B" := (andA A B) (at level 75, right associativity).

 Theorem axiom_III : forall (p : prog) (A B : assertion),
 [p](A /| B) =|= ([p]A /| [p]B).
 Proof.
 intros p A B. split.
 * intros st H. split; unfold box in *; intros st' H1;
   apply H in H1; destruct H1 as [H1' H1'']; assumption.
 * unfold assertImpl . intros st [HA HB]. unfold andA in *. 
  intros st' H1. split. now apply HA in H1. now apply HB in H1.
 Qed.

 Theorem axiom_IV : forall (p p': prog) (A : assertion),
  [p U p']A =|= ([p]A /| [p']A). 
 Proof.
 intros p p' A. split.
 * intros st H. split;
   intros st' H1; unfold box in H; specialize H with st';
   simpl in H; unfold union in H; apply H; [now left|now right].
 * intros st [H H']. intros st' H1. simpl in H1.
   unfold union in H1. destruct H1 as [H1|H1]. 
   now apply H in H1. now apply H' in H1.
 Qed.  
 
 Theorem axiom_V : forall (p p': prog) (A : assertion),
 [p; p']A =|= [p][p']A.
 Proof.
 intros p p' A. split.
 * intros st H st'' H1 st3 H2. apply H.
   simpl in *. exists st''. split; assumption.  
 * intros st' H st'' H1. simpl in H1. 
   inversion H1. destruct H0 as [H' H''].
   eapply H. apply H'. apply H''.
Qed.

 Theorem axiom_VI : forall (A B : assertion),
 [A?]B =|= (A ->> B).
 Proof.
 intros A B. split.
 * intros st H. unfold impl. intros HA. apply H.
   simpl. split; [reflexivity|assumption].
 * intros st H st' HT. unfold impl in H. simpl in HT.
   destruct HT as [H1 H2].  rewrite <- H1. now apply H.
 Qed.

 Theorem axiom_VII : forall (p : prog) (A : assertion),
 (A /| [p][Iteration p]A) =|= [Iteration p]A.
 Proof.
 intros p A. split.
 * unfold andA. intros st [HA HI]. unfold box in *.
   simpl in *. intros st' H. inversion H. subst. apply HA.
   eapply HI. apply H0. apply H1. 
 * intros st H. unfold andA. split.
   + unfold box in H. apply H. simpl. apply rt1n_refl.
   + unfold box at 1. intros. unfold box in *.
     intros st'' H1. apply H. simpl in *.
     apply Relation_Operators.rt1n_trans with (y:=st'). apply H0. apply H1.
 Qed.

 Theorem axiom_VIII : forall (p : prog) (A : assertion),
 (A /| [Iteration p](A ->> [p]A)) |= [Iteration p]A. 
 Proof.
 intros p A st. unfold box in *. simpl in *.  
 unfold impl. intros H. destruct H as [HA HI].
 intros st' H. rewrite <- clos_rt_rt1n_iff in *. 
 apply clos_refl_trans_ind_left with (R:=(progSemantics p)) (x:=st).
 apply HA. intros y z Hyz Hy Hpyz. rewrite clos_rt_rt1n_iff in Hyz.
 apply HI with (st':=y) (st'0:=z) in Hyz. apply Hyz. apply Hy. apply Hpyz.
 assumption.
 Qed.
 
 Definition negA (A : assertion) : assertion :=
  fun st' => ~(A st').

 Notation "-] A" := (negA A) (at level 55, right associativity).

 Definition diamond (p : prog) (A : assertion) : assertion :=
  fun st => ~(box p (-]A) st).

 Notation "< p > A" := (diamond p A) (at level 70, right associativity).
 
 Definition orA (A B : assertion) : assertion := (fun x => (A x \/ B x)).
 Notation "A \| B" := (orA A B) (at level 75, right associativity).

 (** See Theorem 5.6, p.174 *)
 Theorem theorem_I : forall (p : prog) (A B : assertion),
 (diamond p (A \| B)) =|= ((diamond p A) \| (diamond p B)).
 Proof.
 intros p A B.
 Admitted.

 Theorem theorem_II : forall (p : prog) (A B : assertion),
 ((diamond p A) /| [p]B) |= diamond p (A /| B).
 Proof.
 intros p A B. 
 Admitted.

 Theorem theorem_III : forall (p : prog) (A B : assertion),
 (diamond p (A /| B)) =|= ((diamond p A) /| (diamond p B)).
 Proof.
 intros p A B.
 Admitted.

 Theorem theorem_IV : forall (p : prog) (A B : assertion),
 [p](A \| B) =|= ([p]A \| [p]B).
 Proof.
 intros p A B. unfold box. split.
 * intros H. unfold orA in H. admit.
 * intros st H st' H1. destruct H as [H|H]; unfold orA;
   [left|right]; now apply H in H1.
 Qed.
   
 Theorem theorem_V : forall (p : prog),
 (diamond p falseA) =|= falseA.
 Proof.
 intros p. split.
 * unfold diamond. intros st H. unfold box in H. rewrite neg_false in H.
   unfold falseA in *. apply H. intros st' H1. unfold negA. intuition.
 * intros st H. unfold falseA in *. now exfalso.
 Qed.

 Theorem theorem_VI : forall (p : prog) (A : assertion),
 [p]A =|=  ~(diamond p (-] A)).
 Proof.
 intros p A.
 Admitted.

 (** See Theorem 5.7, p.175 *)
 Axiom modal_gen : forall (p : prog) (A : assertion), A |= [p]A.
 
 Axiom mon_diamond : forall (A B : assertion) (p : prog),
 (A ->> B) st) |= (diamond p A ->> diamond p B).

 Axiom mod_box : forall (A B : assertion) (p : prog),
 (A ->> B) |= ([p]A ->> [p]B).
 
(** See definitions, p.167 *)
 Definition hoare_triple (A : assertion) (p : prog) (B : assertion):=
  A ->> [p]B.
 Notation "{{ A }}  p  {{ B }}" := (hoare_triple A p B).

 Definition ifA (A : assertion) (p p' : prog) := (A? ; p) U ((-]A)? ; p'). 
 Notation "'IFA' A 'THEN' p 'ELSE' p' 'FI'" :=
  (ifA A p p') (at level 80, right associativity).
 
 Definition whileA (A : assertion) (p : prog) :=
 (Iteration (A? ; p)); (-] A)?.
 Notation "'WHILE' A 'DO' p 'END'" :=
  (whileA A p) (at level 80, right associativity).

 Definition repeatP (p : prog) (A : assertion) :=
  p; (whileA (-] A) p).
 Notation "'REPEAT' p 'UNTIL' A 'END'" :=
  (repeatP p A) (at level 80, right associativity).

 (** See Theorem 5.19, p.186 *)
 Theorem compos_rule : forall (A B C : assertion) (p p' : prog) (st : state),
  (hoare_triple A p B ->> hoare_triple B p' C ->> hoare_triple A (p;p') C) st.
 Proof.
 Admitted.
 
 Theorem condit_rule : forall (A B C : assertion) (p p' : prog) (st : state),
 (hoare_triple (A /| B) p C ->> hoare_triple ((-]A) /| B) p' C ->>
  hoare_triple B (IFA A THEN p ELSE p' FI) C) st.
 Proof.
 Admitted.

 Theorem while_rule : forall (A B : assertion) (p : prog) (st : state),
 (hoare_triple (A /| B) p B ->> hoare_triple B (WHILE A DO p END) ((-]A) /| B)) st.
 Proof.
 Admitted.

 Theorem weaken_rule : forall (A' A B B' : assertion) (p : prog) (st : state),
 ((A' ->> A) ->> (hoare_triple A p B) ->> 
    (B ->> B') ->> (hoare_triple A' p B')) st.
 Proof.
 Admitted.
End PDL.