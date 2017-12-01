Require Import Notations.
Require Import Logic.
Require Import Relations.
Require Import Setoid.
Require Import Classical.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Arguments clos_refl_trans_1n {A} R x _.
Arguments clos_trans {A} R x _.
Arguments union {A} R1 R2 x y.

Module Type DynLogic.
  Parameters atomProg state : Set.
  Parameter meanFunc : atomProg -> relation state.
End DynLogic.

Module M <: DynLogic.

Inductive id : Type :=
  | Id : string -> id.

Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Definition total_map (A:Set) := id -> A.

Definition t_empty {A:Set} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Set} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition state := total_map nat.

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

Inductive Assign : Set :=
  assign : id -> nat -> Assign.

Definition atomProg := Assign.

(*
Definition meanFunc (a : atomProg) :=
match a with
| assign id rhs => fun st1 st2 : state => st1 = st2
end.
*) 

Definition meanFunc (a : atomProg) :=
  let (id, rhs) := a in fun st1 st2 : state => st2 = (t_update st1 id rhs).
End M.

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

(*
Bind Scope assertion_scope with assertion.
Delimit Scope hprop_scope with assert.
*)

 Definition implA (A B : assertion) : assertion := (fun x => (A x -> B x)).
 
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

 Notation "A ->> B" := (implA A B) (at level 80, right associativity).

 Definition assertImpl (A B : assertion) := forall st, A st -> B st.
 Definition assertEquiv (A B : assertion) := forall st, A st <-> B st.
 Definition valid (A : assertion) := forall st, A st.
  
 Infix "|=" := assertImpl (at level 85, no associativity).
 Infix "=|=" := assertEquiv (at level 90, no associativity).
 Notation "||= A" := (valid A) (at level 90).

 Theorem equivImpl : forall A B, A =|= B <-> (A |= B) /\ (B |= A).
 Proof.
 intros A B; unfold assertImpl, assertEquiv. firstorder.
 Qed.

 Definition andA (A B : assertion) : assertion := (fun x => (A x /\ B x)).
 Notation "A /| B" := (andA A B) (at level 75, right associativity).

 Definition negA (A : assertion) : assertion :=
  fun st' => ~(A st').

 Notation "¬ A" := (negA A) (at level 55, right associativity).

 Definition diamond (p : prog) (A : assertion) : assertion := ¬[p](¬A).

 Notation "< p > A" := (diamond p A) (at level 70, right associativity).
 
 Definition orA (A B : assertion) : assertion := (fun x => (A x \/ B x)).
 Notation "A \| B" := (orA A B) (at level 75, right associativity).

Theorem implIntro : forall A B, ||= A ->> B <-> A |= B.
Proof.
intros A B; unfold assertImpl, valid, implA; split; trivial.
Qed.

Theorem implIntro1 : forall A B C, A |= B ->> C <-> A /| B |= C.
Proof.
intros A B C. unfold assertImpl, implA, andA. firstorder.
Qed.

Proposition assertImplRefl : Reflexive assertImpl.
Admitted.

Proposition assertImplTrans : Transitive assertImpl.
Admitted.

Add Parametric Relation : assertion assertImpl
  reflexivity proved by assertImplRefl
  transitivity proved by assertImplTrans
as AssertImplSetoid.

Proposition assertEquivRefl : Reflexive assertEquiv.
Proof. Admitted.

Proposition assertEquivSymm : Symmetric assertEquiv.
Proof. Admitted.

Proposition assertEquivTrans : Transitive assertEquiv.
Proof. Admitted.

Add Parametric Relation : assertion assertEquiv
  reflexivity proved by assertEquivRefl
  symmetry proved by assertEquivSymm
  transitivity proved by assertEquivTrans
as AssertEquivSetoid.

Add Parametric Morphism : andA
 with signature (assertEquiv ==> assertEquiv ==> assertEquiv)
 as andEquivMorphism.
Proof.
intros A B H1 A' B' H2.
intro st; unfold andA. unfold assertEquiv in *.
firstorder.
Qed.

Add Parametric Morphism : andA
 with signature (assertImpl ++> assertImpl ++> assertImpl)
 as andImplMorphism.
Proof.
intros A B H1 A' B' H2.
intro st; unfold andA. unfold assertEquiv in *.
firstorder.
Qed.

(*
Goal forall A B C, A |= B -> A /| C |= B /| C.
intros A B C H. now rewrite H.
*)

Add Parametric Morphism : orA
 with signature (assertEquiv ==> assertEquiv ==> assertEquiv)
 as orEquivMorphism.
Proof.
intros A B H1 A' B' H2.
intro st; unfold orA. unfold assertEquiv in *.
firstorder.
Qed.

Add Parametric Morphism : orA
 with signature (assertImpl ++> assertImpl ++> assertImpl)
 as orImplMorphism.
intros A B H1 A' B' H2.
intro st; unfold orA. unfold assertEquiv in *.
firstorder.
Qed.

Add Parametric Morphism : implA
 with signature (assertEquiv ==> assertEquiv ==> assertEquiv)
 as implEquivMorphism.
intros A B H1 A' B' H2.
intro st; unfold implA. unfold assertEquiv in *.
firstorder.
Qed.

Add Parametric Morphism : implA
 with signature (assertImpl --> assertImpl ++> assertImpl)
 as implImplMorphism.
Proof.
intros A B H1 A' B' H2 st H3 H4. now apply H2, H3, H1.
Qed.

Add Parametric Morphism : negA
 with signature (assertEquiv ==> assertEquiv)
 as negEquivMorphism.
Proof.
intros A B H st; unfold negA. unfold assertEquiv in *.
firstorder. 
Qed.

Add Parametric Morphism : negA
 with signature (assertImpl --> assertImpl)
 as negImplMorphism.
Proof.
intros A B H st; unfold negA; auto.
Qed.

 (** See Axiom System 5.5, p.173 *)
 Theorem axiom_I : forall (p : prog) (A B : assertion),
    ||= ([p](A ->> B) ->> ([p]A ->> [p]B)).
 Proof.
 intros p A B. apply implIntro. unfold implA. 
 intros st HA. unfold box in *. intros H st' H1. 
 apply HA. apply H1. apply H. apply H1.
 Qed.
 
(* Корректность правила GEN *)
Theorem genSound: forall p A, ||= A -> ||= [p]A.
intros p A HA. unfold valid in *. intros st. 
unfold box. intros st' HP. now apply HA.
Qed.

Add Parametric Morphism (p : prog) : (box p)
 with signature (assertImpl ++> assertImpl)
 as boxImplMorphism.
Proof.
intros A B H. rewrite <- implIntro in H. apply (genSound p) in H.
intro st; apply axiom_I, H.
Qed.

Add Parametric Morphism (p : prog) : (box p)
 with signature (assertEquiv ==> assertEquiv)
 as boxEquivMorphism.
Admitted.
(* Здесь можно использовать equivImpl и переписывание A в B
и наоборот под [p] *)

 Theorem axiom_II : forall (p : prog) (A B : assertion),
   ([p](A /| B)) =|= ([p]A /| [p]B).
 Proof.
 intros p A B. apply equivImpl. split.
 * intros st H. split; unfold box in *; intros st' H1;
   apply H in H1; destruct H1 as [H1' H1'']; assumption.
 * unfold assertImpl . intros st [HA HB]. unfold andA in *. 
   intros st' H1. split. now apply HA in H1. now apply HB in H1. 
 Qed.

 Theorem axiom_III : forall (p p': prog) (A : assertion),
  [p U p']A =|= [p]A /| [p']A.
 Proof.
 intros p p' A. split.
 * intros H. split;
   intros st' H1; unfold box in H; specialize H with st';
   simpl in H; unfold union in H; apply H; [now left|now right].
 * intros [H H']. intros st' H1. simpl in H1.
   unfold union in H1. destruct H1 as [H1|H1]. 
   now apply H in H1. now apply H' in H1.
 Qed.

 Theorem axiom_IV : forall (p p': prog) (A : assertion),
  [p; p']A =|= [p][p']A.
 Proof.
 intros p p' A. split.
 * intros H st'' H1 st3 H2. apply H.
   simpl in *. exists st''. split; assumption.  
 * intros H st'' H1. simpl in H1. 
   inversion H1. destruct H0 as [H' H''].
   eapply H. apply H'. apply H''.
 Qed.

 Theorem axiom_V : forall (A B : assertion),
  [A?]B =|= (A ->> B).
 Proof.
 intros A B. split.
 * intros H. unfold implA. intros HA. apply H.
   simpl. split; [reflexivity|assumption].
 * intros H st' HT. unfold implA in H. simpl in HT.
   destruct HT as [H1 H2].  rewrite <- H1. now apply H.
 Qed.

 Theorem axiom_VI : forall (p : prog) (A : assertion),
 A /| [p][Iteration p]A =|= [Iteration p]A.
 Proof.
 intros p A. split.
 * unfold andA. intros [HA HI]. (* не работает setoid_rewrite <- axiom_IV in HI. *)
   apply <- (axiom_IV p (Iteration p) A st) in HI .
   unfold box in *. simpl in *. intros st' H. inversion H. subst. apply HA.
   apply HI. subst. unfold composeRel. exists y. split. apply H0. apply H1.
 * intros H. unfold andA. split.
   + unfold box in H. apply H. simpl. apply rt1n_refl.
   + unfold box at 1. intros. unfold box in *.
     intros st'' H1. apply H. simpl in *.
     apply Relation_Operators.rt1n_trans with (y:=st'). apply H0. apply H1.
 Qed.

 Theorem axiom_VII : forall (p : prog) (A : assertion),
 (A /| [Iteration p](A ->> [p]A)) |= [Iteration p]A. 
 Proof.
 intros p A st. unfold box in *. simpl in *.  
 unfold implA. intros H. destruct H as [HA HI].
 intros st' H. rewrite <- clos_rt_rt1n_iff in *. 
 apply clos_refl_trans_ind_left with (R:=(progSemantics p)) (x:=st).
 apply HA. intros y z Hyz Hy Hpyz. rewrite clos_rt_rt1n_iff in Hyz.
 apply HI with (st':=y) (st'0:=z) in Hyz. apply Hyz. apply Hy. apply Hpyz.
 assumption.
 Qed.
 
Theorem deMorgan1 : forall A B, ¬(A \| B) =|= ¬A /| ¬B.
Admitted.

Theorem deMorgan2 : forall A B, ¬(A /| B) =|= ¬A \| ¬B.
Admitted.

 (** See Theorem 5.6, p.174 *)
 Theorem theorem_I : forall (p : prog) (A B : assertion),
 diamond p (A \| B) =|= diamond p A \| diamond p B.
 Proof.
intros p A B.
unfold diamond. 
now rewrite deMorgan1, axiom_II, deMorgan2.
Qed.
 
 Lemma dne : forall A, ¬¬A =|= A.
 Proof.
 intros A. split.
 * apply NNPP.
 * intros HA. unfold negA. unfold not.
   intros HNA. now apply HNA.
 Qed.  

 Theorem theorem_II : forall (p : prog) (A : assertion),
 [p]A =|=  ¬(diamond p (¬ A)).
 Proof.
 intros p A. unfold diamond. now rewrite !dne.
 Qed.

 Theorem theorem_III : forall (p : prog) (A B : assertion),
 ([p]A \| [p]B) |= [p](A \| B).  
 Proof.
 intros p A B. intros st HAB. destruct HAB as [HA|HB];
 unfold box; intros st' H; [left|right]; [apply HA|apply HB]; apply H.
 Qed.

  Theorem theorem_IV : forall (p : prog) (A B : assertion),
  (diamond p (A /| B)) |= ((diamond p A) /| (diamond p B)).
 Proof.
 intros p A B. intros st HAB. unfold diamond in *. split;
 unfold negA in *; unfold box in *; intros H; apply HAB;
 intros st' HP; apply or_not_and; [left|right]; now apply H in HP.
 Qed.
 
 Theorem theorem_V : forall (p : prog),
 (diamond p falseA) =|= falseA.
 Proof.
 intros p. split.
 * unfold diamond. intros H. unfold box in H. unfold negA in H.
   rewrite neg_false in H. unfold falseA in *. apply H. 
   intros st' H1. unfold negA. intuition.
 * intros H. unfold falseA in *. now exfalso.
 Qed.

Add Parametric Morphism : valid
 with signature (assertEquiv ==> iff)
 as validEquivMorphism.
Proof.
intros A B H. unfold valid. unfold assertEquiv in H.
firstorder.
Qed.

Ltac propA e1 e2 :=
  setoid_replace e1 with e2;
    [| intro st; unfold andA, orA, implA, negA; tauto].

 Theorem theorem_VI : forall (p : prog) (A B : assertion),
 ((diamond p A) /| [p]B) |= diamond p (A /| B).
 Proof.
intros p A B.
unfold diamond.
rewrite <- implIntro.
propA (¬ ([p] ¬ A) /| [p] B ->> ¬ ([p] ¬ (A /| B)))
      ([p] ¬ (A /| B) /| [p] B ->> [p] ¬ A).
rewrite <- axiom_II.
setoid_replace (¬ (A /| B) /| B) with (¬ A); [| admit].
rewrite implIntro. reflexivity.
Admitted.

 (** See Theorem 5.7, p.175 *)
 Theorem monDiamondSound : forall (A B : assertion) (p : prog),
 ||=(A ->> B) -> ||=(diamond p A ->> diamond p B).
 Proof.
 intros A B p. intros H st.
 intros HdA. rewrite implIntro in H.
 unfold diamond in *. unfold negA in *. unfold not in *.
 intros H1. unfold box in *. apply HdA. intros st' HP HA.
 apply H1 with st'. apply HP. unfold assertImpl in H. now apply H.
 Qed.

 Theorem modBoxSound : forall (A B : assertion) (p : prog),
 ||=(A ->> B) -> ||=([p]A ->> [p]B).
 Proof.
 intros A B p. intros H st.
 assert (H1 : ([p](A ->> B) |= ([p]A ->> [p]B)) ).
 { rewrite <- implIntro. apply axiom_I. } apply H1. 
 now apply genSound.
 Qed.

(** See definitions, p.167 *)
 Definition hoare_triple (A : assertion) (p : prog) (B : assertion):=
  A ->> [p]B.
 Notation "{{ A }}  p  {{ B }}" := (hoare_triple A p B).

 Definition ifA (A : assertion) (p p' : prog) := (A? ; p) U ((¬A)? ; p'). 
 Notation "'IFA' A 'THEN' p 'ELSE' p' 'FI'" :=
  (ifA A p p') (at level 80, right associativity).
 
 Definition whileA (A : assertion) (p : prog) :=
 (Iteration (A? ; p)); (¬A)?.
 Notation "'WHILE' A 'DO' p 'END'" :=
  (whileA A p) (at level 80, right associativity).

 Definition repeatP (p : prog) (A : assertion) :=
  p; (whileA (¬A) p).
 Notation "'REPEAT' p 'UNTIL' A 'END'" :=
  (repeatP p A) (at level 80, right associativity).

 (** See Theorem 5.19, p.186 *)
 Theorem compos_rule : forall (A B C : assertion) (p p' : prog),
  ||=(hoare_triple A p B) -> ||=(hoare_triple B p' C) -> ||=(hoare_triple A (p;p') C).
 Proof.
 intros A B C p p' HAB HBC. unfold hoare_triple in *. 
 unfold implA in *. intros st HA. apply axiom_IV. 
 unfold box in *. intros st' HP' st'' HP''. eapply HBC. eapply HAB.
 apply HA. apply HP'. apply HP''.
 Qed.
 
 Theorem condit_rule : forall (A B C : assertion) (p p' : prog),
 ||=(hoare_triple (A /| B) p C) -> ||=(hoare_triple ((¬A) /| B) p' C) ->
  ||=(hoare_triple B (IFA A THEN p ELSE p' FI) C).
 Proof.
 intros A B C p p' HAB HNAB. unfold hoare_triple in *. 
 unfold ifA. intros st HB. apply axiom_III.
 split; apply axiom_IV; apply axiom_V; 
 [intros HA|intros HNA]; [apply HAB|apply HNAB];
 now split.
 Qed.

 Theorem while_rule : forall (A B : assertion) (p : prog),
 ||=(hoare_triple (A /| B) p B) -> ||=(hoare_triple B (WHILE A DO p END) ((¬A) /| B)).
 Proof.
 intros A B p HABPB st. unfold hoare_triple in *.
 unfold whileA. rewrite implIntro in *. intros HB st'. 
 apply axiom_IV. apply axiom_VI. split.
 * apply axiom_V. intros HNA. now split.
 * unfold box. intros st0 HP0 st1 HP1 st2 HP2.
   simpl in *. destruct HP2 as [HS HNA]. subst.
   split. apply HNA.  
 Admitted.

 Theorem weaken_rule : forall (A' A B B' : assertion) (p : prog),
 ||=(A' ->> A) -> ||=(hoare_triple A p B) -> 
    ||=(B ->> B') -> ||=(hoare_triple A' p B').
 Proof.
 intros A' A B B' p HIA HAB HIB. unfold hoare_triple in *. 
 rewrite implIntro in *. rewrite HIA, HAB, HIB. reflexivity.
 Qed.
End PDL.