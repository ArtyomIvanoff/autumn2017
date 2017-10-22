Require Import Notations.
Require Import Logic.
Require Import Relations.Relation_Operators.
Arguments clos_refl_trans_1n {A} R x _.
Arguments clos_trans {A} R x _.
Arguments union {A} R1 R2 x y.

Definition relation (X: Type) := X -> X -> Prop.

Module Type DYNLOGIC.
  Parameters atomic_prog state : Set.
  Parameter meanFunc : atomic_prog -> relation state.
End DYNLOGIC.

Module PDL (Import D : DYNLOGIC).
 Definition Assertion := state -> Prop.

 Definition impl (A B : Assertion) : Assertion := (fun x => (A x -> B x)).
 Definition necess (A : Assertion) : Prop := forall (st : state), A st.
 Definition possib (A : Assertion) : Prop := exists (st : state), A st.

 Inductive prog : Type :=
 | Elem : atomic_prog -> prog
 | Sequence : prog -> prog -> prog
 | Choice : prog -> prog -> prog
 | Iteration : prog -> prog
 | Test : Assertion -> prog.
 
Fixpoint progSemantics  (p : prog) : relation state :=
 match p with
 | Elem ap => meanFunc ap
 | Sequence p1 p2 => clos_trans (progSemantics p1)
 | Choice p1 p2 => union (progSemantics p1) (progSemantics p2) 
 | Iteration p => clos_refl_trans_1n (progSemantics p) 
 | Test A => eq
 end.
  
 Definition box (pr : prog) (A : Assertion) : Prop := 
   forall (st st' : state), progSemantics  pr st st' -> necess A.


 
 
 
End PDL.