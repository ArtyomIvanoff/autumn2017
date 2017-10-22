Require Import Notations.
Require Import Logic.

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
 
 Definition box (ap : atomic_prog) (A : Assertion) : Prop := 
   forall (st st' : state), meanFunc ap st st' -> necess A.


 
 
 
End PDL.