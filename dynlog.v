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
 
Fixpoint mf (pr : prog) (st st' : state) : Prop :=
 match pr with
 | Elem ap => meanFunc ap st st'
 | Sequence pr1 pr2 => exists st'', mf pr1 st st'' /\ mf pr2 st'' st'
 | Choice pr1 pr2 => mf pr1 st st' \/ mf pr2 st st'
 | Iteration pr1 => True 
 | Test A => st = st' /\ A st
 end.
  
 Definition box (pr : prog) (A : Assertion) : Prop := 
   forall (st st' : state), mf pr st st' -> necess A.


 
 
 
End PDL.