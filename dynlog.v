Require Import Notations.
Require Import Logic.

Module Type DYNLOGIC.
  Parameters program state : Set.
  Parameter meanFunc : program -> state * state.
End DYNLOGIC.

Module PDL (D : DYNLOGIC).
 Inductive prog : Type :=
 | Elem : D.program -> prog
 | Sequence : prog -> prog -> prog
 | Choice : prog -> prog -> prog
 | Iteration : prog -> prog
 | Test : Prop -> prog.

 Definition Assertion := D.state -> Prop.
 Definition box (A : Assertion) : Prop := forall (st : D.state), A st.
 Definition diamond (A : Assertion) : Prop := exists (st : D.state), A st.

End PDL.