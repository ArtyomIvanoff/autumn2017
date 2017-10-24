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
   fun st' => (forall st, progSemantics pr st st' -> A st').
 
 Check box.


 
 
 
End PDL.