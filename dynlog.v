Require Import Notations.
Require Import Logic.

Module Type DYNLOGIC.
  Parameters program state : Set.
  Parameter meanFunc : program -> state * state.
End DYNLOGIC.