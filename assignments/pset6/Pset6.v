(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 4 *)

Require Import Frap Pset6Sig.


Theorem increment2_init_turn_ok :
  invariantFor increment2_sys increment2_init_turn_inv.
Proof.
Admitted.

Theorem increment2_flag_ok:
  invariantFor increment2_sys increment2_flag_inv.
Proof.
Admitted.

Theorem increment2_correct_ok :
  invariantFor increment2_sys increment2_inv.
Proof.
Admitted.