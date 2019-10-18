Require Export P01.


(* Check leb_n_Sn. *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
intros.
reflexivity.
Qed.

