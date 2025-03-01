Require Export P05.



Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
intros.
apply trans_eq with m.
apply H0. apply H.
Qed.

