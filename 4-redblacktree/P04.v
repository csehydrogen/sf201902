Require Export P03.



Theorem lookup_relate:
  forall k t cts ,   Abs t cts -> lookup k t =  cts (int2Z k).
Proof.  (* Copy your proof from Extract.v, and adapt it. *)
intros.
induction H.
- auto.
- simpl. unfold t_update. unfold combine.
  rewrite IHAbs1. rewrite IHAbs2.
  bdestruct (ltb k k0).
  + bdestruct (int2Z k0 =? int2Z k).
    * omega.
    * apply Z.ltb_lt in H1. rewrite H1. auto.
  + bdestruct (ltb k0 k).
    * bdestruct (int2Z k0 =? int2Z k). omega.
      bdestruct (int2Z k <? int2Z k0). omega. auto.
    * bdestruct (int2Z k0 =? int2Z k). auto. omega.
Qed.