Require Export P07.



Lemma makeblack_fiddle:
  forall s n, is_redblack s Black n ->
            exists n, is_redblack (makeBlack s) Red n.
Proof.
intros.
inv H.
- exists O. constructor.
- simpl. exists (S n). constructor.
  apply is_redblack_toblack. auto.
  apply is_redblack_toblack. auto.
- simpl. exists (S n0). constructor. auto. auto.
Qed.

