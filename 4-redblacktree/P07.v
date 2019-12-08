Require Export P06.



Lemma is_redblack_toblack:
  forall s n, is_redblack s Red n -> is_redblack s Black n.
Proof.
intros.
inv H.
- constructor.
- constructor. auto. auto.
Qed.

