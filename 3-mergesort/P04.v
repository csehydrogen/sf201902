Require Export P03.



Lemma merge_len fuel l1 l2
      (FUEL: fuel >= length l1 + length l2):
  length (merge' fuel l1 l2) = length l1 + length l2.
Proof.
generalize dependent l1.
generalize dependent l2.
induction fuel.
- intros. inv FUEL. apply plus_is_O in H0. destruct H0.
  apply length_zero_iff_nil in H. apply length_zero_iff_nil in H0.
  rewrite H. rewrite H0. auto.
- intros. destruct l1. auto. destruct l2. auto.
  simpl. destruct (n <=? n0) eqn:E.
  + simpl. rewrite IHfuel. auto. simpl in FUEL. simpl. omega.
  + simpl. rewrite IHfuel. simpl. omega. simpl. simpl in FUEL. omega.
Qed.

