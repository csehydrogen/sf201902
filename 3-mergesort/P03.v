Require Export P02.



Lemma merge_permutation fuel l1 l2
      (FUEL: fuel >= length l1 + length l2):
  Permutation (l1++l2) (merge' fuel l1 l2).
Proof.
generalize dependent l1.
generalize dependent l2.
induction fuel.
- intros. inv FUEL. rewrite H0. simpl. Search (_ + _ = 0).
  apply plus_is_O in H0. destruct H0. Search length.
  apply length_zero_iff_nil in H. apply length_zero_iff_nil in H0.
  rewrite H. rewrite H0. auto.
- intros. simpl. destruct l1.
  + simpl. auto.
  + destruct l2.
    * Search (_ ++ []). rewrite app_nil_r. auto.
    * destruct (n <=? n0) eqn:E.
      { rewrite <- app_comm_cons. apply perm_skip. apply IHfuel.
        simpl. simpl in FUEL. omega. }
      { eapply perm_trans. apply Permutation_app_comm. rewrite <- app_comm_cons.
        apply perm_skip. eapply perm_trans. apply Permutation_app_comm. apply IHfuel.
        simpl. simpl in FUEL. omega. }
Qed.

