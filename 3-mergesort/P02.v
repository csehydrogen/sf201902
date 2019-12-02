Require Export P01.



Lemma split_permutation l k l1 l2
      (SPLIT: split k l = (l1,l2)):
  Permutation l (l1 ++ l2).
Proof.
generalize dependent l.
generalize dependent l1.
generalize dependent l2.
induction k.
- intros. inv SPLIT. auto.
- intros. simpl in SPLIT. destruct l.
  + inv SPLIT. auto.
  + destruct (split k l) eqn:E. inv SPLIT.
    rewrite <- app_comm_cons. apply perm_skip. apply IHk. apply E.
Qed.

