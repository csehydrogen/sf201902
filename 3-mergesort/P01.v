Require Export D.



Lemma split_len l k l1 l2
      (LEN: k <= length l)
      (SPLIT: split k l = (l1,l2)):
  length l1 = k /\ length l = length l1 + length l2.
Proof.
generalize dependent l.
generalize dependent l1.
generalize dependent l2.
induction k.
- intros. inv SPLIT. auto.
- intros. simpl in SPLIT. destruct l.
  + inv SPLIT. inv LEN.
  + destruct (split k l) eqn:E. destruct l1.
    * inv SPLIT.
    * inv SPLIT. split. 
      { simpl. apply eq_S. apply (IHk l2 l1 l). simpl in LEN.
        Search (S _ <= S _). apply le_S_n in LEN. apply LEN. apply E. }
      { simpl. apply eq_S. apply (IHk l2 l1 l). simpl in LEN.
        Search (S _ <= S _). apply le_S_n in LEN. apply LEN. apply E. }
Qed.