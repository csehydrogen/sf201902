Require Export P06.



Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
intros n X l H.
generalize dependent n.
induction l.
- reflexivity.
- destruct n.
  + discriminate.
  + simpl. intros. apply IHl. injection H as H0. apply H0.
Qed.

