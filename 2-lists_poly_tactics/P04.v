Require Export P03.



Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
intros X l.
induction l as [ | n l' IHl'].
- reflexivity.
- simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl'. reflexivity.
Qed.

