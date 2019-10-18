Require Export P02.



Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
intros s.
induction s as [ | n l' IHl'].
- simpl. reflexivity.
- simpl. destruct n as [ | n'].
  + rewrite leb_n_Sn. reflexivity.
  + simpl. rewrite IHl'. reflexivity.
Qed.

