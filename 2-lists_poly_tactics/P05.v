Require Export P04.

Theorem map_app_distr: forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
intros.
induction l1.
- simpl. reflexivity.
- simpl. rewrite IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl. rewrite <- IHl. rewrite map_app_distr. reflexivity.
Qed.

