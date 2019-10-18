Require Export D.

(* Check app_assoc. *)

Theorem app_nil_r : forall (X: Type) (l : list X),
  l ++ [] = l.
Proof.
intros.
induction l.
- reflexivity.
- simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall (X: Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1.
- simpl. rewrite -> app_nil_r. reflexivity.
- simpl. rewrite -> IHl1, app_assoc. reflexivity.
Qed.

