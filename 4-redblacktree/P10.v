Require Export P09.



Lemma insert_is_redblack:
  forall x xv s n, is_redblack s Red n ->
                    exists n', is_redblack (insert x xv s) Red n'.
Proof.
unfold insert.
intros.
inv H.
- simpl. exists (S O). constructor. constructor. constructor.
- apply makeblack_fiddle with (n := S n0). (* n0 really? *)
  apply ins_is_redblack. constructor. auto. auto.
Qed.

Hint Constructors is_redblack.
Theorem redblack_efficient: forall (l: list (key*D.V)),
    exists n, is_redblack (map_reduce (fun kv tr => insert (fst kv) (snd kv) tr) empty_tree l) Red n.
Proof.
  induction l.
  - eauto.
  - destruct IHl.
    eapply insert_is_redblack; eauto.
Qed.

