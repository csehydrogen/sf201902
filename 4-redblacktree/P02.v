Require Export P01.



Lemma empty_tree_SearchTree: SearchTree empty_tree.
Proof.
apply ST_intro with (lo := 0) (hi := 0).
constructor. omega.
Qed.

