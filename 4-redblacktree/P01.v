Require Export D.

(** **** Exercise: 2 stars (ins_SearchTree)  *)
(** This one is pretty easy, even without proof automation.
  Copy-paste your proof of insert_SearchTree from Extract.v.
  You will need to apply [balance_SearchTree] in two places.
 *)
 Lemma ins_SearchTree:
 forall x vx s lo hi,
                  lo <= int2Z x ->
                  int2Z x < hi ->
                  SearchTree' lo s hi ->
                  SearchTree' lo (ins x vx s) hi.
Proof.
intros.
generalize dependent lo.
generalize dependent hi.
induction s.
repeat constructor. omega. omega.
intros.
inv H1. unfold ins. fold ins. bdestruct (ltb x k).
- apply balance_SearchTree.
  + apply IHs1. omega. omega. auto.
  + auto.
- bdestruct (ltb k x).
  + apply balance_SearchTree. auto. apply IHs2. omega. omega. auto.
  + assert (int2Z x = int2Z k). { omega. }
    constructor; rewrite H3. auto. auto.
Qed.

