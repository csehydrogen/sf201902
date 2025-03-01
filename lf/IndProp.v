(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductive definitions_. *)

(** In past chapters, we have seen two ways of stating that a number
    [n] is even: We can say

      (1) [evenb n = true], or

      (2) [exists k, n = double k].

    Yet another possibility is to say that [n] is even if we can
    establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: 

                              ------------             (ev_0)
                                 even 0

                                 even n
                            ----------------          (ev_SS)
                             even (S (S n))
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [even], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even: 

                             --------  (ev_0)
                              even 0
                             -------- (ev_SS)
                              even 2
                             -------- (ev_SS)
                              even 4
*)

(** (Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this shortly. *)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(** This definition is different in one crucial respect from previous
    uses of [Inductive]: the thing we are defining is not a [Type],
    but rather a function from [nat] to [Prop] -- that is, a property
    of numbers.  We've already seen other inductive definitions that
    result in functions -- for example, [list], whose type is [Type ->
    Type].  What is really new here is that, because the [nat]
    argument of [even] appears to the _right_ of the colon, it is
    allowed to take different values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [even], we would have seen an
    error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type
    constructor on the left of the colon is called a "parameter",
    whereas an argument on the right is called an "index".

    For example, in [Inductive list (X : Type) := ...], [X] is a
    parameter; in [Inductive even : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** We can think of the definition of [even] as defining a Coq
    property [even : nat -> Prop], together with primitive theorems
    [ev_0 : even 0] and [ev_SS : forall n, even n -> even (S (S n))]. *)

(** That definition can also be written as follows...

  Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n, even n -> even (S (S n)).
*)

(** ... making explicit the type of the rule [ev_SS]. *)

(** Such "constructor theorems" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [even] for particular numbers... *)

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [even]. *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  even (double n).
Proof.
induction n.
- apply ev_0.
- simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [even] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [even]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [even n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [even n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [even n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [even n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence that [even n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [even n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with [destruct]. *)

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** We could patch this proof by replacing the goal [even n],
    which does not mention the replaced term [S (S n)], by the
    equivalent goal [even (pred (pred (S (S n))))], which does mention
    this term, after which [destruct] can make progress. But it is
    more straightforward to use our inversion lemma. *)

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

(** Coq provides a tactic called [inversion], which does the work of
    our inversion lemma and more besides. *)

(** The [inversion] tactic can detect (1) that the first case
    ([n = 0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductive
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)
Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)  

    Prove the following result using [inversion].  For extra practice,
    prove it using the inversion lemma. *)

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
intros.
inversion H.
inversion H1.
apply H3.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (even5_nonsense)  

    Prove the following result using [inversion]. *)

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
intros.
inversion H.
inversion H1.
inversion H3.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. When
    applied to equalities, as a special case, it does the work of both
    [discriminate] and [injection]. In addition, it carries out the
    [intros] and [rewrite]s that are typically necessary in the case
    of [injection]. It can also be applied, more generally, to analyze
    evidence for inductively defined propositions.  As examples, we'll
    use it to reprove some theorems from [Tactics.v]. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
(* WORKED IN CLASS *)

(** We could try to proceed by case analysis or induction on [n].  But
    since [even] is mentioned in a premise, this strategy would
    probably lead to a dead end, as in the previous section.  Thus, it
    seems better to first try [inversion] on the evidence for [even].
    Indeed, the first case can be solved trivially. *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [even n'] holds.  Since this isn't
    directly useful, it seems that we are stuck and that performing
    case analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [even]:
    namely [E'].  More formally, we can finish our proof by showing
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question.

    To prove a property of [n] holds for all numbers for which [even
    n] holds, we can use induction on [even n]. This requires us to
    prove two things, corresponding to the two ways in which [even n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [even n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [even n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [even] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum)  *)
Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
intros.
induction H.
- apply H0.
- rewrite plus_Sn_m. rewrite plus_Sn_m. apply ev_SS. apply IHeven.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (even'_ev)  

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [even]: *)

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

(** Prove that this definition is logically equivalent to the old
    one.  (You may want to look at the previous theorem when you get
    to the induction step.) *)

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
split.
- intros. induction H.
  apply ev_0. apply ev_SS, ev_0.
  apply ev_sum. apply IHeven'1. apply IHeven'2.
- intros. induction H. apply even'_0.
  assert (S (S n) = 2 + n). { reflexivity. }
  rewrite H0. apply even'_sum. apply even'_2. apply IHeven.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  

    Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
intros.
induction H0.
- intros. apply H.
- intros. apply IHeven. apply evSS_ev. apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)  

    This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
intros.
assert (even ((n + m) + (n + p)) -> even (m + p)).
{ rewrite plus_assoc. rewrite <- plus_assoc with (p := n). rewrite plus_comm with (n := m).
  rewrite plus_assoc. rewrite <- double_plus. rewrite <- plus_assoc.
  intros. apply ev_ev__ev with (double n) (m + p) in H1. apply H1. apply ev_double. }
apply H1. apply ev_sum. apply H. apply H0.
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [even])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** One useful example is the "less than or equal to" relation on
    numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [even] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation)  

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
| tr n m : total_relation n m.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation)  

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop := .

(** [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n']. 
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises)  

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
intros.
induction H0.
- apply H.
- apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
induction n.
- apply le_n.
- apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
intros.
induction H.
- apply le_n.
- apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
intros.
(**
Why does [induction H] not work here?
Since [S n] and [S m] are not in a primitive form, relation [S n = S m] is lost.
[remember (S n) as x; remember (S m) as y] then [induction H].
You will see [x = S n] and [x = S m], which mean [S n = S m].
**)
inversion H.
- apply le_n.
- apply le_trans with (S n).
  + apply le_S. apply le_n.
  + apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
intros.
induction b.
- rewrite <- plus_n_O. apply le_n.
- rewrite <- plus_n_Sm. apply le_S. apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
intros.
split.
- rewrite <- plus_Sn_m in H. apply le_trans with (S n1 + n2).
  apply le_plus_l. apply H.
- apply le_trans with (S (n1 + n2)). rewrite plus_n_Sm. rewrite plus_comm.
  apply le_plus_l. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
unfold lt.
intros.
apply le_S.
apply H.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
induction n.
- intros. apply O_le_n.
- intros. destruct m.
  + discriminate H.
  + apply n_le_m__Sn_le_Sm. apply IHn. simpl in H. apply H.
Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
intros.
generalize dependent n.
induction m.
- intros. inversion H. reflexivity.
- intros. destruct n.
  + reflexivity.
  + simpl. apply IHm. apply Sn_le_Sm__n_le_m. apply H.
Qed.

(** Hint: This one can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
intros.
apply leb_complete in H.
apply leb_complete in H0.
apply leb_correct.
apply le_trans with m.
apply H. apply H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
split. apply leb_complete. apply leb_correct.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, recommended (R_provability)  

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

Invariant: m + n = o
[R 1 1 2]: c1 c2 c3
[R 2 2 6]: impossible
Dropping [c4] and [c5] changes nothing.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)  

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat
:= fun m n => m + n.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
split.
- intros. unfold fR. induction H.
  + reflexivity.
  + simpl. apply eq_S. apply IHR.
  + rewrite <- plus_n_Sm. apply eq_S. apply IHR.
  + inversion IHR. rewrite <- plus_n_Sm in H1. inversion H1. reflexivity.
  + rewrite plus_comm. apply IHR.
- unfold fR. intros. generalize dependent n. generalize dependent o. induction m.
  + intros. simpl in H. rewrite H. generalize dependent n. induction o.
    * intros. apply c1.
    * intros. apply c3. destruct n. discriminate H. apply IHo with n.
      inversion H. reflexivity.
  + intros. destruct o. inversion H. apply c2. apply IHm. inversion H. reflexivity.
Qed.
(** [] *)

End R.

(** **** Exercise: 2 stars, advanced (subsequence)  

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq : list nat -> list nat -> Prop :=
| subseq_empty : forall l, subseq [] l
| subseq_app1 : forall a l1 l2, subseq l1 l2 -> subseq l1 (a::l2)
| subseq_app2 : forall a l1 l2, subseq l1 l2 -> subseq (a::l1) (a::l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
induction l.
- apply subseq_empty.
- apply subseq_app2. apply IHl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
intros.
generalize dependent l3.
generalize dependent l1.
induction l2.
- intros. inversion H. apply subseq_empty.
- simpl. intros. inversion H.
  + apply subseq_empty.
  + apply subseq_app1. apply IHl2. apply H2.
  + apply subseq_app2. apply IHl2. apply H2.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
intros.
generalize dependent l2.
generalize dependent l1.
induction l3.
- intros. inversion H0. rewrite <- H1 in H. inversion H. apply subseq_empty.
- intros. inversion H0; clear H0; subst.
  + inversion H. apply subseq_empty.
  + apply subseq_app1. apply IHl3 with l2. apply H. apply H3.
  + inversion H; clear H; subst.
    * apply subseq_empty.
    * apply subseq_app1. apply IHl3 with l0. apply H2. apply H3.
    * apply subseq_app2. apply IHl3 with l0. apply H2. apply H3.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)  

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(**
[R 2 [1;0]]: c1 c2 c2
[R 1 [1;2;1;0]]: c1 c2 c2 c2 c3 c3 c2 c3
[R 6 [3;2;1;0]]: impossible
**)

(** [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [even] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        As a special case, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows: *)

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

(** Again, for readability, we can also display this definition using
    inference-rule notation.  At the same time, let's introduce a more
    readable infix notation. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the strings
    [[1]] and [[2]] directly.  Since the goal mentions [[1; 2]]
    instead of [[1] ++ [2]], Coq wouldn't be able to figure out how to
    split the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)  

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
unfold not.
intros.
inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
intros.
destruct H.
- apply MUnionL. apply H.
- apply MUnionR. apply H.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
intros.
induction ss.
- apply MStar0.
- simpl. apply MStarApp.
  + apply H. simpl. left. reflexivity.
  + apply IHss. intros. apply H. simpl. right. apply H0.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec)  

    Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
split.
- generalize dependent s1. induction s2.
  + intros. inversion H. reflexivity.
  + intros. inversion H. apply IHs2 in H4. rewrite H4. inversion H3. reflexivity.
- generalize dependent s1. induction s2.
  + intros. rewrite H. simpl. apply MEmpty.
  + intros. simpl. rewrite H. apply (MApp [x] _ s2).
    * apply MChar.
    * apply IHs2. reflexivity.
Qed.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(** Something interesting happens in the [MStarApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re]), and a second one that applies when [x]
    occurs in [s2] (which matches [Star re]).  This is a good
    illustration of why we need induction on evidence for [exp_match],
    rather than induction on the regular expression [re]: The latter
    would only provide an induction hypothesis for strings that match
    [re], which would not allow us to reason about the case [In x
    s2]. *)

  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)  

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool
:= match re with
| EmptySet => false
| EmptyStr => true
| Char _ => true
| App r1 r2 => (re_not_empty r1) && (re_not_empty r2)
| Union r1 r2 => (re_not_empty r1) || (re_not_empty r2)
| Star _ => true
end.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
split.
- intros. destruct H. induction H.
  + reflexivity.
  + reflexivity.
  + simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
  + simpl. rewrite IHexp_match. reflexivity.
  + simpl. rewrite IHexp_match. apply orb_true_iff. right. reflexivity.
  + reflexivity.
  + reflexivity.
- intros. induction re.
  + inversion H.
  + exists []. apply MEmpty.
  + exists [t]. apply MChar.
  + simpl in H. apply andb_true_iff in H. destruct H. apply IHre1 in H. apply IHre2 in H0.
    destruct H. destruct H0. exists (x ++ x0). apply MApp. apply H. apply H0.
  + simpl in H. apply orb_true_iff in H. destruct H.
    * apply IHre1 in H. destruct H. exists x. apply MUnionL. apply H.
    * apply IHre2 in H. destruct H. exists x. apply MUnionR. apply H.
  + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt: *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we have lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    An awkward way to solve this problem is "manually generalizing" 
    over the problematic expressions by adding explicit equality 
    hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. *)

Abort.

(** The tactic [remember e as x] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [x = e] to the context.  Here's how we can use it to
    show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re'], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.

  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
intros.
remember (Star re) as sre.
induction H.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- exists []. split. reflexivity. intros. inversion H.
- inversion Heqsre. apply IHexp_match2 in Heqsre. destruct Heqsre.
  exists (s1 :: x). destruct H1. split.
  + simpl. rewrite H1. reflexivity.
  + intros. inversion H4.
    * rewrite <- H5. rewrite <- H2. apply H.
    * apply H3. apply H5.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (pumping)  

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(** Now, the pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** To streamline the proof (which you are to fill in), the [omega]
    tactic, which is enabled by the following [Require], is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to [omega] in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used. *)

Import Coq.omega.Omega.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  - (* MChar *)
    simpl. omega.
  - (* MApp *)
    simpl. destruct (pumping_constant re1 <=? length s1) eqn:E.
    apply leb_complete in E.
    + apply IH1 in E. destruct E. destruct H. destruct H.
      intros. exists x. exists x0. exists (x1 ++ s2). destruct H. split.
      * rewrite H. rewrite <- app_assoc. rewrite <- app_assoc.
        reflexivity.
      * split. destruct H1. apply H1. intros.
        rewrite app_assoc. rewrite app_assoc. apply MApp.
        destruct H1. rewrite <- app_assoc. apply H2. apply Hmatch2.
    + destruct (pumping_constant re2 <=? length s2) eqn:E2.
      * apply leb_complete in E2. apply IH2 in E2. destruct E2. destruct H. destruct H. destruct H. destruct H0.
        intros. exists (s1 ++ x). exists x0. exists x1. split.
        { rewrite H. rewrite app_assoc. reflexivity. }
        split. apply H0. intros. rewrite <- app_assoc. apply MApp.
        apply Hmatch1. apply H1.
      * apply leb_complete_conv in E. apply leb_complete_conv in E2.
        intros. rewrite app_length in H. omega.
  - (* MUnionL *)
    simpl. intros. destruct (pumping_constant re1 <=? length s1) eqn:E1.
    + apply leb_complete in E1. apply IH in E1. destruct E1. destruct H0. destruct H0.
      exists x, x0, x1. destruct H0. destruct H1. split.
      apply H0. split. apply H1. intros. apply MUnionL. apply H2.
    + apply leb_complete_conv in E1. omega.
  - (* MUnionR *)
    simpl. intros. destruct (pumping_constant re2 <=? length s2) eqn:E2.
    + apply leb_complete in E2. apply IH in E2. destruct E2. destruct H0. destruct H0.
      exists x, x0, x1. destruct H0. destruct H1. split.
      apply H0. split. apply H1. intros. apply MUnionR. apply H2.
    + apply leb_complete_conv in E2. omega.
  - (* MStar0 *)
    simpl. intros. omega.
  - (* MStarApp *)
    simpl. intros. simpl in IH2. destruct (1 <=? length s1) eqn:E.
    + apply leb_complete in E. exists [], s1, s2. split. simpl. reflexivity.
      split. destruct s1. simpl in E. inversion E. discriminate.
      simpl. induction m.
      * simpl. apply Hmatch2.
      * simpl. rewrite <- app_assoc. apply MStarApp. apply Hmatch1. apply IHm.
    + destruct (1 <=? length s2) eqn:E2. apply leb_complete in E2.
      apply IH2 in E2. destruct E2. destruct H0. destruct H0. destruct H0. destruct H1.
      exists (s1 ++ x), x0, x1. split. rewrite H0. rewrite app_assoc. reflexivity.
      split. apply H1. intros. rewrite <- app_assoc.
      apply MStarApp. apply Hmatch1. apply H2.
      apply leb_complete_conv in E. apply leb_complete_conv in E2.
      rewrite app_length in H. omega.
Qed.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [n =? m].
    Instead of generating an equation such as [(n =? m) = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence for
    [reflect P true] is by showing [P] and then using the [ReflectT]
    constructor.  If we invert this statement, this means that it
    should be possible to extract evidence for [P] from a proof of
    [reflect P true].  Similarly, the only way to show [reflect P
    false] is by combining evidence for [~ P] with the [ReflectF]
    constructor.

    It is easy to formalize this intuition and show that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
intros. inversion H.
- split. reflexivity. intros. apply H0.
- split. intros. apply H0 in H2. destruct H2.
  intros. discriminate.
Qed.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** A smoother proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [apply] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, recommended (eqbP_practice)  

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
intros.
induction l.
- unfold not. intros. inversion H0.
- simpl in H. destruct (eqbP n x).
  + inversion H.
  + simpl. unfold not. intros. destruct H1.
    * apply H0. rewrite H1. reflexivity.
    * apply IHl in H. apply H. apply H1.
Qed.
(** [] *)

(** This small example shows how reflection gives us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    The use of the [reflect] property has been popularized by
    _SSReflect_, a Coq library that has been used to formalize
    important results in mathematics, including as the 4-color theorem
    and the Feit-Thompson theorem.  The name SSReflect stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, recommended (nostutter_defn)  

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] repeats the element [1] but does not
    stutter.)  The property "[nostutter mylist]" means that [mylist]
    does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
| nostutter_0 : nostutter []
| nostutter_1 : forall x, nostutter [x]
| nostutter_cons : forall x y l, x <> y -> nostutter (y :: l) -> nostutter (x :: y :: l).

(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_2:  nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply eqb_false; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
repeat match goal with
  h: nostutter _ |- _ => inversion h; clear h; subst
end.
contradiction H1; auto. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

Inductive in_order_merge {X : Type} : list X -> list X -> list X -> Prop:=
| iom0 : in_order_merge [] [] []
| iomL : forall x l1 l2 l, in_order_merge l1 l2 l -> in_order_merge (x :: l1) l2 (x :: l)
| iomR : forall x l1 l2 l, in_order_merge l1 l2 l -> in_order_merge l1 (x :: l2) (x :: l).

Theorem filter_challenge : forall X (test: X->bool) l l1 l2,
in_order_merge l1 l2 l ->
forallb test l1 = true ->
existsb test l2 = false ->
filter test l = l1.
Proof.
intros.
induction H.
- reflexivity.
- simpl in H0. rewrite andb_true_iff in H0. destruct H0.
  simpl. rewrite H0.
  assert (forall l3, l3 = l1 -> x :: l3 = x :: l1).
  { intros. rewrite H3. reflexivity. }
  apply H3. apply (IHin_order_merge H2 H1).
- simpl in H1. simpl. destruct (test x).
  + discriminate H1.
  + apply (IHin_order_merge H0 H1).
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

Theorem filter_challenge_2 : forall test l1 l,
subseq l1 l ->
forallb test l1 = true ->
length l1 <= length (filter test l).
Proof.
intros.
induction H.
- simpl. apply O_le_n.
- simpl. destruct (test a).
  + simpl. apply le_S. apply IHsubseq. apply H0.
  + apply IHsubseq. apply H0.
- simpl. simpl in H0. destruct (test a).
  + simpl. apply le_n_S. apply IHsubseq.
    inversion H0. reflexivity.
  + discriminate H0.
Qed.
    
(** [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes)  

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X : Type} : list X -> Prop :=
| pal_0 : pal []
| pal_1 : forall x, pal [x]
| pal_cons : forall x l, pal l -> pal ([x] ++ l ++ [x]).

Theorem pal_app_rev : forall X (l: list X), pal (l ++ rev l).
Proof.
intros.
induction l.
- apply pal_0.
- simpl. rewrite app_assoc. apply pal_cons. apply IHl.
Qed.

Theorem pal_rev : forall X (l: list X), pal l -> l = rev l.
Proof.
intros.
induction H.
- reflexivity.
- reflexivity.
- simpl. rewrite rev_app_distr. rewrite <- IHpal. reflexivity.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)  

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

(**
Idea here: if you induction on l, it does not work.
pal_cons decompose l into [x] ++ l0 ++ [x], so length l0 = length l - 2.
But induction on l decreases length l only by 1, so induction hypothesis will be useless.
So we introduce general theorem [rev_pal_n] and induction for all l s.t. length l <= n.
Then induction hypothesis will cover length l = n - 2 case.
[rev_con_back] is lemma for proving rev_pal_n.
**)

Theorem rev_con_back {X : Type} :
forall x (l : list X),
x :: l = rev (x :: l) ->
l = [] \/ exists l1, (l = l1 ++ [x] /\ l1 = rev l1).
Proof.
simpl.
intros.
destruct (rev l) eqn:E.
- inversion H. left. reflexivity.
- right. inversion H; clear H; subst. exists l0. split.
  + reflexivity.
  + rewrite rev_app_distr in E. inversion E. rewrite H0. rewrite H0. reflexivity.
Qed.

Theorem rev_pal_n {X : Type} : forall n (l : list X), length l <= n -> l = rev l -> pal l.
Proof.
induction n.
- intros. inversion H. destruct l. apply pal_0. inversion H2.
- intros. destruct l. apply pal_0. apply rev_con_back in H0. destruct H0.
  + rewrite H0. apply pal_1.
  + destruct H0. destruct H0. rewrite H0. apply pal_cons. apply IHn.
    * rewrite H0 in H. simpl in H. apply Sn_le_Sm__n_le_m in H.
      rewrite app_length in H. simpl in H. 
      rewrite plus_comm in H. apply Le.le_Sn_le in H. apply H.
    * apply H1.
Qed.

Theorem rev_pal {X : Type} : forall (l: list X), l = rev l -> pal l.
Proof.
intros.
apply (rev_pal_n (length l)).
apply le_n. apply H.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)  

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
| disjoint_0 : disjoint [] []
| disjoint_L : forall x l1 l2, ~In x l2 -> disjoint l1 l2 -> disjoint (x :: l1) l2
| disjoint_R : forall x l1 l2, ~In x l1 -> disjoint l1 l2 -> disjoint l1 (x :: l2).

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive NoDup {X : Type} : list X -> Prop :=
| NoDup_0 : NoDup []
| NoDup_1 : forall x l, ~In x l -> NoDup l -> NoDup (x :: l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

Theorem NoDup_disjoint {X : Type} : forall (l1 : list X) (l2 : list X), NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
induction l1.
- simpl. intros. induction H. apply disjoint_0.
  apply disjoint_R. unfold not. intros. inversion H1. apply IHNoDup.
- simpl. intros. inversion H; clear H; subst. apply disjoint_L.
  unfold not in *. intros. apply H2. apply In_app_iff.
  right. apply H. apply IHl1. apply H3.
Qed.

(* I'm too lazy for the converse, [disjoint_NoDup]... *)

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)  

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
induction l.
- intros. inversion H.
- simpl. intros. destruct H.
  + exists [], l. rewrite H. reflexivity.
  + apply IHl in H. destruct H as [l1 [l2]]. exists (x0 :: l1), l2.
    rewrite H. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| repeats_x : forall x l, In x l -> repeats (x :: l)
| repeats_l : forall x l, repeats l -> repeats (x :: l).

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
- (* l1 = [], impossible *)
  simpl. intros. inversion H1.
- (* l1 = x :: l1' *)
  simpl. intros. destruct (H (In x l1')).
  + (* In x l1' *)
    apply repeats_x. apply H2.
  + (* ~ In x l1' *)
    apply repeats_l.
    assert (exists l1 l3 : list X, l2 = l1 ++ x :: l3).
    { apply in_split with X x l2 in H0. apply H0. left. reflexivity. }
    destruct H3 as [l1 [l3]]. apply (IHl1' (l1 ++ l3) H).
    * (* forall x, In x l1 -> In x l2 *)
      intros.
      assert (x <> x0).
      { unfold not. intros. apply H2. rewrite <- H5 in H4. apply H4. }
      assert (In x0 l2 -> In x0 (l1 ++ l3)).
      { intros. apply In_app_iff. rewrite H3 in H6. apply In_app_iff in H6. destruct H6.
        left. apply H6. simpl in H6. destruct H6. unfold not in H5. apply H5 in H6. destruct H6.
        right. apply H6. }
      apply H6. apply H0. right. apply H4.
    * (* length l2 < length l1 *)
      rewrite H3 in H1. rewrite app_length in *. simpl in H1.
      rewrite <- plus_n_Sm in H1. unfold lt in H1. apply Sn_le_Sm__n_le_m in H1.
      apply H1.
Qed.

(**
Idea for proof without excluded_middle:
P: In x l1'
Q: forall x, In x l1 -> In x l2
R: ???

We want to prove something like:
P \/ Q
Q -> R
------
P \/ R

With EM, we went like:
P \/ ~P
~P -> Q -> R
-------
P \/ R

So, instead of proving ~P then Q then R, prove Q->R.
**)

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Export Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)  

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
intros.
split.
- intros. inversion H; clear H; subst. destruct s1.
  + left. split. apply H3. apply H4.
  + right. exists s1, s2. inversion H1; clear H1; subst.
    split. reflexivity. split. apply H3. apply H4.
- intros [[H1 H2] | [s1 [s2 [H1 [H2 H3]]]]].
  + apply (MApp []). apply H1. apply H2.
  + rewrite H1. apply (MApp (a :: s1)). apply H2. apply H3.
Qed.

(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)  

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
intros.
split.
- intros. remember (a :: s) as acs. remember (Star re) as sre. induction H.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + destruct s1.
    * apply IHexp_match2. apply Heqacs. apply Heqsre.
    * exists s1, s2. inversion Heqacs; clear Heqacs; subst.
      split. reflexivity. inversion Heqsre; subst. split. apply H. apply H0.
- intros [s0 [s1 [H0 [H1 H2]]]]. rewrite H0. apply (MStarApp (a :: s0)).
  apply H1. apply H2.
Qed.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)  

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: @reg_exp ascii) : bool
:= match re with
| EmptySet => false
| EmptyStr => true
| Char _ => false
| App r1 r2 => (match_eps r1) && (match_eps r2)
| Union r1 r2 => (match_eps r1) || (match_eps r2)
| Star _ => true
end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)  

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)

Lemma app_nil {X : Type} : forall (l1 l2 : list X), [] = l1 ++ l2 -> l1 = [] /\ l2 = [].
Proof.
intros.
destruct l1.
- split. reflexivity. rewrite H. reflexivity.
- inversion H.
Qed.

Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
unfold refl_matches_eps.
intros.
induction re.
- apply ReflectF. unfold not. apply null_matches_none.
- apply ReflectT. apply empty_matches_eps. reflexivity.
- apply ReflectF. unfold not. intros. inversion H.
- (* App *)
  simpl. inversion IHre1.
  + inversion IHre2.
    * (* true true *) apply ReflectT. apply app_exists. exists [], []. split. reflexivity. split. apply H0. apply H2.
    * (* true false *) apply ReflectF. unfold not. intros. apply app_exists in H3. destruct H3 as [s0 [s1 [X0 [X1 X2]]]]. apply app_nil in X0. destruct X0. rewrite H4 in X2. apply H2. apply X2.
  + simpl.
    (* false _ *) apply ReflectF. unfold not. intros. apply app_exists in H1. destruct H1 as [s0 [s1 [X0 [X1 X2]]]]. apply app_nil in X0. destruct X0. rewrite H1 in X1. apply H0. apply X1.
- (* Union *)
  simpl. inversion IHre1.
  + (* true _ *)
    simpl. apply ReflectT. apply union_disj. left. apply H0.
  + inversion IHre2.
    * (* false true *)
      simpl. apply ReflectT. apply union_disj. right. apply H2.
    * (* false false *)
      apply ReflectF. unfold not. intros. apply union_disj in H3. destruct H3.
      apply H0. apply H3. apply H2. apply H3.
- apply ReflectT. apply MStar0.
Qed.

(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)  

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
:= match re with
| EmptySet => EmptySet
| EmptyStr => EmptySet
| Char t => if eqb t a then EmptyStr else EmptySet
| App r1 r2 => if match_eps r1
               then Union (App (derive a r1) r2) (derive a r2)
               else App (derive a r1) r2
| Union r1 r2 => Union (derive a r1) (derive a r2)
| Star r => App (derive a r) (Star r)
end.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

(** **** Exercise: 4 stars, standard, optional (derive_corr)  

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
unfold derives. unfold is_der.
split.
- generalize dependent a. generalize dependent s. induction re.
  + intros. inversion H.
  + intros. inversion H.
  + intros. inversion H. simpl. rewrite eqb_refl. apply MEmpty.
  + intros. apply app_ne in H. destruct H as [[H0 H1] | [s0 [s1 [H0 [H1 H2]]]]].
    * simpl. destruct (match_eps_refl re1). apply MUnionR. apply IHre2. apply H1. apply H in H0. destruct H0.
    * simpl. destruct (match_eps_refl re1). apply MUnionL.
      rewrite H0. apply MApp. apply IHre1. apply H1. apply H2.
      rewrite H0. apply MApp. apply IHre1. apply H1. apply H2.
  + simpl. intros. apply union_disj in H. destruct H.
    * apply MUnionL. apply IHre1. apply H.
    * apply MUnionR. apply IHre2. apply H.
  + simpl. intros. apply star_ne in H. destruct H as [s0 [s1 [H0 [H1 H2]]]].
    rewrite H0. apply MApp. apply IHre. apply H1. apply H2.
- generalize dependent a. generalize dependent s. induction re.
  + intros. inversion H.
  + intros. inversion H.
  + intros. simpl in H. Search ascii. destruct (eqb_spec t a).
    * inversion H. rewrite e. apply MChar.
    * inversion H.
  + intros. simpl in H. destruct (match_eps_refl re1).
    * (* [] =~ re1 *) inversion H; clear H; subst.
      { inversion H3; clear H3; subst. apply (MApp (a :: s1)). apply IHre1. apply H4. apply H5. }
      { apply (MApp []). apply H0. apply IHre2. apply H3. }
    * inversion H; clear H; subst. apply (MApp (a :: s1)). apply IHre1. apply H4. apply H5.
  + simpl. intros. inversion H; clear H; subst.
    * apply MUnionL. apply IHre1. apply H2.
    * apply MUnionR. apply IHre2. apply H1.
  + simpl. intros. inversion H; clear H; subst. apply (MStarApp (a :: s1)).
    apply IHre. apply H3. apply H4.
Qed.

(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)  

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
:= match s with
| [] => match_eps re
| a :: ss => regex_match ss (derive a re)
end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl)  

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
unfold matches_regex.
induction s.
- simpl. intros. destruct (match_eps_refl re).
  + apply ReflectT. apply H.
  + apply ReflectF. apply H.
- simpl. intros. destruct (regex_match s (derive x re)) eqn:E.
  + apply ReflectT. apply (derive_corr x re s).
    destruct (IHs (derive x re)). apply H. discriminate.
  + apply ReflectF. unfold not. intros. apply (derive_corr x re s) in H.
    destruct (IHs (derive x re)). discriminate. apply H0. apply H.
Qed.

(** [] *)

(* Wed Jan 9 12:02:45 EST 2019 *)
