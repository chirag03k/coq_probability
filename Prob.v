(* Reasoning with random variables and Probability
in Coq *)

Require Import Reals.
Require Import Rdefinitions.
Open Scope R_scope.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import Lra.
Require Import Coq.Program.Equality.
Require Import List.

Definition frac (n m : Z) : R := IZR n / IZR m.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "[ x ]" := (cons x nil).
Implicit Types X : Type.
Generalizable All Variables.

(** In order to understand the idea of random variables, 
    there must be an idea of a sample space. For this project,
    I limit myself to finite sample spaces. 
    
    
    To work with sample spaces, basics of set theory are needed. 
    I will take some of the more basic concepts for granted 
    (e.g. S1 = S2 <-> S2 = S1) as that is not the focus of this project. *)

Definition HasSetEquality {X} (S1 S2 : list X) := 
  forall (x : X), In x S1 <-> In x S2.
Definition IsSubsetOf {X} (S1 S2 : list X) :=
  forall (x : X), In x S1 -> In x S2.
Definition IsUnionOf {X} (S1 S2 S1US2: list X) := 
  forall (x : X), (In x S2 \/ In x S1) <-> In x S1US2.
Definition IsIntersectOf {X} (S1 S2 S1IS2: list X) := 
  forall (x : X), (In x S1IS2 <-> In x S1 /\ In x S2).
Definition IsRemovalOf {X} (S1 S2 S1RS2: list X) := 
  forall (x : X), (In x S1 /\ ~(In x S2)) <-> In x S1RS2.

(** Notation to make working with sets easier *)
Notation "S1 'SetEqual' S2" := (HasSetEquality S1 S2) (at level 50).
Notation "S1 'subsetOf' S2" := (IsSubsetOf S1 S2) (at level 50).
Notation "S1 'unionWith' S2 'is' S1US2" := (IsUnionOf S1 S2 S1US2) (at level 50).
Notation "S1 'intersectWith' S2 'is' S1IS2" := (IsIntersectOf S1 S2 S1IS2) (at level 50).
Notation "S1 'removing' S2 'is' S1RS2" := (IsRemovalOf S1 S2 S1RS2) (at level 50).

(** Additionally, because many operations over sums need to be performed
    in order to work with probability, I need to prove several properties of 
    them. However, working with sums is incredibly difficult, and I was not
    able to prove some key concepts. So, I decided to assert them as axioms
    in order to focus on the proofs that concerned probability. *)

(** An inductively defined type can be used as a sample space.
    For example, the sample space for the results of a coin flip 
    contains 2 outcomes: heads and tails. 
    
    However, in order to iterate over the whole sample space
    I need to be able to iterate over the elements of the type. So,
    I define a list of elements of the type.
    *)

(** I first create a type alias for the different outcomes
    that are possible. A sample space is a list with 
    no duplicates - I use coercion to make it easy to work with. 
    An event is a subset of a sample space.
    
    Because there are often constraints on the objects I work with in 
    probability, I define a new data type, ObjAndProp that can hold 
    properties about an object, as well as the object itself.
    *)

Inductive ObjAndProp {A : Type} {P : A -> Prop}
  : Type := 
  | OandP (x : A) (p : P x).

Definition obj_of {A P} : (@ObjAndProp A P) -> A := fun x => match x with | OandP x _ => x end.
Definition prop_of {A : Type} {P : A -> Prop} (OP : @ObjAndProp A P) : P (obj_of OP) :=
  match OP with | OandP a p => p end.

(* for my own conceptual understanding and readability *)
Notation "A 'thatSatisfies' P" := (@ObjAndProp A P) (at level 50).

Definition Outcome := Type. 
Definition ListSet X := (list X) thatSatisfies (@NoDup X).
Coercion listSet_to_list {X} (S : ListSet X) : list X := obj_of S.
Definition ListSetFactory {X} (S : list X) (H : NoDup S) := OandP S H.
Definition EmptyListSet {X} : ListSet X := ListSetFactory [] (NoDup_nil X).

Definition SampleSpace X := ListSet X.
Coercion ss_to_l {X} : ListSet X -> list X := obj_of.
Coercion ss_to_nodup {X} (SS : ListSet X) : NoDup (ss_to_l SS) := prop_of SS.
Coercion listset_to_ss {X} (SS : SampleSpace X) : ListSet X := SS.

(** An event is a subset of the sample space. An event is different in different 
    sample spaces/probability contexts, in my construction of probability. I also 
    create a property so that one can verify whether a list is an event. *)
Definition Event {X} (sspace : SampleSpace X) := 
  (ListSet X) thatSatisfies (fun x => IsSubsetOf x sspace). 
Definition EventFactory {X} (sspace : SampleSpace X) 
  (E : ListSet X) (H : IsSubsetOf E sspace): Event sspace := OandP E H.
Definition IsEvent {X} (SSpace : SampleSpace X) (L : ListSet X) : Prop := L subsetOf SSpace.
(* utility coercions *)
Coercion ev_to_l {X SSpace} : Event SSpace -> ListSet X := obj_of.
Coercion event_to_verification {X} {SSpace : SampleSpace X} (E : Event SSpace) : IsEvent SSpace E := prop_of E.
Coercion ev_to_v' {X} {SSpace : SampleSpace X} (E : Event SSpace) : IsSubsetOf E SSpace := prop_of E.

(** I define the set operations on events. *)
(* Two important events are the complement, the whole sample space, and the empty event. *)
Definition EmptyEvent {X} (sspace : SampleSpace X) :=
  EventFactory sspace EmptyListSet (ltac:(unfold IsSubsetOf; intros; simpl; tauto)).
Definition WholeSpace {X} (S : SampleSpace X) := 
  EventFactory S S (ltac:(unfold IsSubsetOf; intros; simpl; tauto)).
Definition Complement {X} (S : SampleSpace X) : Event S -> Event S -> Prop := 
  fun e1 e2 => e1 unionWith e2 is (WholeSpace S).

(** As an example, here is the sample space  for a coin flip - possibly 
    the simplest sample space to work with. *)

Inductive CoinFlip_Outcome : Outcome :=
  | Heads
  | Tails.
Definition CoinFlip_List := [Heads; Tails].

(** I wrote this tactic to prove the lack of duplicates
    in a finite list, since it is simply a matter of computation. *)
Ltac verify_nodup := 
  repeat (apply NoDup_cons);
  unfold In, not; intros;
    repeat match goal with
    | H: _ \/ _ |- _ => destruct H
    | H : ?A = ?B |- _ => discriminate
    | H : False |- _ => destruct H
    end;
  try (apply NoDup_nil).

Definition nodup_coinflip : NoDup CoinFlip_List := 
   ltac:(unfold CoinFlip_List; verify_nodup).

Definition CoinFlip : SampleSpace CoinFlip_Outcome := 
  ListSetFactory [Heads; Tails] (ltac:(verify_nodup)).

(** Now, I define the probability mass function.  

    First, the probability of an event must be <= 1 *)
Definition prob_0_to_1 {X} (S : SampleSpace X) (F : X -> R) : Prop :=
  forall (x : X), In x S -> Rle (INR 0) (F x) /\ Rle (F x) (INR 1).

(** Second, the sum of all the probabilties must be = 1. Note that 
    only the probabilities in the sample space need to sum, not necessarily
    all possible outcomes. *)
Definition prob_sum_1 {X} (S : SampleSpace X) (F : X -> R) : Prop :=
    fold_right Rplus (INR 0) (map F S) = (INR 1).

Definition function X := X -> R.
Definition PMF {X} (S : SampleSpace X) (func : function X) : Prop := prob_0_to_1 S func /\ prob_sum_1 S func.

(** To use these definitions in conjunction, I can create a type
    that will let me wrap them like I had the sample space before. *)
Definition PMF_func {X} (SSpace : SampleSpace X) := (function X) thatSatisfies (PMF SSpace).
Coercion to_regfunc {X} {SSpace : SampleSpace X} (pmf : PMF_func SSpace) : function X := obj_of pmf.

(** Because these proofs are computations, I define a tactic to do this automatically. Then,
    I can easily verify when a function is a valid PMF. *)
Ltac verify_prob_bound := unfold prob_0_to_1; intros o; destruct o; simpl; split; unfold frac; lra.
Ltac verify_prob_sum := unfold prob_sum_1; simpl; unfold frac; lra.

(** Now, I define the probability of an event. This is the sum of the probabilities
    of all the outcomes in the event. I define this using the PMF. *)

Definition event_prob_func {X} {S : SampleSpace X} (pmf_func : PMF_func S) : Event S -> R := fun E => 
  let evSet := obj_of E in 
    let f := obj_of pmf_func in 
      fold_right Rplus (INR 0) (map f evSet).
Notation "F 'Pr_(' E ')' " := (event_prob_func F E) (at level 50).

(** Continuing the example from earlier, here is the PMF of a coin flip.
    Proving the properties is simply a matter of computation *)

Definition CoinFlip_f := 
  fun x => match x with
           | Heads =>  frac 1 2 
           | Tails => frac 1 2
           end.
Fact CoinFlip_f_is_PMF : PMF CoinFlip CoinFlip_f.
Proof. split. verify_prob_bound. verify_prob_sum. Qed.

(* A more complex example that makes use of events would be a dice roll.*)

(* Outcomes *)
Inductive d6_outcome : Outcome :=
  | One
  | Two
  | Three
  | Four
  | Five
  | Six.

(* Sample Space*)
Definition d6_roll : SampleSpace d6_outcome :=
  ListSetFactory [One; Two; Three; Four; Five; Six] (ltac:(verify_nodup)).

(* PMF *)
Definition d6_pmf_f : d6_outcome -> R :=
  fun d => match d with
  | One => frac 1 6
  | Two => frac 1 6
  | Three => frac 1 6
  | Four => frac 1 6
  | Five => frac 1 6
  | Six => frac 1 6
  end.
Fact d6_pmf_is_pmf : PMF d6_roll d6_pmf_f.
Proof. split. verify_prob_bound. verify_prob_sum. Qed.
Definition Di : PMF_func d6_roll := (OandP d6_pmf_f d6_pmf_is_pmf).

(** This custom tactic makes proving subsets much easier, and the following one
    allows me to compute probabilities. *)
Ltac prove_subset :=
  unfold IsSubsetOf;
  unfold In; intros x H; destruct H;
  repeat (
    match goal with
    | [ H : ?A = ?x |- ?A = ?x \/ _ ] => left 
    | [ H : ?A = ?x |- _ \/ _ ] => right
    | [ H : ?A = ?x |- _ = _ ] => auto
    | [ H : ?A = ?x |- False ] => subst
    | [ H : False |- _ ] => destruct H
    | [ H : _ \/ _ |- _ ] => destruct H
    end
  ).
Ltac compute_probability := unfold event_prob_func; simpl; unfold frac; lra.

(** Events *)
(** Now, I demonstate the use of events in the sample space. 
    One possible event is rolling all even numbers. *)
Definition even_roll_set : ListSet d6_outcome := ListSetFactory [Two; Four; Six] (ltac:(verify_nodup)).
Lemma even_roll_subset : even_roll_set subsetOf d6_roll. 
Proof. unfold even_roll_set, d6_roll. simpl. prove_subset. Qed.
Definition even_roll_event_of_d6 : Event d6_roll := EventFactory d6_roll even_roll_set even_roll_subset.
Example evenRollProb : Di Pr_( even_roll_event_of_d6 ) = frac 1 2.
Proof. unfold Di. compute_probability. Qed.

(* Another event is rolling a number less than or equal to 3. *)
Definition leq3_roll_set : ListSet d6_outcome := 
  ListSetFactory [One; Two; Three] (ltac:(verify_nodup)).
Lemma leq3_roll_subset : leq3_roll_set subsetOf d6_roll.
Proof. unfold leq3_roll_set, d6_roll. simpl. prove_subset. Qed. 
Definition leq3_roll_event : Event d6_roll := 
  EventFactory d6_roll leq3_roll_set leq3_roll_subset.
Example leq3RollProb : Di Pr_(leq3_roll_event) = frac 1 2.
Proof. unfold Di. compute_probability. Qed.

(** Now, I define the probability of an event given another event. This is the 
    probability of the intersection of the two events divided by the probability
    of the second event. However, this is not obvious, so I will prove it. 
    
    First, I show that unions, intersections, removals, and subsets of events
    are also events. That is, I 'lift' the resulting sets into being Events by showing
    that they are all subsets of the sample space. *) 

Lemma intersection_in_ss : forall {X} (A B C D : ListSet X), A subsetOf D -> B subsetOf D -> A intersectWith B is C -> C subsetOf D.
Proof. unfold IsSubsetOf, IsIntersectOf. intros. apply H0. apply H1. apply H2. Qed. 
Lemma union_in_ss : forall {X} (A B C D : ListSet X), A subsetOf D -> B subsetOf D -> A unionWith B is C -> C subsetOf D.
Proof. unfold IsSubsetOf, IsUnionOf. intros. specialize (H1 x). specialize (H0 x). specialize (H x). 
  destruct H1. apply H3 in H2. destruct H2 as [Hs | Hs]; [apply H0 | apply H]; apply Hs. Qed.
Lemma removal_in_ss : forall {X} (A B C D : ListSet X), A subsetOf D -> B subsetOf D -> A removing B is C -> C subsetOf D.
Proof. unfold IsSubsetOf, IsRemovalOf. intros. specialize (H1 x). specialize (H x). destruct H1. apply H3 in H2 as Hanb. destruct Hanb. auto. Qed.
Lemma subset_in_ss : forall {X} (A B C : ListSet X), A subsetOf B -> B subsetOf C -> A subsetOf C.
Proof. unfold IsSubsetOf. intros. apply H0. specialize (H x). specialize (H0 x). auto. Qed.

(** I can now show that the result of a set operation is another event by
    constructing an event from the result of the set operation. *)
Definition intersection_is_event {X} (S : SampleSpace X) (A B : Event S) : 
  forall (C : ListSet X), A intersectWith B is C -> IsEvent S C
  := fun C H => EventFactory S C (intersection_in_ss A B C S A B H).
Definition union_is_event {X} (S : SampleSpace X) (A B : Event S) : forall (C : ListSet X), A unionWith B is C -> IsEvent S C
  := fun C H => EventFactory S C (union_in_ss A B C S A B H).
Definition removal_is_event {X} (S : SampleSpace X) (A B : Event S) : forall (C : ListSet X), A removing B is C -> IsEvent S C 
  := fun C H => EventFactory S C (removal_in_ss A B C S A B H).
Definition subset_is_event {X} (S : SampleSpace X) (A B : Event S) : A subsetOf B -> IsEvent S A
  := fun H => EventFactory S A (subset_in_ss A B S H B).

(** Thus, set operations between events is well defined. *)
Definition intersection_of_events {X} (S : SampleSpace X) (A B : Event S) : Event S -> Prop := IsIntersectOf A B.
Definition union_event {X} (S : SampleSpace X) (A B : Event S) : Event S -> Prop := IsUnionOf A B.
Definition removal_event {X} (S : SampleSpace X) (A B :Event S) : Event S -> Prop := IsRemovalOf A B.
Definition subset_event {X} (S : SampleSpace X) (A : Event S) : Event S -> Prop := IsSubsetOf A.

(* Conditional probability *)
Definition prob_A_given_B {X} {S : SampleSpace X} (pmf : PMF_func S) (A B : Event S) :=
  fun (C : Event S) (H : A intersectWith B is C) => let Pr := event_prob_func pmf in (Pr C) / (Pr B).

Notation "F 'Pr_(' A '|' B ')' " := (prob_A_given_B F A B) (at level 50).

(** To make this more usable, however, I attempted to  prove that the intersection must exist trivially, and 
    therefore does not need to be provided. I must do this inductively using propositions because
    I do not have a defined equality for X, since it is arbitrary. This requires the law of excluded
    middle, though. I use a weak version to only prove that an element is in the set, or it isn't. 
    
    However, because the Intersect was defined inductively, and not using eq_dec, it is not guaranteed
    to compute the actual intersect for a given datatype, since that datatype may not have 
    a consistent definition of equality.*)

Axiom in_or_out : forall {X} (x : X) (S : list X), In x S \/ ~ In x S.

Inductive Intersect {X : Type} : list X -> list X -> list X -> Prop :=
  | Intersect_nil : forall B, Intersect [] B []
  | Intersect_cons_in : forall x A B AB, In x B -> Intersect A B AB -> Intersect (x :: A) B (x :: AB)
  | Intersect_cons_not_in : forall x A B AB, ~ In x B -> Intersect A B AB -> Intersect (x :: A) B AB.

Theorem intersection_exists {X : Type} (A B : list X) : exists AB, Intersect A B AB.
Proof.
  induction A as [| x A IHA].
  - exists []. constructor.
  - assert (H : In x B \/ ~ In x B).
  { apply in_or_out. }
  destruct H as [HIn | HNotIn].
  + destruct IHA as [AB HAB].
    exists (x :: AB). constructor; assumption.
  + destruct IHA as [AB HAB].
    exists AB. constructor; assumption.
Qed.

(** Here is an example of conditional probability with the dice roll. *)
Example even_and_leq3 : Event d6_roll := 
  EventFactory d6_roll 
    (ListSetFactory [Two] (ltac:(verify_nodup))) 
      (ltac:(unfold d6_roll; simpl; prove_subset)).
Lemma even_and_leq3_is_intersect : even_roll_event_of_d6 intersectWith leq3_roll_event is even_and_leq3.
Proof. unfold IsIntersectOf, even_roll_event_of_d6, leq3_roll_event. simpl. intros.
        split; intros.
        - destruct H. split; auto. split; auto.
        - repeat destruct H; destruct H0; auto; try discriminate; try (repeat destruct H; discriminate).
          destruct H; auto. destruct H; auto. discriminate.
          destruct H; auto. destruct H. discriminate. destruct H. Qed.
Example even_given_leq3_correct : Di Pr_(even_roll_event_of_d6 | leq3_roll_event)
  even_and_leq3 even_and_leq3_is_intersect = 1/3.
Proof. unfold Di, prob_A_given_B, event_prob_func. simpl. unfold frac. lra. Qed.

Require Import Field.
(* Independence *)

(** Conceptually, two events will be independent if the probability of one occuring
    does not affect the probability of the other. This is often defined as 
    P(A and B) = P(A)P(B). *)

Definition events_independent {X} {S : SampleSpace X} (pmf : PMF_func S) (A B : Event S) : Prop :=
  forall C H, (pmf Pr_(A | B) C H) = (pmf Pr_(A)) * (pmf Pr_(B)).

(* Bayes Theorem *)

(** Finally, I prove an important result in probability: Bayes Theorem. 
    Bayes' is integral in solving many problems involving conditional probability,
    as it offers a new way to compute it.
  *)
Lemma converse_conditional : forall {X} {S : SampleSpace X} (pmf : PMF_func S) (A B AnB: Event S)
  (H: A intersectWith B is AnB ), pmf Pr_(B) > 0 -> pmf Pr_(AnB) = (pmf Pr_(B)) * (pmf Pr_(A | B) AnB H).
Proof. intros. 
  assert (Hdiv : (pmf Pr_(AnB)) / (pmf Pr_(B)) = pmf Pr_(A | B) AnB H).
  { unfold prob_A_given_B. reflexivity. }
  assert (Hg0: pmf Pr_(B) <> 0). { apply Rgt_not_eq. apply H0.  }
  apply Rmult_eq_compat_r with (r := (pmf Pr_(B))) in Hdiv.
  field_simplify in Hdiv. apply Hdiv. rewrite Hdiv in Hg0. destruct Hg0. reflexivity. Qed.

(* I dont prove commutativity of the intersect, but I do use it. *)
Theorem Bayes_Theorem : forall {X} {S : SampleSpace X} (pmf : PMF_func S) (A B AnB: Event S)
  (Hba : B intersectWith A is AnB) (Hab : A intersectWith B is AnB), pmf Pr_(A) > 0 -> pmf Pr_(B) > 0 -> 
  pmf Pr_(A | B) AnB Hab = (pmf Pr_(B | A) AnB Hba) * (pmf Pr_(A)) / (pmf Pr_(B)).
Proof. intros.
  pose proof (converse_conditional pmf B A AnB Hba H) as CC1.
  pose proof (converse_conditional pmf A B AnB Hab H0) as CC2.
  rewrite CC1 in CC2. 
  assert (HbGt : pmf Pr_(B) <> 0). { apply Rgt_not_eq. apply H0. }
  apply Rmult_eq_compat_l with (r := /(pmf Pr_( B))) in CC2.
  field_simplify in CC2. symmetry. rewrite Rmult_comm in CC2. apply CC2.
  auto. auto. Qed.

(** Expected Value *)
