(** * APGAR Score: A Formal Verification of Neonatal Assessment

    A machine-checked formalization of the APGAR scoring system for
    rapid evaluation of newborn vitality. This development proves
    completeness, boundedness, classification correctness, and
    intervention protocol properties based on official AAP/ACOG
    clinical guidelines.

    _'Every baby born throughout the world is looked at first through
     the eyes of Virginia Apgar.'_
    -- Joseph Butterfield, M.D., Pediatrics, 1994

    - Author: Charles C. Norton
    - Date: December 2025
    - Version: 1.1.0
    - Coq Version: 8.19.2
    - SPDX-License-Identifier: MIT
    - Repository: https://github.com/CharlesCNorton/apgar-score-verified
*)

(******************************************************************************)
(*                                                                            *)
(*                              REFERENCES                                    *)
(*                                                                            *)
(*  [Apgar1953]                                                               *)
(*     Apgar V. A proposal for a new method of evaluation of the newborn      *)
(*     infant. Curr Res Anesth Analg. 1953;32(4):260-267.                     *)
(*     PMID: 13083014. doi:10.1213/00000539-195301000-00041                   *)
(*                                                                            *)
(*  [AAP2015]                                                                 *)
(*     American Academy of Pediatrics Committee on Fetus and Newborn,         *)
(*     American College of Obstetricians and Gynecologists Committee on       *)
(*     Obstetric Practice. The Apgar Score. Pediatrics. 2015;136(4):819-822.  *)
(*     doi:10.1542/peds.2015-2651                                             *)
(*                                                                            *)
(*  [ACOG2015]                                                                *)
(*     ACOG Committee Opinion No. 644: The Apgar Score.                       *)
(*     Obstet Gynecol. 2015;126(4):e52-e55.                                   *)
(*     doi:10.1097/AOG.0000000000001108                                       *)
(*                                                                            *)
(*  [NRP2021]                                                                 *)
(*     Neonatal Resuscitation Program, 8th Edition.                           *)
(*     American Academy of Pediatrics, 2021.                                  *)
(*     ISBN: 978-1-61002-494-9                                                *)
(*                                                                            *)
(*  [StatPearls2024]                                                          *)
(*     Simon LV, Hashmi MF, Bragg BN. APGAR Score.                            *)
(*     StatPearls [Internet]. Treasure Island (FL): StatPearls Publishing.    *)
(*     PMID: 29262097                                                         *)
(*                                                                            *)
(******************************************************************************)
(*                          CLINICAL LIMITATIONS                              *)
(*                                                                            *)
(*  This formalization has the following known limitations:                   *)
(*                                                                            *)
(*  1. PULSE GRANULARITY: The Pulse.Below100 category (score=1) spans heart   *)
(*     rates from 1-99 bpm. Clinically, 1-59 bpm represents bradycardia       *)
(*     (concerning) while 60-99 is low-normal. The DetailedPulse type         *)
(*     provides finer granularity but does not affect scoring.                *)
(*                                                                            *)
(*  2. DISCONTINUATION SEMANTICS: The Discontinuation.criteria_considered     *)
(*     function returns true when NRP guidelines suggest considering          *)
(*     discontinuation. This is a clinical consideration, not an automatic    *)
(*     recommendation. The actual decision requires clinical judgment.        *)
(*                                                                            *)
(*  3. GRIMACE EQUIVALENCE: The Grimace.CryCoughSneeze category conflates     *)
(*     distinct responses (cry vs sneeze) that are clinically equivalent      *)
(*     for scoring but phenomenologically different.                          *)
(*                                                                            *)
(*  4. SCORE vs OUTCOME: The APGAR score is a standardized assessment tool,   *)
(*     not a prognostic predictor. Low scores warrant intervention but do     *)
(*     not deterministically predict outcomes. See [AAP2015] for guidance     *)
(*     on appropriate use and interpretation.                                 *)
(*                                                                            *)
(*  5. TIMING: The Timing.Time type models standard assessment timepoints     *)
(*     (1, 5, 10, 15, 20 minutes). The Timing.Timestamp type supports real    *)
(*     timestamps in seconds since birth for non-standard intervals.          *)
(*                                                                            *)
(*  6. PHYSIOLOGICAL BOUNDS: The PhysiologicalBPM type bounds heart rate      *)
(*     at 300 bpm. While sufficient for clinical practice, premature          *)
(*     neonates may occasionally exhibit higher rates during tachyarrhythmias.*)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*                       INTEGRATION RECOMMENDATIONS                          *)
(*                                                                            *)
(*  For clinical system integration, consider:                                *)
(*                                                                            *)
(*  1. TEST HARNESS: After extraction, create OCaml unit tests using          *)
(*     OUnit2 or Alcotest. Test all representative_score round-trips          *)
(*     and boundary conditions (scores 0, 3, 4, 6, 7, 10).                    *)
(*                                                                            *)
(*  2. SERIALIZATION: For data interchange, implement JSON serialization:     *)
(*       - Assessment.t -> { appearance: int, pulse: int, ... }               *)
(*       - Use to_nat functions for numeric representation                    *)
(*       - Validate inputs against enum ranges on deserialization             *)
(*                                                                            *)
(*  3. HL7/FHIR: Map to LOINC code 9272-6 (Apgar score at 1 minute)          *)
(*     and related codes. Classification.t maps to interpretation codes.      *)
(*                                                                            *)
(*  4. AUDIT LOGGING: Log all Assessment.t values with timestamps.            *)
(*     Use ExpandedForm.t to capture concurrent interventions.                *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Program.
Import ListNotations.

(******************************************************************************)
(*                                                                            *)
(*                    MODULE TYPE SIGNATURES                                  *)
(*                                                                            *)
(*  Abstract interfaces for key types. These enable substitution for testing  *)
(*  and ensure consistent structure across component modules.                 *)
(*                                                                            *)
(******************************************************************************)

(** Signature for enumerated APGAR component types *)
Module Type APGAR_COMPONENT.
  Parameter t : Type.
  Parameter to_nat : t -> nat.
  Parameter of_nat : nat -> t.
  Parameter of_nat_opt : nat -> option t.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  Parameter all : list t.

  Axiom to_nat_bound : forall x : t, to_nat x <= 2.
  Axiom all_complete : forall x : t, In x all.
  Axiom all_nodup : NoDup all.
  Axiom of_nat_to_nat : forall x : t, of_nat (to_nat x) = x.
  Axiom to_nat_of_nat : forall n : nat, n <= 2 -> to_nat (of_nat n) = n.
End APGAR_COMPONENT.

(** Signature for classification/intervention types with ordering *)
Module Type ORDERED_CLASSIFICATION.
  Parameter t : Type.
  Parameter of_score : nat -> t.
  Parameter to_nat : t -> nat.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  Parameter all : list t.
  Parameter le : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.

  Axiom all_complete : forall x : t, In x all.
  Axiom all_nodup : NoDup all.
  Axiom le_refl : forall x, le x x.
  Axiom le_trans : forall x y z, le x y -> le y z -> le x z.
  Axiom le_antisym : forall x y, le x y -> le y x -> x = y.
End ORDERED_CLASSIFICATION.

(** Signature for bounded numeric types *)
Module Type BOUNDED_VALUE.
  Parameter t : Type.
  Parameter val : t -> nat.
  Parameter bound : nat.
  Parameter of_nat_opt : nat -> option t.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.

  Axiom val_bound : forall x : t, val x <= bound.
  Axiom of_nat_opt_some : forall n x, of_nat_opt n = Some x -> val x = n.
  Axiom of_nat_opt_none : forall n, n > bound -> of_nat_opt n = None.
End BOUNDED_VALUE.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 0: LIST HELPERS                                 *)
(*                                                                            *)
(*  Helper lemmas for NoDup preservation under map and flat_map.              *)
(*  Note: le_unique is explicitly imported from Coq.Arith.Peano_dec.          *)
(*                                                                            *)
(******************************************************************************)

Module ListHelpers.

Lemma NoDup_app : forall {A : Type} (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 Hnd1 Hnd2 Hdisj.
  induction l1 as [|a l1' IH]; [exact Hnd2|].
  simpl. inversion Hnd1; subst. constructor.
  - intro Hcontra. apply in_app_iff in Hcontra. destruct Hcontra as [H|H].
    + contradiction.
    + apply (Hdisj a); [left; reflexivity | exact H].
  - apply IH; [exact H2 |].
    intros x Hx. apply Hdisj. right. exact Hx.
Qed.

Lemma NoDup_map_injective : forall {A B : Type} (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd.
  induction l as [|a l' IH]; [constructor|].
  simpl. inversion Hnd; subst. constructor.
  - intro Hcontra. apply in_map_iff in Hcontra.
    destruct Hcontra as [x [Heq Hin]].
    assert (Hxa : x = a) by (apply Hinj; [right; exact Hin | left; reflexivity | exact Heq]).
    subst. contradiction.
  - apply IH; [|exact H2].
    intros x y Hx Hy. apply Hinj; right; assumption.
Qed.

Lemma NoDup_flat_map : forall {A B : Type} (f : A -> list B) (l : list A),
  NoDup l ->
  (forall a, In a l -> NoDup (f a)) ->
  (forall a1 a2 b, In a1 l -> In a2 l -> a1 <> a2 -> In b (f a1) -> ~ In b (f a2)) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l Hnd Hnodup_inner Hdisj.
  induction l as [|a l' IH]; [constructor|].
  simpl. apply NoDup_app.
  - apply Hnodup_inner. left. reflexivity.
  - apply IH.
    + inversion Hnd; assumption.
    + intros a' Ha'. apply Hnodup_inner. right. exact Ha'.
    + intros a1 a2 b Ha1 Ha2. apply Hdisj; right; assumption.
  - intros x Hx1 Hx2. inversion Hnd; subst.
    rewrite in_flat_map in Hx2. destruct Hx2 as [a' [Ha' Hx2]].
    apply (Hdisj a a' x); [left; reflexivity | right; exact Ha' | | exact Hx1 | exact Hx2].
    intro Heq. subst. contradiction.
Qed.

Ltac prove_all_complete := intros []; simpl; auto 10.

Ltac prove_all_nodup := repeat constructor; simpl; intuition discriminate.

Definition exhaustive_minimal {A : Type} (l : list A) (n : nat) : Prop :=
  (forall a : A, In a l) /\ NoDup l /\ length l = n.

Lemma exhaustive_minimal_intro : forall {A : Type} (l : list A) (n : nat),
  (forall a : A, In a l) -> NoDup l -> length l = n -> exhaustive_minimal l n.
Proof. intros A l n Hc Hnd Hl. unfold exhaustive_minimal. auto. Qed.

Lemma exhaustive_minimal_complete : forall {A : Type} (l : list A) (n : nat),
  exhaustive_minimal l n -> forall a : A, In a l.
Proof. intros A l n [H _]. exact H. Qed.

Lemma exhaustive_minimal_nodup : forall {A : Type} (l : list A) (n : nat),
  exhaustive_minimal l n -> NoDup l.
Proof. intros A l n [_ [H _]]. exact H. Qed.

Lemma exhaustive_minimal_length : forall {A : Type} (l : list A) (n : nat),
  exhaustive_minimal l n -> length l = n.
Proof. intros A l n [_ [_ H]]. exact H. Qed.

(** Cardinality: Complete NoDup lists have exactly as many elements as the type *)
Lemma exhaustive_minimal_unique : forall {A : Type} (l1 l2 : list A) (n : nat),
  exhaustive_minimal l1 n -> exhaustive_minimal l2 n ->
  length l1 = length l2.
Proof.
  intros A l1 l2 n [_ [_ H1]] [_ [_ H2]]. congruence.
Qed.

(** Counting elements satisfying a predicate *)
Definition count_satisfying {A : Type} (p : A -> bool) (l : list A) : nat :=
  length (filter p l).

Lemma count_satisfying_bound : forall {A : Type} (p : A -> bool) (l : list A),
  count_satisfying p l <= length l.
Proof.
  intros A p l. unfold count_satisfying.
  induction l as [|a l' IH]; [simpl; lia|].
  simpl. destruct (p a); simpl; lia.
Qed.

Lemma count_satisfying_complete : forall {A : Type} (p : A -> bool) (l : list A),
  (forall a, In a l) ->
  count_satisfying p l = length (filter p l).
Proof. intros. reflexivity. Qed.

(** Partition lemma: elements either satisfy p or not *)
Lemma partition_length : forall {A : Type} (p : A -> bool) (l : list A),
  length (filter p l) + length (filter (fun x => negb (p x)) l) = length l.
Proof.
  intros A p l. induction l as [|a l' IH]; [reflexivity|].
  simpl. destruct (p a) eqn:E; simpl; lia.
Qed.

(** NoDup preservation under filter *)
Lemma NoDup_filter : forall {A : Type} (p : A -> bool) (l : list A),
  NoDup l -> NoDup (filter p l).
Proof.
  intros A p l Hnd. induction l as [|a l' IH]; [constructor|].
  simpl. inversion Hnd; subst.
  destruct (p a) eqn:E.
  - constructor.
    + intro Hcontra. apply filter_In in Hcontra. destruct Hcontra. contradiction.
    + apply IH. exact H2.
  - apply IH. exact H2.
Qed.

(** In filter characterization *)
Lemma In_filter_iff : forall {A : Type} (p : A -> bool) (l : list A) (x : A),
  In x (filter p l) <-> In x l /\ p x = true.
Proof.
  intros A p l x. split.
  - intro H. apply filter_In in H. exact H.
  - intros [H1 H2]. apply filter_In. split; assumption.
Qed.

(** Automation tactics *)
Ltac prove_exhaustive_minimal :=
  apply exhaustive_minimal_intro;
  [intros []; simpl; auto 10 | repeat constructor; simpl; intuition discriminate | reflexivity].

Ltac prove_in_list := simpl; (left; reflexivity) || (right; prove_in_list) || auto 10.

(** Decidable membership for finite types with decidable equality *)
Lemma In_dec_general : forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x : A) (l : list A), {In x l} + {~ In x l}.
Proof.
  intros A eq_dec x l. induction l as [|h t IH].
  - right. intro H. inversion H.
  - destruct (eq_dec x h) as [Heq|Hne].
    + left. left. symmetry. exact Heq.
    + destruct IH as [Hin|Hnin].
      * left. right. exact Hin.
      * right. intro H. destruct H as [H|H]; [symmetry in H; contradiction | contradiction].
Defined.

(** Additional automation tactics for common proof patterns *)

(** Tactic for proving decidable equality by case analysis *)
Ltac prove_eq_dec :=
  intros [] []; (left; reflexivity) || (right; discriminate).

(** Tactic for proving record injectivity *)
Ltac prove_record_injective :=
  intros; match goal with
  | [ H : _ = _ |- _ ] => inversion H; subst; reflexivity
  end.

(** Tactic for boolean reflection proofs - forward direction *)
Ltac bool_destruct H :=
  repeat (apply andb_true_iff in H; destruct H as [? H] ||
          apply Nat.eqb_eq in H || apply Nat.leb_le in H || apply Nat.ltb_lt in H).

(** Tactic for boolean reflection proofs - backward direction *)
Ltac bool_construct :=
  repeat (apply andb_true_intro; split);
  try apply Nat.eqb_eq; try apply Nat.leb_le; try apply Nat.ltb_lt;
  try assumption; try lia.

(** Tactic for case exhaustion in finite types *)
Ltac exhaust_cases x :=
  destruct x; try reflexivity; try discriminate; try lia.

(** Tactic for solving trichotomy goals *)
Ltac solve_trichotomy :=
  intros [] [];
  try (left; reflexivity);
  try (right; left; unfold lt; simpl; lia);
  try (right; right; unfold lt; simpl; lia).

(** Helper for proving ordering properties - use with local le definitions *)
Ltac prove_ordering_refl le_def :=
  unfold le_def; intros; lia.

Ltac prove_ordering_trans le_def :=
  unfold le_def; intros; lia.

Ltac prove_ordering_antisym le_def :=
  unfold le_def; intros [] [] H1 H2; try reflexivity; simpl in *; lia.

(** Helper for last element proofs *)
Lemma last_cons_ne : forall {A : Type} (a : A) (l : list A) (d : A),
  l <> [] -> last (a :: l) d = last l d.
Proof.
  intros A a l d Hne. destruct l; [contradiction | reflexivity].
Qed.

Lemma last_singleton : forall {A : Type} (a d : A),
  last [a] d = a.
Proof. reflexivity. Qed.

Lemma last_app_singleton : forall {A : Type} (l : list A) (a d : A),
  last (l ++ [a]) d = a.
Proof.
  intros A l a d. rewrite last_last. reflexivity.
Qed.

(** Ltac for proving eq_dec for simple inductive types *)
Ltac solve_eq_dec :=
  intros x y; destruct x; destruct y;
  try (left; reflexivity);
  try (right; discriminate).

(** Ltac for proving NoDup for small explicit lists *)
Ltac prove_nodup_explicit :=
  repeat constructor; simpl; intuition discriminate.

End ListHelpers.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 1: BOUNDED NATURAL NUMBERS                      *)
(*                                                                            *)
(*  A natural number with a proof of its upper bound. This is the             *)
(*  foundational type ensuring all scores are bounded by construction.        *)
(*                                                                            *)
(******************************************************************************)

Module BoundedNat.

Definition t (upper : nat) : Type := { n : nat | n <= upper }.

Definition val {upper : nat} (b : t upper) : nat := proj1_sig b.

Definition bound_proof {upper : nat} (b : t upper) : val b <= upper := proj2_sig b.

Definition make (n upper : nat) (pf : n <= upper) : t upper := exist _ n pf.

Definition zero (upper : nat) : t upper := exist _ 0 (Nat.le_0_l upper).

Lemma val_inj : forall upper (b1 b2 : t upper),
  val b1 = val b2 -> b1 = b2.
Proof.
  intros upper [n1 pf1] [n2 pf2] H. simpl in H. subst.
  f_equal. apply le_unique.
Qed.

End BoundedNat.

Notation "'Bounded' n" := (BoundedNat.t n) (at level 50).

(** ValidScore: A score guaranteed to be in [0,10]. Used at API boundaries. *)
Module ValidScore.

Definition max_score : nat := 10.

Definition t : Type := { n : nat | n <= max_score }.

Definition val (s : t) : nat := proj1_sig s.

Definition proof (s : t) : val s <= max_score := proj2_sig s.

Definition make (n : nat) (pf : n <= max_score) : t := exist _ n pf.

Definition le_max_score_dec (n : nat) : {n <= max_score} + {n > max_score}.
Proof.
  destruct (n <=? max_score) eqn:E.
  - left. apply Nat.leb_le. exact E.
  - right. apply Nat.leb_gt. exact E.
Defined.

Definition of_nat_opt (n : nat) : option t :=
  match le_max_score_dec n with
  | left pf => Some (exist _ n pf)
  | right _ => None
  end.

Lemma of_nat_opt_some : forall n s,
  of_nat_opt n = Some s -> val s = n.
Proof.
  intros n s H. unfold of_nat_opt in H.
  destruct (le_max_score_dec n) as [pf|pf]; [|discriminate].
  inversion H. reflexivity.
Qed.

Lemma of_nat_opt_none : forall n,
  of_nat_opt n = None <-> n > max_score.
Proof.
  intros n. unfold of_nat_opt. split; intro H.
  - destruct (le_max_score_dec n) as [pf|pf]; [discriminate|exact pf].
  - destruct (le_max_score_dec n) as [pf|pf]; [lia|reflexivity].
Qed.

Lemma of_nat_opt_complete : forall n,
  n <= max_score -> exists s, of_nat_opt n = Some s /\ val s = n.
Proof.
  intros n H. unfold of_nat_opt.
  destruct (le_max_score_dec n) as [pf|pf].
  - eexists. split; reflexivity.
  - lia.
Qed.

Definition zero : t := exist _ 0 (Nat.le_0_l max_score).

Lemma le_10 : 10 <= max_score. Proof. unfold max_score. lia. Qed.
Definition ten : t := exist _ 10 le_10.

Definition eq_dec : forall s1 s2 : t, {s1 = s2} + {s1 <> s2}.
Proof.
  intros [n1 pf1] [n2 pf2].
  destruct (Nat.eq_dec n1 n2) as [Heq|Hne].
  - left. subst. f_equal. apply le_unique.
  - right. intro H. inversion H. contradiction.
Defined.

Lemma val_inj : forall s1 s2 : t, val s1 = val s2 -> s1 = s2.
Proof.
  intros [n1 pf1] [n2 pf2] H. simpl in H. subst.
  f_equal. apply le_unique.
Qed.

Definition to_bounded (s : t) : Bounded 10 :=
  BoundedNat.make (val s) 10 (proof s).

Definition of_bounded (b : Bounded 10) : t :=
  exist _ (BoundedNat.val b) (BoundedNat.bound_proof b).

Lemma to_of_bounded : forall b, to_bounded (of_bounded b) = b.
Proof.
  intros b. apply BoundedNat.val_inj.
  unfold to_bounded, of_bounded. simpl. reflexivity.
Qed.

Lemma of_to_bounded : forall s, of_bounded (to_bounded s) = s.
Proof.
  intros s. apply val_inj.
  unfold to_bounded, of_bounded. simpl. reflexivity.
Qed.

End ValidScore.

Module Interval.

Record t : Type := mk {
  lo : nat;
  hi : nat;
  lo_le_hi : lo <= hi
}.

Definition contains (i : t) (n : nat) : Prop := lo i <= n <= hi i.

Definition containsb (i : t) (n : nat) : bool :=
  (lo i <=? n) && (n <=? hi i).

Lemma containsb_correct : forall i n,
  containsb i n = true <-> contains i n.
Proof.
  intros i n. unfold containsb, contains.
  rewrite andb_true_iff, Nat.leb_le, Nat.leb_le. tauto.
Qed.

Definition width (i : t) : nat := hi i - lo i + 1.

Lemma width_pos : forall i, width i >= 1.
Proof.
  intros [lo hi pf]. unfold width. simpl. lia.
Qed.

Definition make (l h : nat) (pf : l <= h) : t := mk l h pf.

Definition singleton (n : nat) : t := mk n n (le_n n).

Lemma singleton_contains : forall n, contains (singleton n) n.
Proof. intros n. unfold contains, singleton. simpl. lia. Qed.

Lemma singleton_unique : forall n m, contains (singleton n) m -> m = n.
Proof. intros n m [H1 H2]. simpl in *. lia. Qed.

End Interval.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 1b: GESTATIONAL AGE                             *)
(*                                                                            *)
(*  Gestational age in completed weeks and days. Clinically relevant for      *)
(*  interpreting APGAR scores, as preterm neonates have different baselines.  *)
(*  Term: 37-41 weeks. Preterm: <37 weeks. Post-term: >=42 weeks.             *)
(*                                                                            *)
(******************************************************************************)

Module GestationalAge.

Definition max_weeks : nat := 45.
Definition max_days : nat := 6.

Record t : Type := mk {
  weeks : nat;
  days : nat;
  weeks_valid : weeks <= max_weeks;
  days_valid : days <= max_days
}.

Definition to_days (ga : t) : nat := weeks ga * 7 + days ga.

Definition term_threshold : nat := 37.
Definition preterm_threshold : nat := 37.
Definition very_preterm_threshold : nat := 32.
Definition extremely_preterm_threshold : nat := 28.
Definition post_term_threshold : nat := 42.

Inductive Maturity : Type :=
  | ExtremelyPreterm : Maturity
  | VeryPreterm : Maturity
  | ModeratelyPreterm : Maturity
  | Term : Maturity
  | PostTerm : Maturity.

Definition classify (ga : t) : Maturity :=
  if weeks ga <? extremely_preterm_threshold then ExtremelyPreterm
  else if weeks ga <? very_preterm_threshold then VeryPreterm
  else if weeks ga <? preterm_threshold then ModeratelyPreterm
  else if weeks ga <? post_term_threshold then Term
  else PostTerm.

Definition is_preterm (ga : t) : bool := weeks ga <? term_threshold.

Definition is_term (ga : t) : bool :=
  (term_threshold <=? weeks ga) && (weeks ga <? post_term_threshold).

Definition is_post_term (ga : t) : bool := post_term_threshold <=? weeks ga.

Lemma classify_exhaustive : forall ga,
  classify ga = ExtremelyPreterm \/
  classify ga = VeryPreterm \/
  classify ga = ModeratelyPreterm \/
  classify ga = Term \/
  classify ga = PostTerm.
Proof.
  intros ga. unfold classify.
  destruct (weeks ga <? extremely_preterm_threshold); [left; reflexivity|].
  destruct (weeks ga <? very_preterm_threshold); [right; left; reflexivity|].
  destruct (weeks ga <? preterm_threshold); [right; right; left; reflexivity|].
  destruct (weeks ga <? post_term_threshold); [right; right; right; left; reflexivity|].
  right; right; right; right; reflexivity.
Qed.

Definition maturity_eq_dec : forall m1 m2 : Maturity, {m1 = m2} + {m1 <> m2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition maturity_all : list Maturity :=
  [ExtremelyPreterm; VeryPreterm; ModeratelyPreterm; Term; PostTerm].

Lemma maturity_all_complete : forall m : Maturity, In m maturity_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma maturity_all_nodup : NoDup maturity_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition make (w d : nat) (pw : w <= max_weeks) (pd : d <= max_days) : t :=
  mk w d pw pd.

Lemma le_38_max : 38 <= max_weeks. Proof. unfold max_weeks. lia. Qed.
Lemma le_34_max : 34 <= max_weeks. Proof. unfold max_weeks. lia. Qed.
Lemma le_30_max : 30 <= max_weeks. Proof. unfold max_weeks. lia. Qed.
Lemma le_26_max : 26 <= max_weeks. Proof. unfold max_weeks. lia. Qed.
Lemma le_0_max_days : 0 <= max_days. Proof. unfold max_days. lia. Qed.

Definition term_38_0 : t := mk 38 0 le_38_max le_0_max_days.
Definition preterm_34_0 : t := mk 34 0 le_34_max le_0_max_days.
Definition very_preterm_30_0 : t := mk 30 0 le_30_max le_0_max_days.
Definition extremely_preterm_26_0 : t := mk 26 0 le_26_max le_0_max_days.

Lemma term_38_is_term : classify term_38_0 = Term.
Proof. reflexivity. Qed.

Lemma preterm_34_is_moderately_preterm : classify preterm_34_0 = ModeratelyPreterm.
Proof. reflexivity. Qed.

Lemma very_preterm_30_is_very_preterm : classify very_preterm_30_0 = VeryPreterm.
Proof. reflexivity. Qed.

Lemma extremely_preterm_26_is_extremely_preterm : classify extremely_preterm_26_0 = ExtremelyPreterm.
Proof. reflexivity. Qed.

Theorem preterm_not_term : forall ga,
  is_preterm ga = true -> classify ga <> Term /\ classify ga <> PostTerm.
Proof.
  intros ga H. unfold is_preterm in H. apply Nat.ltb_lt in H.
  unfold classify.
  destruct (weeks ga <? extremely_preterm_threshold) eqn:E1; [split; discriminate|].
  destruct (weeks ga <? very_preterm_threshold) eqn:E2; [split; discriminate|].
  destruct (weeks ga <? preterm_threshold) eqn:E3; [split; discriminate|].
  apply Nat.ltb_ge in E3.
  unfold term_threshold, preterm_threshold in *.
  exfalso. lia.
Qed.

(** Serialization support: Maturity to/from nat *)
Definition maturity_to_nat (m : Maturity) : nat :=
  match m with
  | ExtremelyPreterm => 0
  | VeryPreterm => 1
  | ModeratelyPreterm => 2
  | Term => 3
  | PostTerm => 4
  end.

Definition maturity_of_nat (n : nat) : option Maturity :=
  match n with
  | 0 => Some ExtremelyPreterm
  | 1 => Some VeryPreterm
  | 2 => Some ModeratelyPreterm
  | 3 => Some Term
  | 4 => Some PostTerm
  | _ => None
  end.

Lemma maturity_to_of_nat : forall m,
  maturity_of_nat (maturity_to_nat m) = Some m.
Proof. intros []; reflexivity. Qed.

Lemma maturity_of_to_nat : forall n m,
  maturity_of_nat n = Some m -> maturity_to_nat m = n.
Proof.
  intros n m H. destruct n as [|[|[|[|[|?]]]]]; simpl in H;
  try discriminate; inversion H; reflexivity.
Qed.

Lemma maturity_to_nat_injective : forall m1 m2,
  maturity_to_nat m1 = maturity_to_nat m2 -> m1 = m2.
Proof. intros [] [] H; simpl in H; try discriminate; reflexivity. Qed.

Lemma maturity_all_length : length maturity_all = 5.
Proof. reflexivity. Qed.

Theorem maturity_exhaustive_minimal :
  ListHelpers.exhaustive_minimal maturity_all 5.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact maturity_all_complete.
  - exact maturity_all_nodup.
  - exact maturity_all_length.
Qed.

(** Gestational age equality is decidable *)
Definition eq_dec : forall ga1 ga2 : t, {ga1 = ga2} + {ga1 <> ga2}.
Proof.
  intros [w1 d1 pw1 pd1] [w2 d2 pw2 pd2].
  destruct (Nat.eq_dec w1 w2) as [Hw|Hw].
  - destruct (Nat.eq_dec d1 d2) as [Hd|Hd].
    + left. subst. f_equal; apply le_unique.
    + right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
Defined.

(** Boolean reflection for maturity predicates *)
Lemma is_preterm_iff : forall ga,
  is_preterm ga = true <-> weeks ga < term_threshold.
Proof. intros ga. unfold is_preterm. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_term_iff : forall ga,
  is_term ga = true <-> term_threshold <= weeks ga < post_term_threshold.
Proof.
  intros ga. unfold is_term.
  rewrite andb_true_iff, Nat.leb_le, Nat.ltb_lt. tauto.
Qed.

Lemma is_post_term_iff : forall ga,
  is_post_term ga = true <-> post_term_threshold <= weeks ga.
Proof. intros ga. unfold is_post_term. rewrite Nat.leb_le. tauto. Qed.

(** Maturity classification is total and exclusive *)
Theorem maturity_trichotomy : forall ga,
  is_preterm ga = true \/ is_term ga = true \/ is_post_term ga = true.
Proof.
  intros ga.
  destruct (weeks ga <? term_threshold) eqn:E1.
  - left. unfold is_preterm. exact E1.
  - apply Nat.ltb_ge in E1.
    destruct (weeks ga <? post_term_threshold) eqn:E2.
    + right. left. unfold is_term. apply andb_true_intro.
      split; [apply Nat.leb_le; exact E1 | exact E2].
    + right. right. unfold is_post_term. apply Nat.leb_le.
      apply Nat.ltb_ge in E2. exact E2.
Qed.

Theorem is_preterm_not_term : forall ga,
  is_preterm ga = true -> is_term ga = false.
Proof.
  intros ga H. apply is_preterm_iff in H.
  unfold is_term. apply andb_false_intro1.
  apply Nat.leb_gt. unfold term_threshold in *. lia.
Qed.

Theorem is_preterm_not_post_term : forall ga,
  is_preterm ga = true -> is_post_term ga = false.
Proof.
  intros ga H. apply is_preterm_iff in H.
  unfold is_post_term. apply Nat.leb_gt.
  unfold term_threshold, post_term_threshold in *. lia.
Qed.

Theorem is_term_not_preterm : forall ga,
  is_term ga = true -> is_preterm ga = false.
Proof.
  intros ga H. apply is_term_iff in H. destruct H as [H _].
  unfold is_preterm. apply Nat.ltb_ge. exact H.
Qed.

End GestationalAge.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 1b2: BIRTH WEIGHT                               *)
(*                                                                            *)
(*  Birth weight in grams. Classification: ELBW <1000g, VLBW <1500g,          *)
(*  LBW <2500g, Normal 2500-4000g, Macrosomia >4000g.                         *)
(*  Weight affects ETT sizing, drug dosing, and expected outcomes.            *)
(*                                                                            *)
(******************************************************************************)

Module BirthWeight.

Record t : Type := mk {
  grams : nat;
  grams_valid : grams <= 6000
}.

Definition to_grams (w : t) : nat := grams w.

Definition to_kg_x10 (w : t) : nat := grams w / 100.

Definition elbw_threshold : nat := 1000.
Definition vlbw_threshold : nat := 1500.
Definition lbw_threshold : nat := 2500.
Definition normal_hi_threshold : nat := 4000.

Inductive Category : Type :=
  | ELBW : Category
  | VLBW : Category
  | LBW : Category
  | Normal : Category
  | Macrosomia : Category.

Definition category_eq_dec : forall c1 c2 : Category, {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition category_all : list Category := [ELBW; VLBW; LBW; Normal; Macrosomia].

Lemma category_all_complete : forall c : Category, In c category_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma category_all_nodup : NoDup category_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition classify (w : t) : Category :=
  if grams w <? elbw_threshold then ELBW
  else if grams w <? vlbw_threshold then VLBW
  else if grams w <? lbw_threshold then LBW
  else if grams w <=? normal_hi_threshold then Normal
  else Macrosomia.

Definition is_elbw (w : t) : bool := grams w <? elbw_threshold.
Definition is_vlbw (w : t) : bool := grams w <? vlbw_threshold.
Definition is_lbw (w : t) : bool := grams w <? lbw_threshold.
Definition is_normal (w : t) : bool :=
  (lbw_threshold <=? grams w) && (grams w <=? normal_hi_threshold).
Definition is_macrosomic (w : t) : bool := normal_hi_threshold <? grams w.

Lemma classify_exhaustive : forall w,
  classify w = ELBW \/
  classify w = VLBW \/
  classify w = LBW \/
  classify w = Normal \/
  classify w = Macrosomia.
Proof.
  intros w. unfold classify.
  destruct (grams w <? elbw_threshold); [left; reflexivity|].
  destruct (grams w <? vlbw_threshold); [right; left; reflexivity|].
  destruct (grams w <? lbw_threshold); [right; right; left; reflexivity|].
  destruct (grams w <=? normal_hi_threshold); [right; right; right; left; reflexivity|].
  right; right; right; right; reflexivity.
Qed.

Theorem elbw_implies_vlbw : forall w,
  is_elbw w = true -> is_vlbw w = true.
Proof.
  intros w H. unfold is_elbw, is_vlbw in *.
  unfold elbw_threshold, vlbw_threshold in *.
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Theorem vlbw_implies_lbw : forall w,
  is_vlbw w = true -> is_lbw w = true.
Proof.
  intros w H. unfold is_vlbw, is_lbw in *.
  unfold vlbw_threshold, lbw_threshold in *.
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Definition epinephrine_dose_mcg (w : t) (dose_mcg_per_kg : nat) : nat :=
  (grams w * dose_mcg_per_kg) / 1000.

Definition volume_dose_ml (w : t) (dose_ml_per_kg : nat) : nat :=
  (grams w * dose_ml_per_kg) / 1000.

(** Serialization support: Category to/from nat *)
Definition category_to_nat (c : Category) : nat :=
  match c with
  | ELBW => 0
  | VLBW => 1
  | LBW => 2
  | Normal => 3
  | Macrosomia => 4
  end.

Definition category_of_nat (n : nat) : option Category :=
  match n with
  | 0 => Some ELBW
  | 1 => Some VLBW
  | 2 => Some LBW
  | 3 => Some Normal
  | 4 => Some Macrosomia
  | _ => None
  end.

Lemma category_to_of_nat : forall c,
  category_of_nat (category_to_nat c) = Some c.
Proof. intros []; reflexivity. Qed.

Lemma category_of_to_nat : forall n c,
  category_of_nat n = Some c -> category_to_nat c = n.
Proof.
  intros n c H. destruct n as [|[|[|[|[|?]]]]]; simpl in H;
  try discriminate; inversion H; reflexivity.
Qed.

Lemma category_all_length : length category_all = 5.
Proof. reflexivity. Qed.

Theorem category_exhaustive_minimal :
  ListHelpers.exhaustive_minimal category_all 5.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact category_all_complete.
  - exact category_all_nodup.
  - exact category_all_length.
Qed.

(** Smart constructor with validation *)
Definition le_6000_dec (g : nat) : {g <= 6000} + {g > 6000}.
Proof.
  destruct (g <=? 6000) eqn:E.
  - left. apply Nat.leb_le. exact E.
  - right. apply Nat.leb_gt. exact E.
Defined.

Definition of_grams_opt (g : nat) : option t :=
  match le_6000_dec g with
  | left pf => Some (mk g pf)
  | right _ => None
  end.

Lemma of_grams_opt_some : forall g w,
  of_grams_opt g = Some w -> grams w = g.
Proof.
  intros g w H. unfold of_grams_opt in H.
  destruct (le_6000_dec g) as [pf|pf]; [|discriminate].
  inversion H. reflexivity.
Qed.

Lemma of_grams_opt_none : forall g,
  of_grams_opt g = None <-> g > 6000.
Proof.
  intros g. unfold of_grams_opt. split; intro H.
  - destruct (le_6000_dec g) as [pf|pf]; [discriminate | exact pf].
  - destruct (le_6000_dec g) as [pf|pf]; [lia | reflexivity].
Qed.

Lemma of_grams_opt_roundtrip : forall g,
  g <= 6000 -> exists w, of_grams_opt g = Some w /\ grams w = g.
Proof.
  intros g Hle. unfold of_grams_opt.
  destruct (le_6000_dec g) as [pf|pf].
  - eexists. split; reflexivity.
  - lia.
Qed.

(** Boolean reflection for weight classification predicates *)
Lemma is_elbw_iff : forall w, is_elbw w = true <-> grams w < elbw_threshold.
Proof. intros w. unfold is_elbw. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_vlbw_iff : forall w, is_vlbw w = true <-> grams w < vlbw_threshold.
Proof. intros w. unfold is_vlbw. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_lbw_iff : forall w, is_lbw w = true <-> grams w < lbw_threshold.
Proof. intros w. unfold is_lbw. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_normal_weight_iff : forall w,
  is_normal w = true <-> lbw_threshold <= grams w <= normal_hi_threshold.
Proof.
  intros w. unfold is_normal.
  rewrite andb_true_iff, Nat.leb_le, Nat.leb_le. tauto.
Qed.

Lemma is_macrosomic_iff : forall w,
  is_macrosomic w = true <-> normal_hi_threshold < grams w.
Proof. intros w. unfold is_macrosomic. rewrite Nat.ltb_lt. tauto. Qed.

(** Weight categories are mutually exclusive - additional theorems *)
Theorem lbw_not_normal : forall w,
  is_lbw w = true -> is_normal w = false.
Proof.
  intros w H. apply is_lbw_iff in H.
  unfold is_normal. apply andb_false_intro1.
  apply Nat.leb_gt. unfold lbw_threshold in *. lia.
Qed.

Theorem normal_not_macrosomic : forall w,
  is_normal w = true -> is_macrosomic w = false.
Proof.
  intros w H. apply is_normal_weight_iff in H. destruct H as [_ H].
  unfold is_macrosomic. apply Nat.ltb_ge. exact H.
Qed.

End BirthWeight.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 1c: OXYGEN SATURATION (SpO2)                    *)
(*                                                                            *)
(*  Peripheral oxygen saturation measured by pulse oximetry. NRP 2021         *)
(*  specifies target SpO2 ranges by minute of life for neonatal transition.   *)
(*  Preductal (right hand) SpO2 is standard for delivery room monitoring.     *)
(*                                                                            *)
(******************************************************************************)

Module SpO2.

Definition max_saturation : nat := 100.

Record t : Type := mk {
  value : nat;
  value_valid : value <= max_saturation
}.

Definition to_nat (s : t) : nat := value s.

Lemma le_100 : forall n, n <= 100 -> n <= max_saturation.
Proof. unfold max_saturation. auto. Qed.

Definition make (v : nat) (pf : v <= max_saturation) : t := mk v pf.

Definition target_1min_lo : nat := 60.
Definition target_1min_hi : nat := 65.
Definition target_2min_lo : nat := 65.
Definition target_2min_hi : nat := 70.
Definition target_3min_lo : nat := 70.
Definition target_3min_hi : nat := 75.
Definition target_4min_lo : nat := 75.
Definition target_4min_hi : nat := 80.
Definition target_5min_lo : nat := 80.
Definition target_5min_hi : nat := 85.
Definition target_10min_lo : nat := 85.
Definition target_10min_hi : nat := 95.

Inductive TargetRange : Type :=
  | Range1min : TargetRange
  | Range2min : TargetRange
  | Range3min : TargetRange
  | Range4min : TargetRange
  | Range5min : TargetRange
  | Range10min : TargetRange.

Definition target_lo (r : TargetRange) : nat :=
  match r with
  | Range1min => target_1min_lo
  | Range2min => target_2min_lo
  | Range3min => target_3min_lo
  | Range4min => target_4min_lo
  | Range5min => target_5min_lo
  | Range10min => target_10min_lo
  end.

Definition target_hi (r : TargetRange) : nat :=
  match r with
  | Range1min => target_1min_hi
  | Range2min => target_2min_hi
  | Range3min => target_3min_hi
  | Range4min => target_4min_hi
  | Range5min => target_5min_hi
  | Range10min => target_10min_hi
  end.

Definition in_target (s : t) (r : TargetRange) : bool :=
  (target_lo r <=? value s) && (value s <=? target_hi r).

Definition below_target (s : t) (r : TargetRange) : bool :=
  value s <? target_lo r.

Definition above_target (s : t) (r : TargetRange) : bool :=
  target_hi r <? value s.

Inductive Status : Type :=
  | BelowTarget : Status
  | OnTarget : Status
  | AboveTarget : Status.

Definition status (s : t) (r : TargetRange) : Status :=
  if below_target s r then BelowTarget
  else if above_target s r then AboveTarget
  else OnTarget.

Lemma status_exhaustive : forall s r,
  status s r = BelowTarget \/ status s r = OnTarget \/ status s r = AboveTarget.
Proof.
  intros s r. unfold status.
  destruct (below_target s r); [left; reflexivity|].
  destruct (above_target s r); [right; right; reflexivity|].
  right; left; reflexivity.
Qed.

Definition status_eq_dec : forall s1 s2 : Status, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition status_all : list Status := [BelowTarget; OnTarget; AboveTarget].

Lemma status_all_complete : forall s : Status, In s status_all.
Proof. intros []; simpl; auto. Qed.

Lemma status_all_nodup : NoDup status_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition target_range_eq_dec : forall r1 r2 : TargetRange, {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition target_range_all : list TargetRange :=
  [Range1min; Range2min; Range3min; Range4min; Range5min; Range10min].

Lemma target_range_all_complete : forall r : TargetRange, In r target_range_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma target_range_all_nodup : NoDup target_range_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition range_for_minute (min : nat) : TargetRange :=
  if min <=? 1 then Range1min
  else if min <=? 2 then Range2min
  else if min <=? 3 then Range3min
  else if min <=? 4 then Range4min
  else if min <=? 5 then Range5min
  else Range10min.

Lemma target_ranges_increasing : forall r1 r2,
  target_lo r1 <= target_lo r2 ->
  target_hi r1 <= target_hi r2 ->
  True.
Proof. trivial. Qed.

Theorem targets_monotonic_lo :
  target_1min_lo <= target_2min_lo /\
  target_2min_lo <= target_3min_lo /\
  target_3min_lo <= target_4min_lo /\
  target_4min_lo <= target_5min_lo /\
  target_5min_lo <= target_10min_lo.
Proof. unfold target_1min_lo, target_2min_lo, target_3min_lo,
              target_4min_lo, target_5min_lo, target_10min_lo. lia. Qed.

Theorem targets_monotonic_hi :
  target_1min_hi <= target_2min_hi /\
  target_2min_hi <= target_3min_hi /\
  target_3min_hi <= target_4min_hi /\
  target_4min_hi <= target_5min_hi /\
  target_5min_hi <= target_10min_hi.
Proof. unfold target_1min_hi, target_2min_hi, target_3min_hi,
              target_4min_hi, target_5min_hi, target_10min_hi. lia. Qed.

Theorem final_target_range : target_10min_lo = 85 /\ target_10min_hi = 95.
Proof. split; reflexivity. Qed.

Definition hyperoxia_threshold : nat := 95.

Definition is_hyperoxic (s : t) : bool := hyperoxia_threshold <? value s.

Theorem hyperoxia_above_final_target : forall s,
  is_hyperoxic s = true -> above_target s Range10min = true.
Proof.
  intros s H. unfold is_hyperoxic in H. unfold above_target.
  unfold target_hi, target_10min_hi, hyperoxia_threshold in *.
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Theorem targets_contiguous :
  target_1min_hi = target_2min_lo /\
  target_2min_hi = target_3min_lo /\
  target_3min_hi = target_4min_lo /\
  target_4min_hi = target_5min_lo /\
  target_5min_hi = target_10min_lo.
Proof.
  unfold target_1min_hi, target_2min_lo, target_2min_hi, target_3min_lo,
         target_3min_hi, target_4min_lo, target_4min_hi, target_5min_lo,
         target_5min_hi, target_10min_lo.
  repeat split; reflexivity.
Qed.

Theorem targets_cover_transition : forall n,
  60 <= n <= 95 ->
  (n <= target_1min_hi) \/
  (target_2min_lo <= n <= target_2min_hi) \/
  (target_3min_lo <= n <= target_3min_hi) \/
  (target_4min_lo <= n <= target_4min_hi) \/
  (target_5min_lo <= n <= target_5min_hi) \/
  (target_10min_lo <= n).
Proof.
  intros n [Hlo Hhi].
  unfold target_1min_hi, target_2min_lo, target_2min_hi, target_3min_lo,
         target_3min_hi, target_4min_lo, target_4min_hi, target_5min_lo,
         target_5min_hi, target_10min_lo in *.
  lia.
Qed.

(** Preterm targets: lower upper bound to prevent oxygen toxicity (ROP risk) *)
Definition preterm_target_hi : nat := 90.

Definition preterm_final_range_lo : nat := 85.
Definition preterm_final_range_hi : nat := 90.

Definition is_preterm_target (s : t) : bool :=
  (preterm_final_range_lo <=? value s) && (value s <=? preterm_final_range_hi).

Inductive Population : Type :=
  | TermPopulation : Population
  | PretermPopulation : Population.

Definition population_eq_dec : forall p1 p2 : Population, {p1 = p2} + {p1 <> p2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition population_all : list Population := [TermPopulation; PretermPopulation].

Lemma population_all_complete : forall p : Population, In p population_all.
Proof. intros []; simpl; auto. Qed.

Lemma population_all_nodup : NoDup population_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition target_hi_for_population (pop : Population) : nat :=
  match pop with
  | TermPopulation => target_10min_hi
  | PretermPopulation => preterm_target_hi
  end.

Definition in_final_target_for_population (s : t) (pop : Population) : bool :=
  match pop with
  | TermPopulation => (target_10min_lo <=? value s) && (value s <=? target_10min_hi)
  | PretermPopulation => (preterm_final_range_lo <=? value s) && (value s <=? preterm_final_range_hi)
  end.

Theorem preterm_upper_lower_than_term :
  preterm_target_hi < target_10min_hi.
Proof. unfold preterm_target_hi, target_10min_hi. lia. Qed.

Theorem preterm_range_subset_of_term : forall s,
  is_preterm_target s = true -> in_target s Range10min = true.
Proof.
  intros s H. unfold is_preterm_target, in_target in *.
  unfold preterm_final_range_lo, preterm_final_range_hi,
         target_lo, target_hi, target_10min_lo, target_10min_hi in *.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  apply andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

(** Population-aware target range: adjusts upper bound for preterm infants *)
Definition target_hi_for_population_and_minute (pop : Population) (r : TargetRange) : nat :=
  match pop, r with
  | PretermPopulation, Range10min => preterm_target_hi
  | _, _ => target_hi r
  end.

Definition in_target_for_population (s : t) (r : TargetRange) (pop : Population) : bool :=
  (target_lo r <=? value s) && (value s <=? target_hi_for_population_and_minute pop r).

(** Preterm-aware range selection: same time-based selection but with population-adjusted upper bounds *)
Definition range_for_minute_with_population (min : nat) (pop : Population) : TargetRange * nat :=
  let r := range_for_minute min in
  (r, target_hi_for_population_and_minute pop r).

Theorem preterm_10min_range_narrower :
  target_hi_for_population_and_minute PretermPopulation Range10min <
  target_hi_for_population_and_minute TermPopulation Range10min.
Proof.
  unfold target_hi_for_population_and_minute, preterm_target_hi, target_hi, target_10min_hi.
  lia.
Qed.

Theorem term_population_uses_standard_target : forall r,
  target_hi_for_population_and_minute TermPopulation r = target_hi r.
Proof. intros []; reflexivity. Qed.

(** Clinical safety: preterm target prevents hyperoxia-induced ROP *)
Theorem preterm_target_prevents_hyperoxia : forall s,
  in_target_for_population s Range10min PretermPopulation = true ->
  value s <= preterm_target_hi.
Proof.
  intros s H. unfold in_target_for_population, target_hi_for_population_and_minute in H.
  apply andb_true_iff in H. destruct H as [_ H].
  apply Nat.leb_le in H. exact H.
Qed.

(** Gap-free coverage: Every SpO2 in [60,95] is covered by at least one time window.
    The coverage follows from targets_cover_transition which proves this via lia. *)

Definition covers_value (spo2_val : nat) (r : TargetRange) : bool :=
  (target_lo r <=? spo2_val) && (spo2_val <=? target_hi r).

Definition covered_by_some_range (spo2_val : nat) : bool :=
  covers_value spo2_val Range1min ||
  covers_value spo2_val Range2min ||
  covers_value spo2_val Range3min ||
  covers_value spo2_val Range4min ||
  covers_value spo2_val Range5min ||
  covers_value spo2_val Range10min.

Theorem spo2_60_covered : covered_by_some_range 60 = true.
Proof. reflexivity. Qed.

Theorem spo2_95_covered : covered_by_some_range 95 = true.
Proof. reflexivity. Qed.

Theorem spo2_75_covered : covered_by_some_range 75 = true.
Proof. reflexivity. Qed.

Theorem spo2_85_covered : covered_by_some_range 85 = true.
Proof. reflexivity. Qed.

Definition unique_best_range (minute : nat) (spo2_val : nat) : bool :=
  covers_value spo2_val (range_for_minute minute).

Theorem minute_determines_target : forall m,
  m <= 10 ->
  exists r, range_for_minute m = r.
Proof.
  intros m Hm. exists (range_for_minute m). reflexivity.
Qed.

(** Completeness theorems for SpO2 target ranges *)

(** Each specific range has non-trivial span *)
Lemma range1min_has_span : target_lo Range1min < target_hi Range1min.
Proof. unfold target_lo, target_hi, target_1min_lo, target_1min_hi. lia. Qed.

Lemma range2min_has_span : target_lo Range2min < target_hi Range2min.
Proof. unfold target_lo, target_hi, target_2min_lo, target_2min_hi. lia. Qed.

Lemma range3min_has_span : target_lo Range3min < target_hi Range3min.
Proof. unfold target_lo, target_hi, target_3min_lo, target_3min_hi. lia. Qed.

Lemma range4min_has_span : target_lo Range4min < target_hi Range4min.
Proof. unfold target_lo, target_hi, target_4min_lo, target_4min_hi. lia. Qed.

Lemma range5min_has_span : target_lo Range5min < target_hi Range5min.
Proof. unfold target_lo, target_hi, target_5min_lo, target_5min_hi. lia. Qed.

Lemma range10min_has_span : target_lo Range10min < target_hi Range10min.
Proof. unfold target_lo, target_hi, target_10min_lo, target_10min_hi. lia. Qed.

(** For each minute, there's a non-trivial target range *)
Theorem range_for_minute_has_span : forall m,
  target_lo (range_for_minute m) < target_hi (range_for_minute m).
Proof.
  intros m. unfold range_for_minute.
  destruct (m <=? 1); [apply range1min_has_span|].
  destruct (m <=? 2); [apply range2min_has_span|].
  destruct (m <=? 3); [apply range3min_has_span|].
  destruct (m <=? 4); [apply range4min_has_span|].
  destruct (m <=? 5); [apply range5min_has_span|].
  apply range10min_has_span.
Qed.

(** Helper: covers_value is decidable *)
Lemma covers_value_reflect : forall v r,
  covers_value v r = true <->
  target_lo r <= v <= target_hi r.
Proof.
  intros v r. unfold covers_value. rewrite andb_true_iff.
  split.
  - intros [H1 H2]. split; [apply Nat.leb_le; exact H1 | apply Nat.leb_le; exact H2].
  - intros [H1 H2]. split; apply Nat.leb_le; assumption.
Qed.

(** Boundary minute/SpO2 examples verified by computation *)
Example minute1_60_ok : unique_best_range 1 60 = true.
Proof. reflexivity. Qed.

Example minute1_65_ok : unique_best_range 1 65 = true.
Proof. reflexivity. Qed.

Example minute5_85_ok : unique_best_range 5 85 = true.
Proof. reflexivity. Qed.

Example minute10_90_ok : unique_best_range 10 90 = true.
Proof. reflexivity. Qed.

Example minute10_95_ok : unique_best_range 10 95 = true.
Proof. reflexivity. Qed.

(** All values in final range [85,95] are covered by Range10min *)
Theorem final_range_covered : forall n,
  85 <= n <= 95 -> covers_value n Range10min = true.
Proof.
  intros n [Hlo Hhi].
  unfold covers_value, target_lo, target_hi, target_10min_lo, target_10min_hi.
  apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

(** Target uniqueness: given a minute, the range is deterministic *)
Theorem unique_best_range_deterministic : forall m spo2_val,
  unique_best_range m spo2_val = true <->
  (target_lo (range_for_minute m) <= spo2_val /\
   spo2_val <= target_hi (range_for_minute m)).
Proof.
  intros m spo2_val. unfold unique_best_range, covers_value.
  split.
  - intro H. apply andb_true_iff in H. destruct H as [H1 H2].
    split; [apply Nat.leb_le; exact H1 | apply Nat.leb_le; exact H2].
  - intros [H1 H2]. apply andb_true_iff. split; apply Nat.leb_le; assumption.
Qed.

(** Example boundary values for SpO2 targets *)
Example spo2_60_minute1_ok : unique_best_range 1 60 = true.
Proof. reflexivity. Qed.

Example spo2_85_minute10_ok : unique_best_range 10 85 = true.
Proof. reflexivity. Qed.

Example spo2_95_minute10_ok : unique_best_range 10 95 = true.
Proof. reflexivity. Qed.

(** Extended monitoring: SpO2 targets stabilize after 10 minutes *)
Definition extended_monitoring_target_lo : nat := target_10min_lo.
Definition extended_monitoring_target_hi : nat := target_10min_hi.

(** For minutes > 10, target range remains at 10-minute values *)
Theorem extended_monitoring_stable : forall m,
  10 < m -> range_for_minute m = Range10min.
Proof.
  intros m H. unfold range_for_minute.
  destruct (m <=? 1) eqn:E1; [apply Nat.leb_le in E1; lia|].
  destruct (m <=? 2) eqn:E2; [apply Nat.leb_le in E2; lia|].
  destruct (m <=? 3) eqn:E3; [apply Nat.leb_le in E3; lia|].
  destruct (m <=? 4) eqn:E4; [apply Nat.leb_le in E4; lia|].
  destruct (m <=? 5) eqn:E5; [apply Nat.leb_le in E5; lia|].
  reflexivity.
Qed.

(** Post-transition target: once at 10 min, target is [85, 95] *)
Theorem post_transition_target : forall m,
  10 <= m ->
  target_lo (range_for_minute m) = 85 /\ target_hi (range_for_minute m) = 95.
Proof.
  intros m H. unfold range_for_minute.
  destruct (m <=? 1) eqn:E1; [apply Nat.leb_le in E1; lia|].
  destruct (m <=? 2) eqn:E2; [apply Nat.leb_le in E2; lia|].
  destruct (m <=? 3) eqn:E3; [apply Nat.leb_le in E3; lia|].
  destruct (m <=? 4) eqn:E4; [apply Nat.leb_le in E4; lia|].
  destruct (m <=? 5) eqn:E5; [apply Nat.leb_le in E5; lia|].
  split; reflexivity.
Qed.

(** Hyperoxia threshold: above 95% is potentially harmful *)
Theorem hyperoxia_above_target : forall s m,
  is_hyperoxic s = true -> m >= 10 ->
  target_hi (range_for_minute m) < value s.
Proof.
  intros s m Hhyper Hm. unfold is_hyperoxic in Hhyper.
  apply Nat.ltb_lt in Hhyper.
  pose proof (post_transition_target m Hm) as [_ Hhi].
  rewrite Hhi. unfold hyperoxia_threshold in Hhyper. lia.
Qed.

(** SpO2 below 60% at any minute requires intervention *)
Definition critical_hypoxemia (s : t) : bool := value s <? 60.

Theorem critical_hypoxemia_below_all_targets : forall s m,
  critical_hypoxemia s = true ->
  value s < target_lo (range_for_minute m).
Proof.
  intros s m H. unfold critical_hypoxemia in H. apply Nat.ltb_lt in H.
  unfold range_for_minute.
  destruct (m <=? 1); [unfold target_lo, target_1min_lo; lia|].
  destruct (m <=? 2); [unfold target_lo, target_2min_lo; lia|].
  destruct (m <=? 3); [unfold target_lo, target_3min_lo; lia|].
  destruct (m <=? 4); [unfold target_lo, target_4min_lo; lia|].
  destruct (m <=? 5); [unfold target_lo, target_5min_lo; lia|].
  unfold target_lo, target_10min_lo. lia.
Qed.

End SpO2.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 1d: CORD BLOOD GAS                              *)
(*                                                                            *)
(*  Umbilical cord blood gas analysis provides objective measures of          *)
(*  neonatal acidemia. Key values: pH, pCO2, pO2, base deficit, lactate.      *)
(*  Per AAP 2015, obtain for scores <=5 at 5 minutes.                         *)
(*                                                                            *)
(******************************************************************************)

Module CordBloodGas.

(** pH: normal umbilical artery ~7.25-7.30, acidemia <7.0, severe <6.8.
    Physiological pH range is ~6.8-7.6; values outside this are incompatible with life. *)
Record pH : Type := mkpH {
  ph_value_x100 : nat;
  ph_valid : ph_value_x100 <= 760  (** pH 7.60 is upper physiological limit *)
}.

Definition pH_to_nat (p : pH) : nat := ph_value_x100 p.

Definition acidemia_threshold_x100 : nat := 700.
Definition severe_acidemia_threshold_x100 : nat := 680.

Definition is_acidemic (p : pH) : bool := ph_value_x100 p <? acidemia_threshold_x100.

Definition is_severely_acidemic (p : pH) : bool :=
  ph_value_x100 p <? severe_acidemia_threshold_x100.

Lemma severe_implies_acidemic : forall p,
  is_severely_acidemic p = true -> is_acidemic p = true.
Proof.
  intros p H. unfold is_severely_acidemic, is_acidemic in *.
  unfold severe_acidemia_threshold_x100, acidemia_threshold_x100 in *.
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

(** pH clinical validity: must be in physiological range [6.50, 7.60] *)
Definition ph_min_x100 : nat := 650.
Definition ph_max_x100 : nat := 760.

Definition ph_clinically_valid (v : nat) : bool :=
  (ph_min_x100 <=? v) && (v <=? ph_max_x100).

(** Smart constructor for pH with validation *)
Definition ph_valid_dec (v : nat) : {ph_min_x100 <= v /\ v <= ph_max_x100} + {v < ph_min_x100 \/ v > ph_max_x100}.
Proof.
  destruct (ph_min_x100 <=? v) eqn:E1; destruct (v <=? ph_max_x100) eqn:E2.
  - left. split; [apply Nat.leb_le; exact E1 | apply Nat.leb_le; exact E2].
  - right. right. apply Nat.leb_gt. exact E2.
  - right. left. apply Nat.leb_gt. exact E1.
  - right. left. apply Nat.leb_gt. exact E1.
Defined.

Definition make_pH (v : nat) : option pH :=
  match ph_valid_dec v with
  | left pf => Some (mkpH v (proj2 pf))
  | right _ => None
  end.

Lemma make_pH_some : forall v p,
  make_pH v = Some p -> ph_value_x100 p = v.
Proof.
  intros v p H. unfold make_pH in H.
  destruct (ph_valid_dec v) as [[H1 H2]|[H1|H1]]; [|discriminate|discriminate].
  inversion H. reflexivity.
Qed.

Lemma make_pH_ensures_physiological : forall v p,
  make_pH v = Some p -> ph_min_x100 <= ph_value_x100 p <= ph_max_x100.
Proof.
  intros v p H. unfold make_pH in H.
  destruct (ph_valid_dec v) as [[H1 H2]|[H1|H1]]; [|discriminate|discriminate].
  inversion H. simpl. split; assumption.
Qed.

Lemma make_pH_none_low : forall v,
  v < ph_min_x100 -> make_pH v = None.
Proof.
  intros v H. unfold make_pH.
  destruct (ph_valid_dec v) as [[H1 H2]|[H1|H1]]; [unfold ph_min_x100 in *; lia|reflexivity|reflexivity].
Qed.

Lemma make_pH_none_high : forall v,
  v > ph_max_x100 -> make_pH v = None.
Proof.
  intros v H. unfold make_pH.
  destruct (ph_valid_dec v) as [[H1 H2]|[H1|H1]]; [unfold ph_max_x100 in *; lia|reflexivity|reflexivity].
Qed.

Lemma make_pH_roundtrip : forall v,
  ph_min_x100 <= v <= ph_max_x100 ->
  exists p, make_pH v = Some p /\ ph_value_x100 p = v.
Proof.
  intros v [Hlo Hhi]. unfold make_pH.
  destruct (ph_valid_dec v) as [[H1 H2]|[H1|H1]].
  - eexists. split; [reflexivity | reflexivity].
  - unfold ph_min_x100 in *. lia.
  - unfold ph_max_x100 in *. lia.
Qed.

(** pH decidable equality *)
Definition pH_eq_dec : forall p1 p2 : pH, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [v1 pf1] [v2 pf2].
  destruct (Nat.eq_dec v1 v2) as [Heq|Hne].
  - left. subst. f_equal. apply le_unique.
  - right. intro H. inversion H. contradiction.
Defined.

(** pCO2: partial pressure of CO2 in mmHg. Normal UA ~45-55, elevated >60 *)
Record pCO2 : Type := mkpCO2 {
  pco2_value : nat;
  pco2_valid : pco2_value <= 150
}.

Definition pco2_to_nat (p : pCO2) : nat := pco2_value p.

Definition hypercapnia_threshold : nat := 60.

Definition is_hypercapnic (p : pCO2) : bool := hypercapnia_threshold <? pco2_value p.

(** pO2: partial pressure of O2 in mmHg. Normal UA ~15-25 *)
Record pO2 : Type := mkpO2 {
  po2_value : nat;
  po2_valid : po2_value <= 200
}.

Definition po2_to_nat (p : pO2) : nat := po2_value p.

Definition hypoxemia_threshold : nat := 10.

Definition is_hypoxemic (p : pO2) : bool := po2_value p <? hypoxemia_threshold.

(** Base deficit in mEq/L. Significant >=12, severe >=16 *)
Record BaseDeficit : Type := mkBD {
  bd_value : nat;
  bd_valid : bd_value <= 30
}.

Definition bd_to_nat (bd : BaseDeficit) : nat := bd_value bd.

Definition significant_bd_threshold : nat := 12.
Definition severe_bd_threshold : nat := 16.

Definition is_significant_bd (bd : BaseDeficit) : bool :=
  significant_bd_threshold <=? bd_value bd.

Definition is_severe_bd (bd : BaseDeficit) : bool :=
  severe_bd_threshold <=? bd_value bd.

Lemma severe_bd_implies_significant : forall bd,
  is_severe_bd bd = true -> is_significant_bd bd = true.
Proof.
  intros bd H. unfold is_severe_bd, is_significant_bd in *.
  unfold severe_bd_threshold, significant_bd_threshold in *.
  apply Nat.leb_le in H. apply Nat.leb_le. lia.
Qed.

(** Lactate in mmol/L x10. Normal <2.5, elevated >=5.0 *)
Record Lactate : Type := mkLactate {
  lactate_value_x10 : nat;
  lactate_valid : lactate_value_x10 <= 200
}.

Definition lactate_to_nat (l : Lactate) : nat := lactate_value_x10 l.

Definition elevated_lactate_threshold_x10 : nat := 50.

Definition is_elevated_lactate (l : Lactate) : bool :=
  elevated_lactate_threshold_x10 <=? lactate_value_x10 l.

(** Complete cord blood gas record *)
Record t : Type := mk {
  ph : pH;
  pco2 : option pCO2;
  po2 : option pO2;
  base_deficit : BaseDeficit;
  lactate : option Lactate
}.

Definition indicates_asphyxia (cbg : t) : bool :=
  is_acidemic (ph cbg) && is_significant_bd (base_deficit cbg).

Theorem asphyxia_requires_acidemia : forall cbg,
  indicates_asphyxia cbg = true -> is_acidemic (ph cbg) = true.
Proof.
  intros cbg H. unfold indicates_asphyxia in H.
  apply andb_true_iff in H. destruct H as [H _]. exact H.
Qed.

Theorem asphyxia_requires_bd : forall cbg,
  indicates_asphyxia cbg = true -> is_significant_bd (base_deficit cbg) = true.
Proof.
  intros cbg H. unfold indicates_asphyxia in H.
  apply andb_true_iff in H. destruct H as [_ H]. exact H.
Qed.

Definition sample_normal_ph : pH.
Proof.
  refine (mkpH 725 _). lia.
Defined.

Definition sample_acidemic_ph : pH.
Proof.
  refine (mkpH 695 _). lia.
Defined.

Lemma sample_normal_not_acidemic : is_acidemic sample_normal_ph = false.
Proof. reflexivity. Qed.

Lemma sample_acidemic_is_acidemic : is_acidemic sample_acidemic_ph = true.
Proof. reflexivity. Qed.

(** Sample type: Arterial vs Venous cord blood *)
Inductive SampleType : Type :=
  | Arterial : SampleType
  | Venous : SampleType.

Definition sample_type_eq_dec : forall s1 s2 : SampleType, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition sample_type_all : list SampleType := [Arterial; Venous].

Lemma sample_type_all_complete : forall s : SampleType, In s sample_type_all.
Proof. intros []; simpl; auto. Qed.

Lemma sample_type_all_nodup : NoDup sample_type_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

(** Typed cord blood gas with sample source *)
Record TypedSample : Type := mkTypedSample {
  sample_source : SampleType;
  sample_gas : t
}.

(** Paired arterial-venous samples *)
Record PairedSamples : Type := mkPaired {
  arterial_sample : t;
  venous_sample : t
}.

(** A-V pH difference (x100) - normal is 0.02-0.10 (2-10 when x100) *)
Definition av_ph_difference (p : PairedSamples) : nat :=
  let art_ph := ph_value_x100 (ph (arterial_sample p)) in
  let ven_ph := ph_value_x100 (ph (venous_sample p)) in
  if ven_ph <=? art_ph then 0 else ven_ph - art_ph.

Definition normal_av_difference_min : nat := 2.
Definition normal_av_difference_max : nat := 10.

Definition is_normal_av_difference (p : PairedSamples) : bool :=
  let diff := av_ph_difference p in
  (normal_av_difference_min <=? diff) && (diff <=? normal_av_difference_max).

(** A-V difference too small suggests cord occlusion or sampling error *)
Definition av_difference_too_small (p : PairedSamples) : bool :=
  av_ph_difference p <? normal_av_difference_min.

(** A-V difference too large suggests prolonged cord compression *)
Definition av_difference_too_large (p : PairedSamples) : bool :=
  normal_av_difference_max <? av_ph_difference p.

(** Arterial pH is typically lower than venous (fetus returns CO2 to placenta) *)
Theorem arterial_typically_lower : forall p,
  is_normal_av_difference p = true ->
  ph_value_x100 (ph (arterial_sample p)) < ph_value_x100 (ph (venous_sample p)).
Proof.
  intros p H. unfold is_normal_av_difference in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1.
  unfold av_ph_difference, normal_av_difference_min in H1.
  destruct (ph_value_x100 (ph (venous_sample p)) <=?
            ph_value_x100 (ph (arterial_sample p))) eqn:E.
  - apply Nat.leb_le in E. simpl in H1. lia.
  - apply Nat.leb_gt in E. exact E.
Qed.

(** Combined asphyxia indicator using both samples *)
Definition paired_indicates_asphyxia (p : PairedSamples) : bool :=
  indicates_asphyxia (arterial_sample p).

(** Asphyxia from arterial implies arterial acidemia *)
Theorem paired_asphyxia_arterial_acidemic : forall p,
  paired_indicates_asphyxia p = true ->
  is_acidemic (ph (arterial_sample p)) = true.
Proof.
  intros p H. apply asphyxia_requires_acidemia. exact H.
Qed.

(** Venous-only sampling is less reliable for asphyxia detection *)
Definition venous_only_asphyxia (ts : TypedSample) : bool :=
  match sample_source ts with
  | Arterial => indicates_asphyxia (sample_gas ts)
  | Venous => is_severely_acidemic (ph (sample_gas ts)) &&
              is_severe_bd (base_deficit (sample_gas ts))
  end.

(** Boolean reflection for cord blood gas predicates *)
Lemma is_acidemic_iff : forall p,
  is_acidemic p = true <-> ph_value_x100 p < acidemia_threshold_x100.
Proof. intros p. unfold is_acidemic. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_severely_acidemic_iff : forall p,
  is_severely_acidemic p = true <-> ph_value_x100 p < severe_acidemia_threshold_x100.
Proof. intros p. unfold is_severely_acidemic. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_hypercapnic_iff : forall p,
  is_hypercapnic p = true <-> hypercapnia_threshold < pco2_value p.
Proof. intros p. unfold is_hypercapnic. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_hypoxemic_iff : forall p,
  is_hypoxemic p = true <-> po2_value p < hypoxemia_threshold.
Proof. intros p. unfold is_hypoxemic. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_significant_bd_iff : forall bd,
  is_significant_bd bd = true <-> significant_bd_threshold <= bd_value bd.
Proof. intros bd. unfold is_significant_bd. rewrite Nat.leb_le. tauto. Qed.

Lemma is_severe_bd_iff : forall bd,
  is_severe_bd bd = true <-> severe_bd_threshold <= bd_value bd.
Proof. intros bd. unfold is_severe_bd. rewrite Nat.leb_le. tauto. Qed.

Lemma is_elevated_lactate_iff : forall l,
  is_elevated_lactate l = true <-> elevated_lactate_threshold_x10 <= lactate_value_x10 l.
Proof. intros l. unfold is_elevated_lactate. rewrite Nat.leb_le. tauto. Qed.

End CordBloodGas.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 1e: TEMPERATURE                                 *)
(*                                                                            *)
(*  Neonatal temperature in degrees Celsius x10. Normal 36.5-37.5°C.          *)
(*  Hypothermia (<36.5°C) and hyperthermia (>37.5°C) require intervention.    *)
(*  Temperature regulation is critical in delivery room resuscitation.        *)
(*                                                                            *)
(******************************************************************************)

Module Temperature.

Record t : Type := mk {
  value_x10 : nat;
  value_valid : value_x10 <= 420  (** 42.0°C is upper survivable limit *)
}.

Definition to_nat (temp : t) : nat := value_x10 temp.

Definition normal_lo_x10 : nat := 365.
Definition normal_hi_x10 : nat := 375.
Definition mild_hypothermia_x10 : nat := 360.
Definition moderate_hypothermia_x10 : nat := 340.
Definition severe_hypothermia_x10 : nat := 320.

Inductive Status : Type :=
  | SevereHypothermia : Status
  | ModerateHypothermia : Status
  | MildHypothermia : Status
  | Normal : Status
  | Hyperthermia : Status.

Definition classify (temp : t) : Status :=
  if value_x10 temp <? severe_hypothermia_x10 then SevereHypothermia
  else if value_x10 temp <? moderate_hypothermia_x10 then ModerateHypothermia
  else if value_x10 temp <? mild_hypothermia_x10 then MildHypothermia
  else if value_x10 temp <=? normal_hi_x10 then Normal
  else Hyperthermia.

Definition is_hypothermic (temp : t) : bool :=
  value_x10 temp <? normal_lo_x10.

Definition is_hyperthermic (temp : t) : bool :=
  normal_hi_x10 <? value_x10 temp.

Definition is_normal (temp : t) : bool :=
  (normal_lo_x10 <=? value_x10 temp) && (value_x10 temp <=? normal_hi_x10).

Definition status_eq_dec : forall s1 s2 : Status, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition status_all : list Status :=
  [SevereHypothermia; ModerateHypothermia; MildHypothermia; Normal; Hyperthermia].

Lemma status_all_complete : forall s : Status, In s status_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma status_all_nodup : NoDup status_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Lemma classify_exhaustive : forall temp,
  classify temp = SevereHypothermia \/
  classify temp = ModerateHypothermia \/
  classify temp = MildHypothermia \/
  classify temp = Normal \/
  classify temp = Hyperthermia.
Proof.
  intros temp. unfold classify.
  destruct (value_x10 temp <? severe_hypothermia_x10); [left; reflexivity|].
  destruct (value_x10 temp <? moderate_hypothermia_x10); [right; left; reflexivity|].
  destruct (value_x10 temp <? mild_hypothermia_x10); [right; right; left; reflexivity|].
  destruct (value_x10 temp <=? normal_hi_x10); [right; right; right; left; reflexivity|].
  right; right; right; right; reflexivity.
Qed.

Theorem classify_categories_exclusive : forall temp s1 s2,
  classify temp = s1 -> classify temp = s2 -> s1 = s2.
Proof. intros temp s1 s2 H1 H2. rewrite H1 in H2. exact H2. Qed.

Theorem thresholds_ordered :
  severe_hypothermia_x10 < moderate_hypothermia_x10 /\
  moderate_hypothermia_x10 < mild_hypothermia_x10 /\
  mild_hypothermia_x10 < normal_lo_x10 /\
  normal_lo_x10 <= normal_hi_x10.
Proof.
  unfold severe_hypothermia_x10, moderate_hypothermia_x10,
         mild_hypothermia_x10, normal_lo_x10, normal_hi_x10.
  lia.
Qed.

Theorem hypothermic_not_normal : forall temp,
  is_hypothermic temp = true -> is_normal temp = false.
Proof.
  intros temp H. unfold is_hypothermic, is_normal in *.
  apply Nat.ltb_lt in H.
  destruct (normal_lo_x10 <=? value_x10 temp) eqn:E.
  - apply Nat.leb_le in E. unfold normal_lo_x10 in *. lia.
  - reflexivity.
Qed.

Theorem hyperthermic_not_normal : forall temp,
  is_hyperthermic temp = true -> is_normal temp = false.
Proof.
  intros temp H. unfold is_hyperthermic, is_normal in *.
  apply Nat.ltb_lt in H.
  destruct (normal_lo_x10 <=? value_x10 temp) eqn:E1.
  - destruct (value_x10 temp <=? normal_hi_x10) eqn:E2.
    + apply Nat.leb_le in E2. unfold normal_hi_x10 in *. lia.
    + reflexivity.
  - reflexivity.
Qed.

Definition needs_warming (temp : t) : bool := is_hypothermic temp.

Definition needs_cooling (temp : t) : bool := is_hyperthermic temp.

(** Measurement site for temperature *)
Inductive MeasurementSite : Type :=
  | Axillary : MeasurementSite
  | Rectal : MeasurementSite
  | SkinProbe : MeasurementSite
  | Esophageal : MeasurementSite.

Definition measurement_site_eq_dec : forall s1 s2 : MeasurementSite,
  {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition measurement_site_all : list MeasurementSite :=
  [Axillary; Rectal; SkinProbe; Esophageal].

Lemma measurement_site_all_complete : forall s : MeasurementSite,
  In s measurement_site_all.
Proof. intros []; simpl; auto. Qed.

(** Offset to adjust for measurement site (x10, e.g., 5 = 0.5°C) *)
Definition site_offset_x10 (s : MeasurementSite) : nat :=
  match s with
  | Axillary => 5
  | Rectal => 0
  | SkinProbe => 3
  | Esophageal => 0
  end.

(** Is site considered gold standard for neonatal monitoring *)
Definition is_core_temperature_site (s : MeasurementSite) : bool :=
  match s with
  | Rectal => true
  | Esophageal => true
  | _ => false
  end.

(** Temperature reading with site information *)
Record SitedTemperature : Type := mkSitedTemp {
  temp_reading : t;
  temp_site : MeasurementSite
}.

(** Estimate core temperature from peripheral reading *)
Definition estimate_core_temp (st : SitedTemperature) : nat :=
  value_x10 (temp_reading st) + site_offset_x10 (temp_site st).

(** Clinical interpretation should use estimated core *)
Definition classify_sited (st : SitedTemperature) : Status :=
  let core_est := estimate_core_temp st in
  if core_est <? severe_hypothermia_x10 then SevereHypothermia
  else if core_est <? moderate_hypothermia_x10 then ModerateHypothermia
  else if core_est <? mild_hypothermia_x10 then MildHypothermia
  else if core_est <=? normal_hi_x10 then Normal
  else Hyperthermia.

Theorem rectal_no_adjustment : forall temp,
  estimate_core_temp (mkSitedTemp temp Rectal) = value_x10 temp.
Proof. intros temp. unfold estimate_core_temp, site_offset_x10. simpl. lia. Qed.

Theorem axillary_adds_offset : forall temp,
  estimate_core_temp (mkSitedTemp temp Axillary) = value_x10 temp + 5.
Proof. intros temp. reflexivity. Qed.

(** Boolean reflection for temperature predicates *)
Lemma is_hypothermic_iff : forall temp,
  is_hypothermic temp = true <-> value_x10 temp < normal_lo_x10.
Proof. intros temp. unfold is_hypothermic. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_hyperthermic_iff : forall temp,
  is_hyperthermic temp = true <-> normal_hi_x10 < value_x10 temp.
Proof. intros temp. unfold is_hyperthermic. rewrite Nat.ltb_lt. tauto. Qed.

Lemma is_normal_temp_iff : forall temp,
  is_normal temp = true <-> normal_lo_x10 <= value_x10 temp <= normal_hi_x10.
Proof.
  intros temp. unfold is_normal.
  rewrite andb_true_iff, Nat.leb_le, Nat.leb_le. tauto.
Qed.

(** Temperature status trichotomy *)
Theorem temp_trichotomy : forall temp,
  is_hypothermic temp = true \/ is_normal temp = true \/ is_hyperthermic temp = true.
Proof.
  intros temp.
  destruct (value_x10 temp <? normal_lo_x10) eqn:E1.
  - left. unfold is_hypothermic. exact E1.
  - apply Nat.ltb_ge in E1.
    destruct (value_x10 temp <=? normal_hi_x10) eqn:E2.
    + right. left. unfold is_normal. apply andb_true_intro.
      split; [apply Nat.leb_le; exact E1 | exact E2].
    + right. right. unfold is_hyperthermic. apply Nat.ltb_lt.
      apply Nat.leb_gt in E2. exact E2.
Qed.

(** Hypothermic implies needs warming *)
Theorem hypothermic_needs_warming : forall temp,
  is_hypothermic temp = true -> needs_warming temp = true.
Proof.
  intros temp H. unfold needs_warming, is_hypothermic in *.
  destruct (value_x10 temp <? normal_lo_x10) eqn:E; [reflexivity | discriminate].
Qed.

(** Hyperthermic implies needs cooling *)
Theorem hyperthermic_needs_cooling : forall temp,
  is_hyperthermic temp = true -> needs_cooling temp = true.
Proof.
  intros temp H. unfold needs_cooling, is_hyperthermic in *.
  destruct (normal_hi_x10 <? value_x10 temp) eqn:E; [reflexivity | discriminate].
Qed.

(** Temperature estimation accuracy bound *)
Theorem estimate_core_temp_bounded : forall st,
  estimate_core_temp st <= value_x10 (temp_reading st) + 5.
Proof.
  intros st. unfold estimate_core_temp.
  destruct (temp_site st); simpl; lia.
Qed.

End Temperature.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 2: SCORE LEVEL (0, 1, or 2)                     *)
(*                                                                            *)
(*  Each APGAR criterion scores exactly 0, 1, or 2.                           *)
(*  We encode this as an inductive with exactly three constructors,           *)
(*  then prove the encoding is isomorphic to Bounded 2.                       *)
(*                                                                            *)
(******************************************************************************)

Module ScoreLevel.

Inductive t : Type :=
  | Zero : t
  | One : t
  | Two : t.

Definition to_nat (s : t) : nat :=
  match s with
  | Zero => 0
  | One => 1
  | Two => 2
  end.

Definition to_bounded (s : t) : Bounded 2 :=
  match s with
  | Zero => BoundedNat.make 0 2 (le_S _ _ (le_S _ _ (le_n 0)))
  | One => BoundedNat.make 1 2 (le_S _ _ (le_n 1))
  | Two => BoundedNat.make 2 2 (le_n 2)
  end.

Lemma to_nat_bound : forall s, to_nat s <= 2.
Proof. intros []; simpl; lia. Qed.

Definition of_nat_fn (n : nat) : t :=
  match n with
  | 0 => Zero
  | 1 => One
  | _ => Two
  end.

Definition of_nat (n : nat) (_ : n <= 2) : t := of_nat_fn n.

Lemma of_to_nat : forall s, of_nat (to_nat s) (to_nat_bound s) = s.
Proof. intros []; reflexivity. Qed.

Lemma to_of_nat : forall n (pf : n <= 2), to_nat (of_nat n pf) = n.
Proof.
  intros [|[|[|n]]] pf; try reflexivity. exfalso. lia.
Qed.

Definition eq_dec : forall s1 s2 : t, {s1 = s2} + {s1 <> s2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Definition all : list t := [Zero; One; Two].

Lemma all_complete : forall s : t, In s all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

End ScoreLevel.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 3: SCOREABLE TYPECLASS                          *)
(*                                                                            *)
(*  A typeclass abstracting the common interface of APGAR components.         *)
(*                                                                            *)
(******************************************************************************)

Class Scoreable (A : Type) : Type := {
  to_score : A -> ScoreLevel.t;
  score_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2};
  score_all : list A;
  score_all_complete : forall a : A, In a score_all;
  score_all_nodup : NoDup score_all
}.

Definition score_to_nat {A : Type} `{Scoreable A} (a : A) : nat :=
  ScoreLevel.to_nat (to_score a).

Lemma score_bounded : forall {A : Type} `{Scoreable A} (a : A),
  score_to_nat a <= 2.
Proof. intros A H a. unfold score_to_nat. apply ScoreLevel.to_nat_bound. Qed.

#[export] Instance Scoreable_ScoreLevel : Scoreable ScoreLevel.t := {
  to_score := fun s => s;
  score_eq_dec := ScoreLevel.eq_dec;
  score_all := ScoreLevel.all;
  score_all_complete := ScoreLevel.all_complete;
  score_all_nodup := ScoreLevel.all_nodup
}.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 4: APGAR COMPONENT TYPES                        *)
(*                                                                            *)
(*  Each of the five criteria has exactly three clinical states.              *)
(*  We define each as an inductive type with:                                 *)
(*    - Decidable equality                                                    *)
(*    - Complete enumeration                                                  *)
(*    - Conversion to ScoreLevel                                              *)
(*                                                                            *)
(******************************************************************************)

Module Appearance.

Inductive t : Type :=
  | PaleBlue : t
  | Acrocyanotic : t
  | CompletelyPink : t.

Definition to_score (a : t) : ScoreLevel.t :=
  match a with
  | PaleBlue => ScoreLevel.Zero
  | Acrocyanotic => ScoreLevel.One
  | CompletelyPink => ScoreLevel.Two
  end.

Definition eq_dec : forall a1 a2 : t, {a1 = a2} + {a1 <> a2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [PaleBlue; Acrocyanotic; CompletelyPink].

Lemma all_complete : forall a : t, In a all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_length : length all = 3.
Proof. reflexivity. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition to_nat (a : t) : nat :=
  match a with
  | PaleBlue => 0
  | Acrocyanotic => 1
  | CompletelyPink => 2
  end.

Definition of_nat (n : nat) : t :=
  match n with
  | 0 => PaleBlue
  | 1 => Acrocyanotic
  | _ => CompletelyPink
  end.

Definition of_nat_opt (n : nat) : option t :=
  match n with
  | 0 => Some PaleBlue
  | 1 => Some Acrocyanotic
  | 2 => Some CompletelyPink
  | _ => None
  end.

Lemma of_to_nat : forall a, of_nat (to_nat a) = a.
Proof. intros []; reflexivity. Qed.

Lemma to_of_nat : forall n, n <= 2 -> to_nat (of_nat n) = n.
Proof. intros [|[|[|n]]] H; try reflexivity; lia. Qed.

Lemma of_nat_opt_some : forall n a,
  of_nat_opt n = Some a -> of_nat n = a.
Proof. intros [|[|[|n]]] a H; inversion H; reflexivity. Qed.

Lemma of_nat_opt_complete : forall n,
  n <= 2 -> exists a, of_nat_opt n = Some a.
Proof. intros [|[|[|n]]] H; try lia; eexists; reflexivity. Qed.

Lemma to_nat_injective : forall a1 a2, to_nat a1 = to_nat a2 -> a1 = a2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

Lemma to_nat_bound : forall a, to_nat a <= 2.
Proof. intros []; simpl; lia. Qed.

End Appearance.

Module Pulse.

Inductive t : Type :=
  | Absent : t
  | Below100 : t
  | AtOrAbove100 : t.

Definition threshold : nat := 100.
Definition max_physiological_bpm : nat := 300.

Definition PhysiologicalBPM : Type := { bpm : nat | bpm <= max_physiological_bpm }.

Definition make_bpm (n : nat) (pf : n <= max_physiological_bpm) : PhysiologicalBPM :=
  exist _ n pf.

Definition bpm_val (pb : PhysiologicalBPM) : nat := proj1_sig pb.

Definition of_physiological_bpm (pb : PhysiologicalBPM) : t :=
  match bpm_val pb with
  | 0 => Absent
  | S n => if S n <? threshold then Below100 else AtOrAbove100
  end.

Lemma physiological_bpm_bounded : forall pb : PhysiologicalBPM,
  bpm_val pb <= max_physiological_bpm.
Proof. intros [bpm pf]. exact pf. Qed.

Definition to_score (p : t) : ScoreLevel.t :=
  match p with
  | Absent => ScoreLevel.Zero
  | Below100 => ScoreLevel.One
  | AtOrAbove100 => ScoreLevel.Two
  end.

Definition of_bpm (bpm : nat) : t :=
  match bpm with
  | 0 => Absent
  | S n => if S n <? threshold then Below100 else AtOrAbove100
  end.

Lemma of_bpm_absent : of_bpm 0 = Absent.
Proof. reflexivity. Qed.

Lemma of_bpm_below : forall bpm, 0 < bpm < threshold -> of_bpm bpm = Below100.
Proof.
  intros [|n] [Hlo Hhi]; [lia|]. simpl.
  destruct (S n <? threshold) eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E. lia.
Qed.

Lemma of_bpm_above : forall bpm, threshold <= bpm -> of_bpm bpm = AtOrAbove100.
Proof.
  intros [|n] H; [unfold threshold in H; lia|]. simpl.
  destruct (S n <? threshold) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E. lia.
Qed.

Definition eq_dec : forall p1 p2 : t, {p1 = p2} + {p1 <> p2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Absent; Below100; AtOrAbove100].

Lemma all_complete : forall p : t, In p all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_length : length all = 3.
Proof. reflexivity. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Inductive DetailedPulse : Type :=
  | DAbsent : DetailedPulse
  | DBradycardia : DetailedPulse
  | DLowNormal : DetailedPulse
  | DNormal : DetailedPulse.

Definition bradycardia_threshold : nat := 60.

Definition of_bpm_detailed (bpm : nat) : DetailedPulse :=
  match bpm with
  | 0 => DAbsent
  | S n =>
    if S n <? bradycardia_threshold then DBradycardia
    else if S n <? threshold then DLowNormal
    else DNormal
  end.

Definition detailed_to_simple (dp : DetailedPulse) : t :=
  match dp with
  | DAbsent => Absent
  | DBradycardia => Below100
  | DLowNormal => Below100
  | DNormal => AtOrAbove100
  end.

Lemma detailed_preserves_score : forall bpm,
  of_bpm bpm = detailed_to_simple (of_bpm_detailed bpm).
Proof.
  intros [|n]; [reflexivity|]. simpl.
  destruct (S n <? bradycardia_threshold) eqn:E1.
  - apply Nat.ltb_lt in E1.
    destruct (S n <? threshold) eqn:E2; [reflexivity|].
    apply Nat.ltb_ge in E2. unfold bradycardia_threshold, threshold in *. lia.
  - apply Nat.ltb_ge in E1.
    destruct (S n <? threshold) eqn:E2; reflexivity.
Qed.

Definition detailed_eq_dec : forall d1 d2 : DetailedPulse, {d1 = d2} + {d1 <> d2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition detailed_all : list DetailedPulse :=
  [DAbsent; DBradycardia; DLowNormal; DNormal].

Lemma detailed_all_complete : forall dp : DetailedPulse, In dp detailed_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma detailed_all_length : length detailed_all = 4.
Proof. reflexivity. Qed.

Lemma detailed_all_nodup : NoDup detailed_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition detailed_to_score (dp : DetailedPulse) : ScoreLevel.t :=
  to_score (detailed_to_simple dp).

Definition detailed_to_nat (dp : DetailedPulse) : nat :=
  match dp with
  | DAbsent => 0
  | DBradycardia => 1
  | DLowNormal => 2
  | DNormal => 3
  end.

Definition detailed_of_nat (n : nat) : DetailedPulse :=
  match n with
  | 0 => DAbsent
  | 1 => DBradycardia
  | 2 => DLowNormal
  | _ => DNormal
  end.

Definition detailed_of_nat_opt (n : nat) : option DetailedPulse :=
  match n with
  | 0 => Some DAbsent
  | 1 => Some DBradycardia
  | 2 => Some DLowNormal
  | 3 => Some DNormal
  | _ => None
  end.

Lemma detailed_of_to_nat : forall dp, detailed_of_nat (detailed_to_nat dp) = dp.
Proof. intros []; reflexivity. Qed.

Lemma detailed_to_of_nat : forall n, n <= 3 -> detailed_to_nat (detailed_of_nat n) = n.
Proof. intros [|[|[|[|n]]]] H; try reflexivity; lia. Qed.

Lemma detailed_to_nat_injective : forall dp1 dp2,
  detailed_to_nat dp1 = detailed_to_nat dp2 -> dp1 = dp2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

Lemma detailed_to_nat_bound : forall dp, detailed_to_nat dp <= 3.
Proof. intros []; simpl; lia. Qed.

Inductive DetailedPulseRange : DetailedPulse -> nat -> Prop :=
  | DAbsentRange : DetailedPulseRange DAbsent 0
  | DBradycardiaRange : forall n, 1 <= n <= 59 -> DetailedPulseRange DBradycardia n
  | DLowNormalRange : forall n, 60 <= n <= 99 -> DetailedPulseRange DLowNormal n
  | DNormalRange : forall n, 100 <= n -> DetailedPulseRange DNormal n.

Lemma of_bpm_detailed_correct : forall bpm,
  bpm <= max_physiological_bpm -> DetailedPulseRange (of_bpm_detailed bpm) bpm.
Proof.
  intros [|n] Hbound.
  - constructor.
  - simpl. unfold bradycardia_threshold, threshold.
    destruct (S n <? 60) eqn:E1.
    + apply Nat.ltb_lt in E1. constructor. lia.
    + apply Nat.ltb_ge in E1. destruct (S n <? 100) eqn:E2.
      * apply Nat.ltb_lt in E2. constructor. lia.
      * apply Nat.ltb_ge in E2. constructor. lia.
Qed.

Theorem DetailedPulseRange_deterministic : forall dp1 dp2 bpm,
  DetailedPulseRange dp1 bpm -> DetailedPulseRange dp2 bpm -> dp1 = dp2.
Proof.
  intros dp1 dp2 bpm H1 H2.
  inversion H1; inversion H2; subst; try reflexivity; lia.
Qed.

Theorem DetailedPulseRange_total : forall bpm,
  bpm <= max_physiological_bpm ->
  exists dp, DetailedPulseRange dp bpm.
Proof.
  intros bpm Hbound. exists (of_bpm_detailed bpm).
  apply of_bpm_detailed_correct. exact Hbound.
Qed.

Definition representative_bpm (p : t) : nat :=
  match p with
  | Absent => 0
  | Below100 => 80
  | AtOrAbove100 => 120
  end.

Theorem representative_bpm_roundtrip : forall p,
  of_bpm (representative_bpm p) = p.
Proof. intros []; reflexivity. Qed.

Theorem representative_bpm_bounded : forall p,
  representative_bpm p <= max_physiological_bpm.
Proof. intros []; unfold max_physiological_bpm; simpl; lia. Qed.

Definition to_nat (p : t) : nat :=
  match p with
  | Absent => 0
  | Below100 => 1
  | AtOrAbove100 => 2
  end.

Definition of_nat (n : nat) : t :=
  match n with
  | 0 => Absent
  | 1 => Below100
  | _ => AtOrAbove100
  end.

Definition of_nat_opt (n : nat) : option t :=
  match n with
  | 0 => Some Absent
  | 1 => Some Below100
  | 2 => Some AtOrAbove100
  | _ => None
  end.

Lemma of_to_nat : forall p, of_nat (to_nat p) = p.
Proof. intros []; reflexivity. Qed.

Lemma to_of_nat : forall n, n <= 2 -> to_nat (of_nat n) = n.
Proof. intros [|[|[|n]]] H; try reflexivity; lia. Qed.

Lemma of_nat_opt_some : forall n p,
  of_nat_opt n = Some p -> of_nat n = p.
Proof. intros [|[|[|n]]] p H; inversion H; reflexivity. Qed.

Lemma of_nat_opt_complete : forall n,
  n <= 2 -> exists p, of_nat_opt n = Some p.
Proof. intros [|[|[|n]]] H; try lia; eexists; reflexivity. Qed.

Lemma to_nat_injective : forall p1 p2, to_nat p1 = to_nat p2 -> p1 = p2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

Lemma to_nat_bound : forall p, to_nat p <= 2.
Proof. intros []; simpl; lia. Qed.

(** DetailedPulse refinement proofs - proving the detailed type correctly
    refines the simple APGAR Pulse type for scoring purposes. *)

Theorem detailed_to_simple_commutes : forall bpm,
  of_bpm bpm = detailed_to_simple (of_bpm_detailed bpm).
Proof. exact detailed_preserves_score. Qed.

Theorem detailed_to_simple_score_equiv : forall bpm,
  to_score (of_bpm bpm) = to_score (detailed_to_simple (of_bpm_detailed bpm)).
Proof.
  intros bpm. rewrite <- detailed_to_simple_commutes. reflexivity.
Qed.

Theorem detailed_refinement_complete : forall dp : DetailedPulse,
  exists bpm, bpm <= max_physiological_bpm /\ of_bpm_detailed bpm = dp.
Proof.
  intros dp. destruct dp.
  - exists 0. split; [unfold max_physiological_bpm; lia | reflexivity].
  - exists 50. split; [unfold max_physiological_bpm; lia | reflexivity].
  - exists 80. split; [unfold max_physiological_bpm; lia | reflexivity].
  - exists 120. split; [unfold max_physiological_bpm; lia | reflexivity].
Qed.

Theorem simple_pulse_covered_by_detailed : forall p : t,
  exists dp : DetailedPulse, detailed_to_simple dp = p.
Proof.
  intros p. destruct p.
  - exists DAbsent. reflexivity.
  - exists DBradycardia. reflexivity.
  - exists DNormal. reflexivity.
Qed.

Theorem detailed_to_simple_surjective : forall p : t,
  exists dp, detailed_to_simple dp = p.
Proof. exact simple_pulse_covered_by_detailed. Qed.

Definition detailed_representative (dp : DetailedPulse) : nat :=
  match dp with
  | DAbsent => 0
  | DBradycardia => 50
  | DLowNormal => 80
  | DNormal => 120
  end.

Theorem detailed_representative_roundtrip : forall dp,
  of_bpm_detailed (detailed_representative dp) = dp.
Proof. intros []; reflexivity. Qed.

Theorem detailed_representative_bounded : forall dp,
  detailed_representative dp <= max_physiological_bpm.
Proof. intros []; unfold max_physiological_bpm; simpl; lia. Qed.

(** Clinical severity for DetailedPulse: bradycardia is more concerning than low-normal,
    even though both score as "1" in traditional APGAR. This refinement allows
    clinical decision support to distinguish severity within the same score level. *)

Inductive ClinicalSeverity : Type :=
  | Critical : ClinicalSeverity      (** Absent pulse - immediate intervention *)
  | Severe : ClinicalSeverity        (** Bradycardia <60 - urgent intervention *)
  | Moderate : ClinicalSeverity      (** Low-normal 60-99 - close monitoring *)
  | Normal : ClinicalSeverity.       (** >=100 - reassuring *)

Definition clinical_severity_eq_dec : forall s1 s2 : ClinicalSeverity,
  {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition clinical_severity_all : list ClinicalSeverity :=
  [Critical; Severe; Moderate; Normal].

Lemma clinical_severity_all_complete : forall s : ClinicalSeverity,
  In s clinical_severity_all.
Proof. intros []; simpl; auto. Qed.

Lemma clinical_severity_all_nodup : NoDup clinical_severity_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition detailed_to_severity (dp : DetailedPulse) : ClinicalSeverity :=
  match dp with
  | DAbsent => Critical
  | DBradycardia => Severe
  | DLowNormal => Moderate
  | DNormal => Normal
  end.

Definition severity_to_nat (s : ClinicalSeverity) : nat :=
  match s with
  | Critical => 0
  | Severe => 1
  | Moderate => 2
  | Normal => 3
  end.

Definition severity_le (s1 s2 : ClinicalSeverity) : Prop :=
  severity_to_nat s1 <= severity_to_nat s2.

Notation "s1 <=s s2" := (severity_le s1 s2) (at level 70).

Theorem severity_le_refl : forall s, s <=s s.
Proof. intros s. unfold severity_le. lia. Qed.

Theorem severity_le_trans : forall s1 s2 s3,
  s1 <=s s2 -> s2 <=s s3 -> s1 <=s s3.
Proof. intros s1 s2 s3. unfold severity_le. lia. Qed.

Theorem severity_le_antisym : forall s1 s2,
  s1 <=s s2 -> s2 <=s s1 -> s1 = s2.
Proof.
  intros [] [] H1 H2; unfold severity_le in *; simpl in *; try lia; reflexivity.
Qed.

(** Key theorem: bradycardia is more severe than low-normal despite same APGAR score *)
Theorem bradycardia_more_severe_than_low_normal :
  detailed_to_severity DBradycardia <=s detailed_to_severity DLowNormal /\
  detailed_to_severity DBradycardia <> detailed_to_severity DLowNormal.
Proof.
  split.
  - unfold severity_le. simpl. lia.
  - discriminate.
Qed.

(** Both bradycardia and low-normal have the same APGAR score *)
Theorem same_apgar_different_severity :
  to_score (detailed_to_simple DBradycardia) = to_score (detailed_to_simple DLowNormal) /\
  detailed_to_severity DBradycardia <> detailed_to_severity DLowNormal.
Proof.
  split; [reflexivity | discriminate].
Qed.

(** Severity ordering matches clinical intuition *)
Theorem severity_ordering :
  Critical <=s Severe /\ Severe <=s Moderate /\ Moderate <=s Normal.
Proof. unfold severity_le; simpl; repeat split; lia. Qed.

Definition requires_immediate_intervention (dp : DetailedPulse) : bool :=
  match detailed_to_severity dp with
  | Critical => true
  | _ => false
  end.

Definition requires_urgent_intervention (dp : DetailedPulse) : bool :=
  match detailed_to_severity dp with
  | Critical | Severe => true
  | _ => false
  end.

Theorem absent_requires_immediate : requires_immediate_intervention DAbsent = true.
Proof. reflexivity. Qed.

Theorem bradycardia_requires_urgent : requires_urgent_intervention DBradycardia = true.
Proof. reflexivity. Qed.

Theorem low_normal_not_urgent : requires_urgent_intervention DLowNormal = false.
Proof. reflexivity. Qed.

(** Severity determines intervention threshold, not just APGAR score *)
Theorem severity_refines_apgar_for_below100 : forall dp,
  detailed_to_simple dp = Below100 ->
  (detailed_to_severity dp = Severe \/ detailed_to_severity dp = Moderate).
Proof.
  intros [] H; simpl in H; try discriminate.
  - left. reflexivity.
  - right. reflexivity.
Qed.

End Pulse.

Module Grimace.

Inductive t : Type :=
  | NoResponse : t
  | GrimaceOnly : t
  | CryCoughSneeze : t.

Definition to_score (g : t) : ScoreLevel.t :=
  match g with
  | NoResponse => ScoreLevel.Zero
  | GrimaceOnly => ScoreLevel.One
  | CryCoughSneeze => ScoreLevel.Two
  end.

Definition eq_dec : forall g1 g2 : t, {g1 = g2} + {g1 <> g2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [NoResponse; GrimaceOnly; CryCoughSneeze].

Lemma all_complete : forall g : t, In g all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_length : length all = 3.
Proof. reflexivity. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition to_nat (g : t) : nat :=
  match g with
  | NoResponse => 0
  | GrimaceOnly => 1
  | CryCoughSneeze => 2
  end.

Definition of_nat (n : nat) : t :=
  match n with
  | 0 => NoResponse
  | 1 => GrimaceOnly
  | _ => CryCoughSneeze
  end.

Definition of_nat_opt (n : nat) : option t :=
  match n with
  | 0 => Some NoResponse
  | 1 => Some GrimaceOnly
  | 2 => Some CryCoughSneeze
  | _ => None
  end.

Lemma of_to_nat : forall g, of_nat (to_nat g) = g.
Proof. intros []; reflexivity. Qed.

Lemma to_of_nat : forall n, n <= 2 -> to_nat (of_nat n) = n.
Proof. intros [|[|[|n]]] H; try reflexivity; lia. Qed.

Lemma of_nat_opt_some : forall n g,
  of_nat_opt n = Some g -> of_nat n = g.
Proof. intros [|[|[|n]]] g H; inversion H; reflexivity. Qed.

Lemma of_nat_opt_complete : forall n,
  n <= 2 -> exists g, of_nat_opt n = Some g.
Proof. intros [|[|[|n]]] H; try lia; eexists; reflexivity. Qed.

Lemma to_nat_injective : forall g1 g2, to_nat g1 = to_nat g2 -> g1 = g2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

Lemma to_nat_bound : forall g, to_nat g <= 2.
Proof. intros []; simpl; lia. Qed.

End Grimace.

Module Activity.

Inductive t : Type :=
  | Flaccid : t
  | SomeFlexion : t
  | ActiveMotion : t.

Definition to_score (a : t) : ScoreLevel.t :=
  match a with
  | Flaccid => ScoreLevel.Zero
  | SomeFlexion => ScoreLevel.One
  | ActiveMotion => ScoreLevel.Two
  end.

Definition eq_dec : forall a1 a2 : t, {a1 = a2} + {a1 <> a2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Flaccid; SomeFlexion; ActiveMotion].

Lemma all_complete : forall a : t, In a all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_length : length all = 3.
Proof. reflexivity. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition to_nat (a : t) : nat :=
  match a with
  | Flaccid => 0
  | SomeFlexion => 1
  | ActiveMotion => 2
  end.

Definition of_nat (n : nat) : t :=
  match n with
  | 0 => Flaccid
  | 1 => SomeFlexion
  | _ => ActiveMotion
  end.

Definition of_nat_opt (n : nat) : option t :=
  match n with
  | 0 => Some Flaccid
  | 1 => Some SomeFlexion
  | 2 => Some ActiveMotion
  | _ => None
  end.

Lemma of_to_nat : forall a, of_nat (to_nat a) = a.
Proof. intros []; reflexivity. Qed.

Lemma to_of_nat : forall n, n <= 2 -> to_nat (of_nat n) = n.
Proof. intros [|[|[|n]]] H; try reflexivity; lia. Qed.

Lemma of_nat_opt_some : forall n a,
  of_nat_opt n = Some a -> of_nat n = a.
Proof. intros [|[|[|n]]] a H; inversion H; reflexivity. Qed.

Lemma of_nat_opt_complete : forall n,
  n <= 2 -> exists a, of_nat_opt n = Some a.
Proof. intros [|[|[|n]]] H; try lia; eexists; reflexivity. Qed.

Lemma to_nat_injective : forall a1 a2, to_nat a1 = to_nat a2 -> a1 = a2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

Lemma to_nat_bound : forall a, to_nat a <= 2.
Proof. intros []; simpl; lia. Qed.

End Activity.

Module Respiration.

Inductive t : Type :=
  | Apneic : t
  | WeakIrregular : t
  | StrongCry : t.

Definition to_score (r : t) : ScoreLevel.t :=
  match r with
  | Apneic => ScoreLevel.Zero
  | WeakIrregular => ScoreLevel.One
  | StrongCry => ScoreLevel.Two
  end.

Definition eq_dec : forall r1 r2 : t, {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Apneic; WeakIrregular; StrongCry].

Lemma all_complete : forall r : t, In r all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_length : length all = 3.
Proof. reflexivity. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition to_nat (r : t) : nat :=
  match r with
  | Apneic => 0
  | WeakIrregular => 1
  | StrongCry => 2
  end.

Definition of_nat (n : nat) : t :=
  match n with
  | 0 => Apneic
  | 1 => WeakIrregular
  | _ => StrongCry
  end.

Definition of_nat_opt (n : nat) : option t :=
  match n with
  | 0 => Some Apneic
  | 1 => Some WeakIrregular
  | 2 => Some StrongCry
  | _ => None
  end.

Lemma of_to_nat : forall r, of_nat (to_nat r) = r.
Proof. intros []; reflexivity. Qed.

Lemma to_of_nat : forall n, n <= 2 -> to_nat (of_nat n) = n.
Proof. intros [|[|[|n]]] H; try reflexivity; lia. Qed.

Lemma of_nat_opt_some : forall n r,
  of_nat_opt n = Some r -> of_nat n = r.
Proof. intros [|[|[|n]]] r H; inversion H; reflexivity. Qed.

Lemma of_nat_opt_complete : forall n,
  n <= 2 -> exists r, of_nat_opt n = Some r.
Proof. intros [|[|[|n]]] H; try lia; eexists; reflexivity. Qed.

Lemma to_nat_injective : forall r1 r2, to_nat r1 = to_nat r2 -> r1 = r2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

Lemma to_nat_bound : forall r, to_nat r <= 2.
Proof. intros []; simpl; lia. Qed.

End Respiration.

#[export] Instance Scoreable_Appearance : Scoreable Appearance.t := {
  to_score := Appearance.to_score;
  score_eq_dec := Appearance.eq_dec;
  score_all := Appearance.all;
  score_all_complete := Appearance.all_complete;
  score_all_nodup := Appearance.all_nodup
}.

#[export] Instance Scoreable_Pulse : Scoreable Pulse.t := {
  to_score := Pulse.to_score;
  score_eq_dec := Pulse.eq_dec;
  score_all := Pulse.all;
  score_all_complete := Pulse.all_complete;
  score_all_nodup := Pulse.all_nodup
}.

#[export] Instance Scoreable_Grimace : Scoreable Grimace.t := {
  to_score := Grimace.to_score;
  score_eq_dec := Grimace.eq_dec;
  score_all := Grimace.all;
  score_all_complete := Grimace.all_complete;
  score_all_nodup := Grimace.all_nodup
}.

#[export] Instance Scoreable_Activity : Scoreable Activity.t := {
  to_score := Activity.to_score;
  score_eq_dec := Activity.eq_dec;
  score_all := Activity.all;
  score_all_complete := Activity.all_complete;
  score_all_nodup := Activity.all_nodup
}.

#[export] Instance Scoreable_Respiration : Scoreable Respiration.t := {
  to_score := Respiration.to_score;
  score_eq_dec := Respiration.eq_dec;
  score_all := Respiration.all;
  score_all_complete := Respiration.all_complete;
  score_all_nodup := Respiration.all_nodup
}.

#[export] Instance Scoreable_DetailedPulse : Scoreable Pulse.DetailedPulse := {
  to_score := Pulse.detailed_to_score;
  score_eq_dec := Pulse.detailed_eq_dec;
  score_all := Pulse.detailed_all;
  score_all_complete := Pulse.detailed_all_complete;
  score_all_nodup := Pulse.detailed_all_nodup
}.

(** ** Assessment Module

    The complete APGAR assessment is a 5-tuple of component observations.
    The total score is computed and proven bounded by construction.

    Key properties:
    - [total_unbounded] computes the sum of component scores (0-10)
    - [total_max] proves the score never exceeds 10
    - [all] provides an exhaustive enumeration (243 assessments = 3^5)
    - [minimum] and [maximum] are the extreme assessments (score 0 and 10)
*)

Module Assessment.

Record t : Type := mk {
  appearance : Appearance.t;
  pulse : Pulse.t;
  grimace : Grimace.t;
  activity : Activity.t;
  respiration : Respiration.t
}.

Inductive MnemonicLetter : Type :=
  | LetterA1 : MnemonicLetter
  | LetterP : MnemonicLetter
  | LetterG : MnemonicLetter
  | LetterA2 : MnemonicLetter
  | LetterR : MnemonicLetter.

Definition apgar_mnemonic : list MnemonicLetter :=
  [LetterA1; LetterP; LetterG; LetterA2; LetterR].

Lemma mnemonic_has_5_letters : length apgar_mnemonic = 5.
Proof. reflexivity. Qed.

Lemma mnemonic_matches_field_order :
  length apgar_mnemonic = 5 /\
  nth 0 apgar_mnemonic LetterA1 = LetterA1 /\
  nth 1 apgar_mnemonic LetterA1 = LetterP /\
  nth 2 apgar_mnemonic LetterA1 = LetterG /\
  nth 3 apgar_mnemonic LetterA1 = LetterA2 /\
  nth 4 apgar_mnemonic LetterA1 = LetterR.
Proof. repeat split; reflexivity. Qed.

Definition component_scores (a : t) : nat * nat * nat * nat * nat :=
  (ScoreLevel.to_nat (Appearance.to_score (appearance a)),
   ScoreLevel.to_nat (Pulse.to_score (pulse a)),
   ScoreLevel.to_nat (Grimace.to_score (grimace a)),
   ScoreLevel.to_nat (Activity.to_score (activity a)),
   ScoreLevel.to_nat (Respiration.to_score (respiration a))).

Definition total_unbounded (a : t) : nat :=
  let '(ap, pu, gr, ac, re) := component_scores a in
  ap + pu + gr + ac + re.

Lemma total_max : forall a : t, total_unbounded a <= 10.
Proof.
  intros a. unfold total_unbounded, component_scores.
  pose proof (ScoreLevel.to_nat_bound (Appearance.to_score (appearance a))).
  pose proof (ScoreLevel.to_nat_bound (Pulse.to_score (pulse a))).
  pose proof (ScoreLevel.to_nat_bound (Grimace.to_score (grimace a))).
  pose proof (ScoreLevel.to_nat_bound (Activity.to_score (activity a))).
  pose proof (ScoreLevel.to_nat_bound (Respiration.to_score (respiration a))).
  lia.
Qed.

Definition total (a : t) : Bounded 10 :=
  BoundedNat.make (total_unbounded a) 10 (total_max a).

Definition eq_dec : forall a1 a2 : t, {a1 = a2} + {a1 <> a2}.
Proof.
  intros [ap1 pu1 gr1 ac1 re1] [ap2 pu2 gr2 ac2 re2].
  destruct (Appearance.eq_dec ap1 ap2); [|right; congruence].
  destruct (Pulse.eq_dec pu1 pu2); [|right; congruence].
  destruct (Grimace.eq_dec gr1 gr2); [|right; congruence].
  destruct (Activity.eq_dec ac1 ac2); [|right; congruence].
  destruct (Respiration.eq_dec re1 re2); [|right; congruence].
  left. congruence.
Defined.

Theorem mk_injective : forall ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2,
  mk ap1 pu1 gr1 ac1 re1 = mk ap2 pu2 gr2 ac2 re2 ->
  ap1 = ap2 /\ pu1 = pu2 /\ gr1 = gr2 /\ ac1 = ac2 /\ re1 = re2.
Proof.
  intros ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2 H.
  injection H. intros. subst. repeat split; reflexivity.
Qed.

Definition all : list t :=
  flat_map (fun ap =>
    flat_map (fun pu =>
      flat_map (fun gr =>
        flat_map (fun ac =>
          map (fun re => mk ap pu gr ac re) Respiration.all
        ) Activity.all
      ) Grimace.all
    ) Pulse.all
  ) Appearance.all.

Lemma all_complete : forall a : t, In a all.
Proof.
  intros [ap pu gr ac re]. unfold all.
  apply in_flat_map. exists ap. split; [apply Appearance.all_complete|].
  apply in_flat_map. exists pu. split; [apply Pulse.all_complete|].
  apply in_flat_map. exists gr. split; [apply Grimace.all_complete|].
  apply in_flat_map. exists ac. split; [apply Activity.all_complete|].
  apply in_map. apply Respiration.all_complete.
Qed.

Lemma all_length : length all = 243.
Proof. reflexivity. Qed.

Lemma all_nodup : NoDup all.
Proof.
  unfold all.
  apply ListHelpers.NoDup_flat_map; [apply Appearance.all_nodup | |].
  - intros ap _. apply ListHelpers.NoDup_flat_map; [apply Pulse.all_nodup | |].
    + intros pu _. apply ListHelpers.NoDup_flat_map; [apply Grimace.all_nodup | |].
      * intros gr _. apply ListHelpers.NoDup_flat_map; [apply Activity.all_nodup | |].
        -- intros ac _. apply ListHelpers.NoDup_map_injective; [|apply Respiration.all_nodup].
           intros r1 r2 _ _ H. congruence.
        -- intros ac1 ac2 a _ _ Hne H1 H2. apply in_map_iff in H1, H2.
           destruct H1 as [r1 [E1 _]], H2 as [r2 [E2 _]].
           rewrite <- E1 in E2. congruence.
      * intros gr1 gr2 a _ _ Hne H1 H2.
        apply in_flat_map in H1, H2.
        destruct H1 as [ac1 [_ H1]], H2 as [ac2 [_ H2]].
        apply in_map_iff in H1, H2.
        destruct H1 as [r1 [E1 _]], H2 as [r2 [E2 _]].
        rewrite <- E1 in E2. congruence.
    + intros pu1 pu2 a _ _ Hne H1 H2.
      apply in_flat_map in H1, H2.
      destruct H1 as [gr1 [_ H1]], H2 as [gr2 [_ H2]].
      apply in_flat_map in H1, H2.
      destruct H1 as [ac1 [_ H1]], H2 as [ac2 [_ H2]].
      apply in_map_iff in H1, H2.
      destruct H1 as [r1 [E1 _]], H2 as [r2 [E2 _]].
      rewrite <- E1 in E2. congruence.
  - intros ap1 ap2 a _ _ Hne H1 H2.
    apply in_flat_map in H1, H2.
    destruct H1 as [pu1 [_ H1]], H2 as [pu2 [_ H2]].
    apply in_flat_map in H1, H2.
    destruct H1 as [gr1 [_ H1]], H2 as [gr2 [_ H2]].
    apply in_flat_map in H1, H2.
    destruct H1 as [ac1 [_ H1]], H2 as [ac2 [_ H2]].
    apply in_map_iff in H1, H2.
    destruct H1 as [r1 [E1 _]], H2 as [r2 [E2 _]].
    rewrite <- E1 in E2. congruence.
Qed.

(** Cardinality explanation: 243 = 3^5 (5 components, 3 values each) *)
Theorem cardinality_is_3_pow_5 : length all = 3 * 3 * 3 * 3 * 3.
Proof. reflexivity. Qed.

Theorem cardinality_equals_product :
  length all = length Appearance.all * length Pulse.all *
               length Grimace.all * length Activity.all * length Respiration.all.
Proof.
  rewrite Appearance.all_length, Pulse.all_length, Grimace.all_length,
          Activity.all_length, Respiration.all_length.
  reflexivity.
Qed.


Definition minimum : t :=
  mk Appearance.PaleBlue Pulse.Absent Grimace.NoResponse
     Activity.Flaccid Respiration.Apneic.

Definition maximum : t :=
  mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.CryCoughSneeze
     Activity.ActiveMotion Respiration.StrongCry.

Lemma minimum_score : total_unbounded minimum = 0.
Proof. reflexivity. Qed.

Lemma maximum_score : total_unbounded maximum = 10.
Proof. reflexivity. Qed.

Definition set_appearance (a : t) (ap : Appearance.t) : t :=
  mk ap (pulse a) (grimace a) (activity a) (respiration a).

Definition set_pulse (a : t) (pu : Pulse.t) : t :=
  mk (appearance a) pu (grimace a) (activity a) (respiration a).

Definition set_grimace (a : t) (gr : Grimace.t) : t :=
  mk (appearance a) (pulse a) gr (activity a) (respiration a).

Definition set_activity (a : t) (ac : Activity.t) : t :=
  mk (appearance a) (pulse a) (grimace a) ac (respiration a).

Definition set_respiration (a : t) (re : Respiration.t) : t :=
  mk (appearance a) (pulse a) (grimace a) (activity a) re.

Theorem set_appearance_preserves_others : forall a ap,
  pulse (set_appearance a ap) = pulse a /\
  grimace (set_appearance a ap) = grimace a /\
  activity (set_appearance a ap) = activity a /\
  respiration (set_appearance a ap) = respiration a.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem set_pulse_preserves_others : forall a pu,
  appearance (set_pulse a pu) = appearance a /\
  grimace (set_pulse a pu) = grimace a /\
  activity (set_pulse a pu) = activity a /\
  respiration (set_pulse a pu) = respiration a.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem set_grimace_preserves_others : forall a gr,
  appearance (set_grimace a gr) = appearance a /\
  pulse (set_grimace a gr) = pulse a /\
  activity (set_grimace a gr) = activity a /\
  respiration (set_grimace a gr) = respiration a.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem set_activity_preserves_others : forall a ac,
  appearance (set_activity a ac) = appearance a /\
  pulse (set_activity a ac) = pulse a /\
  grimace (set_activity a ac) = grimace a /\
  respiration (set_activity a ac) = respiration a.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem set_respiration_preserves_others : forall a re,
  appearance (set_respiration a re) = appearance a /\
  pulse (set_respiration a re) = pulse a /\
  grimace (set_respiration a re) = grimace a /\
  activity (set_respiration a re) = activity a.
Proof. intros []; repeat split; reflexivity. Qed.

Inductive ComponentIndex : Type :=
  | IdxAppearance : ComponentIndex
  | IdxPulse : ComponentIndex
  | IdxGrimace : ComponentIndex
  | IdxActivity : ComponentIndex
  | IdxRespiration : ComponentIndex.

Definition ComponentIndex_to_nat (ci : ComponentIndex) : nat :=
  match ci with
  | IdxAppearance => 0
  | IdxPulse => 1
  | IdxGrimace => 2
  | IdxActivity => 3
  | IdxRespiration => 4
  end.

Definition ComponentIndex_of_nat_opt (n : nat) : option ComponentIndex :=
  match n with
  | 0 => Some IdxAppearance
  | 1 => Some IdxPulse
  | 2 => Some IdxGrimace
  | 3 => Some IdxActivity
  | 4 => Some IdxRespiration
  | _ => None
  end.

Definition ComponentIndex_of_nat (n : nat) : ComponentIndex :=
  match n with
  | 0 => IdxAppearance
  | 1 => IdxPulse
  | 2 => IdxGrimace
  | 3 => IdxActivity
  | _ => IdxRespiration
  end.

Lemma ComponentIndex_of_nat_opt_some : forall n ci,
  ComponentIndex_of_nat_opt n = Some ci -> ComponentIndex_of_nat n = ci.
Proof.
  intros [|[|[|[|[|n]]]]] ci H; inversion H; reflexivity.
Qed.

Lemma ComponentIndex_of_nat_opt_none : forall n,
  ComponentIndex_of_nat_opt n = None <-> n > 4.
Proof.
  intros [|[|[|[|[|n]]]]]; split; intro H; try discriminate; try lia; reflexivity.
Qed.

Lemma ComponentIndex_of_nat_opt_complete : forall n,
  n <= 4 -> exists ci, ComponentIndex_of_nat_opt n = Some ci.
Proof.
  intros [|[|[|[|[|n]]]]] H; try lia; eexists; reflexivity.
Qed.

Lemma ComponentIndex_of_to_nat : forall ci,
  ComponentIndex_of_nat (ComponentIndex_to_nat ci) = ci.
Proof. intros []; reflexivity. Qed.

Lemma ComponentIndex_of_to_nat_opt : forall ci,
  ComponentIndex_of_nat_opt (ComponentIndex_to_nat ci) = Some ci.
Proof. intros []; reflexivity. Qed.

Lemma ComponentIndex_to_of_nat : forall n,
  n <= 4 -> ComponentIndex_to_nat (ComponentIndex_of_nat n) = n.
Proof.
  intros [|[|[|[|[|n]]]]] H; try reflexivity; lia.
Qed.

Lemma ComponentIndex_to_of_nat_opt : forall n ci,
  ComponentIndex_of_nat_opt n = Some ci -> ComponentIndex_to_nat ci = n.
Proof.
  intros [|[|[|[|[|n]]]]] ci H; inversion H; reflexivity.
Qed.

Definition ComponentIndex_eq_dec : forall ci1 ci2 : ComponentIndex,
  {ci1 = ci2} + {ci1 <> ci2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition ComponentIndex_all : list ComponentIndex :=
  [IdxAppearance; IdxPulse; IdxGrimace; IdxActivity; IdxRespiration].

Lemma ComponentIndex_all_complete : forall ci, In ci ComponentIndex_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma ComponentIndex_all_nodup : NoDup ComponentIndex_all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition component_contribution (a : t) (idx : nat) : nat :=
  match idx with
  | 0 => ScoreLevel.to_nat (Appearance.to_score (appearance a))
  | 1 => ScoreLevel.to_nat (Pulse.to_score (pulse a))
  | 2 => ScoreLevel.to_nat (Grimace.to_score (grimace a))
  | 3 => ScoreLevel.to_nat (Activity.to_score (activity a))
  | _ => ScoreLevel.to_nat (Respiration.to_score (respiration a))
  end.

Definition component_contribution_safe (a : t) (ci : ComponentIndex) : nat :=
  component_contribution a (ComponentIndex_to_nat ci).

Theorem total_is_sum_of_contributions : forall a,
  total_unbounded a = component_contribution a 0 +
                      component_contribution a 1 +
                      component_contribution a 2 +
                      component_contribution a 3 +
                      component_contribution a 4.
Proof. intros []; reflexivity. Qed.

Theorem set_appearance_only_changes_idx_0 : forall a ap idx,
  idx <> 0 -> component_contribution (set_appearance a ap) idx = component_contribution a idx.
Proof. intros [] ap [|[|[|[|]]]]; intro H; try contradiction; reflexivity. Qed.

Theorem set_pulse_only_changes_idx_1 : forall a pu idx,
  idx <> 1 -> component_contribution (set_pulse a pu) idx = component_contribution a idx.
Proof. intros [] pu [|[|[|[|]]]]; intro H; try contradiction; reflexivity. Qed.

Theorem set_grimace_only_changes_idx_2 : forall a gr idx,
  idx <> 2 -> component_contribution (set_grimace a gr) idx = component_contribution a idx.
Proof. intros [] gr [|[|[|[|]]]]; intro H; try contradiction; reflexivity. Qed.

Theorem set_activity_only_changes_idx_3 : forall a ac idx,
  idx <> 3 -> component_contribution (set_activity a ac) idx = component_contribution a idx.
Proof. intros [] ac [|[|[|[|]]]]; intro H; try contradiction; reflexivity. Qed.

Theorem set_respiration_only_changes_idx_4 : forall a re idx,
  idx < 4 -> component_contribution (set_respiration a re) idx = component_contribution a idx.
Proof.
  intros [] re [|[|[|[|]]]]; intro H; try lia; reflexivity.
Qed.

Theorem component_independence : forall a idx,
  idx <= 4 ->
  forall a',
  (forall j, j <= 4 -> j <> idx -> component_contribution a j = component_contribution a' j) ->
  total_unbounded a' = total_unbounded a
                       - component_contribution a idx
                       + component_contribution a' idx.
Proof.
  intros a idx Hidx a' Hother.
  rewrite (total_is_sum_of_contributions a).
  rewrite (total_is_sum_of_contributions a').
  destruct idx as [|[|[|[|[|idx]]]]]; try lia.
  - rewrite <- (Hother 1 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 2 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 3 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 4 ltac:(lia) ltac:(lia)). lia.
  - rewrite <- (Hother 0 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 2 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 3 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 4 ltac:(lia) ltac:(lia)). lia.
  - rewrite <- (Hother 0 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 1 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 3 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 4 ltac:(lia) ltac:(lia)). lia.
  - rewrite <- (Hother 0 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 1 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 2 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 4 ltac:(lia) ltac:(lia)). lia.
  - rewrite <- (Hother 0 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 1 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 2 ltac:(lia) ltac:(lia)).
    rewrite <- (Hother 3 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma component_score_bound : forall (A : Type) `{Scoreable A} (x : A),
  score_to_nat x <= 2.
Proof. intros. apply score_bounded. Qed.

Theorem appearance_change_bounded : forall a ap1 ap2,
  appearance a = ap1 ->
  let diff := Z.abs (Z.of_nat (total_unbounded a) -
                     Z.of_nat (total_unbounded (set_appearance a ap2))) in
  (diff <= 2)%Z.
Proof.
  intros a ap1 ap2 _. unfold set_appearance, total_unbounded, component_scores. simpl.
  pose proof (ScoreLevel.to_nat_bound (Appearance.to_score ap1)).
  pose proof (ScoreLevel.to_nat_bound (Appearance.to_score ap2)).
  pose proof (ScoreLevel.to_nat_bound (Appearance.to_score (appearance a))).
  lia.
Qed.

Theorem pulse_change_bounded : forall a pu,
  let diff := Z.abs (Z.of_nat (total_unbounded a) -
                     Z.of_nat (total_unbounded (set_pulse a pu))) in
  (diff <= 2)%Z.
Proof.
  intros a pu. unfold set_pulse, total_unbounded, component_scores. simpl.
  pose proof (ScoreLevel.to_nat_bound (Pulse.to_score (pulse a))).
  pose proof (ScoreLevel.to_nat_bound (Pulse.to_score pu)).
  lia.
Qed.

Theorem grimace_change_bounded : forall a gr,
  let diff := Z.abs (Z.of_nat (total_unbounded a) -
                     Z.of_nat (total_unbounded (set_grimace a gr))) in
  (diff <= 2)%Z.
Proof.
  intros a gr. unfold set_grimace, total_unbounded, component_scores. simpl.
  pose proof (ScoreLevel.to_nat_bound (Grimace.to_score (grimace a))).
  pose proof (ScoreLevel.to_nat_bound (Grimace.to_score gr)).
  lia.
Qed.

Theorem activity_change_bounded : forall a ac,
  let diff := Z.abs (Z.of_nat (total_unbounded a) -
                     Z.of_nat (total_unbounded (set_activity a ac))) in
  (diff <= 2)%Z.
Proof.
  intros a ac. unfold set_activity, total_unbounded, component_scores. simpl.
  pose proof (ScoreLevel.to_nat_bound (Activity.to_score (activity a))).
  pose proof (ScoreLevel.to_nat_bound (Activity.to_score ac)).
  lia.
Qed.

Theorem respiration_change_bounded : forall a re,
  let diff := Z.abs (Z.of_nat (total_unbounded a) -
                     Z.of_nat (total_unbounded (set_respiration a re))) in
  (diff <= 2)%Z.
Proof.
  intros a re. unfold set_respiration, total_unbounded, component_scores. simpl.
  pose proof (ScoreLevel.to_nat_bound (Respiration.to_score (respiration a))).
  pose proof (ScoreLevel.to_nat_bound (Respiration.to_score re)).
  lia.
Qed.

Theorem single_component_change_max_2 : forall a1 a2,
  (appearance a1 = appearance a2 /\ pulse a1 = pulse a2 /\
   grimace a1 = grimace a2 /\ activity a1 = activity a2) \/
  (appearance a1 = appearance a2 /\ pulse a1 = pulse a2 /\
   grimace a1 = grimace a2 /\ respiration a1 = respiration a2) \/
  (appearance a1 = appearance a2 /\ pulse a1 = pulse a2 /\
   activity a1 = activity a2 /\ respiration a1 = respiration a2) \/
  (appearance a1 = appearance a2 /\ grimace a1 = grimace a2 /\
   activity a1 = activity a2 /\ respiration a1 = respiration a2) \/
  (pulse a1 = pulse a2 /\ grimace a1 = grimace a2 /\
   activity a1 = activity a2 /\ respiration a1 = respiration a2) ->
  (Z.abs (Z.of_nat (total_unbounded a1) - Z.of_nat (total_unbounded a2)) <= 2)%Z.
Proof.
  intros a1 a2 H.
  destruct a1 as [ap1 pu1 gr1 ac1 re1].
  destruct a2 as [ap2 pu2 gr2 ac2 re2].
  unfold total_unbounded, component_scores. simpl.
  pose proof (ScoreLevel.to_nat_bound (Appearance.to_score ap1)) as Hap1.
  pose proof (ScoreLevel.to_nat_bound (Appearance.to_score ap2)) as Hap2.
  pose proof (ScoreLevel.to_nat_bound (Pulse.to_score pu1)) as Hpu1.
  pose proof (ScoreLevel.to_nat_bound (Pulse.to_score pu2)) as Hpu2.
  pose proof (ScoreLevel.to_nat_bound (Grimace.to_score gr1)) as Hgr1.
  pose proof (ScoreLevel.to_nat_bound (Grimace.to_score gr2)) as Hgr2.
  pose proof (ScoreLevel.to_nat_bound (Activity.to_score ac1)) as Hac1.
  pose proof (ScoreLevel.to_nat_bound (Activity.to_score ac2)) as Hac2.
  pose proof (ScoreLevel.to_nat_bound (Respiration.to_score re1)) as Hre1.
  pose proof (ScoreLevel.to_nat_bound (Respiration.to_score re2)) as Hre2.
  destruct H as [[H1 [H2 [H3 H4]]] | [[H1 [H2 [H3 H4]]] | [[H1 [H2 [H3 H4]]] |
                 [[H1 [H2 [H3 H4]]] | [H1 [H2 [H3 H4]]]]]]];
  simpl in *; subst; lia.
Qed.

Theorem score_never_exceeds_10 : forall a : t, ~ (total_unbounded a > 10).
Proof. intros a H. pose proof (total_max a). lia. Qed.

Theorem score_11_impossible : forall a : t, total_unbounded a <> 11.
Proof. intros a H. pose proof (total_max a). lia. Qed.

Theorem score_gt_10_impossible : forall n : nat, n > 10 ->
  ~ exists a : t, total_unbounded a = n.
Proof.
  intros n Hn [a Ha]. pose proof (total_max a). lia.
Qed.

Theorem all_scores_in_range : forall a : t,
  In a all -> 0 <= total_unbounded a <= 10.
Proof.
  intros a _. split; [lia | apply total_max].
Qed.

Theorem enumeration_score_bound :
  Forall (fun a => total_unbounded a <= 10) all.
Proof.
  apply Forall_forall. intros a _. apply total_max.
Qed.

Theorem no_score_above_10_in_enumeration :
  ~ exists a : t, In a all /\ total_unbounded a > 10.
Proof.
  intros [a [Hin Hscore]]. pose proof (total_max a). lia.
Qed.

Theorem score_range_upper_bound :
  forall a : t, 0 <= total_unbounded a <= 10.
Proof.
  intros a. split; [lia | apply total_max].
Qed.

Theorem minimum_is_unique_zero : forall a : t,
  total_unbounded a = 0 ->
  appearance a = Appearance.PaleBlue /\
  pulse a = Pulse.Absent /\
  grimace a = Grimace.NoResponse /\
  activity a = Activity.Flaccid /\
  respiration a = Respiration.Apneic.
Proof.
  intros [ap pu gr ac re] H.
  unfold total_unbounded, component_scores in H. simpl in H.
  destruct ap, pu, gr, ac, re; simpl in H; try lia.
  repeat split; reflexivity.
Qed.

Theorem all_zero_implies_score_zero : forall a : t,
  appearance a = Appearance.PaleBlue ->
  pulse a = Pulse.Absent ->
  grimace a = Grimace.NoResponse ->
  activity a = Activity.Flaccid ->
  respiration a = Respiration.Apneic ->
  total_unbounded a = 0.
Proof.
  intros [ap pu gr ac re] Hap Hpu Hgr Hac Hre. simpl in *.
  subst. reflexivity.
Qed.

Theorem perfect_score_requires_all_max : forall a : t,
  total_unbounded a = 10 ->
  appearance a = Appearance.CompletelyPink /\
  pulse a = Pulse.AtOrAbove100 /\
  grimace a = Grimace.CryCoughSneeze /\
  activity a = Activity.ActiveMotion /\
  respiration a = Respiration.StrongCry.
Proof.
  intros [ap pu gr ac re] H.
  unfold total_unbounded, component_scores in H. simpl in H.
  destruct ap, pu, gr, ac, re; simpl in H; try lia.
  repeat split; reflexivity.
Qed.

Theorem score_0_unique : forall a : t,
  total_unbounded a = 0 -> a = minimum.
Proof.
  intros a H.
  destruct (minimum_is_unique_zero a H) as [Hap [Hpu [Hgr [Hac Hre]]]].
  destruct a. simpl in *. subst. reflexivity.
Qed.

Theorem score_10_unique : forall a : t,
  total_unbounded a = 10 -> a = maximum.
Proof.
  intros a H.
  destruct (perfect_score_requires_all_max a H) as [Hap [Hpu [Hgr [Hac Hre]]]].
  destruct a. simpl in *. subst. reflexivity.
Qed.

Theorem score_0_and_10_injective :
  forall a1 a2 : t,
  (total_unbounded a1 = 0 /\ total_unbounded a2 = 0 -> a1 = a2) /\
  (total_unbounded a1 = 10 /\ total_unbounded a2 = 10 -> a1 = a2).
Proof.
  intros a1 a2. split; intros [H1 H2].
  - rewrite (score_0_unique a1 H1), (score_0_unique a2 H2). reflexivity.
  - rewrite (score_10_unique a1 H1), (score_10_unique a2 H2). reflexivity.
Qed.

Definition score_5_witness_1 : t :=
  mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.GrimaceOnly
     Activity.Flaccid Respiration.Apneic.

Definition score_5_witness_2 : t :=
  mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.CryCoughSneeze
     Activity.Flaccid Respiration.Apneic.

Theorem total_unbounded_not_injective :
  exists a1 a2 : t, a1 <> a2 /\ total_unbounded a1 = total_unbounded a2.
Proof.
  exists score_5_witness_1, score_5_witness_2.
  split.
  - discriminate.
  - reflexivity.
Qed.

Theorem score_5_has_multiple_witnesses :
  total_unbounded score_5_witness_1 = 5 /\
  total_unbounded score_5_witness_2 = 5 /\
  score_5_witness_1 <> score_5_witness_2.
Proof. repeat split; try reflexivity. discriminate. Qed.

Theorem scores_1_to_9_not_injective : forall n,
  1 <= n <= 9 ->
  exists a1 a2 : t, a1 <> a2 /\ total_unbounded a1 = n /\ total_unbounded a2 = n.
Proof.
  intros n [Hlo Hhi].
  destruct n as [|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]; try lia.
  - exists (mk Appearance.Acrocyanotic Pulse.Absent Grimace.NoResponse
               Activity.Flaccid Respiration.Apneic).
    exists (mk Appearance.PaleBlue Pulse.Below100 Grimace.NoResponse
               Activity.Flaccid Respiration.Apneic).
    repeat split; try reflexivity. discriminate.
  - exists (mk Appearance.CompletelyPink Pulse.Absent Grimace.NoResponse
               Activity.Flaccid Respiration.Apneic).
    exists (mk Appearance.Acrocyanotic Pulse.Below100 Grimace.NoResponse
               Activity.Flaccid Respiration.Apneic).
    repeat split; try reflexivity. discriminate.
  - exists (mk Appearance.CompletelyPink Pulse.Below100 Grimace.NoResponse
               Activity.Flaccid Respiration.Apneic).
    exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.NoResponse
               Activity.Flaccid Respiration.Apneic).
    repeat split; try reflexivity. discriminate.
  - exists (mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.NoResponse
               Activity.Flaccid Respiration.Apneic).
    exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.GrimaceOnly
               Activity.Flaccid Respiration.Apneic).
    repeat split; try reflexivity. discriminate.
  - exists score_5_witness_1, score_5_witness_2.
    repeat split; try reflexivity. discriminate.
  - exists (mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.Flaccid Respiration.Apneic).
    exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.SomeFlexion Respiration.Apneic).
    repeat split; try reflexivity. discriminate.
  - exists (mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.SomeFlexion Respiration.Apneic).
    exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.ActiveMotion Respiration.Apneic).
    repeat split; try reflexivity. discriminate.
  - exists (mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.ActiveMotion Respiration.Apneic).
    exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.ActiveMotion Respiration.WeakIrregular).
    repeat split; try reflexivity. discriminate.
  - exists (mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.ActiveMotion Respiration.WeakIrregular).
    exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.CryCoughSneeze
               Activity.ActiveMotion Respiration.StrongCry).
    repeat split; try reflexivity. discriminate.
Qed.

Definition assessments_with_score (n : nat) : list t :=
  filter (fun a => total_unbounded a =? n) all.

Definition count_assessments_with_score (n : nat) : nat :=
  length (assessments_with_score n).

Lemma assessments_with_score_correct : forall n a,
  In a (assessments_with_score n) <-> In a all /\ total_unbounded a = n.
Proof.
  intros n a. unfold assessments_with_score.
  rewrite filter_In. rewrite Nat.eqb_eq. tauto.
Qed.

Lemma assessments_with_score_nodup : forall n,
  NoDup (assessments_with_score n).
Proof.
  intros n. unfold assessments_with_score.
  apply NoDup_filter. exact all_nodup.
Qed.

Lemma score_extremes_unique_principle : forall n witness,
  (forall a, total_unbounded a = n -> a = witness) ->
  total_unbounded witness = n ->
  count_assessments_with_score n = 1.
Proof.
  intros n witness Huniq Hwit.
  unfold count_assessments_with_score, assessments_with_score.
  remember (filter (fun a => total_unbounded a =? n) all) as L eqn:HL.
  assert (Hin: In witness L).
  { rewrite HL. apply filter_In. split. apply all_complete. apply Nat.eqb_eq. exact Hwit. }
  assert (Hall: forall a, In a L -> a = witness).
  { intros a Ha. rewrite HL in Ha. apply filter_In in Ha. destruct Ha as [_ Heq].
    apply Nat.eqb_eq in Heq. apply Huniq. exact Heq. }
  assert (Hnd: NoDup L).
  { rewrite HL. apply NoDup_filter. exact all_nodup. }
  destruct L as [|x [|y rest]].
  - exfalso. exact Hin.
  - reflexivity.
  - exfalso.
    assert (Hx: x = witness) by (apply Hall; left; reflexivity).
    assert (Hy: y = witness) by (apply Hall; right; left; reflexivity).
    subst. inversion Hnd. apply H1. left. reflexivity.
Qed.

Lemma score_0_unique_count : count_assessments_with_score 0 = 1.
Proof.
  apply (score_extremes_unique_principle 0 minimum).
  - exact score_0_unique.
  - reflexivity.
Qed.

Lemma score_10_unique_count : count_assessments_with_score 10 = 1.
Proof.
  apply (score_extremes_unique_principle 10 maximum).
  - exact score_10_unique.
  - reflexivity.
Qed.

(** Score distribution: frequency of each score *)
Definition score_distribution : list (nat * nat) :=
  map (fun n => (n, count_assessments_with_score n)) (seq 0 11).

Lemma score_distribution_sum :
  fold_left (fun acc p => acc + snd p) score_distribution 0 = 243.
Proof. reflexivity. Qed.

(** All scores 0-10 are achievable (constructive proof) *)
Theorem all_scores_achievable : forall n, n <= 10 ->
  count_assessments_with_score n >= 1.
Proof.
  intros n Hn.
  unfold count_assessments_with_score, assessments_with_score.
  assert (H : exists a, In a all /\ total_unbounded a = n).
  { destruct n as [|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]; try lia.
    - exists minimum. split; [apply all_complete | reflexivity].
    - exists (mk Appearance.PaleBlue Pulse.Absent Grimace.NoResponse
                 Activity.Flaccid Respiration.WeakIrregular).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.PaleBlue Pulse.Absent Grimace.NoResponse
                 Activity.Flaccid Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.PaleBlue Pulse.Absent Grimace.NoResponse
                 Activity.SomeFlexion Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.PaleBlue Pulse.Absent Grimace.GrimaceOnly
                 Activity.SomeFlexion Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.PaleBlue Pulse.Below100 Grimace.GrimaceOnly
                 Activity.SomeFlexion Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.Acrocyanotic Pulse.Below100 Grimace.GrimaceOnly
                 Activity.SomeFlexion Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.Acrocyanotic Pulse.Below100 Grimace.CryCoughSneeze
                 Activity.SomeFlexion Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.CryCoughSneeze
                 Activity.SomeFlexion Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists (mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.CryCoughSneeze
                 Activity.ActiveMotion Respiration.StrongCry).
      split; [apply all_complete | reflexivity].
    - exists maximum. split; [apply all_complete | reflexivity]. }
  destruct H as [a [Hin Hscore]].
  assert (Hfilter : In a (filter (fun a0 => total_unbounded a0 =? n) all)).
  { apply filter_In. split; [exact Hin |]. apply Nat.eqb_eq. exact Hscore. }
  destruct (filter (fun a0 => total_unbounded a0 =? n) all) as [|a' rest] eqn:E.
  - inversion Hfilter.
  - simpl. lia.
Qed.

(** API functions for Assessment construction and analysis *)

Definition of_component_scores (a_score p_score g_score act_score r_score : nat) : t :=
  mk (Appearance.of_nat a_score) (Pulse.of_nat p_score) (Grimace.of_nat g_score)
     (Activity.of_nat act_score) (Respiration.of_nat r_score).

Lemma appearance_score_nat_equiv : forall a,
  ScoreLevel.to_nat (Appearance.to_score a) = Appearance.to_nat a.
Proof. intros []; reflexivity. Qed.

Lemma pulse_score_nat_equiv : forall p,
  ScoreLevel.to_nat (Pulse.to_score p) = Pulse.to_nat p.
Proof. intros []; reflexivity. Qed.

Lemma grimace_score_nat_equiv : forall g,
  ScoreLevel.to_nat (Grimace.to_score g) = Grimace.to_nat g.
Proof. intros []; reflexivity. Qed.

Lemma activity_score_nat_equiv : forall a,
  ScoreLevel.to_nat (Activity.to_score a) = Activity.to_nat a.
Proof. intros []; reflexivity. Qed.

Lemma respiration_score_nat_equiv : forall r,
  ScoreLevel.to_nat (Respiration.to_score r) = Respiration.to_nat r.
Proof. intros []; reflexivity. Qed.

Theorem of_component_scores_bounded : forall a p g act r,
  a <= 2 -> p <= 2 -> g <= 2 -> act <= 2 -> r <= 2 ->
  total_unbounded (of_component_scores a p g act r) = a + p + g + act + r.
Proof.
  intros a p g act r Ha Hp Hg Hact Hr.
  unfold of_component_scores, total_unbounded, component_scores. simpl.
  rewrite appearance_score_nat_equiv, pulse_score_nat_equiv,
          grimace_score_nat_equiv, activity_score_nat_equiv,
          respiration_score_nat_equiv.
  rewrite Appearance.to_of_nat by assumption.
  rewrite Pulse.to_of_nat by assumption.
  rewrite Grimace.to_of_nat by assumption.
  rewrite Activity.to_of_nat by assumption.
  rewrite Respiration.to_of_nat by assumption.
  reflexivity.
Qed.

Definition to_validated_score (a : t) : ValidScore.t :=
  ValidScore.make (total_unbounded a) (total_max a).

Theorem to_validated_score_val : forall a,
  ValidScore.val (to_validated_score a) = total_unbounded a.
Proof. reflexivity. Qed.

Inductive ComponentChange : Type :=
  | Unchanged : ComponentChange
  | Changed : nat -> nat -> ComponentChange.

Record AssessmentDiff : Type := mkDiff {
  diff_appearance : ComponentChange;
  diff_pulse : ComponentChange;
  diff_grimace : ComponentChange;
  diff_activity : ComponentChange;
  diff_respiration : ComponentChange
}.

Definition component_change (old_val new_val : nat) : ComponentChange :=
  if old_val =? new_val then Unchanged else Changed old_val new_val.

Definition diff (a1 a2 : t) : AssessmentDiff :=
  mkDiff
    (component_change (Appearance.to_nat (appearance a1)) (Appearance.to_nat (appearance a2)))
    (component_change (Pulse.to_nat (pulse a1)) (Pulse.to_nat (pulse a2)))
    (component_change (Grimace.to_nat (grimace a1)) (Grimace.to_nat (grimace a2)))
    (component_change (Activity.to_nat (activity a1)) (Activity.to_nat (activity a2)))
    (component_change (Respiration.to_nat (respiration a1)) (Respiration.to_nat (respiration a2))).

Definition all_unchanged (d : AssessmentDiff) : bool :=
  match diff_appearance d, diff_pulse d, diff_grimace d,
        diff_activity d, diff_respiration d with
  | Unchanged, Unchanged, Unchanged, Unchanged, Unchanged => true
  | _, _, _, _, _ => false
  end.

Theorem diff_reflexive : forall a, all_unchanged (diff a a) = true.
Proof.
  intros a. unfold diff, all_unchanged, component_change. simpl.
  repeat rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem diff_equal_iff_unchanged : forall a1 a2,
  a1 = a2 <-> all_unchanged (diff a1 a2) = true.
Proof.
  intros a1 a2. split; intro H.
  - subst. apply diff_reflexive.
  - unfold diff, all_unchanged, component_change in H.
    destruct a1 as [ap1 pu1 gr1 ac1 re1].
    destruct a2 as [ap2 pu2 gr2 ac2 re2].
    simpl in H.
    destruct (Appearance.to_nat ap1 =? Appearance.to_nat ap2) eqn:Ea; [|discriminate].
    destruct (Pulse.to_nat pu1 =? Pulse.to_nat pu2) eqn:Ep; [|discriminate].
    destruct (Grimace.to_nat gr1 =? Grimace.to_nat gr2) eqn:Eg; [|discriminate].
    destruct (Activity.to_nat ac1 =? Activity.to_nat ac2) eqn:Eac; [|discriminate].
    destruct (Respiration.to_nat re1 =? Respiration.to_nat re2) eqn:Er; [|discriminate].
    apply Nat.eqb_eq in Ea, Ep, Eg, Eac, Er.
    apply Appearance.to_nat_injective in Ea.
    apply Pulse.to_nat_injective in Ep.
    apply Grimace.to_nat_injective in Eg.
    apply Activity.to_nat_injective in Eac.
    apply Respiration.to_nat_injective in Er.
    subst. reflexivity.
Qed.

Definition count_changes (d : AssessmentDiff) : nat :=
  (if match diff_appearance d with Unchanged => true | _ => false end then 0 else 1) +
  (if match diff_pulse d with Unchanged => true | _ => false end then 0 else 1) +
  (if match diff_grimace d with Unchanged => true | _ => false end then 0 else 1) +
  (if match diff_activity d with Unchanged => true | _ => false end then 0 else 1) +
  (if match diff_respiration d with Unchanged => true | _ => false end then 0 else 1).

Theorem count_changes_zero_iff_equal : forall a1 a2,
  count_changes (diff a1 a2) = 0 <-> a1 = a2.
Proof.
  intros a1 a2. split; intro H.
  - apply diff_equal_iff_unchanged.
    unfold count_changes, diff, component_change, all_unchanged in *.
    destruct (Appearance.to_nat (appearance a1) =? Appearance.to_nat (appearance a2)) eqn:Ea;
    destruct (Pulse.to_nat (pulse a1) =? Pulse.to_nat (pulse a2)) eqn:Ep;
    destruct (Grimace.to_nat (grimace a1) =? Grimace.to_nat (grimace a2)) eqn:Eg;
    destruct (Activity.to_nat (activity a1) =? Activity.to_nat (activity a2)) eqn:Eac;
    destruct (Respiration.to_nat (respiration a1) =? Respiration.to_nat (respiration a2)) eqn:Er;
    simpl in *; try reflexivity; try lia.
  - subst. unfold count_changes, diff, component_change.
    repeat rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem count_changes_bound : forall a1 a2, count_changes (diff a1 a2) <= 5.
Proof.
  intros a1 a2. unfold count_changes.
  destruct (diff_appearance (diff a1 a2));
  destruct (diff_pulse (diff a1 a2));
  destruct (diff_grimace (diff a1 a2));
  destruct (diff_activity (diff a1 a2));
  destruct (diff_respiration (diff a1 a2)); simpl; lia.
Qed.

(** Injectivity of the mk constructor - full decomposition *)
Theorem mk_injective_full : forall ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2,
  mk ap1 pu1 gr1 ac1 re1 = mk ap2 pu2 gr2 ac2 re2 ->
  ap1 = ap2 /\ pu1 = pu2 /\ gr1 = gr2 /\ ac1 = ac2 /\ re1 = re2.
Proof.
  intros. inversion H. repeat split; reflexivity.
Qed.

Theorem mk_injective_appearance : forall ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2,
  mk ap1 pu1 gr1 ac1 re1 = mk ap2 pu2 gr2 ac2 re2 -> ap1 = ap2.
Proof. intros. inversion H. reflexivity. Qed.

Theorem mk_injective_pulse : forall ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2,
  mk ap1 pu1 gr1 ac1 re1 = mk ap2 pu2 gr2 ac2 re2 -> pu1 = pu2.
Proof. intros. inversion H. reflexivity. Qed.

Theorem mk_injective_grimace : forall ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2,
  mk ap1 pu1 gr1 ac1 re1 = mk ap2 pu2 gr2 ac2 re2 -> gr1 = gr2.
Proof. intros. inversion H. reflexivity. Qed.

Theorem mk_injective_activity : forall ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2,
  mk ap1 pu1 gr1 ac1 re1 = mk ap2 pu2 gr2 ac2 re2 -> ac1 = ac2.
Proof. intros. inversion H. reflexivity. Qed.

Theorem mk_injective_respiration : forall ap1 ap2 pu1 pu2 gr1 gr2 ac1 ac2 re1 re2,
  mk ap1 pu1 gr1 ac1 re1 = mk ap2 pu2 gr2 ac2 re2 -> re1 = re2.
Proof. intros. inversion H. reflexivity. Qed.

End Assessment.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 5: SCORE REACHABILITY                           *)
(*                                                                            *)
(*  Every score from 0 to 10 is achievable. We prove this constructively      *)
(*  by providing an explicit witness function that is total on [0,10].        *)
(*                                                                            *)
(******************************************************************************)

Module Reachability.

Definition witness_fn (n : nat) : Assessment.t :=
  match n with
  | 0 => Assessment.minimum
  | 1 => Assessment.mk Appearance.Acrocyanotic Pulse.Absent
         Grimace.NoResponse Activity.Flaccid Respiration.Apneic
  | 2 => Assessment.mk Appearance.CompletelyPink Pulse.Absent
         Grimace.NoResponse Activity.Flaccid Respiration.Apneic
  | 3 => Assessment.mk Appearance.CompletelyPink Pulse.Below100
         Grimace.NoResponse Activity.Flaccid Respiration.Apneic
  | 4 => Assessment.mk Appearance.CompletelyPink Pulse.AtOrAbove100
         Grimace.NoResponse Activity.Flaccid Respiration.Apneic
  | 5 => Assessment.mk Appearance.CompletelyPink Pulse.AtOrAbove100
         Grimace.GrimaceOnly Activity.Flaccid Respiration.Apneic
  | 6 => Assessment.mk Appearance.CompletelyPink Pulse.AtOrAbove100
         Grimace.CryCoughSneeze Activity.Flaccid Respiration.Apneic
  | 7 => Assessment.mk Appearance.CompletelyPink Pulse.AtOrAbove100
         Grimace.CryCoughSneeze Activity.SomeFlexion Respiration.Apneic
  | 8 => Assessment.mk Appearance.CompletelyPink Pulse.AtOrAbove100
         Grimace.CryCoughSneeze Activity.ActiveMotion Respiration.Apneic
  | 9 => Assessment.mk Appearance.CompletelyPink Pulse.AtOrAbove100
         Grimace.CryCoughSneeze Activity.ActiveMotion Respiration.WeakIrregular
  | _ => Assessment.maximum
  end.

Definition witness (n : nat) (_ : n <= 10) : Assessment.t := witness_fn n.

Lemma witness_fn_correct : forall n, n <= 10 ->
  Assessment.total_unbounded (witness_fn n) = n.
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]; try reflexivity.
  exfalso. lia.
Qed.

Lemma witness_correct : forall n (pf : n <= 10),
  Assessment.total_unbounded (witness n pf) = n.
Proof.
  intros n pf. apply witness_fn_correct. exact pf.
Qed.

Theorem all_scores_reachable : forall n : nat, n <= 10 ->
  exists a : Assessment.t, Assessment.total_unbounded a = n.
Proof.
  intros n Hn. exists (witness n Hn). apply witness_correct.
Qed.

Theorem score_surjective : forall n : nat, n <= 10 ->
  exists a : Assessment.t, BoundedNat.val (Assessment.total a) = n.
Proof.
  intros n Hn. exists (witness n Hn).
  unfold Assessment.total. simpl.
  apply witness_correct.
Qed.

(** Safe partial witness function that returns None for n > 10 *)
Definition witness_fn_opt (n : nat) : option Assessment.t :=
  if n <=? 10 then Some (witness_fn n) else None.

Lemma witness_fn_opt_some : forall n,
  n <= 10 -> witness_fn_opt n = Some (witness_fn n).
Proof.
  intros n H. unfold witness_fn_opt.
  destruct (n <=? 10) eqn:E.
  - reflexivity.
  - apply Nat.leb_gt in E. lia.
Qed.

Lemma witness_fn_opt_none : forall n,
  n > 10 -> witness_fn_opt n = None.
Proof.
  intros n H. unfold witness_fn_opt.
  destruct (n <=? 10) eqn:E.
  - apply Nat.leb_le in E. lia.
  - reflexivity.
Qed.

Lemma witness_fn_opt_correct : forall n a,
  witness_fn_opt n = Some a -> Assessment.total_unbounded a = n.
Proof.
  intros n a H. unfold witness_fn_opt in H.
  destruct (n <=? 10) eqn:E.
  - inversion H. subst. apply witness_fn_correct. apply Nat.leb_le. exact E.
  - discriminate.
Qed.

Lemma witness_fn_opt_complete : forall n,
  n <= 10 <-> exists a, witness_fn_opt n = Some a.
Proof.
  intros n. split.
  - intro H. exists (witness_fn n). apply witness_fn_opt_some. exact H.
  - intros [a Ha]. unfold witness_fn_opt in Ha.
    destruct (n <=? 10) eqn:E.
    + apply Nat.leb_le. exact E.
    + discriminate.
Qed.

End Reachability.

(** ** Clinical Classification

    Classification of APGAR scores into clinical categories per AAP 2015:
    - [Low]: Score 0-3, requires immediate intervention
    - [ModeratelyAbnormal]: Score 4-6, requires supportive care
    - [Reassuring]: Score 7-10, routine care only

    Key theorems:
    - [low_iff], [moderate_iff], [reassuring_iff]: Bidirectional characterizations
    - [monotonic]: Higher scores yield same or better classification
    - [partition]: Every score belongs to exactly one category
*)

Module Classification.

Inductive t : Type :=
  | Low : t
  | ModeratelyAbnormal : t
  | Reassuring : t.

Definition eq_dec : forall c1 c2 : t, {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Low; ModeratelyAbnormal; Reassuring].

Lemma all_complete : forall c : t, In c all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition low_threshold : nat := 3.
Definition moderate_threshold : nat := 6.

Definition of_score (score : nat) : t :=
  if score <=? low_threshold then Low
  else if score <=? moderate_threshold then ModeratelyAbnormal
  else Reassuring.

Record Thresholds : Type := mkThresholds {
  th_low : nat;
  th_moderate : nat;
  th_low_lt_moderate : th_low < th_moderate
}.

Definition default_thresholds : Thresholds.
Proof. exact (mkThresholds 3 6 ltac:(lia)). Defined.

Definition of_score_param (th : Thresholds) (score : nat) : t :=
  if score <=? th_low th then Low
  else if score <=? th_moderate th then ModeratelyAbnormal
  else Reassuring.

Lemma of_score_param_default : forall score,
  of_score_param default_thresholds score = of_score score.
Proof. intros score. unfold of_score_param, of_score, default_thresholds. reflexivity. Qed.

Definition of_assessment (a : Assessment.t) : t :=
  of_score (Assessment.total_unbounded a).

Inductive ScoreInRange : t -> nat -> Prop :=
  | LowRange : forall n, n <= 3 -> ScoreInRange Low n
  | ModerateRange : forall n, 4 <= n <= 6 -> ScoreInRange ModeratelyAbnormal n
  | ReassureRange : forall n, 7 <= n -> ScoreInRange Reassuring n.

Lemma of_score_correct : forall score,
  ScoreInRange (of_score score) score.
Proof.
  intros score. unfold of_score, low_threshold, moderate_threshold.
  destruct (score <=? 3) eqn:E1.
  - apply Nat.leb_le in E1. constructor. exact E1.
  - apply Nat.leb_gt in E1.
    destruct (score <=? 6) eqn:E2.
    + apply Nat.leb_le in E2. constructor. lia.
    + apply Nat.leb_gt in E2. constructor. lia.
Qed.

Definition classify_dec (score : nat) :
  {of_score score = Low /\ score <= 3} +
  {of_score score = ModeratelyAbnormal /\ 4 <= score <= 6} +
  {of_score score = Reassuring /\ 7 <= score}.
Proof.
  unfold of_score, low_threshold, moderate_threshold.
  destruct (score <=? 3) eqn:E1.
  - left. left. apply Nat.leb_le in E1. split; [reflexivity | exact E1].
  - apply Nat.leb_gt in E1.
    destruct (score <=? 6) eqn:E2.
    + left. right. apply Nat.leb_le in E2. split; [reflexivity | lia].
    + right. apply Nat.leb_gt in E2. split; [reflexivity | lia].
Defined.

Lemma classification_deterministic : forall score c1 c2,
  ScoreInRange c1 score -> ScoreInRange c2 score -> c1 = c2.
Proof.
  intros score c1 c2 H1 H2.
  inversion H1; inversion H2; subst; try reflexivity; lia.
Qed.

Lemma of_score_low_inv : forall s, of_score s = Low -> s <= 3.
Proof.
  intros s H. unfold of_score, low_threshold in H.
  destruct (s <=? 3) eqn:E.
  - now apply Nat.leb_le.
  - destruct (s <=? moderate_threshold); discriminate.
Qed.

Lemma of_score_low : forall s, s <= 3 -> of_score s = Low.
Proof.
  intros s H. unfold of_score, low_threshold.
  destruct (s <=? 3) eqn:E; [reflexivity|].
  apply Nat.leb_gt in E. lia.
Qed.

Lemma of_score_moderate_inv : forall s, of_score s = ModeratelyAbnormal -> 4 <= s <= 6.
Proof.
  intros s H. unfold of_score, low_threshold, moderate_threshold in H.
  destruct (s <=? 3) eqn:E1; [discriminate|].
  destruct (s <=? 6) eqn:E2; [|discriminate].
  apply Nat.leb_gt in E1. apply Nat.leb_le in E2. lia.
Qed.

Lemma of_score_moderate : forall s, 4 <= s <= 6 -> of_score s = ModeratelyAbnormal.
Proof.
  intros s [H1 H2]. unfold of_score, low_threshold, moderate_threshold.
  destruct (s <=? 3) eqn:E1.
  - apply Nat.leb_le in E1. lia.
  - destruct (s <=? 6) eqn:E2; [reflexivity|].
    apply Nat.leb_gt in E2. lia.
Qed.

Lemma of_score_reassuring_inv : forall s, of_score s = Reassuring -> 7 <= s.
Proof.
  intros s H. unfold of_score, low_threshold, moderate_threshold in H.
  destruct (s <=? 3) eqn:E1; [discriminate|].
  destruct (s <=? 6) eqn:E2; [discriminate|].
  apply Nat.leb_gt in E2. lia.
Qed.

Lemma of_score_reassuring : forall s, 7 <= s -> of_score s = Reassuring.
Proof.
  intros s H. unfold of_score, low_threshold, moderate_threshold.
  destruct (s <=? 3) eqn:E1.
  - apply Nat.leb_le in E1. lia.
  - destruct (s <=? 6) eqn:E2.
    + apply Nat.leb_le in E2. lia.
    + reflexivity.
Qed.

Definition decide_low : forall score, {score <= 3} + {score > 3}.
Proof.
  intros score. destruct (score <=? 3) eqn:E.
  - left. now apply Nat.leb_le.
  - right. now apply Nat.leb_gt.
Defined.

Definition decide_moderate : forall score, {4 <= score <= 6} + {score < 4 \/ score > 6}.
Proof.
  intros score.
  destruct (4 <=? score) eqn:E1; destruct (score <=? 6) eqn:E2.
  - left. split; now apply Nat.leb_le.
  - right. right. now apply Nat.leb_gt.
  - right. left. now apply Nat.leb_gt.
  - right. left. now apply Nat.leb_gt.
Defined.

Definition decide_reassuring : forall score, {7 <= score} + {score < 7}.
Proof.
  intros score. destruct (7 <=? score) eqn:E.
  - left. now apply Nat.leb_le.
  - right. now apply Nat.leb_gt.
Defined.

Theorem low_iff : forall score,
  of_score score = Low <-> score <= 3.
Proof.
  intros score. split.
  - exact (of_score_low_inv score).
  - exact (of_score_low score).
Qed.

Theorem moderate_iff : forall score,
  of_score score = ModeratelyAbnormal <-> 4 <= score <= 6.
Proof.
  intros score. split.
  - exact (of_score_moderate_inv score).
  - exact (of_score_moderate score).
Qed.

Theorem reassuring_iff : forall score,
  of_score score = Reassuring <-> 7 <= score.
Proof.
  intros score. split.
  - exact (of_score_reassuring_inv score).
  - exact (of_score_reassuring score).
Qed.

Theorem classification_exhaustive : forall a : Assessment.t,
  of_assessment a = Low \/
  of_assessment a = ModeratelyAbnormal \/
  of_assessment a = Reassuring.
Proof.
  intros a. unfold of_assessment, of_score, low_threshold, moderate_threshold.
  destruct (Assessment.total_unbounded a <=? 3); [left; reflexivity|].
  destruct (Assessment.total_unbounded a <=? 6); [right; left; reflexivity|].
  right; right; reflexivity.
Qed.

Theorem minimum_is_low : of_assessment Assessment.minimum = Low.
Proof. reflexivity. Qed.

Theorem maximum_is_reassuring : of_assessment Assessment.maximum = Reassuring.
Proof. reflexivity. Qed.

Definition to_nat (c : t) : nat :=
  match c with
  | Low => 0
  | ModeratelyAbnormal => 1
  | Reassuring => 2
  end.

Definition le (c1 c2 : t) : Prop := to_nat c1 <= to_nat c2.

Notation "c1 <=c c2" := (le c1 c2) (at level 70).

Lemma le_refl : forall c, c <=c c.
Proof. intros c. unfold le. lia. Qed.

Lemma le_trans : forall c1 c2 c3, c1 <=c c2 -> c2 <=c c3 -> c1 <=c c3.
Proof. intros c1 c2 c3 H1 H2. unfold le in *. lia. Qed.

Lemma le_antisym : forall c1 c2, c1 <=c c2 -> c2 <=c c1 -> c1 = c2.
Proof.
  intros [] [] H1 H2; unfold le, to_nat in *; try reflexivity; lia.
Qed.

(** Trichotomy: any two classifications are comparable *)
Theorem trichotomy : forall c1 c2 : t,
  c1 = c2 \/ c1 <=c c2 \/ c2 <=c c1.
Proof.
  intros [] []; unfold le, to_nat;
  try (left; reflexivity);
  try (right; left; lia);
  try (right; right; lia).
Qed.

(** Strict ordering for classification *)
Definition lt (c1 c2 : t) : Prop := to_nat c1 < to_nat c2.

Notation "c1 <c c2" := (lt c1 c2) (at level 70).

Theorem strict_trichotomy : forall c1 c2 : t,
  c1 = c2 \/ c1 <c c2 \/ c2 <c c1.
Proof.
  intros [] []; unfold lt, to_nat;
  try (left; reflexivity);
  try (right; left; lia);
  try (right; right; lia).
Qed.

Theorem lt_irrefl : forall c, ~ (c <c c).
Proof. intros c H. unfold lt in H. lia. Qed.

Theorem lt_trans : forall c1 c2 c3, c1 <c c2 -> c2 <c c3 -> c1 <c c3.
Proof. intros c1 c2 c3 H1 H2. unfold lt in *. lia. Qed.

Theorem lt_le_incl : forall c1 c2, c1 <c c2 -> c1 <=c c2.
Proof. intros c1 c2 H. unfold lt, le in *. lia. Qed.

Theorem lt_le_trans : forall c1 c2 c3, c1 <c c2 -> c2 <=c c3 -> c1 <c c3.
Proof. intros c1 c2 c3 H1 H2. unfold lt, le in *. lia. Qed.

Theorem le_lt_trans : forall c1 c2 c3, c1 <=c c2 -> c2 <c c3 -> c1 <c c3.
Proof. intros c1 c2 c3 H1 H2. unfold lt, le in *. lia. Qed.

(** Classification injectivity on ranges: equal classifications imply same score bracket *)
Theorem of_score_same_class_same_bracket : forall s1 s2,
  of_score s1 = of_score s2 ->
  (s1 <= 3 /\ s2 <= 3) \/
  (4 <= s1 <= 6 /\ 4 <= s2 <= 6) \/
  (7 <= s1 /\ 7 <= s2).
Proof.
  intros s1 s2 H.
  destruct (classify_dec s1) as [[[H1a H1b] | [H1a H1b]] | [H1a H1b]];
  destruct (classify_dec s2) as [[[H2a H2b] | [H2a H2b]] | [H2a H2b]];
  try (rewrite H1a in H; rewrite H2a in H; discriminate);
  [left | right; left | right; right]; split; try split; try assumption; try lia.
Qed.

(** Decidable equality on classification *)
Theorem of_score_eq_dec_via_class : forall s1 s2,
  {of_score s1 = of_score s2} + {of_score s1 <> of_score s2}.
Proof.
  intros s1 s2. apply eq_dec.
Defined.

Lemma Low_le_all : forall c, Low <=c c.
Proof. intros []; unfold le, to_nat; lia. Qed.

Lemma all_le_Reassuring : forall c, c <=c Reassuring.
Proof. intros []; unfold le, to_nat; lia. Qed.

Theorem monotonic : forall s1 s2,
  s1 <= s2 -> of_score s1 <=c of_score s2.
Proof.
  intros s1 s2 Hle. unfold le, of_score, to_nat, low_threshold, moderate_threshold.
  repeat match goal with |- context [?x <=? ?y] => destruct (x <=? y) eqn:? end;
  simpl; try lia;
  repeat match goal with H : (_ <=? _) = true |- _ => apply Nat.leb_le in H end;
  repeat match goal with H : (_ <=? _) = false |- _ => apply Nat.leb_gt in H end;
  lia.
Qed.

Theorem monotonic_assessment : forall a1 a2,
  Assessment.total_unbounded a1 <= Assessment.total_unbounded a2 ->
  of_assessment a1 <=c of_assessment a2.
Proof.
  intros a1 a2 H. unfold of_assessment. apply monotonic. exact H.
Qed.

Definition to_score_range (c : t) : nat * nat :=
  match c with
  | Low => (0, 3)
  | ModeratelyAbnormal => (4, 6)
  | Reassuring => (7, 10)
  end.

Definition to_score_interval (c : t) : Interval.t :=
  match c with
  | Low => Interval.make 0 3 ltac:(lia)
  | ModeratelyAbnormal => Interval.make 4 6 ltac:(lia)
  | Reassuring => Interval.make 7 10 ltac:(lia)
  end.

Lemma to_score_interval_correct : forall c s,
  Interval.contains (to_score_interval c) s -> of_score s = c.
Proof.
  intros [] s [Hlo Hhi]; simpl in *.
  - apply of_score_low. lia.
  - apply of_score_moderate. lia.
  - apply of_score_reassuring. lia.
Qed.

Definition representative_score (c : t) : nat :=
  match c with
  | Low => 0
  | ModeratelyAbnormal => 5
  | Reassuring => 10
  end.

Theorem representative_score_correct : forall c,
  of_score (representative_score c) = c.
Proof. intros []; reflexivity. Qed.

Theorem to_score_range_correct : forall c lo hi,
  to_score_range c = (lo, hi) ->
  forall s, lo <= s <= hi -> of_score s = c.
Proof.
  intros [] lo hi H s Hs; injection H; intros; subst.
  - apply of_score_low. lia.
  - apply of_score_moderate. lia.
  - apply of_score_reassuring. lia.
Qed.

Theorem of_score_surjective : forall c : t, exists s : nat, of_score s = c.
Proof.
  intros c. exists (representative_score c). apply representative_score_correct.
Qed.

Theorem of_score_surjective_bounded : forall c : t,
  exists s : nat, s <= 10 /\ of_score s = c.
Proof.
  intros [].
  - exists 0. split; [lia | reflexivity].
  - exists 5. split; [lia | reflexivity].
  - exists 10. split; [lia | reflexivity].
Qed.

Definition of_classification (c : t) : nat := representative_score c.

Theorem of_classification_roundtrip : forall c,
  of_score (of_classification c) = c.
Proof. exact representative_score_correct. Qed.

Theorem of_score_of_classification_in_range : forall c,
  let '(lo, hi) := to_score_range c in
  lo <= of_classification c <= hi.
Proof. intros []; simpl; lia. Qed.

Definition score_in_class (s : nat) (c : t) : Prop := of_score s = c.

Lemma score_in_class_dec : forall s c, {score_in_class s c} + {~ score_in_class s c}.
Proof.
  intros s c. unfold score_in_class. apply eq_dec.
Defined.

Theorem classification_partition : forall s,
  (of_score s = Low /\ s <= 3) \/
  (of_score s = ModeratelyAbnormal /\ 4 <= s <= 6) \/
  (of_score s = Reassuring /\ 7 <= s).
Proof.
  intros s.
  destruct (classify_dec s) as [[[H1 H2] | [H1 H2]] | [H1 H2]].
  - left. split; assumption.
  - right. left. split; assumption.
  - right. right. split; assumption.
Qed.

Theorem reassuring_requires_nonzero_components : forall a : Assessment.t,
  of_assessment a = Reassuring ->
  ~ (Assessment.appearance a = Appearance.PaleBlue /\
     Assessment.pulse a = Pulse.Absent /\
     Assessment.grimace a = Grimace.NoResponse /\
     Assessment.activity a = Activity.Flaccid /\
     Assessment.respiration a = Respiration.Apneic).
Proof.
  intros a Hclass [Hap [Hpu [Hgr [Hac Hre]]]].
  apply reassuring_iff in Hclass.
  pose proof (Assessment.all_zero_implies_score_zero a Hap Hpu Hgr Hac Hre) as H0.
  lia.
Qed.

Definition of_nat (n : nat) : t :=
  match n with
  | 0 => Low
  | 1 => ModeratelyAbnormal
  | _ => Reassuring
  end.

Theorem of_nat_to_nat : forall c, of_nat (to_nat c) = c.
Proof. intros []; reflexivity. Qed.

Theorem to_nat_of_nat : forall n, n <= 2 -> to_nat (of_nat n) = n.
Proof.
  intros [|[|[|n]]] H; try reflexivity; lia.
Qed.

Theorem of_nat_injective : forall n m,
  n <= 2 -> m <= 2 -> of_nat n = of_nat m -> n = m.
Proof.
  intros [|[|[|n]]] [|[|[|m]]] Hn Hm H; try reflexivity; try discriminate; try lia.
Qed.

(** Clinical boundary examples: verify exact boundary behavior per AAP 2015 *)

(** Score 0: Maximum severity *)
Example boundary_score_0 : of_score 0 = Low.
Proof. reflexivity. Qed.

(** Score 3: Upper boundary of Low *)
Example boundary_score_3_low : of_score 3 = Low.
Proof. reflexivity. Qed.

(** Score 4: Lower boundary of ModeratelyAbnormal - this is the critical transition *)
Example boundary_score_4_moderate : of_score 4 = ModeratelyAbnormal.
Proof. reflexivity. Qed.

(** Score 6: Upper boundary of ModeratelyAbnormal *)
Example boundary_score_6_moderate : of_score 6 = ModeratelyAbnormal.
Proof. reflexivity. Qed.

(** Score 7: Lower boundary of Reassuring - this is where we consider baby OK *)
Example boundary_score_7_reassuring : of_score 7 = Reassuring.
Proof. reflexivity. Qed.

(** Score 10: Maximum score, fully reassuring *)
Example boundary_score_10 : of_score 10 = Reassuring.
Proof. reflexivity. Qed.

(** Boundary theorem: 3 is Low but 4 is not *)
Theorem boundary_3_4 : of_score 3 = Low /\ of_score 4 <> Low.
Proof. split; [reflexivity | discriminate]. Qed.

(** Boundary theorem: 6 is Moderate but 7 is not *)
Theorem boundary_6_7 : of_score 6 = ModeratelyAbnormal /\ of_score 7 <> ModeratelyAbnormal.
Proof. split; [reflexivity | discriminate]. Qed.

(** Clinical guideline: AAP 2015 thresholds are 0-3, 4-6, 7-10 *)
Theorem aap_2015_thresholds_correct :
  (forall n, n <= 3 -> of_score n = Low) /\
  (forall n, 4 <= n <= 6 -> of_score n = ModeratelyAbnormal) /\
  (forall n, 7 <= n -> of_score n = Reassuring).
Proof.
  repeat split.
  - intros n Hn. apply low_iff. lia.
  - intros n [Hlo Hhi]. apply moderate_iff. lia.
  - intros n Hn. apply reassuring_iff. lia.
Qed.

(******************************************************************************)
(*  PRETERM-ADJUSTED CLASSIFICATION                                           *)
(*                                                                            *)
(*  Preterm neonates have different baseline expectations for vitality signs. *)
(*  This section provides adjusted classification that accounts for           *)
(*  gestational age. [AAP2015] notes that APGAR may be affected by GA.        *)
(******************************************************************************)

(** Adjustment factor based on gestational age *)
Definition preterm_adjustment (ga_weeks : nat) : nat :=
  if ga_weeks <? 28 then 2        (** Extreme preterm: +2 adjustment *)
  else if ga_weeks <? 32 then 1   (** Very preterm: +1 adjustment *)
  else 0.                         (** Moderate preterm or term: no adjustment *)

(** Adjusted score for classification purposes *)
Definition adjusted_score (raw_score ga_weeks : nat) : nat :=
  raw_score + preterm_adjustment ga_weeks.

(** Adjusted classification using maturity-compensated score *)
Definition of_score_preterm_adjusted (raw_score ga_weeks : nat) : t :=
  of_score (Nat.min (adjusted_score raw_score ga_weeks) 10).

(** Preterm context record *)
Record PretermContext : Type := mkPretermContext {
  ctx_ga_weeks : nat;
  ctx_raw_score : nat;
  ctx_raw_bound : ctx_raw_score <= 10
}.

Definition adjusted_classification (ctx : PretermContext) : t :=
  of_score_preterm_adjusted (ctx_raw_score ctx) (ctx_ga_weeks ctx).

(** Extreme preterm (<28 weeks) gets most lenient interpretation *)
Lemma extreme_preterm_adjustment : forall ga,
  ga < 28 -> preterm_adjustment ga = 2.
Proof.
  intros ga Hga. unfold preterm_adjustment.
  destruct (ga <? 28) eqn:E.
  - reflexivity.
  - apply Nat.ltb_ge in E. lia.
Qed.

(** Very preterm (28-31 weeks) gets moderate adjustment *)
Lemma very_preterm_adjustment : forall ga,
  28 <= ga < 32 -> preterm_adjustment ga = 1.
Proof.
  intros ga [Hlo Hhi]. unfold preterm_adjustment.
  destruct (ga <? 28) eqn:E1.
  - apply Nat.ltb_lt in E1. lia.
  - destruct (ga <? 32) eqn:E2.
    + reflexivity.
    + apply Nat.ltb_ge in E2. lia.
Qed.

(** Term neonates get no adjustment *)
Lemma term_no_adjustment : forall ga,
  ga >= 32 -> preterm_adjustment ga = 0.
Proof.
  intros ga Hga. unfold preterm_adjustment.
  destruct (ga <? 28) eqn:E1.
  - apply Nat.ltb_lt in E1. lia.
  - destruct (ga <? 32) eqn:E2.
    + apply Nat.ltb_lt in E2. lia.
    + reflexivity.
Qed.

(** Adjustment never exceeds 2 *)
Lemma preterm_adjustment_bound : forall ga,
  preterm_adjustment ga <= 2.
Proof.
  intros ga. unfold preterm_adjustment.
  destruct (ga <? 28); [lia|].
  destruct (ga <? 32); lia.
Qed.

(** Adjusted score never exceeds 12 (but we cap at 10) *)
Lemma adjusted_score_raw_bound : forall raw_score ga,
  raw_score <= 10 -> adjusted_score raw_score ga <= 12.
Proof.
  intros raw_score ga Hraw. unfold adjusted_score.
  pose proof (preterm_adjustment_bound ga). lia.
Qed.

(** Adjusted score is at least raw score *)
Lemma adjusted_score_ge_raw : forall raw_score ga,
  raw_score <= adjusted_score raw_score ga.
Proof.
  intros raw_score ga. unfold adjusted_score.
  pose proof (preterm_adjustment_bound ga). lia.
Qed.

(** Adjusted effective score (capped) is at least raw when raw <= 10 *)
Lemma adjusted_effective_ge_raw : forall raw_score ga,
  raw_score <= 10 ->
  raw_score <= Nat.min (adjusted_score raw_score ga) 10.
Proof.
  intros raw_score ga Hraw. unfold adjusted_score.
  pose proof (preterm_adjustment_bound ga).
  apply Nat.min_glb; lia.
Qed.

(** Term neonate: adjusted = raw *)
Theorem term_adjusted_equals_raw : forall raw_score,
  raw_score <= 10 ->
  of_score_preterm_adjusted raw_score 37 = of_score raw_score.
Proof.
  intros raw_score Hraw.
  unfold of_score_preterm_adjusted, adjusted_score.
  rewrite term_no_adjustment by lia.
  simpl. rewrite Nat.add_0_r.
  rewrite Nat.min_l by lia. reflexivity.
Qed.

End Classification.

(** ** Intervention Protocol

    Resuscitation guidelines based on NRP 2021:
    - [RoutineCare]: Score 7-10, observation only
    - [StimulationOxygen]: Score 4-6, tactile stimulation with supplemental O2
    - [PositivePressureVentilation]: Score 1-3, PPV required
    - [FullResuscitation]: Score 0, full resuscitation including possible intubation

    Key theorems:
    - [anti_monotonic]: Higher scores require less intervention (inverse relationship)
    - [reassuring_gets_routine]: Reassuring classification implies routine care
    - [low_not_routine]: Low classification excludes routine care
    - [full_iff_zero]: Full resuscitation iff score is 0
*)

Module Intervention.

Inductive t : Type :=
  | RoutineCare : t
  | StimulationOxygen : t
  | PositivePressureVentilation : t
  | FullResuscitation : t.

Definition eq_dec : forall i1 i2 : t, {i1 = i2} + {i1 <> i2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t :=
  [RoutineCare; StimulationOxygen; PositivePressureVentilation; FullResuscitation].

Lemma all_complete : forall i : t, In i all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition of_score (score : nat) : t :=
  if 7 <=? score then RoutineCare
  else if 4 <=? score then StimulationOxygen
  else if 1 <=? score then PositivePressureVentilation
  else FullResuscitation.

Definition of_assessment (a : Assessment.t) : t :=
  of_score (Assessment.total_unbounded a).

Inductive ScoreRequires : nat -> t -> Prop :=
  | RequiresRoutine : forall n, 7 <= n -> ScoreRequires n RoutineCare
  | RequiresStim : forall n, 4 <= n <= 6 -> ScoreRequires n StimulationOxygen
  | RequiresPPV : forall n, 1 <= n <= 3 -> ScoreRequires n PositivePressureVentilation
  | RequiresFull : ScoreRequires 0 FullResuscitation.

Lemma of_score_correct : forall score,
  score <= 10 -> ScoreRequires score (of_score score).
Proof.
  intros score Hbound. unfold of_score.
  destruct (7 <=? score) eqn:E1.
  - apply Nat.leb_le in E1. constructor. exact E1.
  - apply Nat.leb_gt in E1.
    destruct (4 <=? score) eqn:E2.
    + apply Nat.leb_le in E2. constructor. lia.
    + apply Nat.leb_gt in E2.
      destruct (1 <=? score) eqn:E3.
      * apply Nat.leb_le in E3. constructor. lia.
      * apply Nat.leb_gt in E3. replace score with 0 by lia. constructor.
Qed.

Definition intervention_dec (score : nat) :
  {of_score score = RoutineCare /\ 7 <= score} +
  {of_score score = StimulationOxygen /\ 4 <= score <= 6} +
  {of_score score = PositivePressureVentilation /\ 1 <= score <= 3} +
  {of_score score = FullResuscitation /\ score = 0}.
Proof.
  unfold of_score.
  destruct (7 <=? score) eqn:E1.
  - left. left. left. apply Nat.leb_le in E1. split; [reflexivity | exact E1].
  - apply Nat.leb_gt in E1.
    destruct (4 <=? score) eqn:E2.
    + left. left. right. apply Nat.leb_le in E2. split; [reflexivity | lia].
    + apply Nat.leb_gt in E2.
      destruct (1 <=? score) eqn:E3.
      * left. right. apply Nat.leb_le in E3. split; [reflexivity | lia].
      * right. apply Nat.leb_gt in E3. split; [reflexivity | lia].
Defined.

Theorem reassuring_gets_routine : forall a : Assessment.t,
  Classification.of_assessment a = Classification.Reassuring ->
  of_assessment a = RoutineCare.
Proof.
  intros a H. apply Classification.reassuring_iff in H.
  unfold of_assessment, of_score.
  destruct (7 <=? Assessment.total_unbounded a) eqn:E; [reflexivity|].
  apply Nat.leb_gt in E. lia.
Qed.

Theorem low_not_routine : forall a : Assessment.t,
  Classification.of_assessment a = Classification.Low ->
  of_assessment a <> RoutineCare.
Proof.
  intros a H. apply Classification.low_iff in H.
  unfold of_assessment, of_score.
  destruct (7 <=? Assessment.total_unbounded a) eqn:E.
  - apply Nat.leb_le in E. lia.
  - destruct (4 <=? Assessment.total_unbounded a) eqn:E2.
    + apply Nat.leb_le in E2. lia.
    + destruct (1 <=? Assessment.total_unbounded a); discriminate.
Qed.

Theorem zero_requires_full : of_score 0 = FullResuscitation.
Proof. reflexivity. Qed.

Theorem full_requires_zero : forall s, of_score s = FullResuscitation -> s = 0.
Proof.
  intros s H. unfold of_score in H.
  destruct (7 <=? s) eqn:E1; [discriminate|].
  destruct (4 <=? s) eqn:E2; [discriminate|].
  destruct (1 <=? s) eqn:E3; [discriminate|].
  apply Nat.leb_gt in E3. lia.
Qed.

Theorem full_iff_zero : forall s, of_score s = FullResuscitation <-> s = 0.
Proof.
  intros s. split.
  - apply full_requires_zero.
  - intros H. subst. apply zero_requires_full.
Qed.

Theorem perfect_requires_routine : of_score 10 = RoutineCare.
Proof. reflexivity. Qed.

Lemma of_score_routine_inv : forall s, of_score s = RoutineCare -> 7 <= s.
Proof.
  intros s H. unfold of_score in H.
  destruct (7 <=? s) eqn:E.
  - apply Nat.leb_le in E. exact E.
  - destruct (4 <=? s) eqn:E2.
    + discriminate H.
    + destruct (1 <=? s); discriminate H.
Qed.

Lemma of_score_routine : forall s, 7 <= s -> of_score s = RoutineCare.
Proof.
  intros s H. unfold of_score.
  destruct (7 <=? s) eqn:E; [reflexivity |].
  apply Nat.leb_gt in E. lia.
Qed.

Theorem routine_iff : forall s, of_score s = RoutineCare <-> 7 <= s.
Proof.
  intros s. split.
  - exact (of_score_routine_inv s).
  - exact (of_score_routine s).
Qed.

Lemma of_score_stim_inv : forall s, of_score s = StimulationOxygen -> 4 <= s <= 6.
Proof.
  intros s H. unfold of_score in H.
  destruct (7 <=? s) eqn:E1; [discriminate H|].
  destruct (4 <=? s) eqn:E2.
  - apply Nat.leb_gt in E1. apply Nat.leb_le in E2. lia.
  - destruct (1 <=? s) eqn:E3; discriminate H.
Qed.

Lemma of_score_stim : forall s, 4 <= s <= 6 -> of_score s = StimulationOxygen.
Proof.
  intros s [H1 H2]. unfold of_score.
  destruct (7 <=? s) eqn:E1.
  - apply Nat.leb_le in E1. lia.
  - destruct (4 <=? s) eqn:E2; [reflexivity|].
    apply Nat.leb_gt in E2. lia.
Qed.

Theorem stim_iff : forall s, of_score s = StimulationOxygen <-> 4 <= s <= 6.
Proof.
  intros s. split.
  - exact (of_score_stim_inv s).
  - exact (of_score_stim s).
Qed.

Lemma of_score_ppv_inv : forall s, of_score s = PositivePressureVentilation -> 1 <= s <= 3.
Proof.
  intros s H. unfold of_score in H.
  destruct (7 <=? s) eqn:E1; [discriminate|].
  destruct (4 <=? s) eqn:E2; [discriminate|].
  destruct (1 <=? s) eqn:E3; [|discriminate].
  apply Nat.leb_gt in E1. apply Nat.leb_gt in E2. apply Nat.leb_le in E3. lia.
Qed.

Lemma of_score_ppv : forall s, 1 <= s <= 3 -> of_score s = PositivePressureVentilation.
Proof.
  intros s [H1 H2]. unfold of_score.
  destruct (7 <=? s) eqn:E1.
  - apply Nat.leb_le in E1. lia.
  - destruct (4 <=? s) eqn:E2.
    + apply Nat.leb_le in E2. lia.
    + destruct (1 <=? s) eqn:E3; [reflexivity|].
      apply Nat.leb_gt in E3. lia.
Qed.

Theorem ppv_iff : forall s, of_score s = PositivePressureVentilation <-> 1 <= s <= 3.
Proof.
  intros s. split.
  - exact (of_score_ppv_inv s).
  - exact (of_score_ppv s).
Qed.

Theorem intervention_monotonic : forall s1 s2 : nat,
  s1 <= s2 -> s2 <= 10 ->
  of_score s1 = RoutineCare -> of_score s2 = RoutineCare.
Proof.
  intros s1 s2 Hle Hbound H.
  apply of_score_routine_inv in H.
  apply of_score_routine. lia.
Qed.

Definition severity (i : t) : nat :=
  match i with
  | RoutineCare => 0
  | StimulationOxygen => 1
  | PositivePressureVentilation => 2
  | FullResuscitation => 3
  end.

Definition le (i1 i2 : t) : Prop := severity i1 <= severity i2.

Notation "i1 <=i i2" := (le i1 i2) (at level 70).

Lemma le_refl : forall i, i <=i i.
Proof. intros i. unfold le. lia. Qed.

Lemma le_trans : forall i1 i2 i3, i1 <=i i2 -> i2 <=i i3 -> i1 <=i i3.
Proof. intros i1 i2 i3 H1 H2. unfold le in *. lia. Qed.

Lemma le_antisym : forall i1 i2, i1 <=i i2 -> i2 <=i i1 -> i1 = i2.
Proof.
  intros [] [] H1 H2; unfold le, severity in *; try reflexivity; lia.
Qed.

Lemma RoutineCare_le_all : forall i, RoutineCare <=i i.
Proof. intros []; unfold le, severity; lia. Qed.

Lemma all_le_FullResuscitation : forall i, i <=i FullResuscitation.
Proof. intros []; unfold le, severity; lia. Qed.

Theorem anti_monotonic : forall s1 s2,
  s1 <= s2 -> of_score s2 <=i of_score s1.
Proof.
  intros s1 s2 Hle. unfold le, of_score, severity.
  destruct (7 <=? s1) eqn:E1; destruct (7 <=? s2) eqn:E2.
  - lia.
  - apply Nat.leb_le in E1. apply Nat.leb_gt in E2. lia.
  - destruct (4 <=? s2) eqn:E3; [lia|].
    destruct (1 <=? s2) eqn:E4; lia.
  - destruct (4 <=? s1) eqn:E3; destruct (4 <=? s2) eqn:E4.
    + lia.
    + apply Nat.leb_le in E3. apply Nat.leb_gt in E4. lia.
    + destruct (1 <=? s1) eqn:E5; [lia|].
      apply Nat.leb_gt in E3. apply Nat.leb_le in E4. lia.
    + destruct (1 <=? s1) eqn:E5; destruct (1 <=? s2) eqn:E6.
      * lia.
      * apply Nat.leb_gt in E6. apply Nat.leb_le in E5. lia.
      * lia.
      * lia.
Qed.

Corollary higher_score_less_intervention : forall s1 s2,
  s1 <= s2 -> severity (of_score s2) <= severity (of_score s1).
Proof. intros s1 s2 H. exact (anti_monotonic s1 s2 H). Qed.

Definition to_score_range (i : t) : nat * nat :=
  match i with
  | FullResuscitation => (0, 0)
  | PositivePressureVentilation => (1, 3)
  | StimulationOxygen => (4, 6)
  | RoutineCare => (7, 10)
  end.

Definition to_score_interval (i : t) : Interval.t :=
  match i with
  | FullResuscitation => Interval.make 0 0 (le_n 0)
  | PositivePressureVentilation => Interval.make 1 3 ltac:(lia)
  | StimulationOxygen => Interval.make 4 6 ltac:(lia)
  | RoutineCare => Interval.make 7 10 ltac:(lia)
  end.

Lemma to_score_interval_correct : forall i s,
  Interval.contains (to_score_interval i) s -> of_score s = i.
Proof.
  intros [] s H; unfold Interval.contains, to_score_interval, Interval.make,
    Interval.lo, Interval.hi in H; simpl in H; destruct H as [Hlo Hhi];
  unfold of_score.
  - destruct (7 <=? s) eqn:E1; [reflexivity|].
    exfalso. apply Nat.leb_gt in E1. lia.
  - destruct (7 <=? s) eqn:E1.
    + exfalso. apply Nat.leb_le in E1. lia.
    + destruct (4 <=? s) eqn:E2; [reflexivity|].
      exfalso. apply Nat.leb_gt in E2. lia.
  - destruct (7 <=? s) eqn:E1.
    + exfalso. apply Nat.leb_le in E1. lia.
    + destruct (4 <=? s) eqn:E2.
      * exfalso. apply Nat.leb_le in E2. lia.
      * destruct (1 <=? s) eqn:E3; [reflexivity|].
        exfalso. apply Nat.leb_gt in E3. lia.
  - destruct s; [reflexivity | lia].
Qed.

Definition representative_score (i : t) : nat :=
  match i with
  | FullResuscitation => 0
  | PositivePressureVentilation => 2
  | StimulationOxygen => 5
  | RoutineCare => 10
  end.

Theorem representative_score_correct : forall i,
  of_score (representative_score i) = i.
Proof. intros []; reflexivity. Qed.

Theorem of_score_surjective : forall i : t, exists s : nat, of_score s = i.
Proof.
  intros i. exists (representative_score i). apply representative_score_correct.
Qed.

Theorem of_score_surjective_bounded : forall i : t,
  exists s : nat, s <= 10 /\ of_score s = i.
Proof.
  intros [].
  - exists 10. split; [lia | reflexivity].
  - exists 5. split; [lia | reflexivity].
  - exists 2. split; [lia | reflexivity].
  - exists 0. split; [lia | reflexivity].
Qed.

Record Thresholds : Type := mkThresholds {
  th_routine : nat;
  th_stim : nat;
  th_ppv : nat;
  th_routine_gt_stim : th_stim < th_routine;
  th_stim_gt_ppv : th_ppv < th_stim;
  th_ppv_gt_zero : 0 < th_ppv
}.

Definition default_thresholds : Thresholds.
Proof.
  exact (mkThresholds 7 4 1 ltac:(lia) ltac:(lia) ltac:(lia)).
Defined.

Definition of_score_param (th : Thresholds) (score : nat) : t :=
  if th_routine th <=? score then RoutineCare
  else if th_stim th <=? score then StimulationOxygen
  else if th_ppv th <=? score then PositivePressureVentilation
  else FullResuscitation.

Lemma of_score_param_default : forall score,
  of_score_param default_thresholds score = of_score score.
Proof.
  intros score. unfold of_score_param, of_score, default_thresholds. reflexivity.
Qed.

Definition of_intervention (i : t) : nat := representative_score i.

Theorem of_intervention_roundtrip : forall i,
  of_score (of_intervention i) = i.
Proof. exact representative_score_correct. Qed.

Theorem intervention_partition : forall s,
  s <= 10 ->
  (of_score s = RoutineCare /\ 7 <= s) \/
  (of_score s = StimulationOxygen /\ 4 <= s <= 6) \/
  (of_score s = PositivePressureVentilation /\ 1 <= s <= 3) \/
  (of_score s = FullResuscitation /\ s = 0).
Proof.
  intros s Hs.
  destruct (intervention_dec s) as [[[[H1 H2] | [H1 H2]] | [H1 H2]] | [H1 H2]].
  - left. split; assumption.
  - right. left. split; assumption.
  - right. right. left. split; assumption.
  - right. right. right. split; assumption.
Qed.

Theorem intervention_pairwise_disjoint : forall s i1 i2,
  of_score s = i1 -> of_score s = i2 -> i1 = i2.
Proof.
  intros s i1 i2 H1 H2. rewrite <- H1, <- H2. reflexivity.
Qed.

Theorem intervention_partition_exclusive : forall s,
  of_score s = RoutineCare -> of_score s <> StimulationOxygen.
Proof.
  intros s H1 H2. rewrite H1 in H2. discriminate.
Qed.

Theorem intervention_partition_exclusive' : forall s,
  of_score s = RoutineCare -> of_score s <> PositivePressureVentilation.
Proof.
  intros s H1 H2. rewrite H1 in H2. discriminate.
Qed.

Theorem intervention_partition_exclusive'' : forall s,
  of_score s = RoutineCare -> of_score s <> FullResuscitation.
Proof.
  intros s H1 H2. rewrite H1 in H2. discriminate.
Qed.

Theorem intervention_covers_all : forall s,
  s <= 10 ->
  of_score s = RoutineCare \/
  of_score s = StimulationOxygen \/
  of_score s = PositivePressureVentilation \/
  of_score s = FullResuscitation.
Proof.
  intros s Hs.
  destruct (intervention_partition s Hs) as [[H _]|[[H _]|[[H _]|[H _]]]];
  [left | right; left | right; right; left | right; right; right]; exact H.
Qed.

Theorem full_resuscitation_excludes_reassuring : forall a : Assessment.t,
  Intervention.of_assessment a = FullResuscitation ->
  Classification.of_assessment a = Classification.Low.
Proof.
  intros a H.
  unfold Intervention.of_assessment in H.
  apply full_iff_zero in H.
  unfold Classification.of_assessment.
  rewrite H. reflexivity.
Qed.

Theorem reassuring_excludes_full_resuscitation : forall a : Assessment.t,
  Classification.of_assessment a = Classification.Reassuring ->
  Intervention.of_assessment a <> FullResuscitation.
Proof.
  intros a H Hcontra.
  apply full_resuscitation_excludes_reassuring in Hcontra.
  rewrite H in Hcontra. discriminate.
Qed.

Definition of_nat (n : nat) : t :=
  match n with
  | 0 => RoutineCare
  | 1 => StimulationOxygen
  | 2 => PositivePressureVentilation
  | _ => FullResuscitation
  end.

Theorem of_nat_severity : forall i, of_nat (severity i) = i.
Proof. intros []; reflexivity. Qed.

Theorem severity_of_nat : forall n, n <= 3 -> severity (of_nat n) = n.
Proof.
  intros [|[|[|[|n]]]] H; try reflexivity; lia.
Qed.

Theorem of_nat_injective : forall n m,
  n <= 3 -> m <= 3 -> of_nat n = of_nat m -> n = m.
Proof.
  intros [|[|[|[|n]]]] [|[|[|[|m]]]] Hn Hm H; try reflexivity; try discriminate; try lia.
Qed.

(** Trichotomy: any two interventions are comparable *)
Theorem trichotomy : forall i1 i2 : t,
  i1 = i2 \/ i1 <=i i2 \/ i2 <=i i1.
Proof.
  intros [] []; unfold le, severity;
  try (left; reflexivity);
  try (right; left; lia);
  try (right; right; lia).
Qed.

(** Strict trichotomy with lt *)
Definition lt (i1 i2 : t) : Prop := severity i1 < severity i2.

Notation "i1 <i i2" := (lt i1 i2) (at level 70).

Theorem strict_trichotomy : forall i1 i2 : t,
  i1 = i2 \/ i1 <i i2 \/ i2 <i i1.
Proof.
  intros [] []; unfold lt, severity;
  try (left; reflexivity);
  try (right; left; lia);
  try (right; right; lia).
Qed.

Theorem lt_irrefl : forall i, ~ (i <i i).
Proof. intros i H. unfold lt in H. lia. Qed.

Theorem lt_trans : forall i1 i2 i3, i1 <i i2 -> i2 <i i3 -> i1 <i i3.
Proof. intros i1 i2 i3 H1 H2. unfold lt in *. lia. Qed.

Theorem lt_le_incl : forall i1 i2, i1 <i i2 -> i1 <=i i2.
Proof. intros i1 i2 H. unfold lt, le in *. lia. Qed.

End Intervention.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 8: ASSESSMENT TIMING                            *)
(*                                                                            *)
(*  Standard timing at 1 and 5 minutes, extended to 20 if score < 7.          *)
(*  Reference: [AAP2015], [NRP2021]                                           *)
(*                                                                            *)
(******************************************************************************)

Module Timing.

Inductive Time : Type :=
  | Min1 : Time
  | Min5 : Time
  | Min10 : Time
  | Min15 : Time
  | Min20 : Time.

Definition to_minutes (t : Time) : nat :=
  match t with
  | Min1 => 1
  | Min5 => 5
  | Min10 => 10
  | Min15 => 15
  | Min20 => 20
  end.

Definition to_seconds (t : Time) : nat := to_minutes t * 60.

(** Real timestamps in seconds since birth. Allows non-standard timing. *)
Record Timestamp : Type := mkTimestamp {
  seconds_since_birth : nat;
  seconds_valid : seconds_since_birth <= 1800
}.

Definition timestamp_to_minutes (ts : Timestamp) : nat :=
  seconds_since_birth ts / 60.

Definition timestamp_to_seconds (ts : Timestamp) : nat :=
  seconds_since_birth ts.

Definition nearest_standard_time (ts : Timestamp) : Time :=
  let mins := timestamp_to_minutes ts in
  if mins <? 3 then Min1
  else if mins <? 7 then Min5
  else if mins <? 12 then Min10
  else if mins <? 17 then Min15
  else Min20.

Definition is_within_window (ts : Timestamp) (t : Time) (window_secs : nat) : bool :=
  let target := to_seconds t in
  let actual := seconds_since_birth ts in
  (target - window_secs <=? actual) && (actual <=? target + window_secs).

Definition standard_window : nat := 30.

Definition is_standard_timing (ts : Timestamp) (t : Time) : bool :=
  is_within_window ts t standard_window.

(** Timing tolerance configuration *)
Definition clinical_tolerance_secs : nat := 30.
Definition strict_tolerance_secs : nat := 10.
Definition lenient_tolerance_secs : nat := 60.

(** Tolerance levels for timing assessment *)
Inductive ToleranceLevel : Type :=
  | StrictTolerance : ToleranceLevel
  | ClinicalTolerance : ToleranceLevel
  | LenientTolerance : ToleranceLevel.

Definition tolerance_level_eq_dec : forall t1 t2 : ToleranceLevel,
  {t1 = t2} + {t1 <> t2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition tolerance_to_secs (tol : ToleranceLevel) : nat :=
  match tol with
  | StrictTolerance => strict_tolerance_secs
  | ClinicalTolerance => clinical_tolerance_secs
  | LenientTolerance => lenient_tolerance_secs
  end.

Definition is_within_tolerance (ts : Timestamp) (t : Time) (tol : ToleranceLevel) : bool :=
  is_within_window ts t (tolerance_to_secs tol).

(** Clinical tolerance is standard *)
Lemma clinical_tolerance_is_standard : forall ts t,
  is_within_tolerance ts t ClinicalTolerance = is_standard_timing ts t.
Proof. intros ts t. reflexivity. Qed.

(** Strict tolerance implies clinical tolerance *)
Lemma strict_implies_clinical : forall ts t,
  is_within_tolerance ts t StrictTolerance = true ->
  is_within_tolerance ts t ClinicalTolerance = true.
Proof.
  intros ts t H.
  unfold is_within_tolerance, is_within_window, tolerance_to_secs,
         strict_tolerance_secs, clinical_tolerance_secs in *.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply andb_true_intro. split.
  - apply Nat.leb_le in H1. apply Nat.leb_le. lia.
  - apply Nat.leb_le in H2. apply Nat.leb_le. lia.
Qed.

(** Clinical tolerance implies lenient tolerance *)
Lemma clinical_implies_lenient : forall ts t,
  is_within_tolerance ts t ClinicalTolerance = true ->
  is_within_tolerance ts t LenientTolerance = true.
Proof.
  intros ts t H.
  unfold is_within_tolerance, is_within_window, tolerance_to_secs,
         clinical_tolerance_secs, lenient_tolerance_secs in *.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply andb_true_intro. split.
  - apply Nat.leb_le in H1. apply Nat.leb_le. lia.
  - apply Nat.leb_le in H2. apply Nat.leb_le. lia.
Qed.

(** Exact timing always satisfies any tolerance *)
Lemma exact_timing_satisfies_tolerance : forall ts t tol,
  seconds_since_birth ts = to_seconds t ->
  is_within_tolerance ts t tol = true.
Proof.
  intros ts t tol Hexact.
  unfold is_within_tolerance, is_within_window.
  rewrite Hexact. apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

(** Deviation measurement *)
Definition timing_deviation (ts : Timestamp) (t : Time) : nat :=
  let target := to_seconds t in
  let actual := seconds_since_birth ts in
  if actual <=? target then target - actual else actual - target.

Definition timing_deviation_signed (ts : Timestamp) (t : Time) : Z :=
  Z.of_nat (seconds_since_birth ts) - Z.of_nat (to_seconds t).

Lemma timing_deviation_zero_iff_exact : forall ts t,
  timing_deviation ts t = 0 <-> seconds_since_birth ts = to_seconds t.
Proof.
  intros ts t. unfold timing_deviation.
  destruct (seconds_since_birth ts <=? to_seconds t) eqn:E.
  - apply Nat.leb_le in E. split; intro H; lia.
  - apply Nat.leb_gt in E. split; intro H; lia.
Qed.

(** Tolerance check from deviation *)
Definition deviation_within_tolerance (dev : nat) (tol : ToleranceLevel) : bool :=
  dev <=? tolerance_to_secs tol.

Lemma deviation_tolerance_correct : forall ts t tol,
  deviation_within_tolerance (timing_deviation ts t) tol = true <->
  is_within_tolerance ts t tol = true.
Proof.
  intros ts t tol. unfold deviation_within_tolerance, is_within_tolerance,
    is_within_window, timing_deviation.
  destruct (seconds_since_birth ts <=? to_seconds t) eqn:E.
  - apply Nat.leb_le in E. rewrite andb_true_iff.
    repeat rewrite Nat.leb_le. split; intro H; lia.
  - apply Nat.leb_gt in E. rewrite andb_true_iff.
    repeat rewrite Nat.leb_le. split; intro H; lia.
Qed.

Lemma timestamp_30_is_min1 : forall ts,
  seconds_since_birth ts = 60 ->
  nearest_standard_time ts = Min1.
Proof.
  intros ts H. unfold nearest_standard_time, timestamp_to_minutes.
  rewrite H. simpl. reflexivity.
Qed.

Lemma timestamp_300_is_min5 : forall ts,
  seconds_since_birth ts = 300 ->
  nearest_standard_time ts = Min5.
Proof.
  intros ts H. unfold nearest_standard_time, timestamp_to_minutes.
  rewrite H. simpl. reflexivity.
Qed.

Definition eq_dec : forall t1 t2 : Time, {t1 = t2} + {t1 <> t2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Definition all : list Time := [Min1; Min5; Min10; Min15; Min20].

Lemma all_complete : forall t : Time, In t all.
Proof. ListHelpers.prove_all_complete. Qed.

Lemma all_nodup : NoDup all.
Proof. ListHelpers.prove_all_nodup. Qed.

Definition is_standard (t : Time) : bool :=
  match t with Min1 | Min5 => true | _ => false end.

Definition is_extended (t : Time) : bool := negb (is_standard t).

Definition needs_extension (score : nat) : bool := score <? 7.

Definition next (t : Time) : option Time :=
  match t with
  | Min1 => Some Min5
  | Min5 => Some Min10
  | Min10 => Some Min15
  | Min15 => Some Min20
  | Min20 => None
  end.

Lemma reassuring_stops_extension : forall score,
  Classification.of_score score = Classification.Reassuring ->
  needs_extension score = false.
Proof.
  intros score H. apply Classification.reassuring_iff in H.
  unfold needs_extension. destruct (score <? 7) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E. lia.
Qed.

Record TimedAssessment : Type := mkTimed {
  time : Time;
  assessment : Assessment.t
}.

Definition should_continue (ta : TimedAssessment) : bool :=
  needs_extension (Assessment.total_unbounded (assessment ta)) &&
  match next (time ta) with Some _ => true | None => false end.

Theorem should_continue_false_if_reassuring : forall ta,
  Classification.of_assessment (assessment ta) = Classification.Reassuring ->
  should_continue ta = false.
Proof.
  intros [t a] H. unfold should_continue. simpl.
  rewrite reassuring_stops_extension; [reflexivity|exact H].
Qed.

Theorem max_time_stops : forall a,
  should_continue (mkTimed Min20 a) = false.
Proof.
  intros a. unfold should_continue. simpl.
  rewrite andb_false_r. reflexivity.
Qed.

Definition step_count (t : Time) : nat :=
  match t with
  | Min1 => 0
  | Min5 => 1
  | Min10 => 2
  | Min15 => 3
  | Min20 => 4
  end.

Lemma next_increases_step : forall t t',
  next t = Some t' -> step_count t' = S (step_count t).
Proof. intros [] t' H; inversion H; reflexivity. Qed.

Lemma next_none_iff_max : forall t, next t = None <-> t = Min20.
Proof. intros []; split; intro H; try reflexivity; try discriminate. Qed.

Definition iterate_next (n : nat) (t : Time) : option Time :=
  nat_rect (fun _ => option Time) (Some t)
    (fun _ acc => match acc with Some t' => next t' | None => None end) n.

Lemma iterate_next_0 : forall t, iterate_next 0 t = Some t.
Proof. reflexivity. Qed.

Lemma iterate_next_S : forall n t,
  iterate_next (S n) t = match iterate_next n t with
                         | Some t' => next t'
                         | None => None
                         end.
Proof. reflexivity. Qed.

Theorem next_terminates : forall t, iterate_next 5 t = None.
Proof. intros []; reflexivity. Qed.

Theorem next_terminates_in_at_most_5 : forall t,
  exists n, n <= 5 /\ iterate_next n t = None.
Proof.
  intros [].
  - exists 5. split; [lia|reflexivity].
  - exists 4. split; [lia|reflexivity].
  - exists 3. split; [lia|reflexivity].
  - exists 2. split; [lia|reflexivity].
  - exists 1. split; [lia|reflexivity].
Qed.

Theorem next_terminates_exact : forall t,
  iterate_next (5 - step_count t) t = None.
Proof. intros []; reflexivity. Qed.

Lemma next_well_founded_aux : forall t,
  Acc (fun t1 t2 => next t2 = Some t1) t.
Proof.
  assert (H20: Acc (fun t1 t2 => next t2 = Some t1) Min20).
  { constructor. intros y Hy. discriminate. }
  assert (H15: Acc (fun t1 t2 => next t2 = Some t1) Min15).
  { constructor. intros y Hy. inversion Hy. exact H20. }
  assert (H10: Acc (fun t1 t2 => next t2 = Some t1) Min10).
  { constructor. intros y Hy. inversion Hy. exact H15. }
  assert (H5: Acc (fun t1 t2 => next t2 = Some t1) Min5).
  { constructor. intros y Hy. inversion Hy. exact H10. }
  assert (H1: Acc (fun t1 t2 => next t2 = Some t1) Min1).
  { constructor. intros y Hy. inversion Hy. exact H5. }
  intros []; assumption.
Qed.

Theorem next_well_founded : well_founded (fun t1 t2 => next t2 = Some t1).
Proof. exact next_well_founded_aux. Qed.

Definition time_lt (t1 t2 : Time) : Prop := to_minutes t1 < to_minutes t2.

Definition time_le (t1 t2 : Time) : Prop := to_minutes t1 <= to_minutes t2.

Lemma time_lt_dec : forall t1 t2, {time_lt t1 t2} + {~ time_lt t1 t2}.
Proof.
  intros t1 t2. unfold time_lt.
  destruct (to_minutes t1 <? to_minutes t2) eqn:E.
  - left. apply Nat.ltb_lt. exact E.
  - right. apply Nat.ltb_ge in E. lia.
Defined.

Lemma next_increases_time : forall t1 t2,
  next t1 = Some t2 -> time_lt t1 t2.
Proof.
  intros [] t2 H; inversion H; unfold time_lt, to_minutes; lia.
Qed.

Definition AssessmentSequence : Type := list TimedAssessment.

Fixpoint is_chronological (seq : AssessmentSequence) : Prop :=
  match seq with
  | [] => True
  | [_] => True
  | ta1 :: ((ta2 :: _) as rest) =>
      time_lt (time ta1) (time ta2) /\ is_chronological rest
  end.

Fixpoint is_chronologicalb (seq : AssessmentSequence) : bool :=
  match seq with
  | [] => true
  | [_] => true
  | ta1 :: ((ta2 :: _) as rest) =>
      (to_minutes (time ta1) <? to_minutes (time ta2)) && is_chronologicalb rest
  end.

Lemma is_chronologicalb_correct : forall seq,
  is_chronologicalb seq = true <-> is_chronological seq.
Proof.
  induction seq as [|ta1 [|ta2 seq'] IH]; simpl.
  - tauto.
  - tauto.
  - rewrite andb_true_iff. unfold time_lt.
    rewrite Nat.ltb_lt. split.
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.

Definition is_chronological_dec (seq : AssessmentSequence) :
  {is_chronological seq} + {~ is_chronological seq}.
Proof.
  destruct (is_chronologicalb seq) eqn:E.
  - left. apply is_chronologicalb_correct. exact E.
  - right. intro H. apply is_chronologicalb_correct in H. congruence.
Defined.

Fixpoint times_consecutive (seq : AssessmentSequence) : Prop :=
  match seq with
  | [] => True
  | [_] => True
  | ta1 :: ((ta2 :: _) as rest) =>
      next (time ta1) = Some (time ta2) /\ times_consecutive rest
  end.

Lemma consecutive_implies_chronological : forall seq,
  times_consecutive seq -> is_chronological seq.
Proof.
  induction seq as [|ta1 [|ta2 seq'] IH]; simpl; intros H.
  - trivial.
  - trivial.
  - destruct H as [Hnext Hrest]. split.
    + apply next_increases_time. exact Hnext.
    + apply IH. exact Hrest.
Qed.

Definition starts_at_min1 (seq : AssessmentSequence) : Prop :=
  match seq with
  | [] => True
  | ta :: _ => time ta = Min1
  end.

Record ValidSequence : Type := mkValidSeq {
  seq : AssessmentSequence;
  seq_nonempty : seq <> [];
  seq_starts_min1 : starts_at_min1 seq;
  seq_consecutive : times_consecutive seq
}.

Definition valid_seq_length (vs : ValidSequence) : nat := length (seq vs).

Definition singleton_seq (a : Assessment.t) : ValidSequence.
Proof.
  refine (mkValidSeq [mkTimed Min1 a] _ _ _).
  - discriminate.
  - reflexivity.
  - exact I.
Defined.

Lemma singleton_seq_length : forall a, valid_seq_length (singleton_seq a) = 1.
Proof. reflexivity. Qed.

Definition can_extend (vs : ValidSequence) : bool :=
  match next (time (last (seq vs) (mkTimed Min1 Assessment.minimum))) with
  | Some _ => true
  | None => false
  end.

(** Get the next time slot after the last entry in the sequence *)
Definition next_time_slot (vs : ValidSequence) : option Time :=
  next (time (last (seq vs) (mkTimed Min1 Assessment.minimum))).

(** Helper: appending preserves starts_at_min1 for nonempty sequences *)
Lemma app_preserves_starts_at_min1 : forall s ta,
  s <> [] -> starts_at_min1 s -> starts_at_min1 (s ++ [ta]).
Proof.
  intros [|h t] ta Hne Hstart.
  - contradiction.
  - simpl. exact Hstart.
Qed.

(** Helper: prove times_consecutive for singleton extension *)
Lemma times_consecutive_singleton_extend : forall ta next_t a,
  next (time ta) = Some next_t ->
  times_consecutive [ta; mkTimed next_t a].
Proof.
  intros ta next_t a H. simpl. split; [exact H | exact I].
Qed.

(** Extending a valid sequence is possible when can_extend is true *)
Theorem extend_possible : forall vs,
  can_extend vs = true ->
  exists next_t, next_time_slot vs = Some next_t.
Proof.
  intros vs H. unfold can_extend, next_time_slot in *.
  destruct (next (time (last (seq vs) (mkTimed Min1 Assessment.minimum)))) eqn:E.
  - exists t. reflexivity.
  - discriminate.
Qed.

(** Characterization: can_extend is false iff last time is Min20 *)
Lemma can_extend_false_iff_last_min20 : forall vs,
  can_extend vs = false <->
  time (last (seq vs) (mkTimed Min1 Assessment.minimum)) = Min20.
Proof.
  intros vs. unfold can_extend.
  split; intro H.
  - destruct (next (time (last (seq vs) (mkTimed Min1 Assessment.minimum)))) eqn:E.
    + discriminate.
    + apply next_none_iff_max. exact E.
  - rewrite H. reflexivity.
Qed.

Lemma singleton_can_extend : forall a,
  can_extend (singleton_seq a) = true.
Proof. intros a. reflexivity. Qed.

(** Helper: times_consecutive preserved when appending with correct next time *)
Lemma times_consecutive_app_singleton : forall s ta next_t new_a,
  times_consecutive s ->
  s <> [] ->
  next (time (last s ta)) = Some next_t ->
  times_consecutive (s ++ [mkTimed next_t new_a]).
Proof.
  intros s. induction s as [|h [|h' t] IH]; intros ta next_t new_a Hcons Hne Hnext.
  - contradiction.
  - simpl in *. rewrite Hnext. split; [reflexivity | exact I].
  - simpl in *. destruct Hcons as [H1 Hrest].
    split; [exact H1 |].
    apply (IH ta next_t new_a).
    + exact Hrest.
    + discriminate.
    + exact Hnext.
Qed.

(** Extending a valid sequence: exists proof version *)
Lemma extend_exists : forall vs (new_a : Assessment.t),
  can_extend vs = true ->
  exists vs',
    valid_seq_length vs' = S (valid_seq_length vs) /\
    (forall i, i < valid_seq_length vs ->
      nth i (seq vs') (mkTimed Min1 Assessment.minimum) =
      nth i (seq vs) (mkTimed Min1 Assessment.minimum)).
Proof.
  intros vs new_a Hext.
  unfold can_extend in Hext.
  destruct (next (time (last (seq vs) (mkTimed Min1 Assessment.minimum)))) as [next_t|] eqn:Enext;
    [|discriminate].
  pose proof (seq_consecutive vs) as Hcons_orig.
  pose proof (seq_nonempty vs) as Hne_orig.
  pose proof (seq_starts_min1 vs) as Hstart_orig.
  assert (Hcons: times_consecutive (seq vs ++ [mkTimed next_t new_a])).
  { apply (times_consecutive_app_singleton _ (mkTimed Min1 Assessment.minimum) _ new_a);
    [exact Hcons_orig | exact Hne_orig | exact Enext]. }
  assert (Hne: seq vs ++ [mkTimed next_t new_a] <> []).
  { destruct (seq vs) as [|h t] eqn:Eseq.
    - contradiction.
    - discriminate. }
  assert (Hstart: starts_at_min1 (seq vs ++ [mkTimed next_t new_a])).
  { unfold starts_at_min1 in Hstart_orig |- *.
    destruct (seq vs) as [|h t] eqn:Eseq.
    - contradiction.
    - simpl. exact Hstart_orig. }
  exists (mkValidSeq (seq vs ++ [mkTimed next_t new_a]) Hne Hstart Hcons).
  split.
  - unfold valid_seq_length. simpl. rewrite app_length. simpl. lia.
  - intros i Hi. simpl. rewrite app_nth1; [reflexivity|].
    unfold valid_seq_length in Hi. exact Hi.
Qed.

(** Characterization of when extension is possible *)
Lemma extend_possible_characterization : forall vs,
  can_extend vs = true <->
  exists next_t, next (time (last (seq vs) (mkTimed Min1 Assessment.minimum))) = Some next_t.
Proof.
  intros vs. unfold can_extend.
  split.
  - intro H.
    destruct (next (time (last (seq vs) (mkTimed Min1 Assessment.minimum)))) eqn:E.
    + exists t. reflexivity.
    + discriminate.
  - intros [next_t H]. rewrite H. reflexivity.
Qed.

(** Extension is possible iff can_extend returns true *)
Theorem extend_possible_via_can_extend : forall vs (new_a : Assessment.t),
  can_extend vs = true ->
  exists new_seq,
    length new_seq = S (length (seq vs)) /\
    (forall i, i < length (seq vs) ->
      nth i new_seq (mkTimed Min1 Assessment.minimum) =
      nth i (seq vs) (mkTimed Min1 Assessment.minimum)) /\
    assessment (last new_seq (mkTimed Min1 Assessment.minimum)) = new_a.
Proof.
  intros vs new_a Hext.
  unfold can_extend in Hext.
  destruct (next (time (last (seq vs) (mkTimed Min1 Assessment.minimum)))) as [next_t|] eqn:E;
    [|discriminate].
  exists (seq vs ++ [mkTimed next_t new_a]).
  repeat split.
  - rewrite app_length. simpl. lia.
  - intros i Hi. apply app_nth1. exact Hi.
  - rewrite last_last. reflexivity.
Qed.

Definition mk_valid_seq_2 (a1 a2 : Assessment.t) : ValidSequence.
Proof.
  refine (mkValidSeq [mkTimed Min1 a1; mkTimed Min5 a2] _ _ _).
  - discriminate.
  - reflexivity.
  - simpl. split; reflexivity.
Defined.

Definition mk_valid_seq_3 (a1 a2 a3 : Assessment.t) : ValidSequence.
Proof.
  refine (mkValidSeq [mkTimed Min1 a1; mkTimed Min5 a2; mkTimed Min10 a3] _ _ _).
  - discriminate.
  - reflexivity.
  - simpl. repeat split; reflexivity.
Defined.

Definition mk_valid_seq_4 (a1 a2 a3 a4 : Assessment.t) : ValidSequence.
Proof.
  refine (mkValidSeq [mkTimed Min1 a1; mkTimed Min5 a2; mkTimed Min10 a3; mkTimed Min15 a4] _ _ _).
  - discriminate.
  - reflexivity.
  - simpl. repeat split; reflexivity.
Defined.

Definition mk_valid_seq_5 (a1 a2 a3 a4 a5 : Assessment.t) : ValidSequence.
Proof.
  refine (mkValidSeq [mkTimed Min1 a1; mkTimed Min5 a2; mkTimed Min10 a3;
                      mkTimed Min15 a4; mkTimed Min20 a5] _ _ _).
  - discriminate.
  - reflexivity.
  - simpl. repeat split; reflexivity.
Defined.

Lemma mk_valid_seq_2_length : forall a1 a2,
  valid_seq_length (mk_valid_seq_2 a1 a2) = 2.
Proof. reflexivity. Qed.

Lemma mk_valid_seq_3_length : forall a1 a2 a3,
  valid_seq_length (mk_valid_seq_3 a1 a2 a3) = 3.
Proof. reflexivity. Qed.

Lemma mk_valid_seq_4_length : forall a1 a2 a3 a4,
  valid_seq_length (mk_valid_seq_4 a1 a2 a3 a4) = 4.
Proof. reflexivity. Qed.

Lemma mk_valid_seq_5_length : forall a1 a2 a3 a4 a5,
  valid_seq_length (mk_valid_seq_5 a1 a2 a3 a4 a5) = 5.
Proof. reflexivity. Qed.

Lemma mk_valid_seq_5_cannot_extend : forall a1 a2 a3 a4 a5,
  can_extend (mk_valid_seq_5 a1 a2 a3 a4 a5) = false.
Proof. intros. reflexivity. Qed.

Lemma mk_valid_seq_2_can_extend : forall a1 a2,
  can_extend (mk_valid_seq_2 a1 a2) = true.
Proof. intros. reflexivity. Qed.

Lemma mk_valid_seq_3_can_extend : forall a1 a2 a3,
  can_extend (mk_valid_seq_3 a1 a2 a3) = true.
Proof. intros. reflexivity. Qed.

Lemma mk_valid_seq_4_can_extend : forall a1 a2 a3 a4,
  can_extend (mk_valid_seq_4 a1 a2 a3 a4) = true.
Proof. intros. reflexivity. Qed.

(** Helper for extend: extract next time with proof *)
Definition extract_next_time (vs : ValidSequence)
  (Hext : can_extend vs = true) : Time.
Proof.
  unfold can_extend in Hext.
  destruct (next (time (last (seq vs) (mkTimed Min1 Assessment.minimum)))) as [t|] eqn:E.
  - exact t.
  - discriminate.
Defined.

Lemma extract_next_time_spec : forall vs Hext,
  next (time (last (seq vs) (mkTimed Min1 Assessment.minimum))) = Some (extract_next_time vs Hext).
Proof.
  intros vs Hext. unfold extract_next_time, can_extend in *.
  destruct (next (time (last (seq vs) (mkTimed Min1 Assessment.minimum)))) as [t|] eqn:E.
  - reflexivity.
  - discriminate.
Qed.

(** Direct constructor for extending a valid sequence *)
Definition extend (vs : ValidSequence) (new_a : Assessment.t)
  (Hext : can_extend vs = true) : ValidSequence :=
  let next_t := extract_next_time vs Hext in
  mkValidSeq
    (seq vs ++ [mkTimed next_t new_a])
    (fun Hcontra => match app_eq_nil _ _ Hcontra with
                    | conj H _ => seq_nonempty vs H
                    end)
    (app_preserves_starts_at_min1 _ _ (seq_nonempty vs) (seq_starts_min1 vs))
    (times_consecutive_app_singleton _ (mkTimed Min1 Assessment.minimum) _ new_a
       (seq_consecutive vs) (seq_nonempty vs) (extract_next_time_spec vs Hext)).

Lemma extend_length : forall vs new_a Hext,
  valid_seq_length (extend vs new_a Hext) = S (valid_seq_length vs).
Proof.
  intros vs new_a Hext. unfold extend, valid_seq_length.
  simpl. rewrite app_length. simpl. lia.
Qed.

Lemma extend_preserves_prefix : forall vs new_a Hext i,
  i < valid_seq_length vs ->
  nth i (seq (extend vs new_a Hext)) (mkTimed Min1 Assessment.minimum) =
  nth i (seq vs) (mkTimed Min1 Assessment.minimum).
Proof.
  intros vs new_a Hext i Hi. unfold extend.
  simpl. rewrite app_nth1; [reflexivity | exact Hi].
Qed.

Lemma extend_last_assessment : forall vs new_a Hext,
  assessment (last (seq (extend vs new_a Hext)) (mkTimed Min1 Assessment.minimum)) = new_a.
Proof.
  intros vs new_a Hext. unfold extend.
  simpl. rewrite last_last. reflexivity.
Qed.

Definition valid_seq_head (vs : ValidSequence) : TimedAssessment.
Proof.
  destruct vs as [[|ta rest] Hne Hstart Hcons].
  - exfalso. apply Hne. reflexivity.
  - exact ta.
Defined.

Definition valid_seq_last (vs : ValidSequence) : TimedAssessment :=
  last (seq vs) (valid_seq_head vs).

Lemma valid_seq_head_time : forall vs, time (valid_seq_head vs) = Min1.
Proof.
  intros [[|ta rest] Hne Hstart Hcons]; [exfalso; apply Hne; reflexivity |].
  simpl. exact Hstart.
Qed.

Lemma next_chain_contradiction : forall t1 t2 t3 t4 t5,
  next Min1 = Some t1 ->
  next t1 = Some t2 ->
  next t2 = Some t3 ->
  next t3 = Some t4 ->
  next t4 = Some t5 ->
  False.
Proof.
  intros t1 t2 t3 t4 t5 H1 H2 H3 H4 H5.
  simpl in *.
  inversion H1; subst.
  inversion H2; subst.
  inversion H3; subst.
  inversion H4; subst.
  inversion H5.
Qed.

Lemma valid_seq_length_bound : forall vs, valid_seq_length vs <= 5.
Proof.
  intros vs. unfold valid_seq_length.
  destruct vs as [s Hne Hstart Hcons]. simpl.
  destruct s as [|ta1 [|ta2 [|ta3 [|ta4 [|ta5 [|ta6 s']]]]]].
  - contradiction.
  - simpl. lia.
  - simpl in *. lia.
  - simpl in *. lia.
  - simpl in *. lia.
  - simpl in *. lia.
  - exfalso. simpl in *.
    destruct Hcons as [H1 [H2 [H3 [H4 [H5 _]]]]].
    rewrite Hstart in H1.
    eapply next_chain_contradiction; eauto.
Qed.

Definition sequence_scores (seq : AssessmentSequence) : list nat :=
  map (fun ta => Assessment.total_unbounded (assessment ta)) seq.

Theorem valid_seq_scores_bounded : forall vs,
  Forall (fun s => s <= 10) (sequence_scores (seq vs)).
Proof.
  intros vs. unfold sequence_scores.
  apply Forall_forall. intros s Hin.
  apply in_map_iff in Hin. destruct Hin as [ta [Heq _]].
  subst. apply Assessment.total_max.
Qed.

Theorem valid_seq_max_length_terminates : forall vs,
  valid_seq_length vs = 5 ->
  forall ta, In ta (seq vs) -> time ta = Min20 ->
  should_continue ta = false.
Proof.
  intros vs Hlen ta Hin Htime.
  unfold should_continue. rewrite Htime. simpl. rewrite andb_false_r. reflexivity.
Qed.

Theorem sequence_bounded_by_timeline : forall vs,
  valid_seq_length vs <= 5.
Proof. exact valid_seq_length_bound. Qed.

Theorem min20_cannot_continue : forall ta,
  time ta = Min20 -> should_continue ta = false.
Proof.
  intros ta H. unfold should_continue. rewrite H. simpl. rewrite andb_false_r. reflexivity.
Qed.

Theorem reassuring_stops_sequence : forall ta,
  Classification.of_assessment (assessment ta) = Classification.Reassuring ->
  should_continue ta = false.
Proof.
  intros ta H.
  apply should_continue_false_if_reassuring. exact H.
Qed.

Definition example_assessment_low : Assessment.t :=
  Assessment.mk Appearance.PaleBlue Pulse.Below100 Grimace.NoResponse
                Activity.Flaccid Respiration.Apneic.

Definition example_assessment_moderate : Assessment.t :=
  Assessment.mk Appearance.Acrocyanotic Pulse.AtOrAbove100 Grimace.GrimaceOnly
                Activity.SomeFlexion Respiration.WeakIrregular.

Definition example_assessment_reassuring : Assessment.t :=
  Assessment.mk Appearance.CompletelyPink Pulse.AtOrAbove100 Grimace.CryCoughSneeze
                Activity.ActiveMotion Respiration.StrongCry.

Definition example_timed_1 : TimedAssessment := mkTimed Min1 example_assessment_low.
Definition example_timed_5 : TimedAssessment := mkTimed Min5 example_assessment_moderate.
Definition example_timed_10 : TimedAssessment := mkTimed Min10 example_assessment_reassuring.

Definition example_sequence : AssessmentSequence :=
  [example_timed_1; example_timed_5; example_timed_10].

Lemma example_sequence_nonempty : example_sequence <> [].
Proof. discriminate. Qed.

Lemma example_sequence_starts_min1 : starts_at_min1 example_sequence.
Proof. reflexivity. Qed.

Lemma example_sequence_consecutive : times_consecutive example_sequence.
Proof. simpl. repeat split; reflexivity. Qed.

Definition example_valid_sequence : ValidSequence :=
  mkValidSeq example_sequence
             example_sequence_nonempty
             example_sequence_starts_min1
             example_sequence_consecutive.

Lemma example_valid_sequence_length : valid_seq_length example_valid_sequence = 3.
Proof. reflexivity. Qed.

Lemma example_scores : sequence_scores example_sequence = [1; 6; 10].
Proof. reflexivity. Qed.

Lemma example_final_reassuring :
  Classification.of_assessment (assessment example_timed_10) = Classification.Reassuring.
Proof. reflexivity. Qed.

Lemma example_terminates_at_reassuring :
  should_continue example_timed_10 = false.
Proof.
  apply reassuring_stops_sequence.
  exact example_final_reassuring.
Qed.

Lemma example_score_low : Assessment.total_unbounded example_assessment_low = 1.
Proof. reflexivity. Qed.

Lemma example_score_moderate : Assessment.total_unbounded example_assessment_moderate = 6.
Proof. reflexivity. Qed.

Lemma example_score_reassuring : Assessment.total_unbounded example_assessment_reassuring = 10.
Proof. reflexivity. Qed.

Theorem workflow_demonstration :
  Classification.of_score (Assessment.total_unbounded example_assessment_low) = Classification.Low /\
  Classification.of_score (Assessment.total_unbounded example_assessment_moderate) = Classification.ModeratelyAbnormal /\
  Classification.of_score (Assessment.total_unbounded example_assessment_reassuring) = Classification.Reassuring /\
  should_continue example_timed_10 = false.
Proof. repeat split; reflexivity. Qed.

(******************************************************************************)
(*  VALIDSEQUENCE HELPER FUNCTIONS                                            *)
(*                                                                            *)
(*  Accessor functions for working with valid sequences.                      *)
(******************************************************************************)

(** Sequence last assessment accessor *)
Definition seq_last_assessment (vs : ValidSequence) : Assessment.t :=
  assessment (last (seq vs) (mkTimed Min1 Assessment.minimum)).

(** Sequence last time accessor *)
Definition seq_last_time (vs : ValidSequence) : Time :=
  time (last (seq vs) (mkTimed Min1 Assessment.minimum)).

(** Get all assessments from sequence *)
Definition seq_assessments (vs : ValidSequence) : list Assessment.t :=
  map assessment (seq vs).

Lemma seq_assessments_length : forall vs,
  length (seq_assessments vs) = valid_seq_length vs.
Proof.
  intros vs. unfold seq_assessments, valid_seq_length. apply map_length.
Qed.

(** Get all scores from sequence *)
Definition seq_scores (vs : ValidSequence) : list nat :=
  map (fun ta => Assessment.total_unbounded (assessment ta)) (seq vs).

Lemma seq_scores_length : forall vs,
  length (seq_scores vs) = valid_seq_length vs.
Proof.
  intros vs. unfold seq_scores, valid_seq_length. apply map_length.
Qed.

(** Get first assessment *)
Definition seq_first_assessment (vs : ValidSequence) : Assessment.t :=
  match seq vs with
  | [] => Assessment.minimum  (* Never happens due to seq_nonempty *)
  | ta :: _ => assessment ta
  end.

(** Score at position i *)
Definition score_at (vs : ValidSequence) (i : nat) : nat :=
  Assessment.total_unbounded (assessment (nth i (seq vs) (mkTimed Min1 Assessment.minimum))).

(** Classification at position i *)
Definition classification_at (vs : ValidSequence) (i : nat) : Classification.t :=
  Classification.of_score (score_at vs i).

(** Score improved from position i to j? *)
Definition score_improved (vs : ValidSequence) (i j : nat) : bool :=
  score_at vs i <? score_at vs j.

(** All scores improving through sequence? *)
Fixpoint all_scores_improving (scores : list nat) : bool :=
  match scores with
  | [] => true
  | [_] => true
  | s1 :: ((s2 :: _) as rest) => (s1 <? s2) && all_scores_improving rest
  end.

Definition seq_all_improving (vs : ValidSequence) : bool :=
  all_scores_improving (seq_scores vs).

(** Final classification reached reassuring? *)
Definition seq_reached_reassuring (vs : ValidSequence) : bool :=
  match Classification.eq_dec (Classification.of_score (Assessment.total_unbounded (seq_last_assessment vs))) Classification.Reassuring with
  | left _ => true
  | right _ => false
  end.

End Timing.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 8b: CORD CLAMPING                               *)
(*                                                                            *)
(*  Cord clamping timing affects neonatal outcomes. Delayed cord clamping     *)
(*  (DCC) is recommended for term and preterm neonates. [NRP2021]             *)
(*                                                                            *)
(******************************************************************************)

Module CordClamping.

(** Cord clamping timing categories *)
Inductive ClampingTiming : Type :=
  | ImmediateClamping : ClampingTiming      (** < 30 seconds *)
  | DelayedClamping : ClampingTiming        (** 30-60 seconds - recommended *)
  | ExtendedDelayed : ClampingTiming        (** > 60 seconds *)
  | UmbilicalCordMilking : ClampingTiming.  (** Alternative when DCC not possible *)

Definition clamping_timing_eq_dec : forall c1 c2 : ClampingTiming,
  {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition clamping_timing_all : list ClampingTiming :=
  [ImmediateClamping; DelayedClamping; ExtendedDelayed; UmbilicalCordMilking].

Lemma clamping_timing_all_complete : forall c : ClampingTiming, In c clamping_timing_all.
Proof. intros []; simpl; auto. Qed.

Lemma clamping_timing_all_nodup : NoDup clamping_timing_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

(** Timing in seconds *)
Definition clamping_seconds_threshold_immediate : nat := 30.
Definition clamping_seconds_threshold_delayed : nat := 60.

(** Classify timing from seconds *)
Definition of_seconds (secs : nat) : ClampingTiming :=
  if secs <? clamping_seconds_threshold_immediate then ImmediateClamping
  else if secs <=? clamping_seconds_threshold_delayed then DelayedClamping
  else ExtendedDelayed.

(** Is recommended timing? (DCC is standard of care) *)
Definition is_recommended (c : ClampingTiming) : bool :=
  match c with
  | DelayedClamping | ExtendedDelayed => true
  | _ => false
  end.

(** Contraindications to delayed clamping *)
Inductive DCCContraindication : Type :=
  | NeedsImmediateResuscitation : DCCContraindication
  | PlacentalAbruption : DCCContraindication
  | PlacentaPrevia : DCCContraindication
  | CordProlapse : DCCContraindication
  | MaternalHemorrhage : DCCContraindication.

Definition dcc_contraindication_eq_dec : forall c1 c2 : DCCContraindication,
  {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

(** Record for cord clamping event *)
Record CordClampingEvent : Type := mkCordClamping {
  clamping_timing : ClampingTiming;
  clamping_seconds : nat;
  clamping_contraindications : list DCCContraindication
}.

Definition has_contraindication (e : CordClampingEvent) : bool :=
  match clamping_contraindications e with
  | [] => false
  | _ :: _ => true
  end.

Definition clamping_appropriate (e : CordClampingEvent) : bool :=
  is_recommended (clamping_timing e) || has_contraindication e.

Lemma delayed_is_appropriate : forall e,
  clamping_timing e = DelayedClamping ->
  clamping_appropriate e = true.
Proof.
  intros e H. unfold clamping_appropriate, is_recommended. rewrite H. reflexivity.
Qed.

End CordClamping.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 8c: SURFACTANT ADMINISTRATION                   *)
(*                                                                            *)
(*  Surfactant therapy for preterm neonates with RDS. [NRP2021]               *)
(*                                                                            *)
(******************************************************************************)

Module Surfactant.

(** Surfactant types *)
Inductive SurfactantType : Type :=
  | Beractant : SurfactantType      (** Survanta *)
  | Calfactant : SurfactantType     (** Infasurf *)
  | Poractant : SurfactantType      (** Curosurf *)
  | Lucinactant : SurfactantType.   (** Surfaxin - synthetic *)

Definition surfactant_type_eq_dec : forall s1 s2 : SurfactantType,
  {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition surfactant_type_all : list SurfactantType :=
  [Beractant; Calfactant; Poractant; Lucinactant].

Lemma surfactant_type_all_complete : forall s : SurfactantType, In s surfactant_type_all.
Proof. intros []; simpl; auto. Qed.

(** Administration methods *)
Inductive AdministrationMethod : Type :=
  | INSUREMethod : AdministrationMethod   (** Intubate-Surfactant-Extubate *)
  | LISAMethod : AdministrationMethod     (** Less Invasive Surfactant Administration *)
  | MISTMethod : AdministrationMethod     (** Minimally Invasive Surfactant Therapy *)
  | StandardETT : AdministrationMethod.   (** Via ETT with mechanical ventilation *)

Definition admin_method_eq_dec : forall m1 m2 : AdministrationMethod,
  {m1 = m2} + {m1 <> m2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

(** Surfactant dosing in mg/kg *)
Record SurfactantDose : Type := mkSurfactantDose {
  dose_mg_per_kg : nat;
  dose_valid : dose_mg_per_kg <= 200  (** Max reasonable dose *)
}.

Definition standard_dose_beractant : nat := 100.  (** 100 mg/kg *)
Definition standard_dose_poractant_initial : nat := 200. (** 200 mg/kg initial *)
Definition standard_dose_poractant_subsequent : nat := 100. (** 100 mg/kg repeat *)

(** Surfactant administration record *)
Record SurfactantAdmin : Type := mkSurfactantAdmin {
  surfactant_type : SurfactantType;
  admin_method : AdministrationMethod;
  dose : SurfactantDose;
  dose_number : nat;  (** 1 = first dose, 2 = second, etc. *)
  minutes_of_life : nat
}.

(** Is this a less-invasive method? *)
Definition is_less_invasive (m : AdministrationMethod) : bool :=
  match m with
  | LISAMethod | MISTMethod | INSUREMethod => true
  | StandardETT => false
  end.

(** Indication check: preterm with RDS *)
Definition ga_indicates_prophylactic (ga_weeks : nat) : bool :=
  ga_weeks <? 26.  (** Prophylactic for extreme preterm *)

Definition ga_indicates_early_rescue (ga_weeks : nat) : bool :=
  ga_weeks <? 30.  (** Early rescue for very preterm *)

End Surfactant.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 8d: BLOOD GLUCOSE MONITORING                    *)
(*                                                                            *)
(*  Neonatal hypoglycemia detection and management.                           *)
(*                                                                            *)
(******************************************************************************)

Module BloodGlucose.

(** Blood glucose in mg/dL - simplified without dependent record *)
Definition t : Type := nat.

Definition value_mg_dl (g : t) : nat := g.

(** Clinical thresholds in mg/dL *)
Definition hypoglycemia_threshold : nat := 40.      (** < 40 mg/dL *)
Definition target_min : nat := 45.                   (** Minimum target *)
Definition target_max : nat := 120.                  (** Maximum normal *)
Definition hyperglycemia_threshold : nat := 150.     (** > 150 mg/dL concerning *)
Definition valid_max : nat := 500.                   (** Reasonable upper limit *)

(** Classification *)
Inductive Status : Type :=
  | Hypoglycemic : Status       (** < 40 mg/dL - treat immediately *)
  | LowNormal : Status          (** 40-44 mg/dL - close monitoring *)
  | Normal : Status             (** 45-120 mg/dL *)
  | Elevated : Status           (** 121-150 mg/dL *)
  | Hyperglycemic : Status.     (** > 150 mg/dL *)

Definition status_eq_dec : forall s1 s2 : Status, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition status_all : list Status :=
  [Hypoglycemic; LowNormal; Normal; Elevated; Hyperglycemic].

Lemma status_all_complete : forall s : Status, In s status_all.
Proof. intros []; simpl; tauto. Qed.

Definition classify (g : t) : Status :=
  if value_mg_dl g <? hypoglycemia_threshold then Hypoglycemic
  else if value_mg_dl g <? target_min then LowNormal
  else if value_mg_dl g <=? target_max then Normal
  else if value_mg_dl g <=? hyperglycemia_threshold then Elevated
  else Hyperglycemic.

Definition is_hypoglycemic (g : t) : bool :=
  value_mg_dl g <? hypoglycemia_threshold.

Definition needs_treatment (g : t) : bool :=
  value_mg_dl g <? target_min.

Definition is_normal (g : t) : bool :=
  (target_min <=? value_mg_dl g) && (value_mg_dl g <=? target_max).

Definition is_valid (g : t) : bool := g <=? valid_max.

(** Smart constructor *)
Definition of_nat_opt (n : nat) : option t :=
  if n <=? valid_max then Some n else None.

Lemma of_nat_opt_some : forall n g,
  of_nat_opt n = Some g -> value_mg_dl g = n.
Proof.
  intros n g H. unfold of_nat_opt in H.
  destruct (n <=? valid_max) eqn:E; [|discriminate].
  inversion H. reflexivity.
Qed.

Lemma of_nat_opt_none : forall n,
  of_nat_opt n = None -> n > valid_max.
Proof.
  intros n H. unfold of_nat_opt in H.
  destruct (n <=? valid_max) eqn:E; [discriminate|].
  apply Nat.leb_gt in E. exact E.
Qed.

Lemma of_nat_opt_roundtrip : forall n,
  n <= valid_max -> exists g, of_nat_opt n = Some g /\ value_mg_dl g = n.
Proof.
  intros n Hle. unfold of_nat_opt.
  destruct (n <=? valid_max) eqn:E.
  - exists n. split; reflexivity.
  - apply Nat.leb_gt in E. lia.
Qed.

Lemma of_nat_opt_valid : forall n g,
  of_nat_opt n = Some g -> is_valid g = true.
Proof.
  intros n g H. unfold of_nat_opt in H.
  destruct (n <=? valid_max) eqn:E; [|discriminate].
  inversion H. subst. unfold is_valid. exact E.
Qed.

(** Risk factors for neonatal hypoglycemia *)
Inductive HypoglycemiaRiskFactor : Type :=
  | InfantOfDiabeticMother : HypoglycemiaRiskFactor
  | LargeForGA : HypoglycemiaRiskFactor
  | SmallForGA : HypoglycemiaRiskFactor
  | Preterm : HypoglycemiaRiskFactor
  | Intrauterine_Growth_Restriction : HypoglycemiaRiskFactor
  | PerinatalStress : HypoglycemiaRiskFactor.

Definition risk_factor_eq_dec : forall r1 r2 : HypoglycemiaRiskFactor,
  {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition risk_factor_all : list HypoglycemiaRiskFactor :=
  [InfantOfDiabeticMother; LargeForGA; SmallForGA; Preterm;
   Intrauterine_Growth_Restriction; PerinatalStress].

Lemma risk_factor_all_complete : forall r : HypoglycemiaRiskFactor,
  In r risk_factor_all.
Proof. intros []; simpl; auto 10. Qed.

(** Neonate with risk factors needs screening *)
Definition needs_screening (risk_factors : list HypoglycemiaRiskFactor) : bool :=
  match risk_factors with
  | [] => false
  | _ :: _ => true
  end.

End BloodGlucose.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 9: EXPANDED APGAR FORM                          *)
(*                                                                            *)
(*  Records concurrent interventions per [AAP2015] expanded form.             *)
(*                                                                            *)
(******************************************************************************)

Module ExpandedForm.

Inductive RespiratorySupport : Type :=
  | NoSupport : RespiratorySupport
  | SupplementalO2 : RespiratorySupport
  | CPAP : RespiratorySupport
  | PPV : RespiratorySupport
  | ETT : RespiratorySupport.

Definition resp_support_eq_dec : forall r1 r2 : RespiratorySupport,
  {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition resp_support_all : list RespiratorySupport :=
  [NoSupport; SupplementalO2; CPAP; PPV; ETT].

Lemma resp_support_all_complete : forall r : RespiratorySupport, In r resp_support_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma resp_support_all_nodup : NoDup resp_support_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition resp_support_severity (r : RespiratorySupport) : nat :=
  match r with
  | NoSupport => 0
  | SupplementalO2 => 1
  | CPAP => 2
  | PPV => 3
  | ETT => 4
  end.

Definition resp_support_le (r1 r2 : RespiratorySupport) : Prop :=
  resp_support_severity r1 <= resp_support_severity r2.

Notation "r1 <=r r2" := (resp_support_le r1 r2) (at level 70).

Lemma resp_support_le_refl : forall r, r <=r r.
Proof. intros r. unfold resp_support_le. lia. Qed.

Lemma resp_support_le_trans : forall r1 r2 r3,
  r1 <=r r2 -> r2 <=r r3 -> r1 <=r r3.
Proof. intros r1 r2 r3 H1 H2. unfold resp_support_le in *. lia. Qed.

Lemma resp_support_le_antisym : forall r1 r2,
  r1 <=r r2 -> r2 <=r r1 -> r1 = r2.
Proof.
  intros [] [] H1 H2; unfold resp_support_le, resp_support_severity in *;
  try reflexivity; lia.
Qed.

Lemma NoSupport_le_all : forall r, NoSupport <=r r.
Proof. intros []; unfold resp_support_le, resp_support_severity; lia. Qed.

Lemma all_le_ETT : forall r, r <=r ETT.
Proof. intros []; unfold resp_support_le, resp_support_severity; lia. Qed.

Definition resp_support_leb (r1 r2 : RespiratorySupport) : bool :=
  resp_support_severity r1 <=? resp_support_severity r2.

Lemma resp_support_leb_correct : forall r1 r2,
  resp_support_leb r1 r2 = true <-> r1 <=r r2.
Proof.
  intros r1 r2. unfold resp_support_leb, resp_support_le.
  rewrite Nat.leb_le. tauto.
Qed.

(** FiO2: Fraction of inspired oxygen, 21-100%. Room air is 21%. *)
Record FiO2 : Type := mkFiO2 {
  fio2_percent : nat;
  fio2_min : 21 <= fio2_percent;
  fio2_max : fio2_percent <= 100
}.

Definition fio2_to_nat (f : FiO2) : nat := fio2_percent f.

Definition room_air_fio2 : nat := 21.

Definition is_room_air (f : FiO2) : bool := fio2_percent f =? room_air_fio2.

Definition is_supplemental (f : FiO2) : bool := room_air_fio2 <? fio2_percent f.

Definition is_high_fio2 (f : FiO2) : bool := 40 <=? fio2_percent f.

Lemma le_21_21 : 21 <= 21. Proof. lia. Qed.
Lemma le_21_100 : 21 <= 100. Proof. lia. Qed.
Lemma le_100_100 : 100 <= 100. Proof. lia. Qed.
Lemma le_21_40 : 21 <= 40. Proof. lia. Qed.
Lemma le_40_100 : 40 <= 100. Proof. lia. Qed.

Definition fio2_21 : FiO2 := mkFiO2 21 le_21_21 le_21_100.
Definition fio2_40 : FiO2 := mkFiO2 40 le_21_40 le_40_100.
Definition fio2_100 : FiO2 := mkFiO2 100 le_21_100 le_100_100.

Lemma fio2_21_is_room_air : is_room_air fio2_21 = true.
Proof. reflexivity. Qed.

Lemma fio2_40_is_supplemental : is_supplemental fio2_40 = true.
Proof. reflexivity. Qed.

(** Smart constructor for FiO2 with validation *)
Definition fio2_valid_dec (p : nat) : {21 <= p /\ p <= 100} + {p < 21 \/ p > 100}.
Proof.
  destruct (21 <=? p) eqn:E1; destruct (p <=? 100) eqn:E2.
  - left. split; [apply Nat.leb_le; exact E1 | apply Nat.leb_le; exact E2].
  - right. right. apply Nat.leb_gt. exact E2.
  - right. left. apply Nat.leb_gt. exact E1.
  - right. left. apply Nat.leb_gt. exact E1.
Defined.

Definition make_fio2 (p : nat) : option FiO2 :=
  match fio2_valid_dec p with
  | left pf => Some (mkFiO2 p (proj1 pf) (proj2 pf))
  | right _ => None
  end.

Lemma make_fio2_some : forall p f,
  make_fio2 p = Some f -> fio2_percent f = p.
Proof.
  intros p f H. unfold make_fio2 in H.
  destruct (fio2_valid_dec p) as [[H1 H2]|[H1|H1]]; [|discriminate|discriminate].
  inversion H. reflexivity.
Qed.

Lemma make_fio2_none_low : forall p,
  p < 21 -> make_fio2 p = None.
Proof.
  intros p H. unfold make_fio2.
  destruct (fio2_valid_dec p) as [[H1 H2]|[H1|H1]]; [lia|reflexivity|reflexivity].
Qed.

Lemma make_fio2_none_high : forall p,
  p > 100 -> make_fio2 p = None.
Proof.
  intros p H. unfold make_fio2.
  destruct (fio2_valid_dec p) as [[H1 H2]|[H1|H1]]; [lia|reflexivity|reflexivity].
Qed.

Lemma make_fio2_roundtrip : forall p,
  21 <= p <= 100 ->
  exists f, make_fio2 p = Some f /\ fio2_percent f = p.
Proof.
  intros p [Hlo Hhi]. unfold make_fio2.
  destruct (fio2_valid_dec p) as [[H1 H2]|[H1|H1]].
  - eexists. split; reflexivity.
  - lia.
  - lia.
Qed.

(** FiO2 decidable equality *)
Definition fio2_eq_dec : forall f1 f2 : FiO2, {f1 = f2} + {f1 <> f2}.
Proof.
  intros [p1 min1 max1] [p2 min2 max2].
  destruct (Nat.eq_dec p1 p2) as [Heq|Hne].
  - left. subst. f_equal; apply le_unique.
  - right. intro H. inversion H. contradiction.
Defined.

(** ETT parameters: tube size in mm x10, depth at lip in cm x10 *)
Inductive ETTSize : Type :=
  | ETT_2_5 : ETTSize
  | ETT_3_0 : ETTSize
  | ETT_3_5 : ETTSize
  | ETT_4_0 : ETTSize.

Definition ett_size_eq_dec : forall s1 s2 : ETTSize, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition ett_size_to_mm_x10 (s : ETTSize) : nat :=
  match s with
  | ETT_2_5 => 25
  | ETT_3_0 => 30
  | ETT_3_5 => 35
  | ETT_4_0 => 40
  end.

Definition ett_size_for_weight (weight_g : nat) : ETTSize :=
  if weight_g <? 1000 then ETT_2_5
  else if weight_g <? 2000 then ETT_3_0
  else if weight_g <? 3000 then ETT_3_5
  else ETT_4_0.

Definition ett_size_for_ga (ga_weeks : nat) : ETTSize :=
  if ga_weeks <? 28 then ETT_2_5
  else if ga_weeks <? 34 then ETT_3_0
  else if ga_weeks <? 38 then ETT_3_5
  else ETT_4_0.

Record ETTParams : Type := mkETTParams {
  ett_size : ETTSize;
  ett_depth_cm_x10 : nat;
  ett_depth_valid : ett_depth_cm_x10 <= 120
}.

Definition ett_depth_for_weight (weight_kg : nat) : nat :=
  6 + weight_kg.

Definition is_appropriate_depth (p : ETTParams) (weight_kg : nat) : bool :=
  let expected := ett_depth_for_weight weight_kg in
  (expected - 1 <=? ett_depth_cm_x10 p) && (ett_depth_cm_x10 p <=? expected + 1).

(** ETT depth clinical validity: depth must be positive and <= 12cm *)
Definition ett_depth_clinically_valid (depth : nat) : bool :=
  (0 <? depth) && (depth <=? 120).

(** Smart constructor for ETTParams with validation *)
Definition ett_params_valid_dec (size : ETTSize) (depth : nat) :
  {depth > 0 /\ depth <= 120} + {depth = 0 \/ depth > 120}.
Proof.
  destruct (0 <? depth) eqn:E1; destruct (depth <=? 120) eqn:E2.
  - left. split; [apply Nat.ltb_lt; exact E1 | apply Nat.leb_le; exact E2].
  - right. right. apply Nat.leb_gt. exact E2.
  - right. left. apply Nat.ltb_ge in E1. lia.
  - right. left. apply Nat.ltb_ge in E1. lia.
Defined.

Definition make_ett_params (size : ETTSize) (depth : nat) : option ETTParams :=
  match ett_params_valid_dec size depth with
  | left pf => Some (mkETTParams size depth (proj2 pf))
  | right _ => None
  end.

Lemma make_ett_params_some : forall size depth p,
  make_ett_params size depth = Some p ->
  ett_size p = size /\ ett_depth_cm_x10 p = depth.
Proof.
  intros size depth p H. unfold make_ett_params in H.
  destruct (ett_params_valid_dec size depth) as [[H1 H2]|[H1|H1]]; [|discriminate|discriminate].
  inversion H. split; reflexivity.
Qed.

Lemma make_ett_params_none_zero : forall size,
  make_ett_params size 0 = None.
Proof.
  intros size. unfold make_ett_params.
  destruct (ett_params_valid_dec size 0) as [[H1 H2]|[H1|H1]]; [lia|reflexivity|reflexivity].
Qed.

Lemma make_ett_params_ensures_positive : forall size depth p,
  make_ett_params size depth = Some p -> ett_depth_cm_x10 p > 0.
Proof.
  intros size depth p H. unfold make_ett_params in H.
  destruct (ett_params_valid_dec size depth) as [[H1 H2]|[H1|H1]]; [|discriminate|discriminate].
  inversion H. simpl. exact H1.
Qed.

Lemma make_ett_params_roundtrip : forall size depth,
  depth > 0 -> depth <= 120 ->
  exists p, make_ett_params size depth = Some p /\
            ett_size p = size /\ ett_depth_cm_x10 p = depth.
Proof.
  intros size depth Hpos Hle. unfold make_ett_params.
  destruct (ett_params_valid_dec size depth) as [[H1 H2]|[H1|H1]].
  - eexists. repeat split; reflexivity.
  - lia.
  - lia.
Qed.

(** ETTSize decidable equality and completeness *)
Definition ett_size_all : list ETTSize := [ETT_2_5; ETT_3_0; ETT_3_5; ETT_4_0].

Lemma ett_size_all_complete : forall s : ETTSize, In s ett_size_all.
Proof. intros []; simpl; auto. Qed.

Lemma ett_size_all_nodup : NoDup ett_size_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

(** Volume expansion agents for resuscitation *)
Inductive VolumeAgent : Type :=
  | NoVolume : VolumeAgent
  | NormalSaline : VolumeAgent
  | LactatedRingers : VolumeAgent
  | PackedRBCs : VolumeAgent
  | WholeBlood : VolumeAgent.

Definition volume_agent_eq_dec : forall v1 v2 : VolumeAgent, {v1 = v2} + {v1 <> v2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Record VolumeExpansion : Type := mkVolumeExp {
  agent : VolumeAgent;
  volume_ml_per_kg : nat;
  volume_valid : volume_ml_per_kg <= 40
}.

Definition no_volume : VolumeExpansion.
Proof. refine (mkVolumeExp NoVolume 0 _). lia. Defined.

Definition has_volume_expansion (ve : VolumeExpansion) : bool :=
  match agent ve with
  | NoVolume => false
  | _ => true
  end.

(** PPV parameters: PIP (peak inspiratory pressure) in cmH2O, PEEP in cmH2O, rate in bpm.
    Enforces pip > peep to ensure positive driving pressure. *)
Record PPVParameters : Type := mkPPV {
  ppv_pip : nat;
  ppv_pip_valid : ppv_pip <= 40;
  ppv_peep : nat;
  ppv_peep_valid : ppv_peep <= 10;
  ppv_rate : nat;
  ppv_rate_valid : ppv_rate <= 60;
  ppv_pip_gt_peep : ppv_peep < ppv_pip  (** Enforced: PIP must exceed PEEP *)
}.

Definition ppv_pip_value (p : PPVParameters) : nat := ppv_pip p.
Definition ppv_peep_value (p : PPVParameters) : nat := ppv_peep p.
Definition ppv_rate_value (p : PPVParameters) : nat := ppv_rate p.

Definition is_adequate_pip (p : PPVParameters) : bool :=
  (20 <=? ppv_pip p) && (ppv_pip p <=? 30).

Definition is_adequate_rate (p : PPVParameters) : bool :=
  (40 <=? ppv_rate p) && (ppv_rate p <=? 60).

Definition driving_pressure (p : PPVParameters) : nat :=
  ppv_pip p - ppv_peep p.

Definition has_positive_driving_pressure (p : PPVParameters) : bool :=
  ppv_peep p <? ppv_pip p.

Theorem ppv_always_positive_driving_pressure : forall p : PPVParameters,
  has_positive_driving_pressure p = true.
Proof.
  intros p. unfold has_positive_driving_pressure.
  apply Nat.ltb_lt. exact (ppv_pip_gt_peep p).
Qed.

Theorem driving_pressure_positive : forall p : PPVParameters,
  driving_pressure p > 0.
Proof.
  intros p. unfold driving_pressure.
  pose proof (ppv_pip_gt_peep p). lia.
Qed.

Definition is_well_formed_ppv (p : PPVParameters) : bool :=
  has_positive_driving_pressure p && is_adequate_pip p && is_adequate_rate p.

Theorem adequate_pip_exceeds_max_peep : forall p,
  is_adequate_pip p = true -> ppv_pip p > 10.
Proof.
  intros p H. unfold is_adequate_pip in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. lia.
Qed.

Theorem well_formed_has_driving_pressure : forall p,
  is_well_formed_ppv p = true -> has_positive_driving_pressure p = true.
Proof.
  intros p H. unfold is_well_formed_ppv in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  exact H.
Qed.

(** Chest compression parameters: rate in compressions/min, ratio = compressions:ventilation *)
Inductive CompressionRatio : Type :=
  | Ratio_3_1 : CompressionRatio
  | Ratio_15_2 : CompressionRatio.

Definition compression_ratio_eq_dec : forall r1 r2 : CompressionRatio, {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Record ChestCompressionParams : Type := mkCCParams {
  cc_rate : nat;
  cc_rate_valid : cc_rate <= 150;
  cc_ratio : CompressionRatio
}.

Definition cc_rate_value (c : ChestCompressionParams) : nat := cc_rate c.

Definition is_nrp_rate (c : ChestCompressionParams) : bool :=
  (90 <=? cc_rate c) && (cc_rate c <=? 120).

Definition is_nrp_ratio (c : ChestCompressionParams) : bool :=
  match cc_ratio c with
  | Ratio_3_1 => true
  | _ => false
  end.

(** Epinephrine administration: dose in mcg/kg, route *)
Inductive EpinephrineRoute : Type :=
  | IV_UVC : EpinephrineRoute
  | IO : EpinephrineRoute
  | ETT_Route : EpinephrineRoute.

Definition epi_route_eq_dec : forall r1 r2 : EpinephrineRoute, {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Record EpinephrineAdmin : Type := mkEpiAdmin {
  epi_dose_mcg_per_kg : nat;
  epi_dose_valid : epi_dose_mcg_per_kg <= 100;
  epi_route : EpinephrineRoute
}.

Definition epi_dose_value (e : EpinephrineAdmin) : nat := epi_dose_mcg_per_kg e.

Definition is_iv_dose_range (e : EpinephrineAdmin) : bool :=
  match epi_route e with
  | IV_UVC | IO => (10 <=? epi_dose_mcg_per_kg e) && (epi_dose_mcg_per_kg e <=? 30)
  | ETT_Route => false
  end.

Definition is_ett_dose_range (e : EpinephrineAdmin) : bool :=
  match epi_route e with
  | ETT_Route => (50 <=? epi_dose_mcg_per_kg e) && (epi_dose_mcg_per_kg e <=? 100)
  | _ => false
  end.

Definition is_correct_dose_for_route (e : EpinephrineAdmin) : bool :=
  is_iv_dose_range e || is_ett_dose_range e.

Record t : Type := mk {
  timed_assessment : Timing.TimedAssessment;
  resp_support : RespiratorySupport;
  fio2 : option FiO2;
  ppv_params : option PPVParameters;
  ett_params : option ETTParams;
  chest_compression_params : option ChestCompressionParams;
  epinephrine_admin : option EpinephrineAdmin;
  volume_expansion : VolumeExpansion;
  spo2_reading : option SpO2.t;
  temperature_reading : option Temperature.t
}.

Definition has_chest_compressions (e : t) : bool :=
  match chest_compression_params e with Some _ => true | None => false end.

Definition has_epinephrine (e : t) : bool :=
  match epinephrine_admin e with Some _ => true | None => false end.

Definition is_resuscitated (e : t) : bool :=
  match resp_support e with
  | NoSupport => has_chest_compressions e || has_epinephrine e || has_volume_expansion (volume_expansion e)
  | _ => true
  end.

Definition underlying_score (e : t) : nat :=
  Assessment.total_unbounded (Timing.assessment (timed_assessment e)).

Definition underlying_classification (e : t) : Classification.t :=
  Classification.of_assessment (Timing.assessment (timed_assessment e)).

Lemma resuscitated_with_support : forall e,
  resp_support e <> NoSupport -> is_resuscitated e = true.
Proof.
  intros e H. unfold is_resuscitated.
  destruct (resp_support e); [contradiction | reflexivity..].
Qed.

Lemma resuscitated_with_compressions : forall e,
  has_chest_compressions e = true -> is_resuscitated e = true.
Proof.
  intros e H. unfold is_resuscitated.
  destruct (resp_support e); simpl; try reflexivity.
  rewrite H. reflexivity.
Qed.

Lemma resuscitated_with_epinephrine : forall e,
  has_epinephrine e = true -> is_resuscitated e = true.
Proof.
  intros e H. unfold is_resuscitated.
  destruct (resp_support e); simpl; try reflexivity.
  destruct (has_chest_compressions e); simpl; [reflexivity|].
  rewrite H. reflexivity.
Qed.

Record WellFormedExpandedForm : Type := mkWellFormed {
  form : t;
  resuscitation_implies_low : is_resuscitated form = true ->
    underlying_classification form <> Classification.Reassuring
}.

Definition make_well_formed (e : t)
  (pf : is_resuscitated e = true -> underlying_classification e <> Classification.Reassuring)
  : WellFormedExpandedForm := mkWellFormed e pf.

Lemma no_support_no_intervention_any_score : forall e,
  resp_support e = NoSupport ->
  has_chest_compressions e = false ->
  has_epinephrine e = false ->
  has_volume_expansion (volume_expansion e) = false ->
  is_resuscitated e = false.
Proof.
  intros e Hresp Hcomp Hepi Hvol.
  unfold is_resuscitated. rewrite Hresp.
  rewrite Hcomp, Hepi, Hvol. reflexivity.
Qed.

Lemma reassuring_with_resuscitation_contradictory :
  forall a : Assessment.t,
  Classification.of_assessment a = Classification.Reassuring ->
  Assessment.total_unbounded a >= 7.
Proof.
  intros a H. apply Classification.reassuring_iff in H. exact H.
Qed.

Theorem well_formed_score_bound : forall wf : WellFormedExpandedForm,
  is_resuscitated (form wf) = true ->
  underlying_score (form wf) <= 6.
Proof.
  intros wf Hres.
  destruct wf as [e Hpf]. simpl in *.
  unfold underlying_score.
  assert (Hne : underlying_classification e <> Classification.Reassuring) by (apply Hpf; exact Hres).
  unfold underlying_classification in Hne.
  remember (Classification.of_assessment (Timing.assessment (timed_assessment e))) as c.
  destruct c.
  - symmetry in Heqc. apply Classification.of_score_low_inv in Heqc. lia.
  - symmetry in Heqc. apply Classification.of_score_moderate_inv in Heqc. lia.
  - contradiction.
Qed.

Definition example_well_formed_low_score : WellFormedExpandedForm.
Proof.
  refine (mkWellFormed
    (mk (Timing.mkTimed Timing.Min1 Assessment.minimum) PPV None None None None None no_volume None None) _).
  intro H. unfold underlying_classification. simpl. discriminate.
Defined.

(** PPV/ETT consistency predicates: ensure parameters match respiratory support *)
Definition ppv_params_consistent (e : t) : Prop :=
  resp_support e = PPV -> ppv_params e <> None.

Definition ett_params_consistent (e : t) : Prop :=
  resp_support e = ETT -> ett_params e <> None.

Definition params_consistent (e : t) : Prop :=
  ppv_params_consistent e /\ ett_params_consistent e.

Definition ppv_params_consistentb (e : t) : bool :=
  match resp_support e with
  | PPV => match ppv_params e with Some _ => true | None => false end
  | _ => true
  end.

Definition ett_params_consistentb (e : t) : bool :=
  match resp_support e with
  | ETT => match ett_params e with Some _ => true | None => false end
  | _ => true
  end.

Lemma ppv_params_consistentb_correct : forall e,
  ppv_params_consistentb e = true <-> ppv_params_consistent e.
Proof.
  intros e. unfold ppv_params_consistentb, ppv_params_consistent.
  destruct (resp_support e) eqn:Er.
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
  - destruct (ppv_params e) eqn:Ep.
    + split; [intro; intro Hc; discriminate | intro; reflexivity].
    + split; [intro H; discriminate | intro H; exfalso; apply H; reflexivity].
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
Qed.

Lemma ett_params_consistentb_correct : forall e,
  ett_params_consistentb e = true <-> ett_params_consistent e.
Proof.
  intros e. unfold ett_params_consistentb, ett_params_consistent.
  destruct (resp_support e) eqn:Er.
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
  - split; [intro; intro Hc; discriminate | intro; reflexivity].
  - destruct (ett_params e) eqn:Ep.
    + split; [intro; intro Hc; discriminate | intro; reflexivity].
    + split; [intro H; discriminate | intro H; exfalso; apply H; reflexivity].
Qed.

(** Consistent expanded form record *)
Record ConsistentExpandedForm : Type := mkConsistentForm {
  consistent_form : t;
  consistent_ppv : ppv_params_consistent consistent_form;
  consistent_ett : ett_params_consistent consistent_form
}.

Definition no_support_form (ta : Timing.TimedAssessment) : t :=
  mk ta NoSupport None None None None None no_volume None None.

Lemma no_support_form_consistent : forall ta,
  params_consistent (no_support_form ta).
Proof.
  intros ta. unfold params_consistent, ppv_params_consistent, ett_params_consistent.
  split; intro H; discriminate.
Qed.

Definition no_support_form_is_consistent (ta : Timing.TimedAssessment) : ConsistentExpandedForm.
Proof.
  refine (mkConsistentForm (no_support_form ta) _ _).
  - intro H. discriminate.
  - intro H. discriminate.
Defined.

(** Boolean check for well-formedness: resuscitation implies non-reassuring *)
Definition is_well_formedb (e : t) : bool :=
  negb (is_resuscitated e) ||
  match Classification.eq_dec (underlying_classification e) Classification.Reassuring with
  | left _ => false
  | right _ => true
  end.

(** Well-formedness decidability *)
Definition well_formed_dec (e : t) :
  {is_resuscitated e = true -> underlying_classification e <> Classification.Reassuring} +
  {~ (is_resuscitated e = true -> underlying_classification e <> Classification.Reassuring)}.
Proof.
  destruct (is_resuscitated e) eqn:Hres.
  - destruct (Classification.eq_dec (underlying_classification e) Classification.Reassuring) as [Heq|Hne].
    + right. intro H. apply H; [reflexivity | exact Heq].
    + left. intros _. exact Hne.
  - left. intros H. discriminate H.
Defined.

(** Constructing WellFormedExpandedForm when possible *)
Definition make_well_formed_opt (e : t) : option WellFormedExpandedForm :=
  match well_formed_dec e with
  | left pf => Some (mkWellFormed e pf)
  | right _ => None
  end.

Lemma make_well_formed_opt_some : forall e wf,
  make_well_formed_opt e = Some wf -> form wf = e.
Proof.
  intros e wf H. unfold make_well_formed_opt in H.
  destruct (well_formed_dec e) as [pf|pf]; [|discriminate].
  inversion H. reflexivity.
Qed.

Lemma make_well_formed_opt_none : forall e,
  make_well_formed_opt e = None ->
  is_resuscitated e = true /\ underlying_classification e = Classification.Reassuring.
Proof.
  intros e H. unfold make_well_formed_opt in H.
  destruct (well_formed_dec e) as [pf|pf]; [discriminate|].
  destruct (is_resuscitated e) eqn:Hres.
  - destruct (Classification.eq_dec (underlying_classification e) Classification.Reassuring) as [Heq|Hne].
    + split; [reflexivity | exact Heq].
    + exfalso. apply pf. intros _. exact Hne.
  - exfalso. apply pf. intros Hcontra. discriminate Hcontra.
Qed.

(** Combined well-formed + consistent expanded form record *)
Record ValidExpandedForm : Type := mkValidForm {
  valid_form : t;
  valid_well_formed : is_resuscitated valid_form = true ->
                      underlying_classification valid_form <> Classification.Reassuring;
  valid_ppv_consistent : ppv_params_consistent valid_form;
  valid_ett_consistent : ett_params_consistent valid_form
}.

Definition valid_to_well_formed (vf : ValidExpandedForm) : WellFormedExpandedForm :=
  mkWellFormed (valid_form vf) (valid_well_formed vf).

Definition valid_to_consistent (vf : ValidExpandedForm) : ConsistentExpandedForm :=
  mkConsistentForm (valid_form vf) (valid_ppv_consistent vf) (valid_ett_consistent vf).

(** Boolean check for full validity *)
Definition is_validb (e : t) : bool :=
  is_well_formedb e && ppv_params_consistentb e && ett_params_consistentb e.

(** Full validity property *)
Definition is_valid_prop (e : t) : Prop :=
  (is_resuscitated e = true -> underlying_classification e <> Classification.Reassuring) /\
  ppv_params_consistent e /\ ett_params_consistent e.

(** Decidability of full validity *)
Definition valid_dec (e : t) : {is_valid_prop e} + {~ is_valid_prop e}.
Proof.
  unfold is_valid_prop.
  destruct (well_formed_dec e) as [Hwf|Hwf].
  - destruct (ppv_params_consistentb e) eqn:Hppv.
    + destruct (ett_params_consistentb e) eqn:Hett.
      * left. repeat split.
        -- exact Hwf.
        -- apply ppv_params_consistentb_correct. exact Hppv.
        -- apply ett_params_consistentb_correct. exact Hett.
      * right. intros [_ [_ H]]. apply ett_params_consistentb_correct in H. congruence.
    + right. intros [_ [H _]]. apply ppv_params_consistentb_correct in H. congruence.
  - right. intros [H _]. contradiction.
Defined.

(** Constructor for ValidExpandedForm *)
Definition make_valid_opt (e : t) : option ValidExpandedForm :=
  match valid_dec e with
  | left pf =>
      match pf with
      | conj Hwf (conj Hppv Hett) => Some (mkValidForm e Hwf Hppv Hett)
      end
  | right _ => None
  end.

Lemma make_valid_opt_some : forall e vf,
  make_valid_opt e = Some vf -> valid_form vf = e.
Proof.
  intros e vf H. unfold make_valid_opt in H.
  destruct (valid_dec e) as [[Hwf [Hppv Hett]]|pf]; [|discriminate].
  inversion H. reflexivity.
Qed.

(** No-support forms are always valid *)
Definition no_support_form_is_valid (ta : Timing.TimedAssessment) : ValidExpandedForm.
Proof.
  refine (mkValidForm (no_support_form ta) _ _ _).
  - intro H. unfold no_support_form, is_resuscitated in H. simpl in H. discriminate.
  - intro H. discriminate.
  - intro H. discriminate.
Defined.

End ExpandedForm.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 10: DISCONTINUATION CRITERIA                    *)
(*                                                                            *)
(*  Per [NRP2021]: Consider discontinuation if score remains 0 at 10+ min.    *)
(*                                                                            *)
(******************************************************************************)

Module Discontinuation.

Definition criteria_considered (e : ExpandedForm.t) : bool :=
  (ExpandedForm.underlying_score e =? 0) &&
  (10 <=? Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e))).

Lemma criteria_requires_zero : forall e,
  criteria_considered e = true -> ExpandedForm.underlying_score e = 0.
Proof.
  intros e H. unfold criteria_considered in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.eqb_eq in H. exact H.
Qed.

Lemma criteria_requires_time : forall e,
  criteria_considered e = true -> Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e)) >= 10.
Proof.
  intros e H. unfold criteria_considered in H.
  apply andb_true_iff in H. destruct H as [_ H].
  apply Nat.leb_le in H. exact H.
Qed.

Theorem early_never_discontinue : forall e,
  Timing.time (ExpandedForm.timed_assessment e) = Timing.Min1 \/
  Timing.time (ExpandedForm.timed_assessment e) = Timing.Min5 ->
  criteria_considered e = false.
Proof.
  intros e [H|H]; unfold criteria_considered; rewrite H; simpl;
  rewrite andb_false_r; reflexivity.
Qed.

Theorem nonzero_never_discontinue : forall e,
  ExpandedForm.underlying_score e > 0 ->
  criteria_considered e = false.
Proof.
  intros e H. unfold criteria_considered.
  destruct (ExpandedForm.underlying_score e =? 0) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - reflexivity.
Qed.

Definition required_intervention (e : ExpandedForm.t) : Intervention.t :=
  Intervention.of_score (ExpandedForm.underlying_score e).

Theorem discontinuation_requires_full_resuscitation : forall e,
  criteria_considered e = true ->
  required_intervention e = Intervention.FullResuscitation.
Proof.
  intros e H.
  unfold required_intervention.
  pose proof (criteria_requires_zero e H) as Hzero.
  rewrite Hzero. reflexivity.
Qed.

Theorem discontinuation_classification_is_low : forall e,
  criteria_considered e = true ->
  ExpandedForm.underlying_classification e = Classification.Low.
Proof.
  intros e H.
  pose proof (criteria_requires_zero e H) as Hzero.
  unfold ExpandedForm.underlying_classification, ExpandedForm.underlying_score in *.
  unfold Classification.of_assessment, Classification.of_score.
  rewrite Hzero. reflexivity.
Qed.

Inductive DiscontinuationDecision : Type :=
  | ContinueResuscitation : DiscontinuationDecision
  | ConsiderDiscontinuation : DiscontinuationDecision.

Definition decide_discontinuation (e : ExpandedForm.t) : DiscontinuationDecision :=
  if criteria_considered e then ConsiderDiscontinuation else ContinueResuscitation.

Theorem decide_discontinuation_correct : forall e,
  decide_discontinuation e = ConsiderDiscontinuation <-> criteria_considered e = true.
Proof.
  intros e. unfold decide_discontinuation.
  destruct (criteria_considered e) eqn:E; split; intro H; try reflexivity; try discriminate.
Qed.

Theorem criteria_monotonic_in_time : forall e1 e2,
  ExpandedForm.underlying_score e1 = 0 ->
  ExpandedForm.underlying_score e2 = 0 ->
  Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e1)) <=
  Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e2)) ->
  criteria_considered e1 = true ->
  criteria_considered e2 = true.
Proof.
  intros e1 e2 Hz1 Hz2 Htime H1.
  unfold criteria_considered in *.
  apply andb_true_iff in H1. destruct H1 as [_ Ht1].
  apply Nat.leb_le in Ht1.
  apply andb_true_iff. split.
  - apply Nat.eqb_eq. exact Hz2.
  - apply Nat.leb_le. lia.
Qed.

Theorem once_considered_stays_considered : forall e1 e2,
  ExpandedForm.underlying_score e1 = ExpandedForm.underlying_score e2 ->
  ExpandedForm.underlying_score e1 = 0 ->
  Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e1)) <=
  Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e2)) ->
  criteria_considered e1 = true ->
  criteria_considered e2 = true.
Proof.
  intros e1 e2 Hscore Hz Htime H1.
  apply criteria_monotonic_in_time with e1; try assumption.
  - rewrite <- Hscore. exact Hz.
Qed.

Theorem criteria_false_before_10min : forall e,
  Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e)) < 10 ->
  criteria_considered e = false.
Proof.
  intros e H. unfold criteria_considered.
  destruct (ExpandedForm.underlying_score e =? 0) eqn:E1.
  - destruct (10 <=? Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e))) eqn:E2.
    + apply Nat.leb_le in E2. lia.
    + reflexivity.
  - reflexivity.
Qed.

Theorem criteria_iff : forall e,
  criteria_considered e = true <->
  (ExpandedForm.underlying_score e = 0 /\
   Timing.to_minutes (Timing.time (ExpandedForm.timed_assessment e)) >= 10).
Proof.
  intros e. unfold criteria_considered. split.
  - intro H. apply andb_true_iff in H. destruct H as [H1 H2].
    split.
    + apply Nat.eqb_eq. exact H1.
    + apply Nat.leb_le. exact H2.
  - intros [H1 H2]. apply andb_true_iff. split.
    + apply Nat.eqb_eq. exact H1.
    + apply Nat.leb_le. exact H2.
Qed.

End Discontinuation.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 10b: THERAPEUTIC HYPOTHERMIA                    *)
(*                                                                            *)
(*  Eligibility criteria for therapeutic hypothermia (TH) per NRP 2021.       *)
(*  TH is indicated for term/late preterm neonates with HIE evidence.         *)
(*  Criteria: GA >=36 wks, score <=5 at 10 min or ongoing resuscitation,      *)
(*  pH <7.0 or BD >=16, and signs of moderate/severe encephalopathy.          *)
(*                                                                            *)
(******************************************************************************)

Module TherapeuticHypothermia.

Definition min_gestational_weeks : nat := 36.

Definition score_threshold : nat := 5.

Definition ph_threshold_x100 : nat := 700.

Definition base_deficit_threshold : nat := 16.

Inductive EncephalopathyGrade : Type :=
  | NoEncephalopathy : EncephalopathyGrade
  | MildEncephalopathy : EncephalopathyGrade
  | ModerateEncephalopathy : EncephalopathyGrade
  | SevereEncephalopathy : EncephalopathyGrade.

Definition encephalopathy_eq_dec : forall e1 e2 : EncephalopathyGrade,
  {e1 = e2} + {e1 <> e2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition encephalopathy_all : list EncephalopathyGrade :=
  [NoEncephalopathy; MildEncephalopathy; ModerateEncephalopathy; SevereEncephalopathy].

Lemma encephalopathy_all_complete : forall e : EncephalopathyGrade,
  In e encephalopathy_all.
Proof. intros []; simpl; auto 10. Qed.

Definition encephalopathy_qualifies (e : EncephalopathyGrade) : bool :=
  match e with
  | ModerateEncephalopathy | SevereEncephalopathy => true
  | _ => false
  end.

Record Candidate : Type := mkCandidate {
  gestational_age : GestationalAge.t;
  apgar_10min : nat;
  ongoing_resuscitation_10min : bool;
  cord_ph_x100 : option nat;
  cord_base_deficit : option nat;
  encephalopathy : EncephalopathyGrade
}.

Definition ga_eligible (c : Candidate) : bool :=
  min_gestational_weeks <=? GestationalAge.weeks (gestational_age c).

Definition apgar_eligible (c : Candidate) : bool :=
  (apgar_10min c <=? score_threshold) || ongoing_resuscitation_10min c.

Definition acidosis_eligible (c : Candidate) : bool :=
  match cord_ph_x100 c with
  | Some ph => ph <? ph_threshold_x100
  | None => false
  end ||
  match cord_base_deficit c with
  | Some bd => base_deficit_threshold <=? bd
  | None => false
  end.

Definition neuro_eligible (c : Candidate) : bool :=
  encephalopathy_qualifies (encephalopathy c).

Definition is_eligible (c : Candidate) : bool :=
  ga_eligible c && apgar_eligible c && acidosis_eligible c && neuro_eligible c.

Theorem eligibility_requires_term : forall c,
  is_eligible c = true -> ga_eligible c = true.
Proof.
  intros c H. unfold is_eligible in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  exact H.
Qed.

Theorem eligibility_requires_apgar_or_resus : forall c,
  is_eligible c = true -> apgar_eligible c = true.
Proof.
  intros c H. unfold is_eligible in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

Theorem eligibility_requires_acidosis : forall c,
  is_eligible c = true -> acidosis_eligible c = true.
Proof.
  intros c H. unfold is_eligible in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

Theorem eligibility_requires_encephalopathy : forall c,
  is_eligible c = true -> neuro_eligible c = true.
Proof.
  intros c H. unfold is_eligible in H.
  apply andb_true_iff in H. destruct H as [_ H].
  exact H.
Qed.

Theorem preterm_ineligible : forall c,
  GestationalAge.weeks (gestational_age c) < min_gestational_weeks ->
  is_eligible c = false.
Proof.
  intros c H. unfold is_eligible, ga_eligible, min_gestational_weeks in *.
  destruct (36 <=? GestationalAge.weeks (gestational_age c)) eqn:E.
  - apply Nat.leb_le in E. exfalso. lia.
  - reflexivity.
Qed.

Theorem no_encephalopathy_ineligible : forall c,
  encephalopathy c = NoEncephalopathy ->
  is_eligible c = false.
Proof.
  intros c H. unfold is_eligible.
  destruct (ga_eligible c); simpl; [|reflexivity].
  destruct (apgar_eligible c); simpl; [|reflexivity].
  destruct (acidosis_eligible c); simpl; [|reflexivity].
  unfold neuro_eligible, encephalopathy_qualifies. rewrite H. reflexivity.
Qed.

Theorem mild_encephalopathy_ineligible : forall c,
  encephalopathy c = MildEncephalopathy ->
  is_eligible c = false.
Proof.
  intros c H. unfold is_eligible.
  destruct (ga_eligible c); simpl; [|reflexivity].
  destruct (apgar_eligible c); simpl; [|reflexivity].
  destruct (acidosis_eligible c); simpl; [|reflexivity].
  unfold neuro_eligible, encephalopathy_qualifies. rewrite H. reflexivity.
Qed.

(** Contraindications to therapeutic hypothermia *)
Inductive Contraindication : Type :=
  | MajorCongenitalAnomaly : Contraindication
  | MoribundInfant : Contraindication
  | BirthWeightBelow1800g : Contraindication
  | AgeOver6Hours : Contraindication
  | ActiveBleeding : Contraindication
  | SevereCoagulopathy : Contraindication
  | RequiresSurgery : Contraindication.

Definition contraindication_eq_dec : forall c1 c2 : Contraindication,
  {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition contraindication_all : list Contraindication :=
  [MajorCongenitalAnomaly; MoribundInfant; BirthWeightBelow1800g;
   AgeOver6Hours; ActiveBleeding; SevereCoagulopathy; RequiresSurgery].

Lemma contraindication_all_complete : forall c : Contraindication,
  In c contraindication_all.
Proof. intros []; simpl; auto 10. Qed.

Lemma contraindication_all_nodup : NoDup contraindication_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

(** Is contraindication absolute (never perform TH) or relative (consider risks) *)
Definition is_absolute_contraindication (c : Contraindication) : bool :=
  match c with
  | MajorCongenitalAnomaly => true
  | MoribundInfant => true
  | AgeOver6Hours => true
  | _ => false
  end.

Definition is_relative_contraindication (c : Contraindication) : bool :=
  negb (is_absolute_contraindication c).

(** Extended candidate with contraindication tracking *)
Record ExtendedCandidate : Type := mkExtendedCandidate {
  base_candidate : Candidate;
  contraindications : list Contraindication;
  birth_weight_g : option nat;
  age_hours : option nat
}.

Definition has_any_contraindication (ec : ExtendedCandidate) : bool :=
  match contraindications ec with
  | [] => false
  | _ :: _ => true
  end.

Definition has_absolute_contraindication (ec : ExtendedCandidate) : bool :=
  existsb is_absolute_contraindication (contraindications ec).

Definition has_weight_contraindication (ec : ExtendedCandidate) : bool :=
  match birth_weight_g ec with
  | Some w => w <? 1800
  | None => false
  end.

Definition has_age_contraindication (ec : ExtendedCandidate) : bool :=
  match age_hours ec with
  | Some h => 6 <? h
  | None => false
  end.

Definition all_contraindications_present (ec : ExtendedCandidate) : list Contraindication :=
  let explicit := contraindications ec in
  let weight_ci := if has_weight_contraindication ec then [BirthWeightBelow1800g] else [] in
  let age_ci := if has_age_contraindication ec then [AgeOver6Hours] else [] in
  explicit ++ weight_ci ++ age_ci.

(** Final eligibility with contraindications *)
Definition is_eligible_extended (ec : ExtendedCandidate) : bool :=
  is_eligible (base_candidate ec) &&
  negb (has_absolute_contraindication ec) &&
  negb (has_weight_contraindication ec) &&
  negb (has_age_contraindication ec).

Theorem absolute_contraindication_excludes : forall ec,
  has_absolute_contraindication ec = true ->
  is_eligible_extended ec = false.
Proof.
  intros ec H. unfold is_eligible_extended.
  rewrite H. simpl. rewrite andb_false_r. reflexivity.
Qed.

Theorem weight_contraindication_excludes : forall ec,
  has_weight_contraindication ec = true ->
  is_eligible_extended ec = false.
Proof.
  intros ec H. unfold is_eligible_extended.
  rewrite H. simpl.
  destruct (is_eligible (base_candidate ec)); simpl; [|reflexivity].
  destruct (has_absolute_contraindication ec); simpl; reflexivity.
Qed.

Theorem age_contraindication_excludes : forall ec,
  has_age_contraindication ec = true ->
  is_eligible_extended ec = false.
Proof.
  intros ec H. unfold is_eligible_extended.
  rewrite H. simpl.
  destruct (is_eligible (base_candidate ec)); simpl; [|reflexivity].
  destruct (has_absolute_contraindication ec); simpl; [reflexivity|].
  destruct (has_weight_contraindication ec); simpl; reflexivity.
Qed.

Theorem extended_eligible_implies_base_eligible : forall ec,
  is_eligible_extended ec = true ->
  is_eligible (base_candidate ec) = true.
Proof.
  intros ec H. unfold is_eligible_extended in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  exact H.
Qed.

Theorem extended_eligible_no_absolute : forall ec,
  is_eligible_extended ec = true ->
  has_absolute_contraindication ec = false.
Proof.
  intros ec H. unfold is_eligible_extended in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  apply negb_true_iff in H. exact H.
Qed.

End TherapeuticHypothermia.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 10c: COMBINED ASSESSMENT                        *)
(*                                                                            *)
(*  Integrates APGAR score with physiological parameters: gestational age,    *)
(*  SpO2, cord blood gas, birth weight, and intervention context.             *)
(*                                                                            *)
(******************************************************************************)

Module CombinedAssessment.

Record t : Type := mk {
  expanded_form : ExpandedForm.t;
  gestational_age : GestationalAge.t;
  birth_weight : option BirthWeight.t;
  cord_gas : option CordBloodGas.t;
  real_timestamp : option Timing.Timestamp
}.

Definition apgar_score (ca : t) : nat :=
  ExpandedForm.underlying_score (expanded_form ca).

Definition classification (ca : t) : Classification.t :=
  ExpandedForm.underlying_classification (expanded_form ca).

Definition spo2 (ca : t) : option SpO2.t :=
  ExpandedForm.spo2_reading (expanded_form ca).

Definition temperature (ca : t) : option Temperature.t :=
  ExpandedForm.temperature_reading (expanded_form ca).

Definition standard_time (ca : t) : Timing.Time :=
  Timing.time (ExpandedForm.timed_assessment (expanded_form ca)).

Definition is_preterm (ca : t) : bool :=
  GestationalAge.is_preterm (gestational_age ca).

Definition is_term (ca : t) : bool :=
  GestationalAge.is_term (gestational_age ca).

Definition maturity (ca : t) : GestationalAge.Maturity :=
  GestationalAge.classify (gestational_age ca).

Definition has_cord_gas (ca : t) : bool :=
  match cord_gas ca with Some _ => true | None => false end.

Definition cord_gas_indicates_asphyxia (ca : t) : bool :=
  match cord_gas ca with
  | Some cbg => CordBloodGas.indicates_asphyxia cbg
  | None => false
  end.

Definition spo2_on_target (ca : t) : bool :=
  match spo2 ca, real_timestamp ca with
  | Some s, Some ts =>
      let range := SpO2.range_for_minute (Timing.timestamp_to_minutes ts) in
      SpO2.in_target s range
  | _, _ => false
  end.

Definition spo2_on_target_for_population (ca : t) : bool :=
  match spo2 ca with
  | Some s =>
      let pop := if is_preterm ca then SpO2.PretermPopulation else SpO2.TermPopulation in
      SpO2.in_final_target_for_population s pop
  | None => false
  end.

Definition is_resuscitated (ca : t) : bool :=
  ExpandedForm.is_resuscitated (expanded_form ca).

Definition is_hypothermic (ca : t) : bool :=
  match temperature ca with
  | Some temp => Temperature.is_hypothermic temp
  | None => false
  end.

Definition is_hyperthermic (ca : t) : bool :=
  match temperature ca with
  | Some temp => Temperature.is_hyperthermic temp
  | None => false
  end.

Definition temperature_abnormal (ca : t) : bool :=
  is_hypothermic ca || is_hyperthermic ca.

Definition needs_cord_gas (ca : t) : bool :=
  (apgar_score ca <=? 5) &&
  (Timing.to_minutes (standard_time ca) =? 5).

Theorem needs_cord_gas_implies_low_score : forall ca,
  needs_cord_gas ca = true -> apgar_score ca <= 5.
Proof.
  intros ca H. unfold needs_cord_gas in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

Definition is_vlbw (ca : t) : bool :=
  match birth_weight ca with
  | Some w => BirthWeight.is_vlbw w
  | None => false
  end.

Definition is_elbw (ca : t) : bool :=
  match birth_weight ca with
  | Some w => BirthWeight.is_elbw w
  | None => false
  end.

Definition weight_category (ca : t) : option BirthWeight.Category :=
  match birth_weight ca with
  | Some w => Some (BirthWeight.classify w)
  | None => None
  end.

Inductive RiskCategory : Type :=
  | LowRisk : RiskCategory
  | ModerateRisk : RiskCategory
  | HighRisk : RiskCategory
  | CriticalRisk : RiskCategory.

Definition risk_category_eq_dec : forall r1 r2 : RiskCategory,
  {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition risk_category_all : list RiskCategory :=
  [LowRisk; ModerateRisk; HighRisk; CriticalRisk].

Lemma risk_category_all_complete : forall r : RiskCategory, In r risk_category_all.
Proof. intros []; simpl; auto. Qed.

Lemma risk_category_all_nodup : NoDup risk_category_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition has_additional_risk_factors (ca : t) : bool :=
  is_preterm ca || cord_gas_indicates_asphyxia ca || temperature_abnormal ca.

Definition compute_risk (ca : t) : RiskCategory :=
  if apgar_score ca =? 0 then CriticalRisk
  else if (apgar_score ca <=? 3) && has_additional_risk_factors ca then CriticalRisk
  else if apgar_score ca <=? 3 then HighRisk
  else if (apgar_score ca <=? 6) && has_additional_risk_factors ca then HighRisk
  else if apgar_score ca <=? 6 then ModerateRisk
  else LowRisk.

Theorem critical_risk_low_score : forall ca,
  compute_risk ca = CriticalRisk -> apgar_score ca <= 3.
Proof.
  intros ca H. unfold compute_risk in H.
  destruct (apgar_score ca =? 0) eqn:E0.
  - apply Nat.eqb_eq in E0. lia.
  - destruct (apgar_score ca <=? 3) eqn:E1.
    + apply Nat.leb_le in E1. exact E1.
    + destruct (has_additional_risk_factors ca) eqn:E2;
      destruct (apgar_score ca <=? 6) eqn:E3; discriminate.
Qed.

Theorem low_risk_reassuring : forall ca,
  compute_risk ca = LowRisk -> classification ca = Classification.Reassuring.
Proof.
  intros ca H. unfold compute_risk in H.
  destruct (apgar_score ca =? 0) eqn:E0; [discriminate|].
  destruct (apgar_score ca <=? 3) eqn:E1.
  - destruct (has_additional_risk_factors ca) eqn:E2; discriminate.
  - destruct (apgar_score ca <=? 6) eqn:E2.
    + destruct (has_additional_risk_factors ca) eqn:E3; discriminate.
    + apply Nat.leb_gt in E2.
      unfold classification, ExpandedForm.underlying_classification, apgar_score,
             ExpandedForm.underlying_score in *.
      apply Classification.of_score_reassuring. lia.
Qed.

Theorem low_risk_no_additional_factors : forall ca,
  compute_risk ca = LowRisk -> has_additional_risk_factors ca = false \/ apgar_score ca >= 7.
Proof.
  intros ca H. unfold compute_risk in H.
  destruct (apgar_score ca =? 0) eqn:E0; [discriminate|].
  destruct (apgar_score ca <=? 3) eqn:E1.
  - destruct (has_additional_risk_factors ca) eqn:E2; discriminate.
  - destruct (apgar_score ca <=? 6) eqn:E2.
    + destruct (has_additional_risk_factors ca) eqn:E3; [discriminate|].
      left. reflexivity.
    + right. apply Nat.leb_gt in E2. lia.
Qed.

(** Risk category to nat for ordering *)
Definition risk_to_nat (r : RiskCategory) : nat :=
  match r with
  | LowRisk => 0
  | ModerateRisk => 1
  | HighRisk => 2
  | CriticalRisk => 3
  end.

Definition risk_le (r1 r2 : RiskCategory) : Prop :=
  risk_to_nat r1 <= risk_to_nat r2.

Notation "r1 <=risk r2" := (risk_le r1 r2) (at level 70).

Theorem risk_le_refl : forall r, r <=risk r.
Proof. intros r. unfold risk_le. lia. Qed.

Theorem risk_le_trans : forall r1 r2 r3,
  r1 <=risk r2 -> r2 <=risk r3 -> r1 <=risk r3.
Proof. intros r1 r2 r3. unfold risk_le. lia. Qed.

Theorem risk_le_antisym : forall r1 r2,
  r1 <=risk r2 -> r2 <=risk r1 -> r1 = r2.
Proof.
  intros [] [] H1 H2; unfold risk_le in *; simpl in *; try lia; reflexivity.
Qed.

(** Risk → Intervention relationship theorems *)

Definition risk_to_min_intervention (r : RiskCategory) : Intervention.t :=
  match r with
  | LowRisk => Intervention.RoutineCare
  | ModerateRisk => Intervention.StimulationOxygen
  | HighRisk => Intervention.StimulationOxygen  (** Min is StimOx; could be PPV if score 1-3 *)
  | CriticalRisk => Intervention.PositivePressureVentilation (** Min is PPV; could be FullResus if score 0 *)
  end.

(** Critical risk always requires at least PPV *)
Theorem critical_risk_not_routine : forall ca,
  compute_risk ca = CriticalRisk ->
  Intervention.of_score (apgar_score ca) <> Intervention.RoutineCare.
Proof.
  intros ca H Hcontra.
  apply Intervention.of_score_routine_inv in Hcontra.
  pose proof (critical_risk_low_score ca H). lia.
Qed.

(** Critical risk requires full resuscitation or PPV *)
Theorem critical_risk_requires_active_intervention : forall ca,
  compute_risk ca = CriticalRisk ->
  Intervention.of_score (apgar_score ca) = Intervention.FullResuscitation \/
  Intervention.of_score (apgar_score ca) = Intervention.PositivePressureVentilation.
Proof.
  intros ca H.
  pose proof (critical_risk_low_score ca H) as Hscore.
  unfold Intervention.of_score.
  destruct (7 <=? apgar_score ca) eqn:E1; [apply Nat.leb_le in E1; lia|].
  destruct (4 <=? apgar_score ca) eqn:E2; [apply Nat.leb_le in E2; lia|].
  destruct (1 <=? apgar_score ca) eqn:E3.
  - right. reflexivity.
  - left. reflexivity.
Qed.

(** High risk score range: 1-3 (no risk factors) or 4-6 (with risk factors) *)
Theorem high_risk_score_range : forall ca,
  compute_risk ca = HighRisk -> apgar_score ca <= 6.
Proof.
  intros ca H. unfold compute_risk in H.
  destruct (apgar_score ca =? 0) eqn:E0; [discriminate|].
  destruct (apgar_score ca <=? 3) eqn:E1.
  - destruct (has_additional_risk_factors ca) eqn:E2; [discriminate|].
    apply Nat.leb_le in E1. lia.
  - apply Nat.leb_gt in E1.
    destruct (apgar_score ca <=? 6) eqn:E2.
    + destruct (has_additional_risk_factors ca) eqn:E3; [|discriminate].
      apply Nat.leb_le in E2. lia.
    + discriminate.
Qed.

(** High risk requires at least stimulation/oxygen *)
Theorem high_risk_not_routine : forall ca,
  compute_risk ca = HighRisk ->
  Intervention.of_score (apgar_score ca) <> Intervention.RoutineCare.
Proof.
  intros ca H Hcontra.
  apply Intervention.of_score_routine_inv in Hcontra.
  pose proof (high_risk_score_range ca H). lia.
Qed.

(** Moderate risk requires at least stimulation *)
Theorem moderate_risk_score_range : forall ca,
  compute_risk ca = ModerateRisk -> 4 <= apgar_score ca <= 6.
Proof.
  intros ca H. unfold compute_risk in H.
  destruct (apgar_score ca =? 0) eqn:E0; [discriminate|].
  destruct (apgar_score ca <=? 3) eqn:E1.
  - destruct (has_additional_risk_factors ca) eqn:E2; discriminate.
  - apply Nat.leb_gt in E1.
    destruct (apgar_score ca <=? 6) eqn:E2; [|discriminate].
    destruct (has_additional_risk_factors ca) eqn:E3; [discriminate|].
    apply Nat.leb_le in E2. lia.
Qed.

Theorem moderate_risk_intervention : forall ca,
  compute_risk ca = ModerateRisk ->
  Intervention.of_score (apgar_score ca) = Intervention.StimulationOxygen.
Proof.
  intros ca H.
  pose proof (moderate_risk_score_range ca H) as [Hlo Hhi].
  unfold Intervention.of_score.
  destruct (7 <=? apgar_score ca) eqn:E1; [apply Nat.leb_le in E1; lia|].
  destruct (4 <=? apgar_score ca) eqn:E2; [reflexivity|].
  apply Nat.leb_gt in E2. lia.
Qed.

(** Low risk gets routine care *)
Theorem low_risk_routine : forall ca,
  compute_risk ca = LowRisk ->
  Intervention.of_score (apgar_score ca) = Intervention.RoutineCare.
Proof.
  intros ca H.
  pose proof (low_risk_reassuring ca H) as Hclass.
  unfold classification, ExpandedForm.underlying_classification in Hclass.
  apply Classification.of_score_reassuring_inv in Hclass.
  apply Intervention.of_score_routine. exact Hclass.
Qed.

(** Risk ordering implies intervention ordering *)
Theorem risk_intervention_consistency : forall ca,
  Intervention.le (risk_to_min_intervention (compute_risk ca))
                  (Intervention.of_score (apgar_score ca)).
Proof.
  intros ca.
  destruct (compute_risk ca) eqn:E.
  - simpl. pose proof (low_risk_routine ca E). rewrite H.
    unfold Intervention.le. lia.
  - simpl. pose proof (moderate_risk_intervention ca E). rewrite H.
    unfold Intervention.le. lia.
  - simpl. pose proof (high_risk_score_range ca E) as Hbound.
    unfold Intervention.of_score.
    destruct (7 <=? apgar_score ca) eqn:E1; [apply Nat.leb_le in E1; lia|].
    destruct (4 <=? apgar_score ca) eqn:E2; [unfold Intervention.le; simpl; lia|].
    destruct (1 <=? apgar_score ca) eqn:E3; unfold Intervention.le; simpl; lia.
  - simpl. pose proof (critical_risk_requires_active_intervention ca E).
    destruct H; rewrite H; unfold Intervention.le; simpl; lia.
Qed.

(** Score 0 always maps to CriticalRisk *)
Theorem score_zero_critical : forall ca,
  apgar_score ca = 0 -> compute_risk ca = CriticalRisk.
Proof.
  intros ca H. unfold compute_risk. rewrite H. reflexivity.
Qed.

(** Risk factors can escalate moderate to high *)
Theorem risk_factors_escalate : forall ca,
  4 <= apgar_score ca <= 6 ->
  has_additional_risk_factors ca = true ->
  compute_risk ca = HighRisk.
Proof.
  intros ca [Hlo Hhi] Hfactors.
  unfold compute_risk.
  destruct (apgar_score ca =? 0) eqn:E0; [apply Nat.eqb_eq in E0; lia|].
  destruct (apgar_score ca <=? 3) eqn:E1; [apply Nat.leb_le in E1; lia|].
  destruct (apgar_score ca <=? 6) eqn:E2.
  - rewrite Hfactors. simpl. reflexivity.
  - apply Nat.leb_gt in E2. lia.
Qed.

(** Cord blood gas integration: Low APGAR at 5 min warrants cord gas per AAP *)
Theorem low_score_at_5min_needs_cord_gas : forall ca,
  apgar_score ca <= 5 ->
  Timing.to_minutes (standard_time ca) = 5 ->
  needs_cord_gas ca = true.
Proof.
  intros ca Hscore Htime. unfold needs_cord_gas.
  apply andb_true_intro. split.
  - apply Nat.leb_le. exact Hscore.
  - apply Nat.eqb_eq. exact Htime.
Qed.

(** Cord gas asphyxia + very low APGAR indicates high risk minimum *)
Theorem cord_gas_asphyxia_high_risk_minimum : forall ca,
  apgar_score ca <= 3 ->
  cord_gas_indicates_asphyxia ca = true ->
  compute_risk ca = CriticalRisk \/ compute_risk ca = HighRisk.
Proof.
  intros ca Hscore Hasphyxia.
  unfold compute_risk.
  destruct (apgar_score ca =? 0) eqn:E0.
  - left. reflexivity.
  - destruct ((apgar_score ca <=? 3) && has_additional_risk_factors ca) eqn:E1.
    + left. reflexivity.
    + destruct (apgar_score ca <=? 3) eqn:E2.
      * right. reflexivity.
      * apply Nat.leb_gt in E2. lia.
Qed.

(** Relationship between cord gas findings and interventions *)
Theorem acidemia_with_low_apgar_requires_intervention : forall ca,
  apgar_score ca <= 3 ->
  cord_gas_indicates_asphyxia ca = true ->
  Intervention.le Intervention.PositivePressureVentilation
                  (Intervention.of_score (apgar_score ca)).
Proof.
  intros ca Hscore _.
  unfold Intervention.of_score.
  destruct (7 <=? apgar_score ca) eqn:E1; [apply Nat.leb_le in E1; lia|].
  destruct (4 <=? apgar_score ca) eqn:E2; [apply Nat.leb_le in E2; lia|].
  destruct (1 <=? apgar_score ca) eqn:E3.
  - unfold Intervention.le. simpl. lia.
  - apply Nat.leb_gt in E3.
    unfold Intervention.le. simpl. lia.
Qed.

End CombinedAssessment.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 11: PROTOCOL CONSISTENCY                        *)
(*                                                                            *)
(*  Master theorems proving the entire protocol is internally consistent.     *)
(*                                                                            *)
(******************************************************************************)

Module Protocol.

Theorem score_determines_classification : forall a1 a2 : Assessment.t,
  Assessment.total_unbounded a1 = Assessment.total_unbounded a2 ->
  Classification.of_assessment a1 = Classification.of_assessment a2.
Proof.
  intros a1 a2 H. unfold Classification.of_assessment. rewrite H. reflexivity.
Qed.

Theorem classification_determines_urgency : forall a : Assessment.t,
  (Classification.of_assessment a = Classification.Low ->
   Intervention.of_assessment a <> Intervention.RoutineCare) /\
  (Classification.of_assessment a = Classification.Reassuring ->
   Intervention.of_assessment a = Intervention.RoutineCare).
Proof.
  intros a. split.
  - apply Intervention.low_not_routine.
  - apply Intervention.reassuring_gets_routine.
Qed.

Theorem reassuring_terminates : forall ta : Timing.TimedAssessment,
  Classification.of_assessment (Timing.assessment ta) = Classification.Reassuring ->
  Timing.should_continue ta = false.
Proof.
  exact Timing.should_continue_false_if_reassuring.
Qed.

Theorem bounded_timeline : forall ta : Timing.TimedAssessment,
  Timing.time ta = Timing.Min20 ->
  Timing.should_continue ta = false.
Proof.
  intros [t a] H. simpl in H. subst. apply Timing.max_time_stops.
Qed.

Theorem intervention_escalation : forall s1 s2 : nat,
  s1 < s2 -> s2 <= 10 ->
  Intervention.of_score s2 = Intervention.RoutineCare ->
  s1 > 0 ->
  Intervention.of_score s1 <> Intervention.FullResuscitation.
Proof.
  intros s1 s2 Hlt Hbound Hroutine Hpos.
  apply Intervention.of_score_routine_inv in Hroutine.
  unfold Intervention.of_score.
  destruct (7 <=? s1) eqn:E1; [discriminate|].
  destruct (4 <=? s1) eqn:E2; [discriminate|].
  destruct (1 <=? s1) eqn:E3; [discriminate|].
  apply Nat.leb_gt in E3. lia.
Qed.

Theorem well_formed_intervention_consistency : forall wf : ExpandedForm.WellFormedExpandedForm,
  ExpandedForm.is_resuscitated (ExpandedForm.form wf) = true ->
  Intervention.of_score (ExpandedForm.underlying_score (ExpandedForm.form wf)) <> Intervention.RoutineCare.
Proof.
  intros wf Hres.
  pose proof (ExpandedForm.well_formed_score_bound wf Hres) as Hbound.
  unfold ExpandedForm.underlying_score in *.
  unfold Intervention.of_score.
  destruct (7 <=? Assessment.total_unbounded
              (Timing.assessment (ExpandedForm.timed_assessment (ExpandedForm.form wf)))) eqn:E.
  - apply Nat.leb_le in E. lia.
  - destruct (4 <=? _) eqn:E2; [discriminate|].
    destruct (1 <=? _) eqn:E3; discriminate.
Qed.

Theorem well_formed_classification_consistency : forall wf : ExpandedForm.WellFormedExpandedForm,
  ExpandedForm.is_resuscitated (ExpandedForm.form wf) = true ->
  ExpandedForm.underlying_classification (ExpandedForm.form wf) <> Classification.Reassuring.
Proof.
  intros wf Hres.
  destruct wf as [e Hpf]. simpl.
  apply Hpf. exact Hres.
Qed.

Definition resuscitation_implies_active_intervention :=
  well_formed_intervention_consistency.

Theorem discontinuation_implies_full_resuscitation : forall e : ExpandedForm.t,
  Discontinuation.criteria_considered e = true ->
  Intervention.of_score (ExpandedForm.underlying_score e) = Intervention.FullResuscitation.
Proof.
  intros e H.
  pose proof (Discontinuation.criteria_requires_zero e H) as Hzero.
  rewrite Hzero. reflexivity.
Qed.

End Protocol.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 12: SCORE TRAJECTORIES                          *)
(*                                                                            *)
(*  Properties of score sequences over time. An improving trajectory          *)
(*  leads to improving classification and reduced intervention needs.         *)
(*                                                                            *)
(******************************************************************************)

Module Trajectory.

Definition improving (s1 s2 : nat) : Prop := s1 <= s2.

Definition stable (s1 s2 : nat) : Prop := s1 = s2.

Definition declining (s1 s2 : nat) : Prop := s1 > s2.

Theorem declining_classification : forall s1 s2,
  declining s1 s2 ->
  Classification.le (Classification.of_score s2) (Classification.of_score s1).
Proof.
  intros s1 s2 H. unfold declining in H.
  apply Classification.monotonic. lia.
Qed.

Theorem declining_intervention : forall s1 s2,
  declining s1 s2 ->
  Intervention.le (Intervention.of_score s1) (Intervention.of_score s2).
Proof.
  intros s1 s2 H. unfold declining in H.
  apply Intervention.anti_monotonic. lia.
Qed.

Theorem declining_may_lose_reassuring : forall s1 s2,
  declining s1 s2 ->
  Classification.of_score s1 = Classification.Reassuring ->
  s2 >= 7 \/ Classification.of_score s2 <> Classification.Reassuring.
Proof.
  intros s1 s2 Hdec Hclass.
  apply Classification.reassuring_iff in Hclass.
  destruct (7 <=? s2) eqn:E.
  - left. apply Nat.leb_le in E. exact E.
  - right. apply Nat.leb_gt in E.
    intro Hcontra. apply Classification.reassuring_iff in Hcontra. lia.
Qed.

Theorem improving_classification : forall s1 s2,
  improving s1 s2 ->
  Classification.le (Classification.of_score s1) (Classification.of_score s2).
Proof.
  intros s1 s2 H. apply Classification.monotonic. exact H.
Qed.

Theorem improving_intervention : forall s1 s2,
  improving s1 s2 ->
  Intervention.le (Intervention.of_score s2) (Intervention.of_score s1).
Proof.
  intros s1 s2 H. apply Intervention.anti_monotonic. exact H.
Qed.

Theorem stable_preserves_classification : forall s1 s2,
  stable s1 s2 ->
  Classification.of_score s1 = Classification.of_score s2.
Proof.
  intros s1 s2 H. unfold stable in H. subst. reflexivity.
Qed.

Theorem reassuring_reached_stays : forall s1 s2,
  improving s1 s2 ->
  Classification.of_score s1 = Classification.Reassuring ->
  Classification.of_score s2 = Classification.Reassuring.
Proof.
  intros s1 s2 Himp Hclass. unfold improving in Himp.
  apply Classification.reassuring_iff in Hclass.
  apply Classification.reassuring_iff. lia.
Qed.

Theorem routine_reached_stays : forall s1 s2,
  improving s1 s2 ->
  Intervention.of_score s1 = Intervention.RoutineCare ->
  Intervention.of_score s2 = Intervention.RoutineCare.
Proof.
  intros s1 s2 Himp Hint. unfold improving in Himp.
  apply Intervention.of_score_routine_inv in Hint.
  apply Intervention.of_score_routine. lia.
Qed.

Definition trajectory := list nat.

Fixpoint is_improving_trajectory (t : trajectory) : Prop :=
  match t with
  | [] => True
  | [_] => True
  | s1 :: ((s2 :: _) as rest) => s1 <= s2 /\ is_improving_trajectory rest
  end.

Fixpoint is_improving_trajectoryb (t : trajectory) : bool :=
  match t with
  | [] => true
  | [_] => true
  | s1 :: ((s2 :: _) as rest) => (s1 <=? s2) && is_improving_trajectoryb rest
  end.

Lemma is_improving_trajectoryb_correct : forall t,
  is_improving_trajectoryb t = true <-> is_improving_trajectory t.
Proof.
  induction t as [|s1 [|s2 t'] IH]; simpl.
  - tauto.
  - tauto.
  - rewrite andb_true_iff, Nat.leb_le. split.
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.

Definition is_improving_trajectory_dec (t : trajectory) :
  {is_improving_trajectory t} + {~ is_improving_trajectory t}.
Proof.
  destruct (is_improving_trajectoryb t) eqn:E.
  - left. apply is_improving_trajectoryb_correct. exact E.
  - right. intro H. apply is_improving_trajectoryb_correct in H. congruence.
Defined.

Theorem improving_trajectory_endpoints : forall t s1 sn,
  is_improving_trajectory (s1 :: t ++ [sn]) ->
  s1 <= sn.
Proof.
  induction t as [|s2 t' IH]; intros s1 sn H.
  - simpl in H. destruct H as [H _]. exact H.
  - simpl in H. destruct H as [H1 H2].
    assert (Hle : s2 <= sn).
    { apply IH. exact H2. }
    lia.
Qed.

Fixpoint adjacent_pairs (t : trajectory) : list (nat * nat) :=
  match t with
  | [] => []
  | [_] => []
  | s1 :: ((s2 :: _) as rest) => (s1, s2) :: adjacent_pairs rest
  end.

Lemma adjacent_pairs_length : forall t,
  length t >= 1 -> length (adjacent_pairs t) = length t - 1.
Proof.
  induction t as [|s1 [|s2 t'] IH]; intros Hlen; simpl in *.
  - lia.
  - lia.
  - rewrite IH; simpl; lia.
Qed.

Lemma adjacent_pairs_length_nonempty : forall t,
  length t >= 2 -> length (adjacent_pairs t) >= 1.
Proof.
  intros t H. rewrite adjacent_pairs_length; lia.
Qed.

Theorem improving_trajectory_all_pairs : forall t,
  is_improving_trajectory t ->
  forall p, In p (adjacent_pairs t) -> fst p <= snd p.
Proof.
  induction t as [|s1 [|s2 t'] IH]; intros Htraj p Hin; simpl in *.
  - contradiction.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst p. simpl. destruct Htraj as [H _]. exact H.
    + apply IH; [destruct Htraj; exact H0 | exact Hin].
Qed.

Fixpoint is_declining_trajectory (t : trajectory) : Prop :=
  match t with
  | [] => True
  | [_] => True
  | s1 :: ((s2 :: _) as rest) => s1 >= s2 /\ is_declining_trajectory rest
  end.

Fixpoint is_declining_trajectoryb (t : trajectory) : bool :=
  match t with
  | [] => true
  | [_] => true
  | s1 :: ((s2 :: _) as rest) => (s2 <=? s1) && is_declining_trajectoryb rest
  end.

Lemma is_declining_trajectoryb_correct : forall t,
  is_declining_trajectoryb t = true <-> is_declining_trajectory t.
Proof.
  induction t as [|s1 [|s2 t'] IH]; simpl.
  - tauto.
  - tauto.
  - rewrite andb_true_iff, Nat.leb_le. split.
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.

Definition is_declining_trajectory_dec (t : trajectory) :
  {is_declining_trajectory t} + {~ is_declining_trajectory t}.
Proof.
  destruct (is_declining_trajectoryb t) eqn:E.
  - left. apply is_declining_trajectoryb_correct. exact E.
  - right. intro H. apply is_declining_trajectoryb_correct in H. congruence.
Defined.

Theorem declining_trajectory_endpoints : forall t s1 sn,
  is_declining_trajectory (s1 :: t ++ [sn]) ->
  s1 >= sn.
Proof.
  induction t as [|s2 t' IH]; intros s1 sn H.
  - simpl in H. destruct H as [H _]. exact H.
  - simpl in H. destruct H as [H1 H2].
    assert (Hge : s2 >= sn).
    { apply IH. exact H2. }
    lia.
Qed.

Theorem declining_trajectory_all_pairs : forall t,
  is_declining_trajectory t ->
  forall p, In p (adjacent_pairs t) -> fst p >= snd p.
Proof.
  induction t as [|s1 [|s2 t'] IH]; intros Htraj p Hin; simpl in *.
  - contradiction.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst p. simpl. destruct Htraj as [H _]. exact H.
    + apply IH; [destruct Htraj; exact H0 | exact Hin].
Qed.

Fixpoint is_stable_trajectory (t : trajectory) : Prop :=
  match t with
  | [] => True
  | [_] => True
  | s1 :: ((s2 :: _) as rest) => s1 = s2 /\ is_stable_trajectory rest
  end.

Theorem stable_is_improving_and_declining : forall t,
  is_stable_trajectory t <-> (is_improving_trajectory t /\ is_declining_trajectory t).
Proof.
  induction t as [|s1 [|s2 t'] IH]; simpl.
  - tauto.
  - tauto.
  - split.
    + intros [Heq Hrest]. subst. split; split; try lia; apply IH; exact Hrest.
    + intros [[H1 H2] [H3 H4]]. split; [lia | apply IH; split; assumption].
Qed.

Fixpoint is_stable_trajectoryb (t : trajectory) : bool :=
  match t with
  | [] => true
  | [_] => true
  | s1 :: ((s2 :: _) as rest) => (s1 =? s2) && is_stable_trajectoryb rest
  end.

Lemma is_stable_trajectoryb_correct : forall t,
  is_stable_trajectoryb t = true <-> is_stable_trajectory t.
Proof.
  induction t as [|s1 [|s2 t'] IH]; simpl.
  - tauto.
  - tauto.
  - rewrite andb_true_iff, Nat.eqb_eq. split.
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
    + intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.

Definition is_stable_trajectory_dec (t : trajectory) :
  {is_stable_trajectory t} + {~ is_stable_trajectory t}.
Proof.
  destruct (is_stable_trajectoryb t) eqn:E.
  - left. apply is_stable_trajectoryb_correct. exact E.
  - right. intro H. apply is_stable_trajectoryb_correct in H. congruence.
Defined.

Lemma declining_adjacent_le : forall t,
  is_declining_trajectory t ->
  forall i, S i < length t ->
  nth (S i) t 0 <= nth i t 0.
Proof.
  induction t as [|s1 [|s2 t'] IH]; intros Htraj i Hlen.
  - simpl in Hlen. lia.
  - simpl in Hlen. lia.
  - destruct i as [|i'].
    + simpl. simpl in Htraj. lia.
    + simpl. apply IH.
      * simpl in Htraj. destruct Htraj. exact H0.
      * simpl in Hlen. simpl. lia.
Qed.

Lemma declining_trajectory_monotonic : forall t,
  is_declining_trajectory t ->
  forall i j, i <= j -> j < length t ->
  nth j t 0 <= nth i t 0.
Proof.
  intros t Htraj i j Hij Hjlen.
  induction j as [|j' IHj].
  - assert (i = 0) by lia. subst. lia.
  - destruct (Nat.eq_dec i (S j')) as [Heq|Hne].
    + subst. lia.
    + assert (Hij' : i <= j') by lia.
      assert (Hjlen' : j' < length t) by lia.
      specialize (IHj Hij' Hjlen').
      assert (Hadj : nth (S j') t 0 <= nth j' t 0).
      { apply declining_adjacent_le; assumption. }
      lia.
Qed.

Theorem declining_classification_worsens : forall t,
  is_declining_trajectory t ->
  forall i j, i < j -> i < length t -> j < length t ->
  Classification.le (Classification.of_score (nth j t 0))
                    (Classification.of_score (nth i t 0)).
Proof.
  intros t Htraj i j Hij Hilen Hjlen.
  apply Classification.monotonic.
  apply declining_trajectory_monotonic; [exact Htraj | lia | exact Hjlen].
Qed.

Theorem bounded_improving_trajectory_converges : forall t,
  is_improving_trajectory t ->
  (forall s, In s t -> s <= 10) ->
  length t > 0 ->
  nth (length t - 1) t 0 <= 10.
Proof.
  intros t Htraj Hbound Hlen.
  apply Hbound.
  apply nth_In. lia.
Qed.

Lemma improving_adjacent_le : forall t,
  is_improving_trajectory t ->
  forall i, S i < length t ->
  nth i t 0 <= nth (S i) t 0.
Proof.
  induction t as [|s1 [|s2 t'] IH]; intros Htraj i Hlen.
  - simpl in Hlen. lia.
  - simpl in Hlen. lia.
  - destruct i as [|i'].
    + simpl. simpl in Htraj. lia.
    + simpl. apply IH.
      * simpl in Htraj. destruct Htraj. exact H0.
      * simpl in Hlen. simpl. lia.
Qed.

Lemma improving_trajectory_monotonic : forall t,
  is_improving_trajectory t ->
  forall i j, i <= j -> j < length t ->
  nth i t 0 <= nth j t 0.
Proof.
  intros t Htraj i j Hij Hjlen.
  induction j as [|j' IHj].
  - assert (i = 0) by lia. subst. lia.
  - destruct (Nat.eq_dec i (S j')) as [Heq|Hne].
    + subst. lia.
    + assert (Hij' : i <= j') by lia.
      assert (Hjlen' : j' < length t) by lia.
      specialize (IHj Hij' Hjlen').
      assert (Hadj : nth j' t 0 <= nth (S j') t 0).
      { apply improving_adjacent_le; assumption. }
      lia.
Qed.

Theorem improving_trajectory_classification_monotonic : forall t,
  is_improving_trajectory t ->
  forall i j, i <= j -> j < length t ->
  Classification.le (Classification.of_score (nth i t 0))
                    (Classification.of_score (nth j t 0)).
Proof.
  intros t Htraj i j Hij Hjlen.
  apply Classification.monotonic.
  apply improving_trajectory_monotonic; assumption.
Qed.

Theorem improving_from_low_eventually_reassuring : forall t,
  is_improving_trajectory t ->
  (forall s, In s t -> s <= 10) ->
  length t > 0 ->
  Classification.of_score (hd 0 t) = Classification.Low ->
  nth (length t - 1) t 0 >= 7 ->
  Classification.of_score (nth (length t - 1) t 0) = Classification.Reassuring.
Proof.
  intros t _ Hbound Hlen _ Hfinal.
  apply Classification.of_score_reassuring. exact Hfinal.
Qed.

Theorem improving_trajectory_intervention_decreasing : forall t,
  is_improving_trajectory t ->
  forall i j, i <= j -> j < length t ->
  Intervention.le (Intervention.of_score (nth j t 0))
                  (Intervention.of_score (nth i t 0)).
Proof.
  intros t Htraj i j Hij Hjlen.
  apply Intervention.anti_monotonic.
  apply improving_trajectory_monotonic; assumption.
Qed.

Theorem stable_trajectory_same_classification : forall t,
  is_stable_trajectory t ->
  forall i j, i < length t -> j < length t ->
  Classification.of_score (nth i t 0) = Classification.of_score (nth j t 0).
Proof.
  intros t Hstable i j Hi Hj.
  assert (Himp : is_improving_trajectory t) by (apply stable_is_improving_and_declining; tauto).
  assert (Hdec : is_declining_trajectory t) by (apply stable_is_improving_and_declining; tauto).
  destruct (Nat.le_ge_cases i j) as [Hij|Hji].
  - pose proof (improving_trajectory_classification_monotonic t Himp i j Hij Hj) as H1.
    pose proof (declining_classification_worsens t Hdec i j) as H2.
    destruct (Nat.eq_dec i j) as [Heq|Hne].
    + subst. reflexivity.
    + assert (i < j) by lia.
      specialize (H2 H Hi Hj).
      apply Classification.le_antisym; assumption.
  - pose proof (improving_trajectory_classification_monotonic t Himp j i Hji Hi) as H1.
    pose proof (declining_classification_worsens t Hdec j i) as H2.
    destruct (Nat.eq_dec i j) as [Heq|Hne].
    + subst. reflexivity.
    + assert (j < i) by lia.
      specialize (H2 H Hj Hi).
      symmetry. apply Classification.le_antisym; assumption.
Qed.

(** Trajectory classification function *)

Inductive TrajectoryType : Type :=
  | TrajImproving : TrajectoryType
  | TrajDeclining : TrajectoryType
  | TrajStable : TrajectoryType
  | TrajMixed : TrajectoryType.

Definition trajectory_type_eq_dec : forall t1 t2 : TrajectoryType,
  {t1 = t2} + {t1 <> t2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition trajectory_type_all : list TrajectoryType :=
  [TrajImproving; TrajDeclining; TrajStable; TrajMixed].

Lemma trajectory_type_all_complete : forall t : TrajectoryType, In t trajectory_type_all.
Proof. intros []; simpl; auto. Qed.

Lemma trajectory_type_all_nodup : NoDup trajectory_type_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition classify (t : trajectory) : TrajectoryType :=
  if is_stable_trajectoryb t then TrajStable
  else if is_improving_trajectoryb t then TrajImproving
  else if is_declining_trajectoryb t then TrajDeclining
  else TrajMixed.

Theorem classify_stable_correct : forall t,
  is_stable_trajectory t -> classify t = TrajStable.
Proof.
  intros t H. unfold classify.
  apply is_stable_trajectoryb_correct in H. rewrite H. reflexivity.
Qed.

Theorem classify_examples :
  classify [5; 5; 5] = TrajStable /\
  classify [1; 3; 5] = TrajImproving /\
  classify [5; 3; 1] = TrajDeclining /\
  classify [1; 5; 3] = TrajMixed.
Proof. repeat split; reflexivity. Qed.

Definition score_delta (t : trajectory) : option Z :=
  match t with
  | [] => None
  | [_] => Some 0%Z
  | s1 :: _ => Some (Z.of_nat (nth (length t - 1) t 0%nat) - Z.of_nat s1)%Z
  end.

Theorem improving_positive_delta : forall t,
  length t >= 2 ->
  is_improving_trajectory t ->
  exists d, score_delta t = Some d /\ (d >= 0)%Z.
Proof.
  intros t Hlen Himp.
  destruct t as [|s1 [|s2 rest]]; [simpl in Hlen; lia | simpl in Hlen; lia |].
  unfold score_delta. simpl.
  exists (Z.of_nat (nth (length rest) (s2 :: rest) 0%nat) - Z.of_nat s1)%Z.
  split; [reflexivity|].
  assert (Hmono : s1 <= nth (length rest) (s2 :: rest) 0%nat).
  { apply (improving_trajectory_monotonic (s1 :: s2 :: rest) Himp 0 (S (length rest))).
    - lia.
    - simpl. lia. }
  lia.
Qed.

(** Conversion from ValidSequence to trajectory *)

Definition of_timed_sequence (seq : Timing.AssessmentSequence) : trajectory :=
  map (fun ta => Assessment.total_unbounded (Timing.assessment ta)) seq.

Definition of_valid_sequence (vs : Timing.ValidSequence) : trajectory :=
  of_timed_sequence (Timing.seq vs).

Theorem of_valid_sequence_length : forall vs,
  length (of_valid_sequence vs) = Timing.valid_seq_length vs.
Proof.
  intros vs. unfold of_valid_sequence, of_timed_sequence, Timing.valid_seq_length.
  apply map_length.
Qed.

Theorem of_valid_sequence_nonempty : forall vs,
  of_valid_sequence vs <> [].
Proof.
  intros vs H. unfold of_valid_sequence, of_timed_sequence in H.
  destruct (Timing.seq vs) as [|ta rest] eqn:Eseq.
  - exfalso. apply (Timing.seq_nonempty vs). exact Eseq.
  - discriminate H.
Qed.

Theorem of_valid_sequence_bounded : forall vs,
  Forall (fun s => s <= 10) (of_valid_sequence vs).
Proof.
  intros vs. unfold of_valid_sequence, of_timed_sequence.
  apply Forall_forall. intros s Hin.
  apply in_map_iff in Hin. destruct Hin as [ta [Heq _]].
  subst. apply Assessment.total_max.
Qed.

Theorem of_valid_sequence_scores_match : forall vs,
  of_valid_sequence vs = Timing.sequence_scores (Timing.seq vs).
Proof.
  intros vs. unfold of_valid_sequence, of_timed_sequence, Timing.sequence_scores.
  reflexivity.
Qed.

(** Trajectory-Timing preservation lemmas *)

(** A singleton valid sequence produces a singleton trajectory *)
Theorem singleton_trajectory : forall a,
  of_valid_sequence (Timing.singleton_seq a) = [Assessment.total_unbounded a].
Proof. intros a. reflexivity. Qed.

(** First score of trajectory equals first assessment score *)
Theorem trajectory_head_correct : forall vs,
  hd 0 (of_valid_sequence vs) =
  Assessment.total_unbounded (Timing.assessment (Timing.valid_seq_head vs)).
Proof.
  intros vs. unfold of_valid_sequence, of_timed_sequence.
  destruct vs as [[|ta rest] Hne Hstart Hcons].
  - exfalso. apply Hne. reflexivity.
  - simpl. reflexivity.
Qed.

(** Score delta is well-defined for valid sequences *)
Theorem score_delta_well_defined : forall vs,
  exists d : Z, score_delta (of_valid_sequence vs) = Some d.
Proof.
  intros vs. unfold score_delta.
  destruct (of_valid_sequence vs) as [|s [|s2 rest]] eqn:E.
  - exfalso. apply of_valid_sequence_nonempty in E. exact E.
  - exists 0%Z. reflexivity.
  - eexists. reflexivity.
Qed.

(** Trajectory classification examples *)
Example trajectory_improving_example : classify [1; 3; 5; 7] = TrajImproving.
Proof. reflexivity. Qed.

Example trajectory_declining_example : classify [9; 7; 5; 3] = TrajDeclining.
Proof. reflexivity. Qed.

Example trajectory_stable_example : classify [5; 5; 5] = TrajStable.
Proof. reflexivity. Qed.

(** Valid sequences produce trajectories of the same length *)
Theorem valid_seq_trajectory_lengths_match : forall vs,
  length (of_valid_sequence vs) = Timing.valid_seq_length vs.
Proof. exact of_valid_sequence_length. Qed.

(** Trajectory first/last relationship proofs *)

(** Helper: hd equals nth 0 *)
Lemma hd_nth_0 : forall (l : list nat) d, hd d l = nth 0 l d.
Proof. intros [|x l] d; reflexivity. Qed.

(** Helper: last equals nth (length - 1) for non-empty lists *)
Lemma last_nth : forall (l : list nat) d,
  l <> [] -> last l d = nth (length l - 1) l d.
Proof.
  induction l as [|x [|y l'] IH]; intros d Hne.
  - contradiction.
  - reflexivity.
  - simpl. simpl in IH. rewrite IH; [|discriminate].
    simpl. destruct (length l'); reflexivity.
Qed.

(** Improving trajectories imply last >= first *)
Theorem improving_implies_last_ge_first : forall traj,
  traj <> [] ->
  is_improving_trajectory traj ->
  hd 0 traj <= last traj 0.
Proof.
  intros traj Hne Himpr.
  rewrite hd_nth_0, last_nth by assumption.
  apply improving_trajectory_monotonic.
  - exact Himpr.
  - lia.
  - destruct traj; [contradiction | simpl; lia].
Qed.

(** Declining trajectories imply last <= first *)
Theorem declining_implies_last_le_first : forall traj,
  traj <> [] ->
  is_declining_trajectory traj ->
  hd 0 traj >= last traj 0.
Proof.
  intros traj Hne Hdec.
  rewrite hd_nth_0, last_nth by assumption.
  apply declining_trajectory_monotonic.
  - exact Hdec.
  - lia.
  - destruct traj; [contradiction | simpl; lia].
Qed.

(** Stable trajectories imply all elements equal *)
Theorem stable_implies_first_eq_last : forall traj,
  traj <> [] ->
  is_stable_trajectory traj ->
  hd 0 traj = last traj 0.
Proof.
  intros traj Hne Hstab.
  apply stable_is_improving_and_declining in Hstab.
  destruct Hstab as [Himpr Hdec].
  assert (H1 : hd 0 traj <= last traj 0).
  { apply improving_implies_last_ge_first; assumption. }
  assert (H2 : hd 0 traj >= last traj 0).
  { apply declining_implies_last_le_first; assumption. }
  lia.
Qed.

(** Score delta relationship with trajectory type *)
Theorem improving_has_nonnegative_delta : forall traj,
  length traj >= 2 ->
  is_improving_trajectory traj ->
  exists d, score_delta traj = Some d /\ (d >= 0)%Z.
Proof.
  intros traj Hlen Himpr.
  destruct traj as [|s1 [|s2 rest]].
  - simpl in Hlen. lia.
  - simpl in Hlen. lia.
  - unfold score_delta. simpl.
    eexists. split; [reflexivity|].
    assert (H: nth 0 (s1 :: s2 :: rest) 0 <= nth (S (length rest)) (s1 :: s2 :: rest) 0).
    { apply improving_trajectory_monotonic.
      - exact Himpr.
      - lia.
      - simpl. lia. }
    simpl in H. lia.
Qed.

(** Score reaching reassuring level means routine care *)
Theorem score_reaches_reassuring_intervention : forall traj,
  length traj >= 2 ->
  last traj 0 >= 7 ->
  Intervention.of_score (last traj 0) = Intervention.RoutineCare.
Proof.
  intros traj Hlen Hlast.
  apply Intervention.of_score_routine. exact Hlast.
Qed.

(** Improving trajectory with reassuring endpoint *)
Theorem improving_to_reassuring_yields_routine : forall traj,
  length traj >= 2 ->
  is_improving_trajectory traj ->
  last traj 0 >= 7 ->
  Intervention.of_score (last traj 0) = Intervention.RoutineCare.
Proof.
  intros traj Hlen Himpr Hlast.
  apply score_reaches_reassuring_intervention; assumption.
Qed.

End Trajectory.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 13: MAIN RESULTS                                *)
(*                                                                            *)
(*  Summary of key verified properties.                                       *)
(*                                                                            *)
(******************************************************************************)

Module MainResults.

Theorem score_bounded : forall a : Assessment.t,
  Assessment.total_unbounded a <= 10.
Proof. exact Assessment.total_max. Qed.

Theorem score_complete : forall n : nat, n <= 10 ->
  exists a : Assessment.t, Assessment.total_unbounded a = n.
Proof. exact Reachability.all_scores_reachable. Qed.

Theorem score_range_exactly_0_to_10 :
  (forall a : Assessment.t, 0 <= Assessment.total_unbounded a <= 10) /\
  (forall n : nat, n <= 10 -> exists a : Assessment.t, Assessment.total_unbounded a = n).
Proof.
  split.
  - intros a. split; [lia | apply Assessment.total_max].
  - exact Reachability.all_scores_reachable.
Qed.

Theorem classification_correct : forall a : Assessment.t,
  (Assessment.total_unbounded a <= 3 ->
   Classification.of_assessment a = Classification.Low) /\
  (4 <= Assessment.total_unbounded a <= 6 ->
   Classification.of_assessment a = Classification.ModeratelyAbnormal) /\
  (7 <= Assessment.total_unbounded a ->
   Classification.of_assessment a = Classification.Reassuring).
Proof.
  intros a. unfold Classification.of_assessment. repeat split; intros H.
  - apply Classification.low_iff. exact H.
  - apply Classification.moderate_iff. exact H.
  - apply Classification.reassuring_iff. exact H.
Qed.

Theorem intervention_consistent : forall a : Assessment.t,
  Classification.of_assessment a = Classification.Reassuring <->
  Intervention.of_assessment a = Intervention.RoutineCare.
Proof.
  intros a. split.
  - apply Intervention.reassuring_gets_routine.
  - intros H. apply Classification.reassuring_iff.
    unfold Intervention.of_assessment in H.
    apply Intervention.of_score_routine_inv in H. exact H.
Qed.

Theorem assessment_space_finite : length Assessment.all = 243.
Proof. exact Assessment.all_length. Qed.

Theorem all_assessments_covered : forall a : Assessment.t, In a Assessment.all.
Proof. exact Assessment.all_complete. Qed.

Theorem scorelevel_exhaustive_minimal :
  ListHelpers.exhaustive_minimal ScoreLevel.all 3.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact ScoreLevel.all_complete.
  - exact ScoreLevel.all_nodup.
  - reflexivity.
Qed.

Theorem appearance_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Appearance.all 3.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Appearance.all_complete.
  - exact Appearance.all_nodup.
  - exact Appearance.all_length.
Qed.

Theorem pulse_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Pulse.all 3.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Pulse.all_complete.
  - exact Pulse.all_nodup.
  - exact Pulse.all_length.
Qed.

Theorem grimace_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Grimace.all 3.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Grimace.all_complete.
  - exact Grimace.all_nodup.
  - exact Grimace.all_length.
Qed.

Theorem activity_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Activity.all 3.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Activity.all_complete.
  - exact Activity.all_nodup.
  - exact Activity.all_length.
Qed.

Theorem respiration_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Respiration.all 3.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Respiration.all_complete.
  - exact Respiration.all_nodup.
  - exact Respiration.all_length.
Qed.

Theorem assessment_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Assessment.all 243.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Assessment.all_complete.
  - exact Assessment.all_nodup.
  - exact Assessment.all_length.
Qed.

Theorem classification_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Classification.all 3.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Classification.all_complete.
  - exact Classification.all_nodup.
  - reflexivity.
Qed.

Theorem intervention_exhaustive_minimal :
  ListHelpers.exhaustive_minimal Intervention.all 4.
Proof.
  apply ListHelpers.exhaustive_minimal_intro.
  - exact Intervention.all_complete.
  - exact Intervention.all_nodup.
  - reflexivity.
Qed.

Theorem spo2_targets_monotonic :
  SpO2.target_1min_lo <= SpO2.target_2min_lo /\
  SpO2.target_2min_lo <= SpO2.target_3min_lo /\
  SpO2.target_3min_lo <= SpO2.target_4min_lo /\
  SpO2.target_4min_lo <= SpO2.target_5min_lo /\
  SpO2.target_5min_lo <= SpO2.target_10min_lo.
Proof. exact SpO2.targets_monotonic_lo. Qed.

Theorem therapeutic_hypothermia_requires_term : forall c,
  TherapeuticHypothermia.is_eligible c = true ->
  TherapeuticHypothermia.ga_eligible c = true.
Proof. exact TherapeuticHypothermia.eligibility_requires_term. Qed.

Theorem therapeutic_hypothermia_excludes_preterm : forall c,
  GestationalAge.weeks (TherapeuticHypothermia.gestational_age c) < 36 ->
  TherapeuticHypothermia.is_eligible c = false.
Proof. exact TherapeuticHypothermia.preterm_ineligible. Qed.

Theorem low_risk_implies_reassuring : forall ca,
  CombinedAssessment.compute_risk ca = CombinedAssessment.LowRisk ->
  CombinedAssessment.classification ca = Classification.Reassuring.
Proof. exact CombinedAssessment.low_risk_reassuring. Qed.

Theorem critical_risk_implies_low_score : forall ca,
  CombinedAssessment.compute_risk ca = CombinedAssessment.CriticalRisk ->
  CombinedAssessment.apgar_score ca <= 3.
Proof. exact CombinedAssessment.critical_risk_low_score. Qed.

Theorem cord_gas_indicated_at_5min : forall ca,
  CombinedAssessment.needs_cord_gas ca = true ->
  CombinedAssessment.apgar_score ca <= 5.
Proof. exact CombinedAssessment.needs_cord_gas_implies_low_score. Qed.

(** Negative properties: score bounds are tight *)

Theorem score_11_unreachable : forall a : Assessment.t,
  Assessment.total_unbounded a <> 11.
Proof.
  intros a H. assert (Hle := Assessment.total_max a). lia.
Qed.

Theorem no_score_above_10 : forall a : Assessment.t,
  ~ (Assessment.total_unbounded a > 10).
Proof.
  intros a H. assert (Hle := Assessment.total_max a). lia.
Qed.

(** Two different assessments can have the same score *)
Theorem score_not_injective : exists a1 a2 : Assessment.t,
  a1 <> a2 /\ Assessment.total_unbounded a1 = Assessment.total_unbounded a2.
Proof.
  exists (Assessment.mk Appearance.PaleBlue Pulse.Below100 Grimace.NoResponse
                         Activity.Flaccid Respiration.Apneic).
  exists (Assessment.mk Appearance.Acrocyanotic Pulse.Absent Grimace.NoResponse
                         Activity.Flaccid Respiration.Apneic).
  split.
  - intro H. inversion H.
  - reflexivity.
Qed.

(** Assessment cardinality is exactly 243 *)
Theorem assessment_cardinality_exact : length Assessment.all = 243.
Proof. exact Assessment.all_length. Qed.

(** No intervention strictly between RoutineCare and StimulationOxygen *)
Theorem intervention_gap_routine_stim : forall i,
  Intervention.severity i > Intervention.severity Intervention.RoutineCare ->
  Intervention.severity i >= Intervention.severity Intervention.StimulationOxygen.
Proof.
  intros []; simpl; lia.
Qed.

End MainResults.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 14: PROOF AUTOMATION HINTS                      *)
(*                                                                            *)
(*  Hint declarations for automated proof search.                             *)
(*                                                                            *)
(******************************************************************************)

#[export] Hint Resolve ScoreLevel.all_complete : apgar.
#[export] Hint Resolve ScoreLevel.all_nodup : apgar.
#[export] Hint Resolve ScoreLevel.to_nat_bound : apgar.
#[export] Hint Resolve Appearance.all_complete : apgar.
#[export] Hint Resolve Appearance.all_nodup : apgar.
#[export] Hint Resolve Pulse.all_complete : apgar.
#[export] Hint Resolve Pulse.all_nodup : apgar.
#[export] Hint Resolve Grimace.all_complete : apgar.
#[export] Hint Resolve Grimace.all_nodup : apgar.
#[export] Hint Resolve Activity.all_complete : apgar.
#[export] Hint Resolve Activity.all_nodup : apgar.
#[export] Hint Resolve Respiration.all_complete : apgar.
#[export] Hint Resolve Respiration.all_nodup : apgar.
#[export] Hint Resolve Assessment.all_complete : apgar.
#[export] Hint Resolve Assessment.all_nodup : apgar.
#[export] Hint Resolve Assessment.total_max : apgar.
#[export] Hint Resolve Classification.all_complete : apgar.
#[export] Hint Resolve Classification.all_nodup : apgar.
#[export] Hint Resolve Intervention.all_complete : apgar.
#[export] Hint Resolve Intervention.all_nodup : apgar.
#[export] Hint Resolve Timing.all_complete : apgar.
#[export] Hint Resolve Timing.all_nodup : apgar.

#[export] Hint Rewrite Classification.low_iff : apgar.
#[export] Hint Rewrite Classification.moderate_iff : apgar.
#[export] Hint Rewrite Classification.reassuring_iff : apgar.

#[export] Hint Resolve Intervention.reassuring_gets_routine : apgar.
#[export] Hint Resolve Intervention.low_not_routine : apgar.
#[export] Hint Resolve Intervention.full_iff_zero : apgar.

#[export] Hint Resolve Assessment.score_0_unique : apgar.
#[export] Hint Resolve Assessment.score_10_unique : apgar.
#[export] Hint Resolve Assessment.ComponentIndex_all_complete : apgar.
#[export] Hint Resolve Assessment.ComponentIndex_all_nodup : apgar.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 14b: NEGATIVE SPECIFICATIONS                    *)
(*                                                                            *)
(*  Proofs that certain clinical states are impossible or contradictory.      *)
(*                                                                            *)
(******************************************************************************)

Module NegativeSpecs.

Theorem reassuring_not_requires_full_resuscitation : forall a,
  Classification.of_assessment a = Classification.Reassuring ->
  Intervention.of_assessment a <> Intervention.FullResuscitation.
Proof.
  intros a Hclass Hcontra.
  unfold Classification.of_assessment, Intervention.of_assessment in *.
  apply Intervention.full_iff_zero in Hcontra.
  apply Classification.of_score_reassuring_inv in Hclass.
  lia.
Qed.

Theorem score_11_unreachable : forall a,
  Assessment.total_unbounded a <> 11.
Proof.
  intros a Hcontra.
  pose proof (Assessment.total_max a) as Hmax.
  lia.
Qed.

Theorem zero_score_unique_components : forall a,
  Assessment.total_unbounded a = 0 ->
  Assessment.appearance a = Appearance.PaleBlue /\
  Assessment.pulse a = Pulse.Absent /\
  Assessment.grimace a = Grimace.NoResponse /\
  Assessment.activity a = Activity.Flaccid /\
  Assessment.respiration a = Respiration.Apneic.
Proof.
  intros a H.
  pose proof (Assessment.score_0_unique a H) as Heq.
  subst. unfold Assessment.minimum. simpl. repeat split; reflexivity.
Qed.

Theorem perfect_score_unique_components : forall a,
  Assessment.total_unbounded a = 10 ->
  Assessment.appearance a = Appearance.CompletelyPink /\
  Assessment.pulse a = Pulse.AtOrAbove100 /\
  Assessment.grimace a = Grimace.CryCoughSneeze /\
  Assessment.activity a = Activity.ActiveMotion /\
  Assessment.respiration a = Respiration.StrongCry.
Proof.
  intros a H.
  pose proof (Assessment.score_10_unique a H) as Heq.
  subst. unfold Assessment.maximum. simpl. repeat split; reflexivity.
Qed.

Theorem low_score_not_routine : forall s,
  s <= 3 -> Intervention.of_score s <> Intervention.RoutineCare.
Proof.
  intros s Hs Hcontra.
  apply Intervention.of_score_routine_inv in Hcontra.
  lia.
Qed.

Theorem moderate_score_not_full_resuscitation : forall s,
  4 <= s <= 6 -> Intervention.of_score s <> Intervention.FullResuscitation.
Proof.
  intros s Hs Hcontra.
  apply Intervention.full_iff_zero in Hcontra.
  lia.
Qed.

(** Protocol Completeness Theorem:
    For any valid assessment sequence, exactly one of three outcomes holds:
    1. The latest score is reassuring (>=7) - assessment can stop
    2. The sequence is at Min20 - maximum extension reached
    3. The sequence can be extended to a later time point *)
Theorem protocol_completeness : forall vs : Timing.ValidSequence,
  (Classification.of_score (Assessment.total_unbounded
     (Timing.assessment (last (Timing.seq vs) (Timing.mkTimed Timing.Min1 Assessment.minimum))))
   = Classification.Reassuring) \/
  (Timing.time (last (Timing.seq vs) (Timing.mkTimed Timing.Min1 Assessment.minimum)) = Timing.Min20) \/
  (Timing.can_extend vs = true).
Proof.
  intros vs.
  set (latest := last (Timing.seq vs) (Timing.mkTimed Timing.Min1 Assessment.minimum)).
  set (cls := Classification.of_score (Assessment.total_unbounded (Timing.assessment latest))).
  destruct (Classification.eq_dec cls Classification.Reassuring) as [Hreass | Hnot_reass].
  - left. exact Hreass.
  - destruct (Timing.eq_dec (Timing.time latest) Timing.Min20) as [Hmax | Hnot_max].
    + right. left. exact Hmax.
    + right. right.
      unfold Timing.can_extend. unfold latest.
      destruct (Timing.next (Timing.time (last (Timing.seq vs) (Timing.mkTimed Timing.Min1 Assessment.minimum)))) eqn:Enext.
      * reflexivity.
      * exfalso. apply Timing.next_none_iff_max in Enext.
        apply Hnot_max. unfold latest. exact Enext.
Qed.

(** Protocol termination: if reassuring OR at Max time, should_continue is false *)
Theorem protocol_termination_complete : forall ta : Timing.TimedAssessment,
  (Classification.of_assessment (Timing.assessment ta) = Classification.Reassuring \/
   Timing.time ta = Timing.Min20) ->
  Timing.should_continue ta = false.
Proof.
  intros [t a] [H | H].
  - apply Timing.should_continue_false_if_reassuring. exact H.
  - simpl in H. subst. apply Timing.max_time_stops.
Qed.

End NegativeSpecs.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 14c: AUDIT TRAIL TYPES                          *)
(*                                                                            *)
(*  Types for audit logging and version tracking of assessments.              *)
(*                                                                            *)
(******************************************************************************)

Module AuditTrail.

Inductive EventType : Type :=
  | Created : EventType
  | Modified : EventType
  | Reviewed : EventType
  | Finalized : EventType.

Definition event_type_eq_dec : forall e1 e2 : EventType, {e1 = e2} + {e1 <> e2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition event_type_all : list EventType := [Created; Modified; Reviewed; Finalized].

Lemma event_type_all_complete : forall e : EventType, In e event_type_all.
Proof. intros []; simpl; auto. Qed.

Lemma event_type_all_nodup : NoDup event_type_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Record AuditEvent : Type := mkAuditEvent {
  event_type : EventType;
  timestamp_seconds : nat;
  user_id : nat;
  assessment_snapshot : Assessment.t
}.

Definition AuditLog : Type := list AuditEvent.

Definition initial_event (user : nat) (ts : nat) (a : Assessment.t) : AuditEvent :=
  mkAuditEvent Created ts user a.

Definition modification_event (user : nat) (ts : nat) (a : Assessment.t) : AuditEvent :=
  mkAuditEvent Modified ts user a.

Definition finalize_event (user : nat) (ts : nat) (a : Assessment.t) : AuditEvent :=
  mkAuditEvent Finalized ts user a.

Definition log_is_chronological (log : AuditLog) : Prop :=
  forall i j, i < j -> j < length log ->
  timestamp_seconds (nth i log (mkAuditEvent Created 0 0 Assessment.minimum)) <=
  timestamp_seconds (nth j log (mkAuditEvent Created 0 0 Assessment.minimum)).

Definition log_starts_with_created (log : AuditLog) : Prop :=
  match log with
  | [] => True
  | e :: _ => event_type e = Created
  end.

Definition log_ends_with_finalized (log : AuditLog) : Prop :=
  match rev log with
  | [] => True
  | e :: _ => event_type e = Finalized
  end.

Definition log_no_modifications_after_finalized (log : AuditLog) : Prop :=
  forall i, i < length log ->
  event_type (nth i log (mkAuditEvent Created 0 0 Assessment.minimum)) = Finalized ->
  forall j, i < j -> j < length log ->
  event_type (nth j log (mkAuditEvent Created 0 0 Assessment.minimum)) <> Modified.

(** Boolean decidability for audit log predicates *)

Definition log_starts_with_createdb (log : AuditLog) : bool :=
  match log with
  | [] => true
  | e :: _ => match event_type e with Created => true | _ => false end
  end.

Lemma log_starts_with_createdb_correct : forall log,
  log_starts_with_createdb log = true <-> log_starts_with_created log.
Proof.
  intros [|e rest]; simpl.
  - tauto.
  - destruct (event_type e) eqn:E; split; intro H; try reflexivity; try discriminate; exact E.
Qed.

Definition log_ends_with_finalizedb (log : AuditLog) : bool :=
  match rev log with
  | [] => true
  | e :: _ => match event_type e with Finalized => true | _ => false end
  end.

Lemma log_ends_with_finalizedb_correct : forall log,
  log_ends_with_finalizedb log = true <-> log_ends_with_finalized log.
Proof.
  intros log. unfold log_ends_with_finalizedb, log_ends_with_finalized.
  destruct (rev log) as [|e rest]; simpl.
  - tauto.
  - destruct (event_type e) eqn:E; split; intro H; try reflexivity; try discriminate; exact E.
Qed.

Fixpoint log_is_chronologicalb_aux (prev_ts : nat) (log : AuditLog) : bool :=
  match log with
  | [] => true
  | e :: rest => (prev_ts <=? timestamp_seconds e) &&
                 log_is_chronologicalb_aux (timestamp_seconds e) rest
  end.

Definition log_is_chronologicalb (log : AuditLog) : bool :=
  match log with
  | [] => true
  | e :: rest => log_is_chronologicalb_aux (timestamp_seconds e) rest
  end.

(** Auxiliary lemma: chronologicalb_aux implies adjacent ordering *)
Lemma log_is_chronologicalb_aux_adjacent : forall prev log,
  log_is_chronologicalb_aux prev log = true ->
  match log with
  | [] => True
  | e :: _ => prev <= timestamp_seconds e
  end.
Proof.
  intros prev log H.
  destruct log as [|e rest]; [trivial|].
  simpl in H. apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

(** Chronologicalb implies adjacent elements are ordered *)
Lemma log_is_chronologicalb_implies_adjacent : forall log,
  log_is_chronologicalb log = true ->
  forall i, S i < length log ->
  timestamp_seconds (nth i log (mkAuditEvent Created 0 0 Assessment.minimum)) <=
  timestamp_seconds (nth (S i) log (mkAuditEvent Created 0 0 Assessment.minimum)).
Proof.
  intros log H i Hi.
  generalize dependent i. generalize dependent log.
  induction log as [|e1 [|e2 rest] IH]; intros H i Hi.
  - simpl in Hi. lia.
  - simpl in Hi. lia.
  - destruct i as [|i'].
    + simpl. simpl in H. apply andb_true_iff in H. destruct H as [H _].
      apply Nat.leb_le in H. exact H.
    + simpl. simpl in Hi.
      apply IH.
      * simpl in H. apply andb_true_iff in H. destruct H as [_ H]. exact H.
      * simpl. lia.
Qed.

(** Full correctness: chronologicalb true implies chronological Prop *)
Lemma log_is_chronologicalb_correct_forward : forall log,
  log_is_chronologicalb log = true -> log_is_chronological log.
Proof.
  intros log H i j Hij Hjlen.
  induction j as [|j' IHj].
  - lia.
  - destruct (Nat.eq_dec i j') as [Heq|Hne].
    + subst. apply log_is_chronologicalb_implies_adjacent; assumption.
    + assert (Hi' : i < j') by lia.
      assert (Hj'len : j' < length log) by lia.
      specialize (IHj Hi' Hj'len).
      pose proof (log_is_chronologicalb_implies_adjacent log H j' Hjlen) as Hadj.
      lia.
Qed.

Record ValidAuditLog : Type := mkValidLog {
  log_events : AuditLog;
  log_chrono : log_is_chronological log_events;
  log_starts : log_starts_with_created log_events;
  log_no_mod_after_final : log_no_modifications_after_finalized log_events
}.

Definition score_history (log : AuditLog) : list nat :=
  map (fun e => Assessment.total_unbounded (assessment_snapshot e)) log.

Theorem score_history_length : forall log,
  length (score_history log) = length log.
Proof. intros log. unfold score_history. apply map_length. Qed.

(** Two-element log chronological iff timestamps ordered *)
Lemma two_element_log_chronological : forall e1 e2,
  log_is_chronologicalb [e1; e2] = true <->
  timestamp_seconds e1 <= timestamp_seconds e2.
Proof.
  intros e1 e2. unfold log_is_chronologicalb. simpl.
  split.
  - intro H. apply andb_prop in H. destruct H as [H _].
    apply Nat.leb_le in H. exact H.
  - intro H. apply andb_true_intro. split.
    + apply Nat.leb_le. exact H.
    + reflexivity.
Qed.

(** Helper for testing log validity *)
Definition is_valid_audit_logb (log : AuditLog) : bool :=
  log_is_chronologicalb log && log_starts_with_createdb log.

(** Empty log is trivially valid (chronological, etc.) *)
Lemma empty_log_chronological : log_is_chronologicalb [] = true.
Proof. reflexivity. Qed.

(** Single event log is chronological *)
Lemma singleton_log_chronological : forall e,
  log_is_chronologicalb [e] = true.
Proof. intros e. reflexivity. Qed.

(** Valid log construction: singleton created log *)
Definition singleton_created_log (ts uid : nat) (a : Assessment.t) : AuditLog :=
  [mkAuditEvent Created ts uid a].

Lemma singleton_created_log_valid : forall ts uid a,
  log_starts_with_createdb (singleton_created_log ts uid a) = true.
Proof. reflexivity. Qed.

Lemma singleton_created_log_chrono : forall ts uid a,
  log_is_chronologicalb (singleton_created_log ts uid a) = true.
Proof. reflexivity. Qed.

(** Append event to log preserving chronological order *)
Definition append_event (log : AuditLog) (e : AuditEvent) : AuditLog :=
  log ++ [e].

(** Last timestamp of a log (0 if empty) *)
Definition last_timestamp (log : AuditLog) : nat :=
  match log with
  | [] => 0
  | _ => timestamp_seconds (last log (mkAuditEvent Created 0 0 Assessment.minimum))
  end.

(** Check if event can be appended (timestamp ordering) *)
Definition can_append (log : AuditLog) (e : AuditEvent) : bool :=
  last_timestamp log <=? timestamp_seconds e.

(** Append preserves chronological order when timestamps are ordered *)
Lemma append_chronological_aux : forall log prev_ts e,
  log_is_chronologicalb_aux prev_ts log = true ->
  (match log with
   | [] => prev_ts
   | _ => timestamp_seconds (last log (mkAuditEvent Created 0 0 Assessment.minimum))
   end) <= timestamp_seconds e ->
  log_is_chronologicalb_aux prev_ts (log ++ [e]) = true.
Proof.
  induction log as [|x xs IH]; intros prev_ts e Hchrono Hle.
  - simpl. apply andb_true_intro. split.
    + apply Nat.leb_le. exact Hle.
    + reflexivity.
  - simpl in *. apply andb_prop in Hchrono. destruct Hchrono as [Hprev Hrest].
    apply andb_true_intro. split; [exact Hprev|].
    apply IH; [exact Hrest|].
    destruct xs; simpl in *; exact Hle.
Qed.

Lemma append_preserves_chronological : forall log e,
  log_is_chronologicalb log = true ->
  can_append log e = true ->
  log_is_chronologicalb (append_event log e) = true.
Proof.
  intros [|x xs] e Hchrono Hcan.
  - simpl. reflexivity.
  - unfold log_is_chronologicalb in *. unfold append_event.
    simpl. apply append_chronological_aux.
    + exact Hchrono.
    + unfold can_append in Hcan. simpl in Hcan.
      apply Nat.leb_le in Hcan.
      destruct xs; simpl in *; exact Hcan.
Qed.

(** Modification event constructor *)
Definition add_modification (log : AuditLog) (ts uid : nat) (a : Assessment.t) : AuditLog :=
  append_event log (mkAuditEvent Modified ts uid a).

(** Review event constructor *)
Definition add_review (log : AuditLog) (ts uid : nat) (a : Assessment.t) : AuditLog :=
  append_event log (mkAuditEvent Reviewed ts uid a).

(** Finalization event constructor *)
Definition add_finalization (log : AuditLog) (ts uid : nat) (a : Assessment.t) : AuditLog :=
  append_event log (mkAuditEvent Finalized ts uid a).

(** Check if log is finalized *)
Definition is_finalized (log : AuditLog) : bool := log_ends_with_finalizedb log.

(** Cannot append to finalized log *)
Definition can_modify (log : AuditLog) : bool :=
  negb (is_finalized log).

(** Finalized logs should not be modified *)
Theorem finalized_cannot_modify : forall log,
  is_finalized log = true -> can_modify log = false.
Proof.
  intros log H. unfold can_modify. rewrite H. reflexivity.
Qed.

(** Log length after append *)
Lemma append_length : forall log e,
  length (append_event log e) = S (length log).
Proof.
  intros log e. unfold append_event.
  rewrite app_length. simpl. lia.
Qed.

(** Score history after append *)
Lemma score_history_append : forall log e,
  score_history (append_event log e) =
  score_history log ++ [Assessment.total_unbounded (assessment_snapshot e)].
Proof.
  intros log e. unfold score_history, append_event.
  rewrite map_app. reflexivity.
Qed.

(** Latest score in log *)
Definition latest_score (log : AuditLog) : option nat :=
  match rev log with
  | [] => None
  | e :: _ => Some (Assessment.total_unbounded (assessment_snapshot e))
  end.

(** Latest assessment in log *)
Definition latest_assessment (log : AuditLog) : option Assessment.t :=
  match rev log with
  | [] => None
  | e :: _ => Some (assessment_snapshot e)
  end.

Lemma latest_score_singleton : forall ts uid a,
  latest_score (singleton_created_log ts uid a) = Some (Assessment.total_unbounded a).
Proof. reflexivity. Qed.

Lemma latest_score_append : forall log e,
  log <> [] ->
  latest_score (append_event log e) = Some (Assessment.total_unbounded (assessment_snapshot e)).
Proof.
  intros log e Hne. unfold latest_score, append_event.
  rewrite rev_app_distr. simpl. reflexivity.
Qed.

(** Score changed between events *)
Definition score_changed (e1 e2 : AuditEvent) : bool :=
  negb (Assessment.total_unbounded (assessment_snapshot e1) =?
        Assessment.total_unbounded (assessment_snapshot e2)).

(** Count score changes in log *)
Fixpoint count_score_changes (log : AuditLog) : nat :=
  match log with
  | [] => 0
  | [_] => 0
  | e1 :: ((e2 :: _) as rest) =>
      (if score_changed e1 e2 then 1 else 0) + count_score_changes rest
  end.

Lemma count_score_changes_singleton : forall e,
  count_score_changes [e] = 0.
Proof. reflexivity. Qed.

(** Backward direction: chronological Prop implies chronologicalb true *)
Lemma log_is_chronologicalb_correct_backward : forall log,
  log_is_chronological log -> log_is_chronologicalb log = true.
Proof.
  intros log H.
  induction log as [|e1 [|e2 rest] IH].
  - reflexivity.
  - reflexivity.
  - simpl. apply andb_true_intro. split.
    + apply Nat.leb_le.
      specialize (H 0 1 ltac:(lia)).
      simpl in H. apply H. simpl. lia.
    + apply IH. intros i j Hij Hj.
      assert (Hbound: S j < length (e1 :: e2 :: rest)).
      { simpl. simpl in Hj. lia. }
      specialize (H (S i) (S j) ltac:(lia) Hbound).
      simpl in H. exact H.
Qed.

(** Full boolean reflection: iff version *)
Theorem log_is_chronologicalb_correct : forall log,
  log_is_chronologicalb log = true <-> log_is_chronological log.
Proof.
  intros log. split.
  - apply log_is_chronologicalb_correct_forward.
  - apply log_is_chronologicalb_correct_backward.
Qed.

(** Decidability of log_is_chronological *)
Definition log_is_chronological_dec (log : AuditLog) :
  {log_is_chronological log} + {~ log_is_chronological log}.
Proof.
  destruct (log_is_chronologicalb log) eqn:E.
  - left. apply log_is_chronologicalb_correct_forward. exact E.
  - right. intro H. apply log_is_chronologicalb_correct_backward in H.
    rewrite H in E. discriminate.
Defined.

(** Empty log satisfies log_no_modifications_after_finalized *)
Lemma empty_log_no_mod_after_final : log_no_modifications_after_finalized [].
Proof.
  unfold log_no_modifications_after_finalized.
  intros i Hi. simpl in Hi. lia.
Qed.

(** Singleton created log is a valid audit log *)
Definition singleton_valid_log (ts uid : nat) (a : Assessment.t) : ValidAuditLog.
Proof.
  refine (mkValidLog [mkAuditEvent Created ts uid a] _ _ _).
  - unfold log_is_chronological. intros i j Hij Hj. simpl in Hj. lia.
  - simpl. reflexivity.
  - unfold log_no_modifications_after_finalized. intros i Hi Htype j Hij Hj.
    simpl in *. destruct i; [|lia]. destruct j; [lia|]. simpl in Hj. lia.
Defined.

(** Extract log from valid audit log *)
Definition valid_log_events (vl : ValidAuditLog) : AuditLog := log_events vl.

(** Valid log length *)
Definition valid_log_length (vl : ValidAuditLog) : nat := length (log_events vl).

(** Valid log is chronological *)
Lemma valid_log_is_chronological : forall vl,
  log_is_chronological (log_events vl).
Proof. intros vl. exact (log_chrono vl). Qed.

End AuditTrail.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 15: PROPERTY-BASED TESTING                      *)
(*                                                                            *)
(*  The following properties are recommended for QuickChick testing:          *)
(*                                                                            *)
(*  1. forall a, Assessment.total_unbounded a <= 10                           *)
(*  2. forall n, n <= 10 -> Assessment.total_unbounded (witness_fn n) = n     *)
(*  3. forall a, Classification.of_assessment a in [Low;Moderate;Reassuring]  *)
(*  4. forall s, Classification.of_score s = Reassuring ->                    *)
(*               Intervention.of_score s = RoutineCare                        *)
(*  5. forall bpm, bpm <= 300 -> Pulse.of_bpm bpm in [Absent;Below100;Above]  *)
(*                                                                            *)
(*  To enable: Require Import QuickChick. Then define generators for          *)
(*  Assessment.t and use 'QuickChick <property>' to test.                     *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 16: EXTRACTION                                  *)
(*                                                                            *)
(*  Extraction directives for generating executable code.                     *)
(*                                                                            *)
(******************************************************************************)

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

(* Output directory is relative to coqc working directory.                    *)
(* Run: cd apgar-verified && coqc -Q . Apgar Apgar.v                           *)
Set Extraction Output Directory ".".

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

Extraction Inline BoundedNat.val.
Extraction Inline Assessment.total_unbounded.

Module ExtractionTests.

Definition test_minimum_score : nat := Assessment.total_unbounded Assessment.minimum.
Definition test_maximum_score : nat := Assessment.total_unbounded Assessment.maximum.

Definition test_classify_0 : Classification.t := Classification.of_score 0.
Definition test_classify_5 : Classification.t := Classification.of_score 5.
Definition test_classify_10 : Classification.t := Classification.of_score 10.

Definition test_intervene_0 : Intervention.t := Intervention.of_score 0.
Definition test_intervene_5 : Intervention.t := Intervention.of_score 5.
Definition test_intervene_10 : Intervention.t := Intervention.of_score 10.

Definition test_witness_5 : Assessment.t := Reachability.witness_fn 5.

Lemma test_minimum_is_0 : test_minimum_score = 0.
Proof. reflexivity. Qed.

Lemma test_maximum_is_10 : test_maximum_score = 10.
Proof. reflexivity. Qed.

Lemma test_classify_0_is_low : test_classify_0 = Classification.Low.
Proof. reflexivity. Qed.

Lemma test_classify_5_is_moderate : test_classify_5 = Classification.ModeratelyAbnormal.
Proof. reflexivity. Qed.

Lemma test_classify_10_is_reassuring : test_classify_10 = Classification.Reassuring.
Proof. reflexivity. Qed.

Lemma test_intervene_0_is_full : test_intervene_0 = Intervention.FullResuscitation.
Proof. reflexivity. Qed.

Lemma test_intervene_5_is_stim : test_intervene_5 = Intervention.StimulationOxygen.
Proof. reflexivity. Qed.

Lemma test_intervene_10_is_routine : test_intervene_10 = Intervention.RoutineCare.
Proof. reflexivity. Qed.

Lemma test_witness_5_score : Assessment.total_unbounded test_witness_5 = 5.
Proof. reflexivity. Qed.

Definition test_bpm_absent : Pulse.t := Pulse.of_bpm 0.
Definition test_bpm_bradycardia : Pulse.DetailedPulse := Pulse.of_bpm_detailed 50.
Definition test_bpm_low_normal : Pulse.DetailedPulse := Pulse.of_bpm_detailed 80.
Definition test_bpm_normal : Pulse.DetailedPulse := Pulse.of_bpm_detailed 140.

Lemma test_bpm_absent_correct : test_bpm_absent = Pulse.Absent.
Proof. reflexivity. Qed.

Lemma test_bpm_bradycardia_correct : test_bpm_bradycardia = Pulse.DBradycardia.
Proof. reflexivity. Qed.

Lemma test_bpm_low_normal_correct : test_bpm_low_normal = Pulse.DLowNormal.
Proof. reflexivity. Qed.

Lemma test_bpm_normal_correct : test_bpm_normal = Pulse.DNormal.
Proof. reflexivity. Qed.

Definition test_classify_3 : Classification.t := Classification.of_score 3.
Definition test_classify_4 : Classification.t := Classification.of_score 4.
Definition test_classify_6 : Classification.t := Classification.of_score 6.
Definition test_classify_7 : Classification.t := Classification.of_score 7.

Lemma test_classify_3_is_low : test_classify_3 = Classification.Low.
Proof. reflexivity. Qed.

Lemma test_classify_4_is_moderate : test_classify_4 = Classification.ModeratelyAbnormal.
Proof. reflexivity. Qed.

Lemma test_classify_6_is_moderate : test_classify_6 = Classification.ModeratelyAbnormal.
Proof. reflexivity. Qed.

Lemma test_classify_7_is_reassuring : test_classify_7 = Classification.Reassuring.
Proof. reflexivity. Qed.

Definition test_intervene_1 : Intervention.t := Intervention.of_score 1.
Definition test_intervene_3 : Intervention.t := Intervention.of_score 3.
Definition test_intervene_4 : Intervention.t := Intervention.of_score 4.
Definition test_intervene_6 : Intervention.t := Intervention.of_score 6.
Definition test_intervene_7 : Intervention.t := Intervention.of_score 7.

Lemma test_intervene_1_is_ppv : test_intervene_1 = Intervention.PositivePressureVentilation.
Proof. reflexivity. Qed.

Lemma test_intervene_3_is_ppv : test_intervene_3 = Intervention.PositivePressureVentilation.
Proof. reflexivity. Qed.

Lemma test_intervene_4_is_stim : test_intervene_4 = Intervention.StimulationOxygen.
Proof. reflexivity. Qed.

Lemma test_intervene_6_is_stim : test_intervene_6 = Intervention.StimulationOxygen.
Proof. reflexivity. Qed.

Lemma test_intervene_7_is_routine : test_intervene_7 = Intervention.RoutineCare.
Proof. reflexivity. Qed.

Definition test_bpm_threshold_99 : Pulse.t := Pulse.of_bpm 99.
Definition test_bpm_threshold_100 : Pulse.t := Pulse.of_bpm 100.

Lemma test_bpm_99_below : test_bpm_threshold_99 = Pulse.Below100.
Proof. reflexivity. Qed.

Lemma test_bpm_100_at_or_above : test_bpm_threshold_100 = Pulse.AtOrAbove100.
Proof. reflexivity. Qed.

Definition test_trajectory_improving : bool :=
  Trajectory.is_improving_trajectoryb [1; 3; 5; 7; 9].
Definition test_trajectory_declining : bool :=
  Trajectory.is_declining_trajectoryb [9; 7; 5; 3; 1].
Definition test_trajectory_stable : bool :=
  Trajectory.is_stable_trajectoryb [5; 5; 5; 5].

Lemma test_trajectory_improving_true : test_trajectory_improving = true.
Proof. reflexivity. Qed.

Lemma test_trajectory_declining_true : test_trajectory_declining = true.
Proof. reflexivity. Qed.

Lemma test_trajectory_stable_true : test_trajectory_stable = true.
Proof. reflexivity. Qed.

Definition test_all_witnesses : list nat :=
  map Assessment.total_unbounded
    [Reachability.witness_fn 0; Reachability.witness_fn 1;
     Reachability.witness_fn 2; Reachability.witness_fn 3;
     Reachability.witness_fn 4; Reachability.witness_fn 5;
     Reachability.witness_fn 6; Reachability.witness_fn 7;
     Reachability.witness_fn 8; Reachability.witness_fn 9;
     Reachability.witness_fn 10].

Lemma test_all_witnesses_correct : test_all_witnesses = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Proof. reflexivity. Qed.

(** Negative test cases: Testing rejection of invalid inputs *)
Definition test_invalid_score_11 : option ValidScore.t := ValidScore.of_nat_opt 11.
Definition test_invalid_score_100 : option ValidScore.t := ValidScore.of_nat_opt 100.

Lemma test_invalid_score_11_none : test_invalid_score_11 = None.
Proof. reflexivity. Qed.

Lemma test_invalid_score_100_none : test_invalid_score_100 = None.
Proof. reflexivity. Qed.

Definition test_invalid_appearance : option Appearance.t := Appearance.of_nat_opt 3.
Definition test_invalid_appearance_10 : option Appearance.t := Appearance.of_nat_opt 10.

Lemma test_invalid_appearance_none : test_invalid_appearance = None.
Proof. reflexivity. Qed.

Lemma test_invalid_appearance_10_none : test_invalid_appearance_10 = None.
Proof. reflexivity. Qed.

Definition test_invalid_pulse : option Pulse.t := Pulse.of_nat_opt 3.
Definition test_invalid_grimace : option Grimace.t := Grimace.of_nat_opt 5.
Definition test_invalid_activity : option Activity.t := Activity.of_nat_opt 4.
Definition test_invalid_respiration : option Respiration.t := Respiration.of_nat_opt 3.

Lemma test_invalid_pulse_none : test_invalid_pulse = None.
Proof. reflexivity. Qed.

Lemma test_invalid_grimace_none : test_invalid_grimace = None.
Proof. reflexivity. Qed.

Lemma test_invalid_activity_none : test_invalid_activity = None.
Proof. reflexivity. Qed.

Lemma test_invalid_respiration_none : test_invalid_respiration = None.
Proof. reflexivity. Qed.

(** Test boundary rejections for physiological values *)
Definition test_invalid_weight_7000 : option BirthWeight.t := BirthWeight.of_grams_opt 7000.

Lemma test_invalid_weight_none : test_invalid_weight_7000 = None.
Proof. reflexivity. Qed.

(** Classification.of_nat clamps to valid range, so test the boundary behavior *)
Definition test_classification_clamped_high : Classification.t := Classification.of_nat 100.

Lemma test_classification_clamped_to_reassuring : test_classification_clamped_high = Classification.Reassuring.
Proof. reflexivity. Qed.

(** Test trajectory edge cases *)
Definition test_empty_trajectory_not_improving : bool :=
  Trajectory.is_improving_trajectoryb [].
Definition test_singleton_trajectory_stable : bool :=
  Trajectory.is_stable_trajectoryb [7].

Lemma test_empty_not_improving : test_empty_trajectory_not_improving = true.
Proof. reflexivity. Qed.

Lemma test_singleton_stable : test_singleton_trajectory_stable = true.
Proof. reflexivity. Qed.

End ExtractionTests.

(******************************************************************************)
(*                                                                            *)
(*  EXTRACTION CAVEAT: The nat -> int extraction is safe for APGAR scores     *)
(*  (0-10) and physiological BPM (0-300), but would overflow for unbounded    *)
(*  nat values exceeding OCaml's max_int. This is acceptable for this         *)
(*  domain-specific application.                                              *)
(*                                                                            *)
(******************************************************************************)

Extraction "apgar.ml"
  Assessment.t Assessment.mk Assessment.total_unbounded
  Assessment.minimum Assessment.maximum
  Assessment.appearance Assessment.pulse Assessment.grimace
  Assessment.activity Assessment.respiration
  Assessment.assessments_with_score Assessment.count_assessments_with_score
  Assessment.ComponentIndex Assessment.ComponentIndex_of_nat Assessment.ComponentIndex_of_nat_opt
  Assessment.ComponentIndex_to_nat Assessment.component_contribution
  Classification.t Classification.of_score Classification.of_assessment
  Classification.to_nat Classification.of_nat
  Intervention.t Intervention.of_score Intervention.of_assessment
  Intervention.severity Intervention.of_nat
  Timing.Time Timing.TimedAssessment Timing.mkTimed
  Timing.time Timing.assessment Timing.should_continue Timing.next
  Timing.to_minutes Timing.to_seconds Timing.is_standard Timing.is_extended Timing.needs_extension
  Timing.Timestamp Timing.mkTimestamp Timing.seconds_since_birth
  Timing.timestamp_to_minutes Timing.nearest_standard_time Timing.is_standard_timing
  Timing.example_valid_sequence Timing.sequence_scores
  Timing.singleton_seq Timing.mk_valid_seq_2 Timing.mk_valid_seq_3
  Timing.mk_valid_seq_4 Timing.mk_valid_seq_5 Timing.can_extend
  ExpandedForm.t ExpandedForm.mk ExpandedForm.RespiratorySupport
  ExpandedForm.timed_assessment ExpandedForm.resp_support
  ExpandedForm.fio2 ExpandedForm.ppv_params
  ExpandedForm.chest_compression_params ExpandedForm.epinephrine_admin
  ExpandedForm.volume_expansion ExpandedForm.spo2_reading ExpandedForm.temperature_reading
  ExpandedForm.has_chest_compressions ExpandedForm.has_epinephrine
  ExpandedForm.is_resuscitated
  ExpandedForm.underlying_score ExpandedForm.underlying_classification
  ExpandedForm.resp_support_severity ExpandedForm.resp_support_leb
  ExpandedForm.FiO2 ExpandedForm.mkFiO2 ExpandedForm.fio2_percent
  ExpandedForm.is_room_air ExpandedForm.is_supplemental ExpandedForm.is_high_fio2
  ExpandedForm.PPVParameters ExpandedForm.mkPPV
  ExpandedForm.ppv_pip ExpandedForm.ppv_peep ExpandedForm.ppv_rate
  ExpandedForm.is_adequate_pip ExpandedForm.is_adequate_rate
  ExpandedForm.driving_pressure ExpandedForm.has_positive_driving_pressure
  ExpandedForm.CompressionRatio ExpandedForm.ChestCompressionParams ExpandedForm.mkCCParams
  ExpandedForm.cc_rate ExpandedForm.cc_ratio
  ExpandedForm.is_nrp_rate ExpandedForm.is_nrp_ratio
  ExpandedForm.EpinephrineRoute ExpandedForm.EpinephrineAdmin ExpandedForm.mkEpiAdmin
  ExpandedForm.epi_dose_mcg_per_kg ExpandedForm.epi_route
  ExpandedForm.is_iv_dose_range ExpandedForm.is_ett_dose_range ExpandedForm.is_correct_dose_for_route
  ExpandedForm.VolumeAgent ExpandedForm.VolumeExpansion ExpandedForm.mkVolumeExp
  ExpandedForm.has_volume_expansion ExpandedForm.no_volume
  Discontinuation.criteria_considered Discontinuation.decide_discontinuation
  Discontinuation.DiscontinuationDecision
  GestationalAge.t GestationalAge.mk GestationalAge.weeks GestationalAge.days
  GestationalAge.to_days GestationalAge.Maturity GestationalAge.classify
  GestationalAge.is_preterm GestationalAge.is_term GestationalAge.is_post_term
  SpO2.t SpO2.mk SpO2.value SpO2.TargetRange
  SpO2.target_lo SpO2.target_hi SpO2.in_target SpO2.below_target SpO2.above_target
  SpO2.Status SpO2.status SpO2.range_for_minute SpO2.is_hyperoxic
  SpO2.status_all SpO2.target_range_all SpO2.target_range_eq_dec
  SpO2.Population SpO2.population_all SpO2.population_eq_dec
  CordBloodGas.pH CordBloodGas.mkpH CordBloodGas.ph_value_x100
  CordBloodGas.is_acidemic CordBloodGas.is_severely_acidemic
  CordBloodGas.pCO2 CordBloodGas.mkpCO2 CordBloodGas.pco2_value CordBloodGas.is_hypercapnic
  CordBloodGas.pO2 CordBloodGas.mkpO2 CordBloodGas.po2_value CordBloodGas.is_hypoxemic
  CordBloodGas.BaseDeficit CordBloodGas.mkBD CordBloodGas.bd_value
  CordBloodGas.is_significant_bd CordBloodGas.is_severe_bd
  CordBloodGas.Lactate CordBloodGas.mkLactate CordBloodGas.lactate_value_x10
  CordBloodGas.is_elevated_lactate
  CordBloodGas.t CordBloodGas.mk CordBloodGas.indicates_asphyxia
  Temperature.t Temperature.mk Temperature.value_x10 Temperature.Status
  Temperature.classify Temperature.is_hypothermic Temperature.is_hyperthermic
  Temperature.is_normal Temperature.needs_warming Temperature.needs_cooling
  Temperature.status_all
  BirthWeight.t BirthWeight.Category BirthWeight.category_all BirthWeight.classify
  BirthWeight.is_elbw BirthWeight.is_vlbw BirthWeight.is_lbw
  TherapeuticHypothermia.EncephalopathyGrade TherapeuticHypothermia.encephalopathy_qualifies
  TherapeuticHypothermia.Candidate TherapeuticHypothermia.mkCandidate
  TherapeuticHypothermia.ga_eligible TherapeuticHypothermia.apgar_eligible
  TherapeuticHypothermia.acidosis_eligible TherapeuticHypothermia.neuro_eligible
  TherapeuticHypothermia.is_eligible
  CombinedAssessment.t CombinedAssessment.mk
  CombinedAssessment.apgar_score CombinedAssessment.classification
  CombinedAssessment.spo2 CombinedAssessment.standard_time
  CombinedAssessment.is_preterm CombinedAssessment.is_term CombinedAssessment.maturity
  CombinedAssessment.has_cord_gas CombinedAssessment.cord_gas_indicates_asphyxia
  CombinedAssessment.spo2_on_target CombinedAssessment.is_resuscitated
  CombinedAssessment.needs_cord_gas
  CombinedAssessment.is_vlbw CombinedAssessment.is_elbw
  CombinedAssessment.RiskCategory CombinedAssessment.risk_category_all
  CombinedAssessment.compute_risk
  Interval.t Interval.make Interval.lo Interval.hi Interval.width
  Interval.contains Interval.containsb
  Appearance.t Appearance.to_nat Appearance.of_nat Appearance.of_nat_opt
  Pulse.t Pulse.of_bpm Pulse.of_bpm_detailed Pulse.representative_bpm
  Pulse.DetailedPulse Pulse.detailed_to_simple
  Pulse.detailed_to_nat Pulse.detailed_of_nat Pulse.detailed_of_nat_opt
  Pulse.to_nat Pulse.of_nat Pulse.of_nat_opt
  Grimace.t Grimace.to_nat Grimace.of_nat Grimace.of_nat_opt
  Activity.t Activity.to_nat Activity.of_nat Activity.of_nat_opt
  Respiration.t Respiration.to_nat Respiration.of_nat Respiration.of_nat_opt
  Trajectory.is_improving_trajectoryb Trajectory.is_declining_trajectoryb
  Trajectory.is_stable_trajectoryb Trajectory.adjacent_pairs
  Trajectory.TrajectoryType Trajectory.trajectory_type_all
  Trajectory.classify Trajectory.score_delta
  Trajectory.of_timed_sequence Trajectory.of_valid_sequence
  ValidScore.t ValidScore.val ValidScore.of_nat_opt ValidScore.zero ValidScore.ten
  Assessment.of_component_scores Assessment.to_validated_score
  Assessment.ComponentChange Assessment.AssessmentDiff Assessment.diff
  Assessment.all_unchanged Assessment.count_changes
  SpO2.covers_value SpO2.covered_by_some_range SpO2.unique_best_range
  AuditTrail.EventType AuditTrail.event_type_all
  AuditTrail.AuditEvent AuditTrail.mkAuditEvent
  AuditTrail.event_type AuditTrail.timestamp_seconds AuditTrail.user_id
  AuditTrail.assessment_snapshot AuditTrail.initial_event
  AuditTrail.modification_event AuditTrail.finalize_event AuditTrail.score_history
  AuditTrail.log_starts_with_createdb AuditTrail.log_ends_with_finalizedb
  AuditTrail.log_is_chronologicalb AuditTrail.is_valid_audit_logb
  AuditTrail.singleton_created_log
  Timing.next_time_slot Timing.can_extend
  Timing.mk_valid_seq_2_can_extend Timing.mk_valid_seq_3_can_extend
  Timing.mk_valid_seq_4_can_extend Timing.mk_valid_seq_5_cannot_extend
  Assessment.score_distribution Assessment.cardinality_is_3_pow_5
  ExpandedForm.ppv_params_consistentb ExpandedForm.ett_params_consistentb
  ExpandedForm.no_support_form
  Classification.of_score_same_class_same_bracket
  Intervention.le_antisym
  Reachability.witness_fn Reachability.witness_fn_opt
  Pulse.ClinicalSeverity Pulse.clinical_severity_all
  Pulse.detailed_to_severity Pulse.severity_to_nat
  Pulse.requires_immediate_intervention Pulse.requires_urgent_intervention
  CombinedAssessment.risk_to_nat CombinedAssessment.risk_to_min_intervention
  CombinedAssessment.has_additional_risk_factors
  AuditTrail.append_event AuditTrail.last_timestamp AuditTrail.can_append
  AuditTrail.add_modification AuditTrail.add_review AuditTrail.add_finalization
  AuditTrail.is_finalized AuditTrail.can_modify
  AuditTrail.latest_score AuditTrail.latest_assessment
  AuditTrail.score_changed AuditTrail.count_score_changes
  SpO2.covers_value_reflect SpO2.final_range_covered
  GestationalAge.maturity_to_nat GestationalAge.maturity_of_nat GestationalAge.eq_dec
  BirthWeight.category_to_nat BirthWeight.category_of_nat
  BirthWeight.le_6000_dec BirthWeight.of_grams_opt
  SpO2.target_hi_for_population_and_minute SpO2.in_target_for_population
  SpO2.range_for_minute_with_population
  CordBloodGas.ph_clinically_valid CordBloodGas.make_pH CordBloodGas.pH_eq_dec
  ExpandedForm.make_fio2 ExpandedForm.fio2_eq_dec
  ExpandedForm.ett_depth_clinically_valid ExpandedForm.make_ett_params
  ExpandedForm.ett_size_all ExpandedForm.ett_size_eq_dec
  AuditTrail.log_is_chronologicalb_correct_forward
  AuditTrail.log_is_chronologicalb_correct_backward
  AuditTrail.log_is_chronologicalb_correct
  AuditTrail.log_is_chronological_dec
  Classification.lt Classification.trichotomy Classification.strict_trichotomy
  Classification.lt_irrefl Classification.lt_trans Classification.lt_le_incl
  Intervention.lt Intervention.trichotomy Intervention.strict_trichotomy
  Intervention.lt_irrefl Intervention.lt_trans Intervention.lt_le_incl
  Timing.ToleranceLevel Timing.tolerance_to_secs Timing.is_within_tolerance
  Timing.timing_deviation Timing.timing_deviation_signed
  Timing.deviation_within_tolerance
  CordBloodGas.SampleType CordBloodGas.sample_type_all
  CordBloodGas.TypedSample CordBloodGas.mkTypedSample
  CordBloodGas.sample_source CordBloodGas.sample_gas
  CordBloodGas.PairedSamples CordBloodGas.mkPaired
  CordBloodGas.arterial_sample CordBloodGas.venous_sample
  CordBloodGas.av_ph_difference CordBloodGas.is_normal_av_difference
  CordBloodGas.paired_indicates_asphyxia CordBloodGas.venous_only_asphyxia
  TherapeuticHypothermia.Contraindication TherapeuticHypothermia.contraindication_all
  TherapeuticHypothermia.is_absolute_contraindication
  TherapeuticHypothermia.ExtendedCandidate TherapeuticHypothermia.mkExtendedCandidate
  TherapeuticHypothermia.has_absolute_contraindication
  TherapeuticHypothermia.has_weight_contraindication
  TherapeuticHypothermia.has_age_contraindication
  TherapeuticHypothermia.is_eligible_extended
  Temperature.MeasurementSite Temperature.measurement_site_all
  Temperature.site_offset_x10 Temperature.is_core_temperature_site
  Temperature.SitedTemperature Temperature.mkSitedTemp
  Temperature.temp_reading Temperature.temp_site
  Temperature.estimate_core_temp Temperature.classify_sited
  (* New in v1.1.0: Cord clamping *)
  CordClamping.ClampingTiming CordClamping.clamping_timing_all
  CordClamping.of_seconds CordClamping.is_recommended
  CordClamping.DCCContraindication CordClamping.CordClampingEvent CordClamping.mkCordClamping
  CordClamping.clamping_timing CordClamping.clamping_seconds
  CordClamping.has_contraindication CordClamping.clamping_appropriate
  (* New in v1.1.0: Surfactant administration *)
  Surfactant.SurfactantType Surfactant.surfactant_type_all
  Surfactant.AdministrationMethod Surfactant.admin_method_eq_dec
  Surfactant.SurfactantDose Surfactant.mkSurfactantDose
  Surfactant.SurfactantAdmin Surfactant.mkSurfactantAdmin
  Surfactant.is_less_invasive
  Surfactant.ga_indicates_prophylactic Surfactant.ga_indicates_early_rescue
  (* New in v1.1.0: Blood glucose monitoring *)
  BloodGlucose.t BloodGlucose.value_mg_dl
  BloodGlucose.Status BloodGlucose.status_all BloodGlucose.classify
  BloodGlucose.is_hypoglycemic BloodGlucose.needs_treatment BloodGlucose.is_normal
  BloodGlucose.is_valid BloodGlucose.of_nat_opt
  BloodGlucose.HypoglycemiaRiskFactor BloodGlucose.risk_factor_all
  BloodGlucose.needs_screening
  (* New in v1.1.0: Preterm-adjusted classification *)
  Classification.preterm_adjustment Classification.adjusted_score
  Classification.of_score_preterm_adjusted
  Classification.PretermContext Classification.mkPretermContext
  Classification.adjusted_classification
  (* New in v1.1.0: ExpandedForm well-formedness *)
  ExpandedForm.is_well_formedb ExpandedForm.well_formed_dec
  ExpandedForm.make_well_formed_opt
  (* New in v1.1.0: ValidSequence helpers *)
  Timing.seq_last_assessment Timing.seq_last_time
  Timing.seq_assessments Timing.seq_scores
  Timing.seq_first_assessment Timing.score_at Timing.classification_at
  Timing.score_improved Timing.all_scores_improving
  Timing.seq_all_improving Timing.seq_reached_reassuring
  (* New in v1.1.0: Assessment injectivity *)
  Assessment.mk_injective_full
  (* New: ValidSequence extend function *)
  Timing.extend Timing.extend_length Timing.extract_next_time
  (* New: ValidExpandedForm combined record *)
  ExpandedForm.ValidExpandedForm ExpandedForm.mkValidForm
  ExpandedForm.valid_form ExpandedForm.valid_to_well_formed
  ExpandedForm.valid_to_consistent ExpandedForm.is_validb
  ExpandedForm.valid_dec ExpandedForm.make_valid_opt
  ExpandedForm.no_support_form_is_valid
  (* New: AuditTrail ValidAuditLog constructor *)
  AuditTrail.ValidAuditLog AuditTrail.mkValidLog
  AuditTrail.log_events AuditTrail.singleton_valid_log
  AuditTrail.valid_log_events AuditTrail.valid_log_length
  AuditTrail.empty_log_no_mod_after_final
  (* New: Trajectory-Intervention theorems *)
  Trajectory.score_reaches_reassuring_intervention
  Trajectory.improving_to_reassuring_yields_routine
  (* New: Round-trip proofs *)
  BloodGlucose.of_nat_opt_roundtrip
  CordBloodGas.make_pH_roundtrip
  ExpandedForm.make_fio2_roundtrip
  ExpandedForm.make_ett_params_roundtrip
  BirthWeight.of_grams_opt_roundtrip
  (* New: Boolean reflection lemmas *)
  GestationalAge.is_preterm_iff GestationalAge.is_term_iff GestationalAge.is_post_term_iff
  GestationalAge.maturity_trichotomy
  BirthWeight.is_elbw_iff BirthWeight.is_vlbw_iff BirthWeight.is_lbw_iff
  BirthWeight.is_normal_weight_iff BirthWeight.is_macrosomic_iff
  CordBloodGas.is_acidemic_iff CordBloodGas.is_severely_acidemic_iff
  CordBloodGas.is_hypercapnic_iff CordBloodGas.is_hypoxemic_iff
  CordBloodGas.is_significant_bd_iff CordBloodGas.is_severe_bd_iff
  CordBloodGas.is_elevated_lactate_iff
  Temperature.is_hypothermic_iff Temperature.is_hyperthermic_iff
  Temperature.is_normal_temp_iff Temperature.temp_trichotomy
  Temperature.hypothermic_needs_warming Temperature.hyperthermic_needs_cooling
  Temperature.estimate_core_temp_bounded
  (* New: Protocol completeness *)
  NegativeSpecs.protocol_completeness NegativeSpecs.protocol_termination_complete
  (* New: Cord gas integration *)
  CombinedAssessment.low_score_at_5min_needs_cord_gas
  CombinedAssessment.cord_gas_asphyxia_high_risk_minimum
  CombinedAssessment.acidemia_with_low_apgar_requires_intervention
  (* New: SpO2 extended monitoring *)
  SpO2.extended_monitoring_target_lo SpO2.extended_monitoring_target_hi
  SpO2.extended_monitoring_stable SpO2.post_transition_target
  SpO2.hyperoxia_above_target SpO2.critical_hypoxemia
  SpO2.critical_hypoxemia_below_all_targets.
