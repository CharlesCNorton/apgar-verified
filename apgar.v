(******************************************************************************)
(*                                                                            *)
(*              APGAR Score: A Formal Verification of Neonatal Assessment     *)
(*                                                                            *)
(*     A machine-checked formalization of the APGAR scoring system for        *)
(*     rapid evaluation of newborn vitality. This development proves          *)
(*     completeness, boundedness, classification correctness, and             *)
(*     intervention protocol properties based on official AAP/ACOG            *)
(*     clinical guidelines.                                                   *)
(*                                                                            *)
(*     'Every baby born throughout the world is looked at first through       *)
(*      the eyes of Virginia Apgar.'                                          *)
(*     -- Joseph Butterfield, M.D., Pediatrics, 1994                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*                              REFERENCES                                    *)
(*                                                                            *)
(*  [Apgar1953]                                                               *)
(*     Apgar V. A proposal for a new method of evaluation of the newborn      *)
(*     infant. Curr Res Anesth Analg. 1953;32(4):260-267.                     *)
(*     PMID: 13083014                                                         *)
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
(*                                                                            *)
(*  [NRP2021]                                                                 *)
(*     Neonatal Resuscitation Program, 8th Edition.                           *)
(*     American Academy of Pediatrics, 2021.                                  *)
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
(*  5. TIMING SIMPLIFICATION: Real assessments may occur at non-standard      *)
(*     intervals. This formalization only models the standard 1, 5, 10,       *)
(*     15, and 20 minute timepoints per protocol.                             *)
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
Import ListNotations.

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

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 5: APGAR ASSESSMENT                             *)
(*                                                                            *)
(*  The complete assessment is a 5-tuple of component observations.           *)
(*  The total score is computed and proven bounded by construction.           *)
(*                                                                            *)
(******************************************************************************)

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

Definition ComponentIndex_of_nat (n : nat) : ComponentIndex :=
  match n with
  | 0 => IdxAppearance
  | 1 => IdxPulse
  | 2 => IdxGrimace
  | 3 => IdxActivity
  | _ => IdxRespiration
  end.

Lemma ComponentIndex_of_to_nat : forall ci,
  ComponentIndex_of_nat (ComponentIndex_to_nat ci) = ci.
Proof. intros []; reflexivity. Qed.

Lemma ComponentIndex_to_of_nat : forall n,
  n <= 4 -> ComponentIndex_to_nat (ComponentIndex_of_nat n) = n.
Proof.
  intros [|[|[|[|[|n]]]]] H; try reflexivity; lia.
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

End Reachability.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 6: CLINICAL CLASSIFICATION                      *)
(*                                                                            *)
(*  Classification of scores into clinical categories per [AAP2015].          *)
(*  We use a view type to make classification structurally evident.           *)
(*                                                                            *)
(******************************************************************************)

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

End Classification.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 7: INTERVENTION PROTOCOL                        *)
(*                                                                            *)
(*  Resuscitation guidelines based on [NRP2021].                              *)
(*  Each intervention level has a corresponding score range.                  *)
(*                                                                            *)
(******************************************************************************)

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

End Timing.

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

Record t : Type := mk {
  timed_assessment : Timing.TimedAssessment;
  resp_support : RespiratorySupport;
  chest_compressions : bool;
  epinephrine : bool
}.

Definition is_resuscitated (e : t) : bool :=
  match resp_support e with
  | NoSupport => chest_compressions e || epinephrine e
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
  chest_compressions e = true -> is_resuscitated e = true.
Proof.
  intros e H. unfold is_resuscitated.
  destruct (resp_support e); simpl; try reflexivity.
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
  chest_compressions e = false ->
  epinephrine e = false ->
  is_resuscitated e = false.
Proof.
  intros e Hresp Hcomp Hepi.
  unfold is_resuscitated. rewrite Hresp.
  rewrite Hcomp, Hepi. reflexivity.
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
    (mk (Timing.mkTimed Timing.Min1 Assessment.minimum) PPV false false) _).
  intro H. unfold underlying_classification. simpl. discriminate.
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

End Discontinuation.

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

Theorem resuscitation_implies_active_intervention : forall wf : ExpandedForm.WellFormedExpandedForm,
  ExpandedForm.is_resuscitated (ExpandedForm.form wf) = true ->
  Intervention.of_score (ExpandedForm.underlying_score (ExpandedForm.form wf)) <> Intervention.RoutineCare.
Proof.
  exact well_formed_intervention_consistency.
Qed.

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
  Classification.t Classification.of_score Classification.of_assessment
  Classification.to_nat Classification.of_nat
  Intervention.t Intervention.of_score Intervention.of_assessment
  Intervention.severity Intervention.of_nat
  Timing.Time Timing.TimedAssessment Timing.mkTimed
  Timing.time Timing.assessment Timing.should_continue Timing.next
  ExpandedForm.t ExpandedForm.mk ExpandedForm.RespiratorySupport
  ExpandedForm.timed_assessment ExpandedForm.resp_support
  ExpandedForm.chest_compressions ExpandedForm.epinephrine
  ExpandedForm.is_resuscitated
  ExpandedForm.underlying_score ExpandedForm.underlying_classification
  Discontinuation.criteria_considered Discontinuation.decide_discontinuation
  Pulse.of_bpm Pulse.of_bpm_detailed
  Pulse.DetailedPulse Pulse.detailed_to_simple
  Reachability.witness_fn.
