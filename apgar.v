(******************************************************************************)
(*                                                                            *)
(*          APGAR Score: A Formal Verification of Neonatal Assessment         *)
(*                                                                            *)
(*     The five-sign Apgar score per the AAP/ACOG statement: components,      *)
(*     bounded totals over the 243-assessment space, the score distribution,  *)
(*     partial assessments, classification, the timing rule and the           *)
(*     expanded reporting form. Delivery-room context per the Neonatal        *)
(*     Resuscitation Program, 8th and 9th editions: saturation targets,       *)
(*     initial oxygen, ventilation, chest compressions, epinephrine,          *)
(*     intubation and cessation of efforts, with the relation between the     *)
(*     total score and the indicated intervention. Therapeutic hypothermia    *)
(*     eligibility per the NICHD trial, score trajectories, an audit log,     *)
(*     and extraction to OCaml.                                               *)
(*                                                                            *)
(*     It has been said that every baby born in a modern hospital anywhere    *)
(*     in the world is looked at first through the eyes of Dr. Virginia       *)
(*     Apgar.                                                                 *)
(*     - National Library of Medicine, The Virginia Apgar Papers              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*                              REFERENCES                                    *)
(*                                                                            *)
(*  [Apgar1953]                                                               *)
(*     Apgar V. A proposal for a new method of evaluation of the newborn      *)
(*     infant. Curr Res Anesth Analg. 1953;32(4):260-267.                     *)
(*                                                                            *)
(*  [AAP2015]                                                                 *)
(*     American Academy of Pediatrics Committee on Fetus and Newborn,         *)
(*     American College of Obstetricians and Gynecologists Committee on       *)
(*     Obstetric Practice. The Apgar Score. Pediatrics. 2015;136(4):819-822.  *)
(*     doi:10.1542/peds.2015-2651. Issued jointly as ACOG Committee Opinion   *)
(*     No. 644, reaffirmed 2025.                                              *)
(*                                                                            *)
(*  [NRP8]                                                                    *)
(*     Weiner GM, Zaichkin J, eds. Textbook of Neonatal Resuscitation,        *)
(*     8th ed. American Academy of Pediatrics and American Heart              *)
(*     Association; 2021. ISBN 978-1-61002-524-9.                             *)
(*                                                                            *)
(*  [AHA2020]                                                                 *)
(*     Aziz K, Lee HC, Escobedo MB, et al. Part 5: Neonatal Resuscitation:    *)
(*     2020 American Heart Association Guidelines for Cardiopulmonary         *)
(*     Resuscitation and Emergency Cardiovascular Care. Circulation.          *)
(*     2020;142(suppl 2):S524-S550. doi:10.1161/CIR.0000000000000902          *)
(*                                                                            *)
(*  [NRP9]                                                                    *)
(*     Textbook of Neonatal Resuscitation, 9th ed. American Academy of        *)
(*     Pediatrics and American Heart Association; 2025. Differences from      *)
(*     the 8th edition are taken from Canadian Paediatric Society, NRP 9th    *)
(*     Edition: Canadian Practice Changes; 2026.                              *)
(*                                                                            *)
(*  [Kempley2008]                                                             *)
(*     Kempley ST, Moreiras JW, Petrone FL. Endotracheal tube length for      *)
(*     neonatal intubation. Resuscitation. 2008;77(3):369-373.                *)
(*                                                                            *)
(*  [WHO1997]                                                                 *)
(*     World Health Organization. Thermal protection of the newborn: a        *)
(*     practical guide. WHO/RHT/MSM/97.2; 1997.                               *)
(*                                                                            *)
(*  [WHO2023]                                                                 *)
(*     World Health Organization. Preterm birth. Fact sheet; 2023.            *)
(*                                                                            *)
(*  [ICD10]                                                                   *)
(*     World Health Organization. International Statistical Classification    *)
(*     of Diseases and Related Health Problems, 10th Revision, Volume 2:      *)
(*     Instruction Manual. Definitions of low, very low and extremely low     *)
(*     birth weight.                                                          *)
(*                                                                            *)
(*  [ACOG2013]                                                                *)
(*     ACOG Committee Opinion No. 579: Definition of term pregnancy.          *)
(*     Obstet Gynecol. 2013;122(5):1139-1140.                                 *)
(*                                                                            *)
(*  [ACOG2014]                                                                *)
(*     Executive summary: Neonatal Encephalopathy and Neurologic Outcome,     *)
(*     second edition. Obstet Gynecol. 2014;123(4):896-901.                   *)
(*                                                                            *)
(*  [Engle2007]                                                               *)
(*     Engle WA, Tomashek KM, Wallman C; Committee on Fetus and Newborn.      *)
(*     Late-preterm infants: a population at risk. Pediatrics.                *)
(*     2007;120(6):1390-1401.                                                 *)
(*                                                                            *)
(*  [Shankaran2005]                                                           *)
(*     Shankaran S, Laptook AR, Ehrenkranz RA, et al. Whole-body hypothermia  *)
(*     for neonates with hypoxic-ischemic encephalopathy. N Engl J Med.       *)
(*     2005;353(15):1574-1584.                                                *)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*                          UNITS AND ENCODINGS                               *)
(*                                                                            *)
(*  Quantities are natural numbers in fixed units: heart rate in beats per    *)
(*  minute, oxygen saturation and inspired oxygen in percent, temperature     *)
(*  in tenths of a degree Celsius, pH in hundredths, base deficit in tenths   *)
(*  of mmol/L, weight in grams, epinephrine in micrograms, volumes in         *)
(*  microlitres or millilitres as named, tube diameter in tenths of a         *)
(*  millimetre, tube depth in millimetres, time in seconds or minutes as      *)
(*  named. A bounded quantity is a RangedNat instance whose constructor       *)
(*  [make] rejects values outside its range; the ranges are input             *)
(*  plausibility limits and carry no clinical meaning.                        *)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*                            SCOPE OF THE MODEL                              *)
(*                                                                            *)
(*  1. HEART RATE AT 100. The score table of [AAP2015] lists heart rate       *)
(*     below 100 and above 100 per minute. A rate of exactly 100 is scored    *)
(*     2 here, matching the NRP action threshold of below 100.                *)
(*                                                                            *)
(*  2. TIMING. [AAP2015] reports the score at 1 and 5 minutes for all         *)
(*     infants and at 5-minute intervals thereafter until 20 minutes for      *)
(*     infants with a score less than 7. The rule is read as re-evaluated     *)
(*     at each interval: a score of 7 or more at 5 minutes or later ends      *)
(*     the series.                                                            *)
(*                                                                            *)
(*  3. CLASSIFICATION. [AAP2015] defines the bands 0-3, 4-6 and 7-10 for      *)
(*     the 5-minute score of term and late-preterm infants.                   *)
(*     [Classification.of_score] applies the same bands to any score as a     *)
(*     label; [ExpandedForm.five_minute_class] is defined only where the      *)
(*     source defines them.                                                   *)
(*                                                                            *)
(*  4. SATURATION TARGETS. The NRP table has rows for minutes 1 to 5 and      *)
(*     10 (minutes 2 to 5 and 10 in the 9th edition). For minutes 6 to 9      *)
(*     the model accepts the interval from the 5-minute lower bound to the    *)
(*     10-minute upper bound, and it applies the 10-minute row to later       *)
(*     minutes.                                                               *)
(*                                                                            *)
(*  5. TUBE SIZE. The 9th edition table assigns 2.5 mm below 1,200 g and      *)
(*     3.0 mm from 1,201 g; a weight of exactly 1,200 g is assigned 3.0 mm.   *)
(*                                                                            *)
(*  6. INTERVENTION. Per [AAP2015] the score is not used to determine the     *)
(*     need for resuscitation. The NRP module takes heart rate and            *)
(*     respiratory effort as inputs, and [ScoreAndResuscitation] states       *)
(*     what the total does and does not determine.                            *)
(*                                                                            *)
(*  7. THERAPEUTIC HYPOTHERMIA. The module encodes the physiological,         *)
(*     neurological and exclusion criteria of [Shankaran2005]. Consent and    *)
(*     the standardized examination itself are outside the model.             *)
(*                                                                            *)
(*  8. PROGNOSIS. Per [AAP2015] the score does not predict individual         *)
(*     mortality or neurologic outcome. Nothing here models outcome.          *)
(*                                                                            *)
(*  9. EXTRACTION. Natural numbers extract to OCaml int. Values of bounded    *)
(*     types are to be built with their [make] constructors.                  *)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*                               INTEGRATION                                  *)
(*                                                                            *)
(*  LOINC codes for the total score: 9272-6 (1 minute), 9274-2 (5 minutes),   *)
(*  9271-8 (10 minutes). Component and classification types serialize         *)
(*  through their [to_nat] and [of_nat_opt] functions.                        *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith List Bool Lia Eqdep_dec.
Import ListNotations.

(** Recursors are generated only for the inductive predicates that are used
    by induction; the data types are enumerations and records. *)
Unset Elimination Schemes.

(** Constants of three or more digits are written in the definitions with
    these factors, which keeps their unary representation and the extracted
    code small. [arith] is [lia] with the factors unfolded. *)
Definition hundred : nat := 10 * 10.
Definition thousand : nat := 10 * hundred.

Ltac arith := unfold thousand, hundred in *; lia.

(** [decide_thresholds] case-splits on every numeric comparison in the goal,
    records the outcome as an arithmetic fact and discards the cases whose
    facts are contradictory; [calc] simplifies without unfolding the
    comparisons, so that [decide_thresholds] finds them. [threshold_spec]
    then proves a conjunction of characterizations of the form
    [f x = c <-> P x] once [f x] has been reduced to a constructor. *)
Ltac decide_thresholds :=
  repeat (match goal with
  | |- context [?a <? ?b] =>
      let E := fresh "E" in
      destruct (a <? b) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]
  | |- context [?a <=? ?b] =>
      let E := fresh "E" in
      destruct (a <=? b) eqn:E; [apply Nat.leb_le in E | apply Nat.leb_gt in E]
  | |- context [?a =? ?b] =>
      let E := fresh "E" in
      destruct (a =? b) eqn:E; [apply Nat.eqb_eq in E | apply Nat.eqb_neq in E]
  end; cbv iota; try (exfalso; arith)).
Ltac calc :=
  cbn -[Nat.leb Nat.ltb Nat.eqb Nat.add Nat.mul Nat.div hundred thousand].
Ltac split_conj := repeat match goal with |- _ /\ _ => split end.
Ltac threshold_spec :=
  split_conj; split; intro; first [reflexivity | discriminate | arith].

(** [solve_cases] closes a goal built from equalities between constructors
    and arithmetic facts, after breaking up the hypotheses. *)
Ltac finish_cases :=
  first [ assumption | reflexivity | discriminate
        | match goal with
          | H : ?x <> ?x |- _ => exfalso; apply H; reflexivity
          end
        | arith
        | split; finish_cases | left; finish_cases | right; finish_cases ].
Ltac solve_cases :=
  intros;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         end;
  finish_cases.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 0: LIST HELPERS                                 *)
(*                                                                            *)
(*  Duplicate-freedom under map and flat_map, exhaustive enumerations, and    *)
(*  counting by injection and involution.                                     *)
(*                                                                            *)
(******************************************************************************)

Module ListHelpers.

Lemma NoDup_map_injective : forall {A B : Type} (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd. induction Hnd as [|a l' Hnotin Hnd IH]; simpl.
  - constructor.
  - constructor; [|exact IH].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Hfx Hx]].
    apply Hinj in Hfx. subst x. contradiction.
Qed.

Lemma NoDup_flat_map : forall {A B : Type} (f : A -> list B) (l : list A),
  NoDup l ->
  (forall a, NoDup (f a)) ->
  (forall a1 a2 b, a1 <> a2 -> In b (f a1) -> ~ In b (f a2)) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l Hnd Hinner Hdisj.
  induction Hnd as [|a l' Hnotin Hnd IH]; simpl.
  - constructor.
  - apply NoDup_app; [apply Hinner | exact IH |].
    intros b Hb1 Hb2. apply in_flat_map in Hb2. destruct Hb2 as [a' [Ha' Hb2]].
    apply (Hdisj a a' b); [|exact Hb1|exact Hb2].
    intro Heq. subst a'. contradiction.
Qed.

(** [enumerates l n]: the list [l] holds every inhabitant exactly once and
    has [n] elements. *)
Definition enumerates {A : Type} (l : list A) (n : nat) : Prop :=
  (forall a : A, In a l) /\ NoDup l /\ length l = n.

(** Number of elements of [l] satisfying [p]. *)
Definition count {A : Type} (p : A -> bool) (l : list A) : nat :=
  length (filter p l).

Lemma count_app : forall {A : Type} (p : A -> bool) (l1 l2 : list A),
  count p (l1 ++ l2) = count p l1 + count p l2.
Proof.
  intros A p l1 l2. unfold count. rewrite filter_app, length_app. reflexivity.
Qed.

Lemma count_ext : forall {A : Type} (p q : A -> bool) (l : list A),
  (forall a, p a = q a) -> count p l = count q l.
Proof.
  intros A p q l H. unfold count. rewrite (filter_ext p q H). reflexivity.
Qed.

Lemma count_map : forall {A B : Type} (f : A -> B) (p : B -> bool) (l : list A),
  count p (map f l) = count (fun a => p (f a)) l.
Proof.
  intros A B f p l. unfold count. induction l as [|a l' IH]; simpl.
  - reflexivity.
  - destruct (p (f a)); simpl; rewrite IH; reflexivity.
Qed.

Lemma count_false : forall {A : Type} (l : list A),
  count (fun _ => false) l = 0.
Proof.
  intros A l. unfold count.
  induction l as [|a l' IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma count_none : forall {A : Type} (p : A -> bool) (l : list A),
  (forall a, p a = false) -> count p l = 0.
Proof.
  intros A p l H. rewrite (count_ext p (fun _ => false) l H). apply count_false.
Qed.

Lemma count_le_of_injection : forall {A : Type} (p q : A -> bool) (f : A -> A)
    (l : list A),
  (forall a, In a l) -> NoDup l -> (forall x y, f x = f y -> x = y) ->
  (forall a, p a = true -> q (f a) = true) ->
  count p l <= count q l.
Proof.
  intros A p q f l Hall Hnd Hinj Hpq. unfold count.
  rewrite <- (length_map f (filter p l)).
  apply NoDup_incl_length.
  - apply NoDup_map_injective; [exact Hinj | apply NoDup_filter; exact Hnd].
  - intros b Hb. apply in_map_iff in Hb. destruct Hb as [a [Hfa Ha]].
    apply filter_In in Ha. destruct Ha as [_ Hpa].
    apply filter_In. split; [apply Hall | rewrite <- Hfa; apply Hpq; exact Hpa].
Qed.

(** An involution that carries [p] to [q] makes the two counts equal. *)
Lemma count_involution : forall {A : Type} (p q : A -> bool) (f : A -> A)
    (l : list A),
  (forall a, In a l) -> NoDup l -> (forall a, f (f a) = a) ->
  (forall a, q (f a) = p a) ->
  count p l = count q l.
Proof.
  intros A p q f l Hall Hnd Hinv Hpq.
  assert (Hinj : forall x y, f x = f y -> x = y).
  { intros x y H. rewrite <- (Hinv x), <- (Hinv y), H. reflexivity. }
  apply Nat.le_antisymm.
  - apply (count_le_of_injection p q f l Hall Hnd Hinj).
    intros a Ha. rewrite Hpq. exact Ha.
  - apply (count_le_of_injection q p f l Hall Hnd Hinj).
    intros a Ha. rewrite <- Hpq, Hinv. exact Ha.
Qed.

End ListHelpers.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 1: RANGED NATURAL NUMBERS                       *)
(*                                                                            *)
(*  A natural number carried with a boolean proof that it lies in a closed    *)
(*  range. Each bounded quantity instantiates this functor, which supplies    *)
(*  the validating constructor and its specification.                         *)
(*                                                                            *)
(******************************************************************************)

Module Type BOUNDS.
  Parameter lo hi : nat.
End BOUNDS.

Module RangedNat (Import B : BOUNDS).

Definition in_range (n : nat) : bool := (lo <=? n) && (n <=? hi).

Record t : Type := mk {
  value : nat;
  value_ok : in_range value = true
}.

Lemma in_range_iff : forall n, in_range n = true <-> lo <= n <= hi.
Proof.
  intros n. unfold in_range.
  rewrite andb_true_iff, !Nat.leb_le. reflexivity.
Qed.

Lemma value_bounds : forall r : t, lo <= value r <= hi.
Proof. intros [v p]. simpl. apply in_range_iff. exact p. Qed.

Lemma value_inj : forall r1 r2 : t, value r1 = value r2 -> r1 = r2.
Proof.
  intros [v1 p1] [v2 p2] H. simpl in H. subst v2.
  f_equal. apply UIP_dec. apply bool_dec.
Qed.

Definition eq_dec : forall r1 r2 : t, {r1 = r2} + {r1 <> r2}.
Proof.
  intros r1 r2. destruct (Nat.eq_dec (value r1) (value r2)) as [E|N].
  - left. apply value_inj. exact E.
  - right. intro H. apply N. rewrite H. reflexivity.
Defined.

(** Validating constructor. *)
Definition make (n : nat) : option t :=
  match bool_dec (in_range n) true with
  | left pf => Some (mk n pf)
  | right _ => None
  end.

Lemma make_some : forall n r, make n = Some r -> value r = n.
Proof.
  intros n r H. unfold make in H.
  destruct (bool_dec (in_range n) true) as [pf|pf]; [|discriminate].
  inversion H. reflexivity.
Qed.

Lemma make_accepts : forall n, (exists r, make n = Some r) <-> lo <= n <= hi.
Proof.
  intros n. unfold make. split.
  - intros [r H].
    destruct (bool_dec (in_range n) true) as [pf|pf]; [|discriminate].
    apply in_range_iff. exact pf.
  - intros H. destruct (bool_dec (in_range n) true) as [pf|pf].
    + eexists. reflexivity.
    + exfalso. apply pf. apply in_range_iff. exact H.
Qed.

Lemma make_rejects : forall n, make n = None <-> n < lo \/ hi < n.
Proof.
  intros n. split.
  - intros H. destruct (le_lt_dec lo n) as [Hlo|Hlo]; [|left; exact Hlo].
    destruct (le_lt_dec n hi) as [Hhi|Hhi]; [|right; exact Hhi].
    assert (Hex : exists r, make n = Some r) by (apply make_accepts; lia).
    destruct Hex as [r Hr]. rewrite Hr in H. discriminate.
  - intros H. destruct (make n) as [r|] eqn:E; [|reflexivity].
    assert (Hin : lo <= n <= hi) by (apply make_accepts; exists r; exact E).
    lia.
Qed.

Lemma make_value : forall r : t, make (value r) = Some r.
Proof.
  intros r. unfold make.
  destruct (bool_dec (in_range (value r)) true) as [pf|pf].
  - f_equal. apply value_inj. reflexivity.
  - exfalso. apply pf. exact (value_ok r).
Qed.

End RangedNat.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 2: SCORE LEVEL                                  *)
(*                                                                            *)
(*  Each sign of the Apgar score is graded 0, 1 or 2 [Apgar1953].             *)
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

Definition of_nat_opt (n : nat) : option t :=
  match n with
  | 0 => Some Zero
  | 1 => Some One
  | 2 => Some Two
  | _ => None
  end.

Definition eq_dec : forall s1 s2 : t, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Zero; One; Two].

Lemma all_enumerates : ListHelpers.enumerates all 3.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Lemma to_nat_bound : forall s, to_nat s <= 2.
Proof. intros []; simpl; lia. Qed.

Lemma to_nat_inj : forall s1 s2, to_nat s1 = to_nat s2 -> s1 = s2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

Lemma of_nat_opt_spec : forall n s, of_nat_opt n = Some s <-> to_nat s = n.
Proof.
  intros n s. split.
  - destruct n as [|[|[|n]]]; simpl; intro H; inversion H; reflexivity.
  - intro H. subst n. destruct s; reflexivity.
Qed.

Lemma of_nat_opt_none : forall n, of_nat_opt n = None <-> 2 < n.
Proof.
  intros n. destruct n as [|[|[|n]]]; simpl; split; intro H;
    try discriminate; try lia; reflexivity.
Qed.

(** The complement exchanges the grades 0 and 2. *)
Definition complement (s : t) : t :=
  match s with
  | Zero => Two
  | One => One
  | Two => Zero
  end.

Lemma complement_involutive : forall s, complement (complement s) = s.
Proof. intros []; reflexivity. Qed.

Lemma complement_to_nat : forall s, to_nat (complement s) + to_nat s = 2.
Proof. intros []; reflexivity. Qed.

End ScoreLevel.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 3: THE FIVE SIGNS                               *)
(*                                                                            *)
(*  Each sign has three findings in bijection with the score levels. A sign   *)
(*  module supplies its findings and the bijection; ComponentTheory derives   *)
(*  the numeric encoding, the enumeration and decidable equality. Finding     *)
(*  names follow the score table of [AAP2015]; module names follow the        *)
(*  acronym.                                                                  *)
(*                                                                            *)
(******************************************************************************)

Module Type COMPONENT_BASE.
  Parameter t : Type.
  Parameter to_score : t -> ScoreLevel.t.
  Parameter of_score : ScoreLevel.t -> t.
  Parameter of_to_score : forall x : t, of_score (to_score x) = x.
  Parameter to_of_score : forall s : ScoreLevel.t, to_score (of_score s) = s.
End COMPONENT_BASE.

Module ComponentTheory (Import B : COMPONENT_BASE).

Definition to_nat (x : t) : nat := ScoreLevel.to_nat (to_score x).

Definition of_nat_opt (n : nat) : option t :=
  option_map of_score (ScoreLevel.of_nat_opt n).

Definition all : list t := map of_score ScoreLevel.all.

Definition complement (x : t) : t :=
  of_score (ScoreLevel.complement (to_score x)).

Lemma to_score_inj : forall x y : t, to_score x = to_score y -> x = y.
Proof.
  intros x y H. rewrite <- (of_to_score x), <- (of_to_score y), H. reflexivity.
Qed.

Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (ScoreLevel.eq_dec (to_score x) (to_score y)) as [E|N].
  - left. apply to_score_inj. exact E.
  - right. intro H. apply N. rewrite H. reflexivity.
Defined.

Lemma all_enumerates : ListHelpers.enumerates all 3.
Proof.
  destruct ScoreLevel.all_enumerates as [Hc [Hn Hl]].
  unfold ListHelpers.enumerates, all. repeat split.
  - intros x. rewrite <- (of_to_score x). apply in_map. apply Hc.
  - apply ListHelpers.NoDup_map_injective; [|exact Hn].
    intros s1 s2 H. rewrite <- (to_of_score s1), <- (to_of_score s2), H.
    reflexivity.
Qed.

Lemma to_nat_bound : forall x : t, to_nat x <= 2.
Proof. intros x. apply ScoreLevel.to_nat_bound. Qed.

Lemma to_nat_inj : forall x y : t, to_nat x = to_nat y -> x = y.
Proof.
  intros x y H. apply to_score_inj. apply ScoreLevel.to_nat_inj. exact H.
Qed.

Lemma of_nat_opt_spec : forall n x, of_nat_opt n = Some x <-> to_nat x = n.
Proof.
  intros n x. unfold of_nat_opt, to_nat. split.
  - intro H. destruct (ScoreLevel.of_nat_opt n) as [s|] eqn:E; simpl in H;
      [|discriminate].
    inversion H. rewrite to_of_score. apply ScoreLevel.of_nat_opt_spec. exact E.
  - intro H. apply ScoreLevel.of_nat_opt_spec in H. rewrite H. simpl.
    rewrite of_to_score. reflexivity.
Qed.

Lemma of_nat_opt_none : forall n, of_nat_opt n = None <-> 2 < n.
Proof.
  intros n. unfold of_nat_opt. rewrite <- ScoreLevel.of_nat_opt_none.
  destruct (ScoreLevel.of_nat_opt n); simpl; split; intro H;
    (reflexivity || discriminate).
Qed.

Lemma of_nat_opt_to_nat : forall x : t, of_nat_opt (to_nat x) = Some x.
Proof. intros x. apply of_nat_opt_spec. reflexivity. Qed.

Lemma complement_involutive : forall x : t, complement (complement x) = x.
Proof.
  intros x. unfold complement.
  rewrite to_of_score, ScoreLevel.complement_involutive. apply of_to_score.
Qed.

Lemma complement_to_nat : forall x : t, to_nat (complement x) + to_nat x = 2.
Proof.
  intros x. unfold complement, to_nat. rewrite to_of_score.
  apply ScoreLevel.complement_to_nat.
Qed.

End ComponentTheory.

(** Color. *)
Module Appearance.

Inductive Finding : Type :=
  | BlueOrPale : Finding
  | Acrocyanotic : Finding
  | CompletelyPink : Finding.

Definition t : Type := Finding.

Definition to_score (a : t) : ScoreLevel.t :=
  match a with
  | BlueOrPale => ScoreLevel.Zero
  | Acrocyanotic => ScoreLevel.One
  | CompletelyPink => ScoreLevel.Two
  end.

Definition of_score (s : ScoreLevel.t) : t :=
  match s with
  | ScoreLevel.Zero => BlueOrPale
  | ScoreLevel.One => Acrocyanotic
  | ScoreLevel.Two => CompletelyPink
  end.

Lemma of_to_score : forall x : t, of_score (to_score x) = x.
Proof. intros []; reflexivity. Qed.

Lemma to_of_score : forall s : ScoreLevel.t, to_score (of_score s) = s.
Proof. intros []; reflexivity. Qed.

Include ComponentTheory.

End Appearance.

(** Heart rate. *)
Module Pulse.

Inductive Finding : Type :=
  | Absent : Finding
  | Below100 : Finding
  | AtLeast100 : Finding.

Definition t : Type := Finding.

Definition to_score (p : t) : ScoreLevel.t :=
  match p with
  | Absent => ScoreLevel.Zero
  | Below100 => ScoreLevel.One
  | AtLeast100 => ScoreLevel.Two
  end.

Definition of_score (s : ScoreLevel.t) : t :=
  match s with
  | ScoreLevel.Zero => Absent
  | ScoreLevel.One => Below100
  | ScoreLevel.Two => AtLeast100
  end.

Lemma of_to_score : forall x : t, of_score (to_score x) = x.
Proof. intros []; reflexivity. Qed.

Lemma to_of_score : forall s : ScoreLevel.t, to_score (of_score s) = s.
Proof. intros []; reflexivity. Qed.

Include ComponentTheory.

(** Finding from a measured rate in beats per minute. *)
Definition of_bpm (bpm : nat) : t :=
  if bpm =? 0 then Absent
  else if bpm <? hundred then Below100
  else AtLeast100.

Theorem of_bpm_spec : forall bpm,
  (of_bpm bpm = Absent <-> bpm = 0) /\
  (of_bpm bpm = Below100 <-> 0 < bpm < 100) /\
  (of_bpm bpm = AtLeast100 <-> 100 <= bpm).
Proof.
  intros bpm. unfold of_bpm. decide_thresholds; threshold_spec.
Qed.

(** Heart-rate bands at the NRP action thresholds of 60 and 100 per minute
    [NRP8]. *)
Inductive Band : Type :=
  | BandAbsent : Band
  | BandBelow60 : Band
  | Band60to99 : Band
  | BandAtLeast100 : Band.

Definition band_eq_dec : forall b1 b2 : Band, {b1 = b2} + {b1 <> b2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition band_all : list Band :=
  [BandAbsent; BandBelow60; Band60to99; BandAtLeast100].

Lemma band_all_enumerates : ListHelpers.enumerates band_all 4.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Definition band_of_bpm (bpm : nat) : Band :=
  if bpm =? 0 then BandAbsent
  else if bpm <? 60 then BandBelow60
  else if bpm <? hundred then Band60to99
  else BandAtLeast100.

Theorem band_of_bpm_spec : forall bpm,
  (band_of_bpm bpm = BandAbsent <-> bpm = 0) /\
  (band_of_bpm bpm = BandBelow60 <-> 0 < bpm < 60) /\
  (band_of_bpm bpm = Band60to99 <-> 60 <= bpm < 100) /\
  (band_of_bpm bpm = BandAtLeast100 <-> 100 <= bpm).
Proof.
  intros bpm. unfold band_of_bpm. decide_thresholds; threshold_spec.
Qed.

(** The band refines the scored finding. *)
Definition of_band (b : Band) : t :=
  match b with
  | BandAbsent => Absent
  | BandBelow60 => Below100
  | Band60to99 => Below100
  | BandAtLeast100 => AtLeast100
  end.

Theorem band_refines_finding : forall bpm,
  of_band (band_of_bpm bpm) = of_bpm bpm.
Proof.
  intros bpm. unfold band_of_bpm, of_bpm.
  decide_thresholds; reflexivity.
Qed.

Definition band_rank (b : Band) : nat :=
  match b with
  | BandAbsent => 0
  | BandBelow60 => 1
  | Band60to99 => 2
  | BandAtLeast100 => 3
  end.

Theorem band_of_bpm_monotone : forall b1 b2,
  b1 <= b2 -> band_rank (band_of_bpm b1) <= band_rank (band_of_bpm b2).
Proof.
  intros b1 b2 Hle. unfold band_of_bpm.
  decide_thresholds; simpl; arith.
Qed.

(** Heart rate estimated by counting beats for six seconds and multiplying
    by ten [NRP8]. The action thresholds fall at counts of 6 and 10. *)
Definition bpm_of_six_second_count (beats : nat) : nat := 10 * beats.

Theorem six_second_count_spec : forall beats,
  (band_of_bpm (bpm_of_six_second_count beats) = BandAbsent <-> beats = 0) /\
  (band_of_bpm (bpm_of_six_second_count beats) = BandBelow60 <->
     1 <= beats <= 5) /\
  (band_of_bpm (bpm_of_six_second_count beats) = Band60to99 <->
     6 <= beats <= 9) /\
  (band_of_bpm (bpm_of_six_second_count beats) = BandAtLeast100 <->
     10 <= beats).
Proof.
  intros beats.
  destruct (band_of_bpm_spec (bpm_of_six_second_count beats))
    as [H0 [H1 [H2 H3]]].
  unfold bpm_of_six_second_count in *.
  rewrite H0, H1, H2, H3. split_conj; split; intro; lia.
Qed.

End Pulse.

(** Reflex irritability. *)
Module Grimace.

Inductive Finding : Type :=
  | NoResponse : Finding
  | GrimaceOnly : Finding
  | CryOrWithdrawal : Finding.

Definition t : Type := Finding.

Definition to_score (g : t) : ScoreLevel.t :=
  match g with
  | NoResponse => ScoreLevel.Zero
  | GrimaceOnly => ScoreLevel.One
  | CryOrWithdrawal => ScoreLevel.Two
  end.

Definition of_score (s : ScoreLevel.t) : t :=
  match s with
  | ScoreLevel.Zero => NoResponse
  | ScoreLevel.One => GrimaceOnly
  | ScoreLevel.Two => CryOrWithdrawal
  end.

Lemma of_to_score : forall x : t, of_score (to_score x) = x.
Proof. intros []; reflexivity. Qed.

Lemma to_of_score : forall s : ScoreLevel.t, to_score (of_score s) = s.
Proof. intros []; reflexivity. Qed.

Include ComponentTheory.

End Grimace.

(** Muscle tone. *)
Module Activity.

Inductive Finding : Type :=
  | Limp : Finding
  | SomeFlexion : Finding
  | ActiveMotion : Finding.

Definition t : Type := Finding.

Definition to_score (a : t) : ScoreLevel.t :=
  match a with
  | Limp => ScoreLevel.Zero
  | SomeFlexion => ScoreLevel.One
  | ActiveMotion => ScoreLevel.Two
  end.

Definition of_score (s : ScoreLevel.t) : t :=
  match s with
  | ScoreLevel.Zero => Limp
  | ScoreLevel.One => SomeFlexion
  | ScoreLevel.Two => ActiveMotion
  end.

Lemma of_to_score : forall x : t, of_score (to_score x) = x.
Proof. intros []; reflexivity. Qed.

Lemma to_of_score : forall s : ScoreLevel.t, to_score (of_score s) = s.
Proof. intros []; reflexivity. Qed.

Include ComponentTheory.

End Activity.

(** Respiratory effort. *)
Module Respiration.

Inductive Finding : Type :=
  | Absent : Finding
  | WeakCry : Finding
  | GoodCry : Finding.

Definition t : Type := Finding.

Definition to_score (r : t) : ScoreLevel.t :=
  match r with
  | Absent => ScoreLevel.Zero
  | WeakCry => ScoreLevel.One
  | GoodCry => ScoreLevel.Two
  end.

Definition of_score (s : ScoreLevel.t) : t :=
  match s with
  | ScoreLevel.Zero => Absent
  | ScoreLevel.One => WeakCry
  | ScoreLevel.Two => GoodCry
  end.

Lemma of_to_score : forall x : t, of_score (to_score x) = x.
Proof. intros []; reflexivity. Qed.

Lemma to_of_score : forall s : ScoreLevel.t, to_score (of_score s) = s.
Proof. intros []; reflexivity. Qed.

Include ComponentTheory.

End Respiration.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 4: ASSESSMENT                                   *)
(*                                                                            *)
(*  An assessment is one finding per sign; its total is the sum of the five   *)
(*  grades [Apgar1953]. The section enumerates the 243 assessments, fixes     *)
(*  the range of the total, counts the assessments at each total, and bounds  *)
(*  the change in total by the number of signs that differ.                   *)
(*                                                                            *)
(******************************************************************************)

(** Tuples of grades and the coefficients of (1 + x + x^2)^n that count
    them by sum. *)
Module Trinomial.

(** All lists of length [n] over the grades 0, 1 and 2. *)
Fixpoint tuples (n : nat) : list (list nat) :=
  match n with
  | 0 => [[]]
  | S n' =>
      map (cons 0) (tuples n') ++ map (cons 1) (tuples n')
        ++ map (cons 2) (tuples n')
  end.

(** [coeff n k] is the coefficient of x^k in (1 + x + x^2)^n. *)
Fixpoint coeff (n k : nat) : nat :=
  match n with
  | 0 => match k with 0 => 1 | S _ => 0 end
  | S n' =>
      coeff n' k
      + match k with 0 => 0 | S k1 => coeff n' k1 end
      + match k with S (S k2) => coeff n' k2 | _ => 0 end
  end.

Definition has_sum (k : nat) (l : list nat) : bool := list_sum l =? k.

Lemma tuples_length : forall n, length (tuples n) = 3 ^ n.
Proof.
  induction n as [|n' IH]; [reflexivity|].
  simpl tuples. rewrite !length_app, !length_map, IH, Nat.pow_succ_r'. lia.
Qed.

Lemma count_cons : forall s k T,
  ListHelpers.count (has_sum k) (map (cons s) T) =
  ListHelpers.count (fun l => s + list_sum l =? k) T.
Proof. intros s k T. rewrite ListHelpers.count_map. reflexivity. Qed.

(** The number of [n]-tuples of grades with sum [k] is the coefficient of
    x^k in (1 + x + x^2)^n. *)
Theorem count_tuples : forall n k,
  ListHelpers.count (has_sum k) (tuples n) = coeff n k.
Proof.
  induction n as [|n' IH]; intros k.
  - destruct k; reflexivity.
  - simpl tuples.
    rewrite !ListHelpers.count_app, !count_cons, Nat.add_assoc.
    simpl coeff. f_equal; [f_equal|].
    + rewrite <- IH. apply ListHelpers.count_ext. intros l. reflexivity.
    + destruct k as [|k1].
      * apply ListHelpers.count_none. intros l. reflexivity.
      * rewrite <- IH. apply ListHelpers.count_ext. intros l. reflexivity.
    + destruct k as [|[|k2]].
      * apply ListHelpers.count_none. intros l. reflexivity.
      * apply ListHelpers.count_none. intros l. reflexivity.
      * rewrite <- IH. apply ListHelpers.count_ext. intros l. reflexivity.
Qed.

Lemma coeff_zero_above : forall n k, 2 * n < k -> coeff n k = 0.
Proof.
  induction n as [|n' IH]; intros k Hk.
  - destruct k; [lia | reflexivity].
  - destruct k as [|[|k2]]; try lia. simpl coeff.
    rewrite (IH (S (S k2))), (IH (S k2)), (IH k2) by lia. reflexivity.
Qed.

End Trinomial.

Module Assessment.

Record t : Type := mk {
  appearance : Appearance.t;
  pulse : Pulse.t;
  grimace : Grimace.t;
  activity : Activity.t;
  respiration : Respiration.t
}.

(** Grades of the five signs in the order of the acronym. *)
Definition scores (a : t) : list nat :=
  [Appearance.to_nat (appearance a); Pulse.to_nat (pulse a);
   Grimace.to_nat (grimace a); Activity.to_nat (activity a);
   Respiration.to_nat (respiration a)].

Definition total (a : t) : nat := list_sum (scores a).

Theorem total_le_10 : forall a : t, total a <= 10.
Proof.
  intros [ap pu gr ac re]. unfold total, scores. simpl.
  pose proof (Appearance.to_nat_bound ap).
  pose proof (Pulse.to_nat_bound pu).
  pose proof (Grimace.to_nat_bound gr).
  pose proof (Activity.to_nat_bound ac).
  pose proof (Respiration.to_nat_bound re).
  lia.
Qed.

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

(** Validated construction from five grades. *)
Definition of_nats_opt (ap pu gr ac re : nat) : option t :=
  match Appearance.of_nat_opt ap, Pulse.of_nat_opt pu, Grimace.of_nat_opt gr,
        Activity.of_nat_opt ac, Respiration.of_nat_opt re with
  | Some a, Some p, Some g, Some c, Some r => Some (mk a p g c r)
  | _, _, _, _, _ => None
  end.

Theorem of_nats_opt_spec : forall ap pu gr ac re a,
  of_nats_opt ap pu gr ac re = Some a <-> scores a = [ap; pu; gr; ac; re].
Proof.
  intros ap pu gr ac re a. split.
  - unfold of_nats_opt. intro H.
    destruct (Appearance.of_nat_opt ap) as [x1|] eqn:E1; simpl in H;
      [|discriminate].
    destruct (Pulse.of_nat_opt pu) as [x2|] eqn:E2; simpl in H;
      [|discriminate].
    destruct (Grimace.of_nat_opt gr) as [x3|] eqn:E3; simpl in H;
      [|discriminate].
    destruct (Activity.of_nat_opt ac) as [x4|] eqn:E4; simpl in H;
      [|discriminate].
    destruct (Respiration.of_nat_opt re) as [x5|] eqn:E5; simpl in H;
      [|discriminate].
    inversion H. unfold scores. simpl.
    apply Appearance.of_nat_opt_spec in E1. apply Pulse.of_nat_opt_spec in E2.
    apply Grimace.of_nat_opt_spec in E3. apply Activity.of_nat_opt_spec in E4.
    apply Respiration.of_nat_opt_spec in E5.
    rewrite E1, E2, E3, E4, E5. reflexivity.
  - unfold scores. intro H. injection H as <- <- <- <- <-.
    unfold of_nats_opt.
    rewrite Appearance.of_nat_opt_to_nat, Pulse.of_nat_opt_to_nat,
      Grimace.of_nat_opt_to_nat, Activity.of_nat_opt_to_nat,
      Respiration.of_nat_opt_to_nat.
    destruct a; reflexivity.
Qed.

(** ** Enumeration *)

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

Local Ltac disjoint_blocks :=
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  intros ? ? ? ? H1 H2;
  repeat (apply in_flat_map in H1; destruct H1 as [? [_ H1]]);
  repeat (apply in_flat_map in H2; destruct H2 as [? [_ H2]]);
  apply in_map_iff in H1; apply in_map_iff in H2;
  destruct H1 as [? [H1 _]]; destruct H2 as [? [H2 _]];
  rewrite <- H1 in H2; congruence.

Theorem all_enumerates : ListHelpers.enumerates all 243.
Proof.
  destruct Appearance.all_enumerates as [Cap [Nap _]].
  destruct Pulse.all_enumerates as [Cpu [Npu _]].
  destruct Grimace.all_enumerates as [Cgr [Ngr _]].
  destruct Activity.all_enumerates as [Cac [Nac _]].
  destruct Respiration.all_enumerates as [Cre [Nre _]].
  unfold ListHelpers.enumerates. split; [|split].
  - intros [ap pu gr ac re]. unfold all.
    apply in_flat_map. exists ap. split; [apply Cap|].
    apply in_flat_map. exists pu. split; [apply Cpu|].
    apply in_flat_map. exists gr. split; [apply Cgr|].
    apply in_flat_map. exists ac. split; [apply Cac|].
    apply in_map. apply Cre.
  - unfold all.
    apply ListHelpers.NoDup_flat_map; [exact Nap | | disjoint_blocks].
    intros ap.
    apply ListHelpers.NoDup_flat_map; [exact Npu | | disjoint_blocks].
    intros pu.
    apply ListHelpers.NoDup_flat_map; [exact Ngr | | disjoint_blocks].
    intros gr.
    apply ListHelpers.NoDup_flat_map; [exact Nac | | disjoint_blocks].
    intros ac. apply ListHelpers.NoDup_map_injective; [|exact Nre].
    intros r1 r2 H. congruence.
  - reflexivity.
Qed.

(** ** Range of the total *)

Definition minimum : t :=
  mk Appearance.BlueOrPale Pulse.Absent Grimace.NoResponse
     Activity.Limp Respiration.Absent.

Definition maximum : t :=
  mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.CryOrWithdrawal
     Activity.ActiveMotion Respiration.GoodCry.

Theorem total_zero_iff : forall a : t, total a = 0 <-> a = minimum.
Proof.
  intros a. split.
  - destruct a as [[] [] [] [] []]; intro H; try reflexivity;
      cbv in H; discriminate H.
  - intro H. subst a. reflexivity.
Qed.

Theorem total_ten_iff : forall a : t, total a = 10 <-> a = maximum.
Proof.
  intros a. split.
  - destruct a as [[] [] [] [] []]; intro H; try reflexivity;
      cbv in H; discriminate H.
  - intro H. subst a. reflexivity.
Qed.

(** An assessment with each total from 0 to 10. *)
Definition witness (n : nat) : t :=
  match n with
  | 0 => minimum
  | 1 => mk Appearance.Acrocyanotic Pulse.Absent Grimace.NoResponse
            Activity.Limp Respiration.Absent
  | 2 => mk Appearance.CompletelyPink Pulse.Absent Grimace.NoResponse
            Activity.Limp Respiration.Absent
  | 3 => mk Appearance.CompletelyPink Pulse.Below100 Grimace.NoResponse
            Activity.Limp Respiration.Absent
  | 4 => mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.NoResponse
            Activity.Limp Respiration.Absent
  | 5 => mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.GrimaceOnly
            Activity.Limp Respiration.Absent
  | 6 => mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.CryOrWithdrawal
            Activity.Limp Respiration.Absent
  | 7 => mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.CryOrWithdrawal
            Activity.SomeFlexion Respiration.Absent
  | 8 => mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.CryOrWithdrawal
            Activity.ActiveMotion Respiration.Absent
  | 9 => mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.CryOrWithdrawal
            Activity.ActiveMotion Respiration.WeakCry
  | _ => maximum
  end.

(** The totals are exactly the numbers 0 to 10. *)
Theorem total_range : forall n, (exists a : t, total a = n) <-> n <= 10.
Proof.
  intros n. split.
  - intros [a H]. subst n. apply total_le_10.
  - intros H. exists (witness n).
    do 11 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

(** ** Distribution of the total *)

Definition count_with_total (k : nat) : nat :=
  ListHelpers.count (fun a => total a =? k) all.

Lemma scores_all : map scores all = Trinomial.tuples 5.
Proof. vm_compute. reflexivity. Qed.

(** The number of assessments with total [k] is the coefficient of x^k in
    (1 + x + x^2)^5. *)
Theorem distribution : forall k, count_with_total k = Trinomial.coeff 5 k.
Proof.
  intros k. unfold count_with_total.
  rewrite <- Trinomial.count_tuples, <- scores_all, ListHelpers.count_map.
  reflexivity.
Qed.

Theorem distribution_table :
  map count_with_total (seq 0 11) = [1; 5; 15; 30; 45; 51; 45; 30; 15; 5; 1].
Proof. vm_compute. reflexivity. Qed.

(** The complement of an assessment exchanges the grades 0 and 2 of every
    sign. *)
Definition complement (a : t) : t :=
  mk (Appearance.complement (appearance a)) (Pulse.complement (pulse a))
     (Grimace.complement (grimace a)) (Activity.complement (activity a))
     (Respiration.complement (respiration a)).

Lemma complement_involutive : forall a : t, complement (complement a) = a.
Proof.
  intros [ap pu gr ac re]. unfold complement. simpl.
  rewrite Appearance.complement_involutive, Pulse.complement_involutive,
    Grimace.complement_involutive, Activity.complement_involutive,
    Respiration.complement_involutive.
  reflexivity.
Qed.

Lemma complement_total : forall a : t, total (complement a) + total a = 10.
Proof.
  intros [ap pu gr ac re]. unfold total, scores, complement. simpl.
  pose proof (Appearance.complement_to_nat ap).
  pose proof (Pulse.complement_to_nat pu).
  pose proof (Grimace.complement_to_nat gr).
  pose proof (Activity.complement_to_nat ac).
  pose proof (Respiration.complement_to_nat re).
  lia.
Qed.

(** The distribution is symmetric about 5, by the complement involution. *)
Theorem distribution_symmetric : forall k,
  k <= 10 -> count_with_total k = count_with_total (10 - k).
Proof.
  intros k Hk. unfold count_with_total.
  destruct all_enumerates as [Hc [Hn _]].
  apply (ListHelpers.count_involution _ _ complement all Hc Hn
           complement_involutive).
  intros a. pose proof (complement_total a) as Ht.
  pose proof (total_le_10 a) as Hb.
  destruct (total a =? k) eqn:E.
  - apply Nat.eqb_eq in E. apply Nat.eqb_eq. lia.
  - apply Nat.eqb_neq in E. apply Nat.eqb_neq. lia.
Qed.

(** The count rises strictly up to total 5, where it is greatest. *)
Theorem distribution_increasing : forall k,
  k < 5 -> count_with_total k < count_with_total (S k).
Proof.
  intros k Hk. rewrite !distribution.
  do 5 (destruct k as [|k]; [vm_compute; lia|]). lia.
Qed.

Theorem distribution_mode : forall k,
  count_with_total k <= count_with_total 5.
Proof.
  intros k. rewrite !distribution.
  do 11 (destruct k as [|k]; [vm_compute; lia|]).
  rewrite Trinomial.coeff_zero_above by lia. lia.
Qed.

(** Totals 0 and 10 identify the assessment; every total from 1 to 9 is
    shared by at least five assessments. *)
Theorem interior_totals_shared : forall k,
  1 <= k <= 9 -> 5 <= count_with_total k.
Proof.
  intros k [Hlo Hhi]. rewrite distribution.
  do 10 (destruct k as [|k]; [try lia; vm_compute; lia|]). lia.
Qed.

(** ** Signs and the distance between assessments *)

Inductive Sign : Type :=
  | Color : Sign
  | HeartRate : Sign
  | ReflexIrritability : Sign
  | MuscleTone : Sign
  | RespiratoryEffort : Sign.

Definition sign_eq_dec : forall s1 s2 : Sign, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition sign_all : list Sign :=
  [Color; HeartRate; ReflexIrritability; MuscleTone; RespiratoryEffort].

Lemma sign_all_enumerates : ListHelpers.enumerates sign_all 5.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto 6.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Definition score_of (s : Sign) (a : t) : nat :=
  match s with
  | Color => Appearance.to_nat (appearance a)
  | HeartRate => Pulse.to_nat (pulse a)
  | ReflexIrritability => Grimace.to_nat (grimace a)
  | MuscleTone => Activity.to_nat (activity a)
  | RespiratoryEffort => Respiration.to_nat (respiration a)
  end.

Lemma scores_by_sign : forall a : t,
  scores a = map (fun s => score_of s a) sign_all.
Proof. intros a. reflexivity. Qed.

(** Signs graded differently in two assessments. *)
Definition changed (a1 a2 : t) : list Sign :=
  filter (fun s => negb (score_of s a1 =? score_of s a2)) sign_all.

Definition hamming (a1 a2 : t) : nat := length (changed a1 a2).

Theorem changed_spec : forall a1 a2 s,
  In s (changed a1 a2) <-> score_of s a1 <> score_of s a2.
Proof.
  intros a1 a2 s. unfold changed.
  rewrite filter_In, negb_true_iff, Nat.eqb_neq. split.
  - intros [_ H]. exact H.
  - intro H. split; [apply sign_all_enumerates | exact H].
Qed.

Theorem hamming_le_5 : forall a1 a2, hamming a1 a2 <= 5.
Proof. intros a1 a2. unfold hamming, changed. apply filter_length_le. Qed.

Theorem hamming_zero_iff : forall a1 a2, hamming a1 a2 = 0 <-> a1 = a2.
Proof.
  intros a1 a2. split.
  - intro H. unfold hamming in H. apply length_zero_iff_nil in H.
    assert (Hs : forall s, score_of s a1 = score_of s a2).
    { intros s.
      destruct (Nat.eq_dec (score_of s a1) (score_of s a2)) as [E|N];
        [exact E|].
      apply changed_spec in N. rewrite H in N. contradiction. }
    pose proof (Hs Color) as H1. pose proof (Hs HeartRate) as H2.
    pose proof (Hs ReflexIrritability) as H3. pose proof (Hs MuscleTone) as H4.
    pose proof (Hs RespiratoryEffort) as H5.
    destruct a1 as [ap1 pu1 gr1 ac1 re1], a2 as [ap2 pu2 gr2 ac2 re2].
    simpl in H1, H2, H3, H4, H5.
    apply Appearance.to_nat_inj in H1. apply Pulse.to_nat_inj in H2.
    apply Grimace.to_nat_inj in H3. apply Activity.to_nat_inj in H4.
    apply Respiration.to_nat_inj in H5.
    rewrite H1, H2, H3, H4, H5. reflexivity.
  - intro H. subst a2. apply ListHelpers.count_none.
    intros s. rewrite Nat.eqb_refl. reflexivity.
Qed.

Definition distance (m n : nat) : nat := (m - n) + (n - m).

(** The total moves by at most two points for each sign that differs. *)
Theorem total_lipschitz : forall a1 a2,
  distance (total a1) (total a2) <= 2 * hamming a1 a2.
Proof.
  intros [ap1 pu1 gr1 ac1 re1] [ap2 pu2 gr2 ac2 re2].
  unfold distance, hamming, changed, total, scores. simpl.
  pose proof (Appearance.to_nat_bound ap1).
  pose proof (Appearance.to_nat_bound ap2).
  pose proof (Pulse.to_nat_bound pu1). pose proof (Pulse.to_nat_bound pu2).
  pose proof (Grimace.to_nat_bound gr1). pose proof (Grimace.to_nat_bound gr2).
  pose proof (Activity.to_nat_bound ac1).
  pose proof (Activity.to_nat_bound ac2).
  pose proof (Respiration.to_nat_bound re1).
  pose proof (Respiration.to_nat_bound re2).
  destruct (Appearance.to_nat ap1 =? Appearance.to_nat ap2) eqn:E1;
  destruct (Pulse.to_nat pu1 =? Pulse.to_nat pu2) eqn:E2;
  destruct (Grimace.to_nat gr1 =? Grimace.to_nat gr2) eqn:E3;
  destruct (Activity.to_nat ac1 =? Activity.to_nat ac2) eqn:E4;
  destruct (Respiration.to_nat re1 =? Respiration.to_nat re2) eqn:E5;
  simpl;
  repeat match goal with
  | E : (_ =? _) = true |- _ => apply Nat.eqb_eq in E
  | E : (_ =? _) = false |- _ => apply Nat.eqb_neq in E
  end; lia.
Qed.

(** The bound is attained: one sign can move the total by two. *)
Theorem total_lipschitz_tight :
  exists a1 a2, hamming a1 a2 = 1 /\ distance (total a1) (total a2) = 2.
Proof.
  exists minimum, (witness 2). split; reflexivity.
Qed.

End Assessment.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 5: CLASSIFICATION                               *)
(*                                                                            *)
(*  [AAP2015]: a 5-minute score of 7 to 10 is reassuring, 4 to 6 moderately   *)
(*  abnormal and 0 to 3 low, in the term and late-preterm infant.             *)
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

Lemma all_enumerates : ListHelpers.enumerates all 3.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Definition of_score (score : nat) : t :=
  if score <=? 3 then Low
  else if score <=? 6 then ModeratelyAbnormal
  else Reassuring.

Definition of_assessment (a : Assessment.t) : t :=
  of_score (Assessment.total a).

Theorem of_score_spec : forall s,
  (of_score s = Low <-> s <= 3) /\
  (of_score s = ModeratelyAbnormal <-> 4 <= s <= 6) /\
  (of_score s = Reassuring <-> 7 <= s).
Proof.
  intros s. unfold of_score.
  destruct (s <=? 3) eqn:E1.
  - apply Nat.leb_le in E1. threshold_spec.
  - apply Nat.leb_gt in E1. destruct (s <=? 6) eqn:E2.
    + apply Nat.leb_le in E2. threshold_spec.
    + apply Nat.leb_gt in E2. threshold_spec.
Qed.

(** Score interval of each class. *)
Definition range (c : t) : nat * nat :=
  match c with
  | Low => (0, 3)
  | ModeratelyAbnormal => (4, 6)
  | Reassuring => (7, 10)
  end.

Theorem range_spec : forall c s,
  s <= 10 -> (of_score s = c <-> fst (range c) <= s <= snd (range c)).
Proof.
  intros c s Hs. destruct (of_score_spec s) as [L [M R]].
  destruct c; simpl; [rewrite L | rewrite M | rewrite R]; lia.
Qed.

(** ** Serialization *)

Definition to_nat (c : t) : nat :=
  match c with
  | Low => 0
  | ModeratelyAbnormal => 1
  | Reassuring => 2
  end.

Definition of_nat_opt (n : nat) : option t :=
  match n with
  | 0 => Some Low
  | 1 => Some ModeratelyAbnormal
  | 2 => Some Reassuring
  | _ => None
  end.

Lemma of_nat_opt_spec : forall n c, of_nat_opt n = Some c <-> to_nat c = n.
Proof.
  intros n c. split.
  - destruct n as [|[|[|n]]]; simpl; intro H; inversion H; reflexivity.
  - intro H. subst n. destruct c; reflexivity.
Qed.

(** ** Order *)

Definition le (c1 c2 : t) : Prop := to_nat c1 <= to_nat c2.

Lemma le_refl : forall c, le c c.
Proof. intros c. unfold le. lia. Qed.

Lemma le_trans : forall c1 c2 c3, le c1 c2 -> le c2 c3 -> le c1 c3.
Proof. intros c1 c2 c3. unfold le. lia. Qed.

Lemma le_antisym : forall c1 c2, le c1 c2 -> le c2 c1 -> c1 = c2.
Proof. intros [] []; unfold le; simpl; intros H1 H2; try reflexivity; lia. Qed.

Lemma le_total : forall c1 c2, le c1 c2 \/ le c2 c1.
Proof. intros c1 c2. unfold le. lia. Qed.

(** A higher score never yields a lower class. *)
Theorem of_score_monotone : forall s1 s2,
  s1 <= s2 -> le (of_score s1) (of_score s2).
Proof.
  intros s1 s2 H. unfold le, of_score.
  destruct (s1 <=? 3) eqn:A1; destruct (s1 <=? 6) eqn:A2;
  destruct (s2 <=? 3) eqn:B1; destruct (s2 <=? 6) eqn:B2; simpl; try lia;
  repeat match goal with
  | E : (_ <=? _) = true |- _ => apply Nat.leb_le in E
  | E : (_ <=? _) = false |- _ => apply Nat.leb_gt in E
  end; lia.
Qed.

(** The class changes between consecutive scores exactly at 3 and at 6. *)
Theorem class_changes_iff : forall s,
  of_score s <> of_score (S s) <-> s = 3 \/ s = 6.
Proof.
  intros s. destruct (of_score_spec s) as [L [M R]].
  destruct (of_score_spec (S s)) as [L' [M' R']]. split.
  - intro Hne.
    destruct (le_lt_dec s 2);
      [exfalso; apply Hne; rewrite (proj2 L), (proj2 L') by lia; reflexivity|].
    destruct (Nat.eq_dec s 3); [left; assumption|].
    destruct (le_lt_dec s 5);
      [exfalso; apply Hne; rewrite (proj2 M), (proj2 M') by lia; reflexivity|].
    destruct (Nat.eq_dec s 6); [right; assumption|].
    exfalso. apply Hne. rewrite (proj2 R), (proj2 R') by lia. reflexivity.
  - intros [H|H]; subst s; simpl; discriminate.
Qed.

End Classification.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 6: PARTIAL ASSESSMENT                           *)
(*                                                                            *)
(*  An assessment in which some signs were not observed. The total of any     *)
(*  completion lies between the bounds obtained by grading each missing       *)
(*  sign 0 and 2, every value between the bounds is the total of some         *)
(*  completion, and the class is determined exactly when both bounds fall     *)
(*  in the same class.                                                        *)
(*                                                                            *)
(******************************************************************************)

Module PartialAssessment.

Record t : Type := mk {
  appearance : option Appearance.t;
  pulse : option Pulse.t;
  grimace : option Grimace.t;
  activity : option Activity.t;
  respiration : option Respiration.t
}.

Definition of_assessment (a : Assessment.t) : t :=
  mk (Some (Assessment.appearance a)) (Some (Assessment.pulse a))
     (Some (Assessment.grimace a)) (Some (Assessment.activity a))
     (Some (Assessment.respiration a)).

Definition agrees {A : Type} (o : option A) (x : A) : Prop :=
  match o with
  | Some y => x = y
  | None => True
  end.

(** [completes pa a]: the assessment [a] has every observed finding of
    [pa]. *)
Definition completes (pa : t) (a : Assessment.t) : Prop :=
  agrees (appearance pa) (Assessment.appearance a) /\
  agrees (pulse pa) (Assessment.pulse a) /\
  agrees (grimace pa) (Assessment.grimace a) /\
  agrees (activity pa) (Assessment.activity a) /\
  agrees (respiration pa) (Assessment.respiration a).

Definition lower {A : Type} (to_nat : A -> nat) (o : option A) : nat :=
  match o with
  | Some x => to_nat x
  | None => 0
  end.

Definition upper {A : Type} (to_nat : A -> nat) (o : option A) : nat :=
  match o with
  | Some x => to_nat x
  | None => 2
  end.

Definition unobserved {A : Type} (o : option A) : nat :=
  match o with
  | Some _ => 0
  | None => 1
  end.

Definition score_min (pa : t) : nat :=
  lower Appearance.to_nat (appearance pa) + lower Pulse.to_nat (pulse pa)
  + lower Grimace.to_nat (grimace pa) + lower Activity.to_nat (activity pa)
  + lower Respiration.to_nat (respiration pa).

Definition score_max (pa : t) : nat :=
  upper Appearance.to_nat (appearance pa) + upper Pulse.to_nat (pulse pa)
  + upper Grimace.to_nat (grimace pa) + upper Activity.to_nat (activity pa)
  + upper Respiration.to_nat (respiration pa).

(** Number of signs not observed. *)
Definition missing (pa : t) : nat :=
  unobserved (appearance pa) + unobserved (pulse pa) + unobserved (grimace pa)
  + unobserved (activity pa) + unobserved (respiration pa).

Lemma lower_le_upper : forall {A : Type} (to_nat : A -> nat) (o : option A),
  lower to_nat o <= upper to_nat o.
Proof. intros A to_nat [x|]; simpl; lia. Qed.

Lemma upper_lower : forall {A : Type} (to_nat : A -> nat) (o : option A),
  upper to_nat o = lower to_nat o + 2 * unobserved o.
Proof. intros A to_nat [x|]; simpl; lia. Qed.

(** Each missing sign widens the interval by two points. *)
Theorem width : forall pa, score_max pa = score_min pa + 2 * missing pa.
Proof.
  intros pa. unfold score_max, score_min, missing.
  rewrite !upper_lower. lia.
Qed.

Theorem completion_bounds : forall pa a,
  completes pa a -> score_min pa <= Assessment.total a <= score_max pa.
Proof.
  intros [oa op og oc or] [ap pu gr ac re] [H1 [H2 [H3 [H4 H5]]]].
  unfold score_min, score_max, Assessment.total, Assessment.scores.
  simpl in *.
  pose proof (Appearance.to_nat_bound ap).
  pose proof (Pulse.to_nat_bound pu).
  pose proof (Grimace.to_nat_bound gr).
  pose proof (Activity.to_nat_bound ac).
  pose proof (Respiration.to_nat_bound re).
  destruct oa; destruct op; destruct og; destruct oc; destruct or;
    simpl in *; subst; lia.
Qed.

Lemma split_sum : forall l u L U n,
  l <= u -> L <= U -> l + L <= n <= u + U ->
  exists d r, l <= d <= u /\ L <= r <= U /\ d + r = n.
Proof.
  intros l u L U n Hlu HLU Hn.
  exists (Nat.min u (n - L)), (n - Nat.min u (n - L)). lia.
Qed.

Lemma fill : forall {A : Type} (to_nat : A -> nat)
    (of_nat_opt : nat -> option A),
  (forall n x, of_nat_opt n = Some x <-> to_nat x = n) ->
  (forall n, of_nat_opt n = None <-> 2 < n) ->
  forall (o : option A) d,
  lower to_nat o <= d <= upper to_nat o ->
  exists x, agrees o x /\ to_nat x = d.
Proof.
  intros A to_nat of_nat_opt Hspec Hnone o d Hd.
  destruct o as [y|]; simpl in Hd.
  - exists y. split; [reflexivity | lia].
  - destruct (of_nat_opt d) as [x|] eqn:E.
    + exists x. split; [exact I | apply Hspec; exact E].
    + apply Hnone in E. lia.
Qed.

(** The totals of the completions are exactly the interval from
    [score_min] to [score_max]. *)
Theorem interval_exact : forall pa n,
  score_min pa <= n <= score_max pa <->
  exists a, completes pa a /\ Assessment.total a = n.
Proof.
  intros pa n. split.
  - intros Hn. destruct pa as [oa op og oc or].
    unfold score_min, score_max in Hn. simpl in Hn.
    pose proof (lower_le_upper Appearance.to_nat oa) as B1.
    pose proof (lower_le_upper Pulse.to_nat op) as B2.
    pose proof (lower_le_upper Grimace.to_nat og) as B3.
    pose proof (lower_le_upper Activity.to_nat oc) as B4.
    pose proof (lower_le_upper Respiration.to_nat or) as B5.
    destruct (split_sum (lower Appearance.to_nat oa)
                (upper Appearance.to_nat oa)
                (lower Pulse.to_nat op + lower Grimace.to_nat og
                 + lower Activity.to_nat oc + lower Respiration.to_nat or)
                (upper Pulse.to_nat op + upper Grimace.to_nat og
                 + upper Activity.to_nat oc + upper Respiration.to_nat or) n)
      as [d1 [r1 [D1 [R1 E1]]]]; [lia | lia | lia |].
    destruct (split_sum (lower Pulse.to_nat op) (upper Pulse.to_nat op)
                (lower Grimace.to_nat og + lower Activity.to_nat oc
                 + lower Respiration.to_nat or)
                (upper Grimace.to_nat og + upper Activity.to_nat oc
                 + upper Respiration.to_nat or) r1)
      as [d2 [r2 [D2 [R2 E2]]]]; [lia | lia | lia |].
    destruct (split_sum (lower Grimace.to_nat og) (upper Grimace.to_nat og)
                (lower Activity.to_nat oc + lower Respiration.to_nat or)
                (upper Activity.to_nat oc + upper Respiration.to_nat or) r2)
      as [d3 [r3 [D3 [R3 E3]]]]; [lia | lia | lia |].
    destruct (split_sum (lower Activity.to_nat oc) (upper Activity.to_nat oc)
                (lower Respiration.to_nat or) (upper Respiration.to_nat or) r3)
      as [d4 [d5 [D4 [D5 E4]]]]; [lia | lia | lia |].
    destruct (fill Appearance.to_nat Appearance.of_nat_opt
                Appearance.of_nat_opt_spec Appearance.of_nat_opt_none oa d1 D1)
      as [x1 [A1 T1]].
    destruct (fill Pulse.to_nat Pulse.of_nat_opt
                Pulse.of_nat_opt_spec Pulse.of_nat_opt_none op d2 D2)
      as [x2 [A2 T2]].
    destruct (fill Grimace.to_nat Grimace.of_nat_opt
                Grimace.of_nat_opt_spec Grimace.of_nat_opt_none og d3 D3)
      as [x3 [A3 T3]].
    destruct (fill Activity.to_nat Activity.of_nat_opt
                Activity.of_nat_opt_spec Activity.of_nat_opt_none oc d4 D4)
      as [x4 [A4 T4]].
    destruct (fill Respiration.to_nat Respiration.of_nat_opt
                Respiration.of_nat_opt_spec Respiration.of_nat_opt_none
                or d5 D5)
      as [x5 [A5 T5]].
    exists (Assessment.mk x1 x2 x3 x4 x5). split.
    + unfold completes. simpl.
      split; [exact A1 | split; [exact A2 | split; [exact A3 | split;
        [exact A4 | exact A5]]]].
    + unfold Assessment.total, Assessment.scores. simpl. lia.
  - intros [a [Hc Ht]]. subst n. apply completion_bounds. exact Hc.
Qed.

(** All completions fall in one class exactly when the two bounds do. *)
Theorem class_determined_iff : forall pa,
  (forall a1 a2, completes pa a1 -> completes pa a2 ->
     Classification.of_assessment a1 = Classification.of_assessment a2) <->
  Classification.of_score (score_min pa) =
  Classification.of_score (score_max pa).
Proof.
  intros pa. pose proof (width pa) as Hw. split.
  - intros H.
    destruct (proj1 (interval_exact pa (score_min pa))) as [a1 [C1 T1]];
      [lia|].
    destruct (proj1 (interval_exact pa (score_max pa))) as [a2 [C2 T2]];
      [lia|].
    specialize (H a1 a2 C1 C2). unfold Classification.of_assessment in H.
    rewrite T1, T2 in H. exact H.
  - intros Heq a1 a2 C1 C2.
    apply completion_bounds in C1. apply completion_bounds in C2.
    unfold Classification.of_assessment.
    assert (Hclass : forall n, score_min pa <= n <= score_max pa ->
              Classification.of_score n =
              Classification.of_score (score_min pa)).
    { intros n [Hlo Hhi]. apply Classification.le_antisym.
      - rewrite Heq. apply Classification.of_score_monotone. exact Hhi.
      - apply Classification.of_score_monotone. exact Hlo. }
    rewrite (Hclass _ C1), (Hclass _ C2). reflexivity.
Qed.

(** A fully observed assessment is its own only completion. *)
Theorem of_assessment_complete : forall a a',
  completes (of_assessment a) a' <-> a' = a.
Proof.
  intros [ap pu gr ac re] [ap' pu' gr' ac' re']. unfold completes. simpl.
  split.
  - intros [H1 [H2 [H3 [H4 H5]]]]. subst. reflexivity.
  - intro H. inversion H. repeat split.
Qed.

End PartialAssessment.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 7: TIMING                                       *)
(*                                                                            *)
(*  [AAP2015]: the score is reported at 1 minute and 5 minutes after birth    *)
(*  for all infants, and at 5-minute intervals thereafter until 20 minutes    *)
(*  for infants with a score less than 7. The section gives the rule as a     *)
(*  function of the scores observed, a declarative description of the         *)
(*  series it produces, and a decision procedure for that description.        *)
(*                                                                            *)
(******************************************************************************)

Module Timing.

Inductive Time : Type :=
  | Min1 : Time
  | Min5 : Time
  | Min10 : Time
  | Min15 : Time
  | Min20 : Time.

Definition eq_dec : forall t1 t2 : Time, {t1 = t2} + {t1 <> t2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list Time := [Min1; Min5; Min10; Min15; Min20].

Lemma all_enumerates : ListHelpers.enumerates all 5.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto 6.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Definition to_minutes (t : Time) : nat :=
  match t with
  | Min1 => 1
  | Min5 => 5
  | Min10 => 10
  | Min15 => 15
  | Min20 => 20
  end.

Definition to_seconds (t : Time) : nat := 60 * to_minutes t.

Lemma to_minutes_inj : forall t1 t2, to_minutes t1 = to_minutes t2 -> t1 = t2.
Proof. intros [] [] H; try reflexivity; discriminate. Qed.

(** Whether a further score is due after the score at time [t]. The
    5-minute score follows the 1-minute score for every infant; from 5
    minutes on a further score is due while the score is below 7, and none
    after 20 minutes. *)
Definition continues (t : Time) (score : nat) : bool :=
  match t with
  | Min1 => true
  | Min5 | Min10 | Min15 => score <? 7
  | Min20 => false
  end.

Record Timed : Type := mkTimed {
  time : Time;
  assessment : Assessment.t
}.

(** ** The series produced by the rule *)

(** [scan ts obs] records the assessment [obs t] at each time of [ts] in
    turn, for as long as the rule calls for a further score. *)
Fixpoint scan (ts : list Time) (obs : Time -> Assessment.t) : list Timed :=
  match ts with
  | [] => []
  | t :: ts' =>
      mkTimed t (obs t) ::
      (if continues t (Assessment.total (obs t)) then scan ts' obs else [])
  end.

Definition series (obs : Time -> Assessment.t) : list Timed := scan all obs.

Definition score_at (obs : Time -> Assessment.t) (t : Time) : nat :=
  Assessment.total (obs t).

(** The 1- and 5-minute scores are always present, and the series has
    between two and five scores according to where the score first
    reaches 7. *)
Theorem series_length_spec : forall obs,
  (length (series obs) = 2 <-> 7 <= score_at obs Min5) /\
  (length (series obs) = 3 <->
     score_at obs Min5 < 7 /\ 7 <= score_at obs Min10) /\
  (length (series obs) = 4 <->
     score_at obs Min5 < 7 /\ score_at obs Min10 < 7 /\
     7 <= score_at obs Min15) /\
  (length (series obs) = 5 <->
     score_at obs Min5 < 7 /\ score_at obs Min10 < 7 /\
     score_at obs Min15 < 7).
Proof.
  intros obs. unfold series, all, score_at. cbn [scan continues].
  decide_thresholds; cbn [length]; threshold_spec.
Qed.

(** A series that ends before 20 minutes ends on a score of 7 or more. *)
Theorem series_ends_at_7_or_20 : forall obs,
  length (series obs) < 5 ->
  7 <= Assessment.total
         (assessment (last (series obs) (mkTimed Min1 (obs Min1)))).
Proof.
  intros obs. unfold series, all. cbn [scan continues].
  decide_thresholds; cbn [length last assessment]; intro H; lia.
Qed.

(** Every score from 5 minutes on that is followed by another is below 7. *)
Theorem series_interior_below_7 : forall obs i,
  1 <= i -> S i < length (series obs) ->
  Assessment.total
    (assessment (nth i (series obs) (mkTimed Min1 (obs Min1)))) < 7.
Proof.
  intros obs i. unfold series, all. cbn [scan continues].
  decide_thresholds; cbn [length]; intros H1 H2;
    do 4 (destruct i as [|i]; [cbn [nth assessment]; lia|]); lia.
Qed.

(** ** Declarative description *)

(** [Follows ts l]: the series [l] takes its times from [ts] in order, each
    score but the last calls for a further score, and the last does not. *)
Set Elimination Schemes.
Inductive Follows : list Time -> list Timed -> Prop :=
  | follows_stop : forall t ts a,
      continues t (Assessment.total a) = false ->
      Follows (t :: ts) [mkTimed t a]
  | follows_step : forall t ts a rest,
      continues t (Assessment.total a) = true ->
      Follows ts rest ->
      Follows (t :: ts) (mkTimed t a :: rest).
Unset Elimination Schemes.

Definition Valid (l : list Timed) : Prop := Follows all l.

Lemma scan_follows : forall ts obs,
  ts <> [] -> (forall s, continues (last ts Min20) s = false) ->
  Follows ts (scan ts obs).
Proof.
  induction ts as [|t ts' IH]; intros obs Hne Hlast.
  - contradiction.
  - cbn [scan]. destruct (continues t (Assessment.total (obs t))) eqn:E.
    + apply follows_step; [exact E|].
      destruct ts' as [|t' ts''].
      * simpl in Hlast. rewrite Hlast in E. discriminate.
      * apply IH; [discriminate | exact Hlast].
    + apply follows_stop. exact E.
Qed.

Lemma scan_ext : forall ts obs1 obs2,
  (forall x, In x ts -> obs1 x = obs2 x) -> scan ts obs1 = scan ts obs2.
Proof.
  induction ts as [|t ts' IH]; intros obs1 obs2 H; cbn [scan].
  - reflexivity.
  - rewrite (H t (or_introl eq_refl)).
    rewrite (IH obs1 obs2) by (intros x Hx; apply H; right; exact Hx).
    reflexivity.
Qed.

Lemma follows_scan : forall ts l,
  Follows ts l -> NoDup ts -> exists obs, scan ts obs = l.
Proof.
  intros ts l H.
  induction H as [t ts a Hstop | t ts a rest Hcont Hrest IH]; intros Hnd.
  - exists (fun _ => a). cbn [scan]. rewrite Hstop. reflexivity.
  - assert (Hnotin : ~ In t ts) by (inversion Hnd; assumption).
    assert (Hnd' : NoDup ts) by (inversion Hnd; assumption).
    destruct (IH Hnd') as [obs' Hobs'].
    exists (fun x => if eq_dec x t then a else obs' x). cbn [scan].
    destruct (eq_dec t t) as [_|N]; [|contradiction].
    rewrite Hcont. f_equal. rewrite <- Hobs'. apply scan_ext.
    intros x Hx. destruct (eq_dec x t) as [E|_]; [|reflexivity].
    subst x. contradiction.
Qed.

(** The series produced by the rule are exactly the valid ones. *)
Theorem valid_iff_series : forall l,
  Valid l <-> exists obs, series obs = l.
Proof.
  intros l. split.
  - intro H. apply (follows_scan all l H). apply all_enumerates.
  - intros [obs H]. subst l. apply scan_follows; [discriminate|].
    intros s. reflexivity.
Qed.

Lemma follows_shape : forall ts l,
  Follows ts l ->
  map time l = firstn (length l) ts /\ 1 <= length l <= length ts.
Proof.
  intros ts l H.
  induction H as [t ts a Hstop | t ts a rest Hcont Hrest [IHt IHl]].
  - simpl. split; [reflexivity | lia].
  - simpl. split; [rewrite IHt; reflexivity | lia].
Qed.

Lemma follows_cons_inv : forall t ts x rest,
  Follows (t :: ts) (x :: rest) ->
  time x = t /\
  ((rest = [] /\ continues t (Assessment.total (assessment x)) = false) \/
   (continues t (Assessment.total (assessment x)) = true /\ Follows ts rest)).
Proof. intros t ts x rest H. inversion H; subst; simpl; split; auto. Qed.

(** A valid series holds between two and five scores, taken at the
    standard times in order. *)
Theorem valid_shape : forall l,
  Valid l -> map time l = firstn (length l) all /\ 2 <= length l <= 5.
Proof.
  intros l H. destruct (follows_shape all l H) as [Ht Hl].
  split; [exact Ht|]. split; [|exact (proj2 Hl)].
  unfold Valid, all in H. inversion H as [? ? ? Hstop | ? ? ? ? Hcont Hrest].
  - discriminate Hstop.
  - destruct (follows_shape _ _ Hrest) as [_ Hl']. simpl. lia.
Qed.

(** ** Decision procedure *)

Fixpoint followsb (ts : list Time) (l : list Timed) : bool :=
  match ts, l with
  | t :: ts', x :: rest =>
      (if eq_dec (time x) t then true else false) &&
      (if continues t (Assessment.total (assessment x))
       then followsb ts' rest
       else match rest with [] => true | _ :: _ => false end)
  | _, _ => false
  end.

Lemma followsb_correct : forall ts l, followsb ts l = true <-> Follows ts l.
Proof.
  induction ts as [|t ts' IH]; intros l.
  - simpl. split; [discriminate | intro H; inversion H].
  - destruct l as [|[t0 a] rest].
    + simpl. split; [discriminate | intro H; inversion H].
    + cbn [followsb time assessment]. split.
      * intro H. apply andb_true_iff in H. destruct H as [Ht Hc].
        destruct (eq_dec t0 t) as [E|N]; [subst t0 | discriminate].
        destruct (continues t (Assessment.total a)) eqn:Ec.
        -- apply follows_step; [exact Ec | apply IH; exact Hc].
        -- destruct rest; [apply follows_stop; exact Ec | discriminate].
      * intro H. inversion H; subst;
          match goal with
          | |- context [eq_dec ?x ?y] =>
              destruct (eq_dec x y) as [_|N]; [|contradiction]
          end;
          match goal with
          | Hc : continues _ _ = _ |- _ => rewrite Hc
          end.
        -- reflexivity.
        -- simpl. apply IH. assumption.
Qed.

Definition validb (l : list Timed) : bool := followsb all l.

Theorem validb_correct : forall l, validb l = true <-> Valid l.
Proof. intros l. apply followsb_correct. Qed.

End Timing.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 8: PHYSIOLOGICAL CONTEXT                        *)
(*                                                                            *)
(*  Gestational age, birth weight, oxygen saturation, temperature and cord    *)
(*  blood gas, each with the categories and thresholds of its source.         *)
(*                                                                            *)
(******************************************************************************)

(** Edition of the Neonatal Resuscitation Program whose values are used
    where the 8th and 9th editions differ. *)
Module Edition.

Inductive t : Type :=
  | NRP8 : t
  | NRP9 : t.

Definition eq_dec : forall e1 e2 : t, {e1 = e2} + {e1 <> e2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [NRP8; NRP9].

Lemma all_enumerates : ListHelpers.enumerates all 2.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto.
  - repeat constructor; simpl; intuition discriminate.
Qed.

End Edition.

(** Gestational age in completed weeks and days. Preterm subcategories
    follow [WHO2023] and term subcategories [ACOG2013]; late preterm is
    34 0/7 to 36 6/7 weeks [Engle2007]. *)
Module GestationalAge.

Module Weeks.
  Definition lo : nat := 20.
  Definition hi : nat := 45.
  Include RangedNat.
End Weeks.

Module Days.
  Definition lo : nat := 0.
  Definition hi : nat := 6.
  Include RangedNat.
End Days.

Record t : Type := mk {
  weeks_part : Weeks.t;
  days_part : Days.t
}.

Definition weeks (ga : t) : nat := Weeks.value (weeks_part ga).
Definition days (ga : t) : nat := Days.value (days_part ga).
Definition total_days (ga : t) : nat := 7 * weeks ga + days ga.

Definition make (w d : nat) : option t :=
  match Weeks.make w, Days.make d with
  | Some w', Some d' => Some (mk w' d')
  | _, _ => None
  end.

Theorem make_spec : forall w d ga,
  make w d = Some ga <-> weeks ga = w /\ days ga = d.
Proof.
  intros w d ga. unfold make, weeks, days. split.
  - intro H.
    destruct (Weeks.make w) as [w'|] eqn:E1; simpl in H; [|discriminate].
    destruct (Days.make d) as [d'|] eqn:E2; simpl in H; [|discriminate].
    inversion H. simpl.
    split; [apply Weeks.make_some; exact E1 | apply Days.make_some; exact E2].
  - intros [Hw Hd]. subst w d.
    rewrite Weeks.make_value, Days.make_value. destruct ga; reflexivity.
Qed.

Theorem make_accepts : forall w d,
  (exists ga, make w d = Some ga) <-> 20 <= w <= 45 /\ d <= 6.
Proof.
  intros w d. split.
  - intros [ga H]. apply make_spec in H. destruct H as [Hw Hd]. subst w d.
    pose proof (Weeks.value_bounds (weeks_part ga)) as B1.
    pose proof (Days.value_bounds (days_part ga)) as B2.
    unfold weeks, days, Weeks.lo, Weeks.hi, Days.lo, Days.hi in *. lia.
  - intros [Hw Hd].
    destruct (proj2 (Weeks.make_accepts w)) as [w' Ew];
      [unfold Weeks.lo, Weeks.hi; lia|].
    destruct (proj2 (Days.make_accepts d)) as [d' Ed];
      [unfold Days.lo, Days.hi; lia|].
    exists (mk w' d'). unfold make. rewrite Ew, Ed. reflexivity.
Qed.

(** The age in days determines the weeks and the days. *)
Theorem total_days_inj : forall ga1 ga2,
  total_days ga1 = total_days ga2 -> ga1 = ga2.
Proof.
  intros [w1 d1] [w2 d2]. unfold total_days, weeks, days. simpl. intro H.
  pose proof (Days.value_bounds d1) as B1.
  pose proof (Days.value_bounds d2) as B2.
  unfold Days.lo, Days.hi in B1, B2.
  assert (Hw : Weeks.value w1 = Weeks.value w2) by lia.
  assert (Hd : Days.value d1 = Days.value d2) by lia.
  apply Weeks.value_inj in Hw. apply Days.value_inj in Hd.
  rewrite Hw, Hd. reflexivity.
Qed.

Inductive Maturity : Type :=
  | ExtremelyPreterm : Maturity
  | VeryPreterm : Maturity
  | ModerateToLatePreterm : Maturity
  | EarlyTerm : Maturity
  | FullTerm : Maturity
  | LateTerm : Maturity
  | Postterm : Maturity.

Definition maturity_eq_dec : forall m1 m2 : Maturity, {m1 = m2} + {m1 <> m2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition maturity_all : list Maturity :=
  [ExtremelyPreterm; VeryPreterm; ModerateToLatePreterm; EarlyTerm; FullTerm;
   LateTerm; Postterm].

Lemma maturity_all_enumerates : ListHelpers.enumerates maturity_all 7.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto 8.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Definition classify (ga : t) : Maturity :=
  if weeks ga <? 28 then ExtremelyPreterm
  else if weeks ga <? 32 then VeryPreterm
  else if weeks ga <? 37 then ModerateToLatePreterm
  else if weeks ga <? 39 then EarlyTerm
  else if weeks ga <? 41 then FullTerm
  else if weeks ga <? 42 then LateTerm
  else Postterm.

Theorem classify_spec : forall ga,
  (classify ga = ExtremelyPreterm <-> weeks ga < 28) /\
  (classify ga = VeryPreterm <-> 28 <= weeks ga < 32) /\
  (classify ga = ModerateToLatePreterm <-> 32 <= weeks ga < 37) /\
  (classify ga = EarlyTerm <-> 37 <= weeks ga < 39) /\
  (classify ga = FullTerm <-> 39 <= weeks ga < 41) /\
  (classify ga = LateTerm <-> weeks ga = 41) /\
  (classify ga = Postterm <-> 42 <= weeks ga).
Proof. intros ga. unfold classify. decide_thresholds; threshold_spec. Qed.

Definition is_preterm (ga : t) : bool := weeks ga <? 37.

Definition is_term (ga : t) : bool := (37 <=? weeks ga) && (weeks ga <? 42).

Definition is_postterm (ga : t) : bool := 42 <=? weeks ga.

Definition is_late_preterm (ga : t) : bool :=
  (34 <=? weeks ga) && (weeks ga <? 37).

(** Exactly one of preterm, term and postterm holds. *)
Theorem maturity_partition : forall ga,
  (is_preterm ga = true /\ is_term ga = false /\ is_postterm ga = false) \/
  (is_preterm ga = false /\ is_term ga = true /\ is_postterm ga = false) \/
  (is_preterm ga = false /\ is_term ga = false /\ is_postterm ga = true).
Proof.
  intros ga. unfold is_preterm, is_term, is_postterm.
  decide_thresholds; simpl; finish_cases.
Qed.

Theorem preterm_iff : forall ga,
  is_preterm ga = true <->
  classify ga = ExtremelyPreterm \/ classify ga = VeryPreterm \/
  classify ga = ModerateToLatePreterm.
Proof.
  intros ga. unfold is_preterm, classify.
  decide_thresholds; split; solve_cases.
Qed.

Theorem term_iff : forall ga,
  is_term ga = true <->
  classify ga = EarlyTerm \/ classify ga = FullTerm \/ classify ga = LateTerm.
Proof.
  intros ga. unfold is_term, classify.
  decide_thresholds; simpl; split; solve_cases.
Qed.

Theorem postterm_iff : forall ga,
  is_postterm ga = true <-> classify ga = Postterm.
Proof.
  intros ga. unfold is_postterm, classify.
  decide_thresholds; split; solve_cases.
Qed.

Theorem late_preterm_classified : forall ga,
  is_late_preterm ga = true -> classify ga = ModerateToLatePreterm.
Proof.
  intros ga. unfold is_late_preterm, classify.
  decide_thresholds; simpl; solve_cases.
Qed.

End GestationalAge.

(** Birth weight in grams. Low is below 2,500 g, very low below 1,500 g and
    extremely low below 1,000 g [ICD10]. *)
Module BirthWeight.

Definition lo : nat := 2 * hundred.
Definition hi : nat := 10 * thousand.
Include RangedNat.

Definition grams (w : t) : nat := value w.

Inductive Category : Type :=
  | ExtremelyLow : Category
  | VeryLow : Category
  | Low : Category
  | NotLow : Category.

Definition category_eq_dec : forall c1 c2 : Category, {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition classify (w : t) : Category :=
  if grams w <? thousand then ExtremelyLow
  else if grams w <? 15 * hundred then VeryLow
  else if grams w <? 25 * hundred then Low
  else NotLow.

Theorem classify_spec : forall w,
  (classify w = ExtremelyLow <-> grams w < 1000) /\
  (classify w = VeryLow <-> 1000 <= grams w < 1500) /\
  (classify w = Low <-> 1500 <= grams w < 2500) /\
  (classify w = NotLow <-> 2500 <= grams w).
Proof. intros w. unfold classify. decide_thresholds; threshold_spec. Qed.

(** The definitions are cumulative. *)
Definition is_low (w : t) : bool := grams w <? 25 * hundred.
Definition is_very_low (w : t) : bool := grams w <? 15 * hundred.
Definition is_extremely_low (w : t) : bool := grams w <? thousand.

Theorem low_weight_nested : forall w,
  (is_extremely_low w = true -> is_very_low w = true) /\
  (is_very_low w = true -> is_low w = true).
Proof.
  intros w. unfold is_extremely_low, is_very_low, is_low.
  decide_thresholds; split; solve_cases.
Qed.

End BirthWeight.

(** Preductal oxygen saturation in percent, with the target table of the
    Neonatal Resuscitation Program [NRP8] [NRP9]. *)
Module SpO2.

Definition lo : nat := 0.
Definition hi : nat := hundred.
Include RangedNat.

(** Rows of the table: minute after birth and target range. *)
Definition table (e : Edition.t) : list (nat * (nat * nat)) :=
  match e with
  | Edition.NRP8 =>
      [(1, (60, 65)); (2, (65, 70)); (3, (70, 75)); (4, (75, 80));
       (5, (80, 85)); (10, (85, 95))]
  | Edition.NRP9 =>
      [(2, (65, 70)); (3, (70, 75)); (4, (75, 80)); (5, (80, 85));
       (10, (85, 95))]
  end.

(** Target range at a minute after birth. Minutes 6 to 9 take the interval
    from the 5-minute lower bound to the 10-minute upper bound, and minutes
    after 10 take the 10-minute row. *)
Definition target (e : Edition.t) (minute : nat) : option (nat * nat) :=
  match minute with
  | 0 => None
  | 1 => match e with
         | Edition.NRP8 => Some (60, 65)
         | Edition.NRP9 => None
         end
  | 2 => Some (65, 70)
  | 3 => Some (70, 75)
  | 4 => Some (75, 80)
  | 5 => Some (80, 85)
  | 6 | 7 | 8 | 9 => Some (80, 95)
  | _ => Some (85, 95)
  end.

Local Ltac minute_cases m :=
  destruct m as [|[|[|[|[|[|[|[|[|[|[|m]]]]]]]]]]].

Theorem target_tabulated : forall e m r,
  In (m, r) (table e) -> target e m = Some r.
Proof.
  intros [] m r H; simpl in H;
    repeat (destruct H as [H|H]; [inversion H; reflexivity|]);
    contradiction.
Qed.

(** The 9th edition table is the 8th edition table without its first
    row. *)
Theorem table_editions : table Edition.NRP9 = tl (table Edition.NRP8).
Proof. reflexivity. Qed.

Theorem target_editions : forall m,
  m <> 1 -> target Edition.NRP9 m = target Edition.NRP8 m.
Proof. intros m H. minute_cases m; try reflexivity. contradiction. Qed.

Theorem target_none_iff : forall e m,
  target e m = None <-> m = 0 \/ (e = Edition.NRP9 /\ m = 1).
Proof. intros e m. destruct e; minute_cases m; simpl; split; solve_cases. Qed.

Theorem target_bounds : forall e m l h,
  target e m = Some (l, h) -> 60 <= l /\ l < h /\ h <= 95.
Proof.
  intros e m l h H. destruct e; minute_cases m; simpl in H;
    try discriminate; inversion H; lia.
Qed.

(** Both bounds rise with time. *)
Theorem target_monotone : forall e m1 m2 l1 h1 l2 h2,
  m1 <= m2 ->
  target e m1 = Some (l1, h1) -> target e m2 = Some (l2, h2) ->
  l1 <= l2 /\ h1 <= h2.
Proof.
  intros e m1 m2 l1 h1 l2 h2 Hle H1 H2.
  destruct e; minute_cases m1; minute_cases m2; simpl in H1, H2;
    try discriminate; inversion H1; inversion H2; lia.
Qed.

(** Through minute 5 each tabulated range begins where the previous one
    ends. *)
Theorem target_contiguous : forall e m l1 h1 l2 h2,
  m <= 4 ->
  target e m = Some (l1, h1) -> target e (S m) = Some (l2, h2) ->
  h1 = l2.
Proof.
  intros e m l1 h1 l2 h2 Hm H1 H2.
  destruct e; minute_cases m; simpl in H1, H2;
    try discriminate; try lia; inversion H1; inversion H2; lia.
Qed.

Inductive Status : Type :=
  | BelowTarget : Status
  | OnTarget : Status
  | AboveTarget : Status.

Definition status_eq_dec : forall s1 s2 : Status, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition status (e : Edition.t) (minute : nat) (s : t) : option Status :=
  match target e minute with
  | None => None
  | Some (l, h) =>
      Some (if value s <? l then BelowTarget
            else if h <? value s then AboveTarget
            else OnTarget)
  end.

Theorem status_spec : forall e m s l h,
  target e m = Some (l, h) ->
  (status e m s = Some BelowTarget <-> value s < l) /\
  (status e m s = Some OnTarget <-> l <= value s <= h) /\
  (status e m s = Some AboveTarget <-> h < value s).
Proof.
  intros e m s l h Ht. pose proof (target_bounds e m l h Ht) as Hb.
  unfold status. rewrite Ht. decide_thresholds; threshold_spec.
Qed.

(** A saturation below 60 is below every target and one above 95 is above
    every target. *)
Theorem below_60_below_target : forall e m s st,
  value s < 60 -> status e m s = Some st -> st = BelowTarget.
Proof.
  intros e m s st Hs. unfold status.
  destruct (target e m) as [[l h]|] eqn:Ht; [|discriminate].
  pose proof (target_bounds e m l h Ht) as Hb.
  decide_thresholds; intro H; inversion H; try reflexivity; lia.
Qed.

Theorem above_95_above_target : forall e m s st,
  95 < value s -> status e m s = Some st -> st = AboveTarget.
Proof.
  intros e m s st Hs. unfold status.
  destruct (target e m) as [[l h]|] eqn:Ht; [|discriminate].
  pose proof (target_bounds e m l h Ht) as Hb.
  decide_thresholds; intro H; inversion H; try reflexivity; lia.
Qed.

End SpO2.

(** Body temperature in tenths of a degree Celsius. The bands are those of
    [WHO1997]; the normal band, 36.5 to 37.5, is the range to be maintained
    in the delivery room [AHA2020]. *)
Module Temperature.

Definition lo : nat := 2 * hundred.
Definition hi : nat := 45 * 10.
Include RangedNat.

Inductive Status : Type :=
  | SevereHypothermia : Status
  | ModerateHypothermia : Status
  | MildHypothermia : Status
  | Normal : Status
  | Hyperthermia : Status.

Definition status_eq_dec : forall s1 s2 : Status, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition classify (temp : t) : Status :=
  if value temp <? 32 * 10 then SevereHypothermia
  else if value temp <? 36 * 10 then ModerateHypothermia
  else if value temp <? 36 * 10 + 5 then MildHypothermia
  else if value temp <=? 37 * 10 + 5 then Normal
  else Hyperthermia.

Theorem classify_spec : forall temp,
  (classify temp = SevereHypothermia <-> value temp < 320) /\
  (classify temp = ModerateHypothermia <-> 320 <= value temp < 360) /\
  (classify temp = MildHypothermia <-> 360 <= value temp < 365) /\
  (classify temp = Normal <-> 365 <= value temp <= 375) /\
  (classify temp = Hyperthermia <-> 375 < value temp).
Proof. intros temp. unfold classify. decide_thresholds; threshold_spec. Qed.

Definition is_hypothermic (temp : t) : bool := value temp <? 36 * 10 + 5.

Definition in_target (temp : t) : bool :=
  (36 * 10 + 5 <=? value temp) && (value temp <=? 37 * 10 + 5).

Definition is_hyperthermic (temp : t) : bool := 37 * 10 + 5 <? value temp.

Theorem hypothermic_iff : forall temp,
  is_hypothermic temp = true <->
  classify temp = SevereHypothermia \/ classify temp = ModerateHypothermia \/
  classify temp = MildHypothermia.
Proof.
  intros temp. unfold is_hypothermic, classify.
  decide_thresholds; split; solve_cases.
Qed.

Theorem in_target_iff : forall temp,
  in_target temp = true <-> classify temp = Normal.
Proof.
  intros temp. unfold in_target, classify.
  decide_thresholds; simpl; split; solve_cases.
Qed.

Theorem hyperthermic_iff : forall temp,
  is_hyperthermic temp = true <-> classify temp = Hyperthermia.
Proof.
  intros temp. unfold is_hyperthermic, classify.
  decide_thresholds; split; solve_cases.
Qed.

End Temperature.

(** Umbilical cord blood gas: pH in hundredths and base deficit in tenths of
    mmol/L. A base excess is recorded as a deficit of zero. *)
Module CordBloodGas.

Module PH.
  Definition lo : nat := 6 * hundred.
  Definition hi : nat := 8 * hundred.
  Include RangedNat.
End PH.

Module BaseDeficit.
  Definition lo : nat := 0.
  Definition hi : nat := 4 * hundred.
  Include RangedNat.
End BaseDeficit.

Record t : Type := mk {
  ph : PH.t;
  base_deficit : BaseDeficit.t
}.

Definition ph_below_7 (g : t) : bool := PH.value (ph g) <? 7 * hundred.

Definition base_deficit_at_least_12 (g : t) : bool :=
  12 * 10 <=? BaseDeficit.value (base_deficit g).

(** [ACOG2014]: umbilical artery pH less than 7.0, or base deficit greater
    than or equal to 12 mmol/L, or both. *)
Definition acidemia_sign (g : t) : bool :=
  ph_below_7 g || base_deficit_at_least_12 g.

Theorem acidemia_sign_iff : forall g,
  acidemia_sign g = true <->
  PH.value (ph g) < 700 \/ 120 <= BaseDeficit.value (base_deficit g).
Proof.
  intros g. unfold acidemia_sign, ph_below_7, base_deficit_at_least_12.
  decide_thresholds; simpl; split; solve_cases.
Qed.

(** [AAP2015]: with a score of 5 or less at 5 minutes, an umbilical arterial
    blood gas sample should be obtained. *)
Definition sample_indicated (five_minute_score : nat) : bool :=
  five_minute_score <=? 5.

Theorem sample_indicated_iff : forall s,
  sample_indicated s = true <-> s <= 5.
Proof. intros s. unfold sample_indicated. apply Nat.leb_le. Qed.

(** The sample is indicated for every low score and for no reassuring
    score, and the moderately abnormal band is divided between 5 and 6. *)
Theorem sample_indicated_by_class : forall s,
  (Classification.of_score s = Classification.Low ->
     sample_indicated s = true) /\
  (Classification.of_score s = Classification.Reassuring ->
     sample_indicated s = false) /\
  (sample_indicated 5 = true /\ sample_indicated 6 = false /\
   Classification.of_score 5 = Classification.of_score 6).
Proof.
  intros s. unfold sample_indicated, Classification.of_score.
  decide_thresholds; split_conj; solve_cases.
Qed.

End CordBloodGas.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 9: NEONATAL RESUSCITATION                       *)
(*                                                                            *)
(*  Decision points and parameters of the resuscitation algorithm [NRP8]      *)
(*  [AHA2020], with the values the 9th edition changes [NRP9]. The inputs     *)
(*  are heart rate and respiratory effort.                                    *)
(*                                                                            *)
(******************************************************************************)

Module NRP.

(** ** Rapid evaluation at birth *)

Record RapidEvaluation : Type := mkRapid {
  term_gestation : bool;
  good_tone : bool;
  breathing_or_crying : bool
}.

(** An infant for whom all three answers are yes stays with the mother for
    routine care. *)
Definition routine_care (r : RapidEvaluation) : bool :=
  term_gestation r && good_tone r && breathing_or_crying r.

Theorem routine_care_iff : forall r,
  routine_care r = true <->
  term_gestation r = true /\ good_tone r = true /\
  breathing_or_crying r = true.
Proof. intros [[] [] []]; simpl; split; solve_cases. Qed.

(** ** Findings after the initial steps *)

Inductive Effort : Type :=
  | Apnea : Effort
  | Gasping : Effort
  | LaboredBreathing : Effort
  | EffectiveBreathing : Effort.

Definition effort_eq_dec : forall e1 e2 : Effort, {e1 = e2} + {e1 <> e2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Record Findings : Type := mkFindings {
  effort : Effort;
  heart_rate : Pulse.Band;
  persistent_cyanosis : bool
}.

Definition apnea_or_gasping (e : Effort) : bool :=
  match e with
  | Apnea | Gasping => true
  | LaboredBreathing | EffectiveBreathing => false
  end.

Definition hr_below_100 (b : Pulse.Band) : bool :=
  match b with
  | Pulse.BandAtLeast100 => false
  | _ => true
  end.

Definition hr_below_60 (b : Pulse.Band) : bool :=
  match b with
  | Pulse.BandAbsent | Pulse.BandBelow60 => true
  | _ => false
  end.

Lemma hr_below_100_iff : forall bpm,
  hr_below_100 (Pulse.band_of_bpm bpm) = true <-> bpm < 100.
Proof.
  intros bpm. unfold Pulse.band_of_bpm.
  decide_thresholds; simpl; split; solve_cases.
Qed.

Lemma hr_below_60_iff : forall bpm,
  hr_below_60 (Pulse.band_of_bpm bpm) = true <-> bpm < 60.
Proof.
  intros bpm. unfold Pulse.band_of_bpm.
  decide_thresholds; simpl; split; solve_cases.
Qed.

(** ** Decision points *)

(** Seconds of ventilation that inflates the lungs before the heart rate
    decides on chest compressions, and seconds of coordinated compressions
    before it decides on epinephrine. *)
Definition ventilation_reassess_secs : nat := 30.
Definition compression_reassess_secs : nat := 60.

(** Ventilation is indicated for apnea or gasping, or a heart rate below
    100 per minute. *)
Definition ventilation_indicated (f : Findings) : bool :=
  apnea_or_gasping (effort f) || hr_below_100 (heart_rate f).

(** Supplemental oxygen and CPAP are considered for labored breathing or
    persistent cyanosis in an infant who is breathing with a heart rate of
    at least 100. *)
Definition oxygen_or_cpap_considered (f : Findings) : bool :=
  negb (ventilation_indicated f) &&
  ((match effort f with LaboredBreathing => true | _ => false end)
   || persistent_cyanosis f).

(** Chest compressions are indicated when the heart rate stays below 60
    after 30 seconds of ventilation that inflates the lungs. *)
Definition compressions_indicated (b : Pulse.Band)
    (effective_ventilation_secs : nat) : bool :=
  hr_below_60 b && (ventilation_reassess_secs <=? effective_ventilation_secs).

(** Epinephrine is indicated when the heart rate stays below 60 after 60
    seconds of chest compressions coordinated with ventilation. *)
Definition epinephrine_indicated (b : Pulse.Band) (compression_secs : nat)
    : bool :=
  hr_below_60 b && (compression_reassess_secs <=? compression_secs).

(** ** Indicated step *)

Inductive Step : Type :=
  | Observe : Step
  | OxygenOrCPAP : Step
  | Ventilate : Step
  | Compress : Step
  | GiveEpinephrine : Step.

Definition step_eq_dec : forall s1 s2 : Step, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition step_all : list Step :=
  [Observe; OxygenOrCPAP; Ventilate; Compress; GiveEpinephrine].

Lemma step_all_enumerates : ListHelpers.enumerates step_all 5.
Proof.
  unfold ListHelpers.enumerates. repeat split.
  - intros []; simpl; auto 6.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Definition step_rank (s : Step) : nat :=
  match s with
  | Observe => 0
  | OxygenOrCPAP => 1
  | Ventilate => 2
  | Compress => 3
  | GiveEpinephrine => 4
  end.

Record State : Type := mkState {
  findings : Findings;
  effective_ventilation_secs : nat;
  compression_secs : nat
}.

Definition step (s : State) : Step :=
  if epinephrine_indicated (heart_rate (findings s)) (compression_secs s)
  then GiveEpinephrine
  else if compressions_indicated (heart_rate (findings s))
            (effective_ventilation_secs s)
  then Compress
  else if ventilation_indicated (findings s) then Ventilate
  else if oxygen_or_cpap_considered (findings s) then OxygenOrCPAP
  else Observe.

Local Ltac unfold_step :=
  unfold step, epinephrine_indicated, compressions_indicated,
    ventilation_indicated, oxygen_or_cpap_considered,
    ventilation_reassess_secs, compression_reassess_secs.

Theorem step_spec : forall s,
  (step s = GiveEpinephrine <->
     hr_below_60 (heart_rate (findings s)) = true /\
     60 <= compression_secs s) /\
  (step s = Compress <->
     hr_below_60 (heart_rate (findings s)) = true /\
     compression_secs s < 60 /\ 30 <= effective_ventilation_secs s) /\
  (step s = Ventilate <->
     ventilation_indicated (findings s) = true /\
     (hr_below_60 (heart_rate (findings s)) = false \/
      (compression_secs s < 60 /\ effective_ventilation_secs s < 30))) /\
  (step s = OxygenOrCPAP <-> oxygen_or_cpap_considered (findings s) = true) /\
  (step s = Observe <->
     ventilation_indicated (findings s) = false /\
     oxygen_or_cpap_considered (findings s) = false).
Proof.
  intros [[ef hb cy] v c]. unfold_step.
  destruct ef, hb, cy; calc; decide_thresholds; calc;
    split_conj; split; solve_cases.
Qed.

(** For the same respiratory effort and elapsed times, a lower heart-rate
    band never indicates a lesser step. *)
Theorem step_monotone_in_heart_rate : forall ef cy b1 b2 v c,
  Pulse.band_rank b1 <= Pulse.band_rank b2 ->
  step_rank (step (mkState (mkFindings ef b2 cy) v c)) <=
  step_rank (step (mkState (mkFindings ef b1 cy) v c)).
Proof.
  intros ef cy b1 b2 v c. unfold_step.
  destruct ef, cy, b1, b2; calc; decide_thresholds; calc; intro H; lia.
Qed.

(** Compressions are not indicated before 30 seconds of effective
    ventilation, nor epinephrine before 60 seconds of compressions. *)
Theorem no_early_escalation : forall s,
  (effective_ventilation_secs s < 30 -> step s <> Compress) /\
  (compression_secs s < 60 -> step s <> GiveEpinephrine).
Proof.
  intros s. destruct (step_spec s) as [He [Hc _]]. split; intros Hlt Heq.
  - apply Hc in Heq. lia.
  - apply He in Heq. lia.
Qed.

(** ** Ventilation *)

(** Ventilation rate in breaths per minute [NRP8] [NRP9]. *)
Definition ventilation_rate (e : Edition.t) : nat * nat :=
  match e with
  | Edition.NRP8 => (40, 60)
  | Edition.NRP9 => (30, 60)
  end.

Definition rate_in_range (e : Edition.t) (rate : nat) : bool :=
  (fst (ventilation_rate e) <=? rate) && (rate <=? snd (ventilation_rate e)).

Theorem rate_range_widened : forall rate,
  rate_in_range Edition.NRP8 rate = true ->
  rate_in_range Edition.NRP9 rate = true.
Proof.
  intros rate. unfold rate_in_range. calc.
  decide_thresholds; calc; solve_cases.
Qed.

(** Initial peak inflation pressure and end-expiratory pressure in cm of
    water [NRP8]. *)
Definition initial_pip : nat * nat := (20, 25).
Definition peep : nat := 5.

Theorem initial_driving_pressure : peep < fst initial_pip.
Proof. unfold peep, initial_pip. simpl. lia. Qed.

(** ** Chest compressions *)

(** Three compressions and one ventilation in each two-second cycle
    [AHA2020]. *)
Definition compressions_per_cycle : nat := 3.
Definition ventilations_per_cycle : nat := 1.
Definition cycle_secs : nat := 2.

Theorem compression_rates :
  60 / cycle_secs * compressions_per_cycle = 90 /\
  60 / cycle_secs * ventilations_per_cycle = 30.
Proof. split; reflexivity. Qed.

(** ** Oxygen *)

(** Range of initial inspired oxygen in percent, by gestational age in
    weeks [NRP8] [NRP9]. *)
Definition initial_fio2 (e : Edition.t) (ga_weeks : nat) : nat * nat :=
  match e with
  | Edition.NRP8 => if 35 <=? ga_weeks then (21, 21) else (21, 30)
  | Edition.NRP9 =>
      if 35 <=? ga_weeks then (21, 21)
      else if 32 <=? ga_weeks then (21, 30)
      else (30, hundred)
  end.

(** Inspired oxygen during chest compressions [NRP8]. *)
Definition compressions_fio2 : nat := hundred.

Theorem initial_fio2_bounds : forall e w,
  21 <= fst (initial_fio2 e w) /\
  fst (initial_fio2 e w) <= snd (initial_fio2 e w) /\
  snd (initial_fio2 e w) <= 100.
Proof.
  intros e w. destruct e; unfold initial_fio2; decide_thresholds; calc; arith.
Qed.

(** No initial setting exceeds the oxygen given with compressions. *)
Theorem initial_fio2_below_compressions : forall e w,
  snd (initial_fio2 e w) <= compressions_fio2.
Proof.
  intros e w. pose proof (initial_fio2_bounds e w) as H.
  unfold compressions_fio2. arith.
Qed.

(** The editions agree from 32 weeks; below 32 weeks the 9th edition
    starts where the 8th edition range ends. *)
Theorem initial_fio2_editions : forall w,
  (32 <= w -> initial_fio2 Edition.NRP9 w = initial_fio2 Edition.NRP8 w) /\
  (w < 32 ->
     fst (initial_fio2 Edition.NRP9 w) = snd (initial_fio2 Edition.NRP8 w)).
Proof.
  intros w. unfold initial_fio2. decide_thresholds; split; solve_cases.
Qed.

(** ** Epinephrine *)

Inductive Route : Type :=
  | Intravenous : Route
  | Intraosseous : Route
  | Endotracheal : Route.

Definition route_eq_dec : forall r1 r2 : Route, {r1 = r2} + {r1 <> r2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

(** Dose range in micrograms per kilogram [AHA2020]. *)
Definition dose_range (r : Route) : nat * nat :=
  match r with
  | Intravenous | Intraosseous => (10, 30)
  | Endotracheal => (50, hundred)
  end.

(** Suggested initial dose in micrograms per kilogram [NRP8]. *)
Definition suggested_dose (r : Route) : nat :=
  match r with
  | Intravenous | Intraosseous => 20
  | Endotracheal => hundred
  end.

Definition dose_in_range (r : Route) (mcg_per_kg : nat) : bool :=
  (fst (dose_range r) <=? mcg_per_kg) && (mcg_per_kg <=? snd (dose_range r)).

Theorem suggested_dose_in_range : forall r,
  dose_in_range r (suggested_dose r) = true.
Proof. intros []; reflexivity. Qed.

(** No dose is in range for both an intravascular and the endotracheal
    route. *)
Theorem route_ranges_disjoint : forall d,
  dose_in_range Intravenous d = true -> dose_in_range Endotracheal d = false.
Proof.
  intros d. unfold dose_in_range. calc.
  decide_thresholds; calc; solve_cases.
Qed.

(** Dose in micrograms for a weight in grams, and its volume in microlitres
    at the concentration of 0.1 mg/mL. *)
Definition dose_mcg (weight_g mcg_per_kg : nat) : nat :=
  weight_g * mcg_per_kg / thousand.

Definition volume_ul (mcg : nat) : nat := 10 * mcg.

Theorem dose_mcg_monotone : forall w1 w2 d1 d2,
  w1 <= w2 -> d1 <= d2 -> dose_mcg w1 d1 <= dose_mcg w2 d2.
Proof.
  intros w1 w2 d1 d2 Hw Hd. unfold dose_mcg.
  apply Nat.Div0.div_le_mono. apply Nat.mul_le_mono; assumption.
Qed.

(** For a 3,000 g infant the suggested doses are 0.06 mg in 0.6 mL
    intravenously and 0.3 mg in 3 mL by endotracheal tube. *)
Example dose_3000g_intravenous :
  dose_mcg 3000 (suggested_dose Intravenous) = 60 /\ volume_ul 60 = 600.
Proof. split; reflexivity. Qed.

Example dose_3000g_endotracheal :
  dose_mcg 3000 (suggested_dose Endotracheal) = 300 /\ volume_ul 300 = 3000.
Proof. split; reflexivity. Qed.

(** The dose may be repeated every 3 to 5 minutes while the heart rate
    stays below 60 [AHA2020]. *)
Definition repeat_interval_secs : nat * nat := (18 * 10, 30 * 10).

Definition repeat_due (b : Pulse.Band) (secs_since_dose : nat) : bool :=
  hr_below_60 b && (fst repeat_interval_secs <=? secs_since_dose).

(** ** Volume expansion *)

(** Ten millilitres per kilogram of normal saline or blood [AHA2020]. *)
Definition volume_expansion_ml (weight_g : nat) : nat :=
  weight_g * 10 / thousand.

Example volume_expansion_3000g : volume_expansion_ml 3000 = 30.
Proof. reflexivity. Qed.

(** ** Endotracheal tube *)

Inductive TubeSize : Type :=
  | Tube25 : TubeSize
  | Tube30 : TubeSize
  | Tube35 : TubeSize.

Definition tube_eq_dec : forall t1 t2 : TubeSize, {t1 = t2} + {t1 <> t2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

(** Internal diameter in tenths of a millimetre. *)
Definition tube_diameter (t : TubeSize) : nat :=
  match t with
  | Tube25 => 25
  | Tube30 => 30
  | Tube35 => 35
  end.

(** Tube size by weight in grams and by gestational age in weeks [NRP8]
    [NRP9]. *)
Definition tube_by_weight (e : Edition.t) (weight_g : nat) : TubeSize :=
  match e with
  | Edition.NRP8 =>
      if weight_g <? thousand then Tube25
      else if weight_g <=? 2 * thousand then Tube30
      else Tube35
  | Edition.NRP9 =>
      if weight_g <? 12 * hundred then Tube25
      else if weight_g <=? 22 * hundred then Tube30
      else Tube35
  end.

Definition tube_by_gestation (ga_weeks : nat) : TubeSize :=
  if ga_weeks <? 28 then Tube25
  else if ga_weeks <=? 34 then Tube30
  else Tube35.

Theorem tube_by_weight_monotone : forall e w1 w2,
  w1 <= w2 ->
  tube_diameter (tube_by_weight e w1) <= tube_diameter (tube_by_weight e w2).
Proof.
  intros e w1 w2 H. destruct e; unfold tube_by_weight;
    decide_thresholds; simpl; arith.
Qed.

Theorem tube_by_gestation_monotone : forall w1 w2,
  w1 <= w2 ->
  tube_diameter (tube_by_gestation w1) <= tube_diameter (tube_by_gestation w2).
Proof.
  intros w1 w2 H. unfold tube_by_gestation. decide_thresholds; simpl; arith.
Qed.

(** The editions assign different sizes exactly from 1,000 g up to but not
    including 1,200 g, and above 2,000 g up to 2,200 g. *)
Theorem tube_editions_differ_iff : forall w,
  tube_by_weight Edition.NRP8 w <> tube_by_weight Edition.NRP9 w <->
  1000 <= w < 1200 \/ 2000 < w <= 2200.
Proof.
  intros w. unfold tube_by_weight. decide_thresholds; split; solve_cases.
Qed.

(** Insertion depth in millimetres at the lip by gestational age in weeks
    [NRP8], after [Kempley2008]. The 9th edition measures to the upper gum
    [NRP9]. *)
Definition depth_by_gestation (ga_weeks : nat) : option nat :=
  if ga_weeks <? 23 then None
  else if ga_weeks <=? 24 then Some 55
  else if ga_weeks <=? 26 then Some 60
  else if ga_weeks <=? 29 then Some 65
  else if ga_weeks <=? 32 then Some 70
  else if ga_weeks <=? 34 then Some 75
  else if ga_weeks <=? 37 then Some 80
  else if ga_weeks <=? 40 then Some 85
  else if ga_weeks <=? 43 then Some 90
  else None.

(** Depth in millimetres from the nasal-tragus length: the length plus one
    centimetre [NRP8]. *)
Definition depth_by_ntl (ntl_mm : nat) : nat := ntl_mm + 10.

Theorem depth_defined_iff : forall w,
  (exists d, depth_by_gestation w = Some d) <-> 23 <= w <= 43.
Proof.
  intros w. unfold depth_by_gestation. decide_thresholds; split;
    first [ intros [d H]; (discriminate || lia)
          | intro H; first [lia | eexists; reflexivity] ].
Qed.

Theorem depth_bounds : forall w d,
  depth_by_gestation w = Some d -> 55 <= d <= 90.
Proof.
  intros w d. unfold depth_by_gestation.
  decide_thresholds; intro H; try discriminate; inversion H; lia.
Qed.

Theorem depth_monotone : forall w1 w2 d1 d2,
  w1 <= w2 ->
  depth_by_gestation w1 = Some d1 -> depth_by_gestation w2 = Some d2 ->
  d1 <= d2.
Proof.
  intros w1 w2 d1 d2 Hle. unfold depth_by_gestation.
  decide_thresholds; intros H1 H2; try discriminate;
    inversion H1; inversion H2; lia.
Qed.

(** ** Cessation of efforts *)

(** With no heart rate after all steps of resuscitation have been
    performed, cessation is discussed with the team and the family; a
    reasonable time frame is around 20 minutes after birth [AHA2020]. *)
Definition cessation_discussion (b : Pulse.Band) (all_steps_performed : bool)
    (minutes_after_birth : nat) : bool :=
  (match b with Pulse.BandAbsent => true | _ => false end)
  && all_steps_performed && (20 <=? minutes_after_birth).

Theorem cessation_discussion_iff : forall b p m,
  cessation_discussion b p m = true <->
  b = Pulse.BandAbsent /\ p = true /\ 20 <= m.
Proof.
  intros b p m. unfold cessation_discussion.
  destruct b, p; calc; decide_thresholds; split; solve_cases.
Qed.

(** ** Umbilical cord management *)

(** Seconds for which clamping is deferred in an infant who does not need
    immediate resuscitation [NRP8] [NRP9]. *)
Definition deferral_secs (e : Edition.t) : nat :=
  match e with
  | Edition.NRP8 => 30
  | Edition.NRP9 => 60
  end.

(** Cord milking is not recommended before 28 weeks [NRP8] [NRP9]. *)
Definition milking_not_recommended (ga_weeks : nat) : bool := ga_weeks <? 28.

(** Milking the intact cord may be a reasonable alternative to early
    clamping for a nonvigorous infant of 35 to 42 weeks [NRP9]. *)
Definition milking_reasonable_if_nonvigorous (e : Edition.t) (ga_weeks : nat)
    : bool :=
  match e with
  | Edition.NRP8 => false
  | Edition.NRP9 => (35 <=? ga_weeks) && (ga_weeks <=? 42)
  end.

Theorem deferral_lengthened :
  deferral_secs Edition.NRP8 < deferral_secs Edition.NRP9.
Proof. simpl. lia. Qed.

Theorem milking_recommendations_disjoint : forall e w,
  milking_reasonable_if_nonvigorous e w = true ->
  milking_not_recommended w = false.
Proof.
  intros e w. destruct e;
    unfold milking_reasonable_if_nonvigorous, milking_not_recommended;
    decide_thresholds; simpl; solve_cases.
Qed.

End NRP.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 10: SCORE AND RESUSCITATION                     *)
(*                                                                            *)
(*  [AAP2015]: the score is not used to determine the need for initial        *)
(*  resuscitation, what resuscitation steps are necessary, or when to use     *)
(*  them. The section states what the total does determine about the NRP      *)
(*  criterion for ventilation: totals up to 2 meet it, the total 10 does      *)
(*  not, and every total from 3 to 9 is reached both by assessments that      *)
(*  meet it and by assessments that do not.                                   *)
(*                                                                            *)
(******************************************************************************)

Module ScoreAndResuscitation.

(** The scored findings that by themselves meet the criterion for
    ventilation: absent respiratory effort, or a heart rate below 100. *)
Definition ventilation_criterion (a : Assessment.t) : bool :=
  (match Assessment.respiration a with
   | Respiration.Absent => true
   | _ => false
   end)
  || (match Assessment.pulse a with
      | Pulse.AtLeast100 => false
      | _ => true
      end).

(** Findings of the algorithm that agree with an assessment on heart rate
    and on absent respiratory effort. *)
Definition consistent (a : Assessment.t) (f : NRP.Findings) : Prop :=
  Pulse.of_band (NRP.heart_rate f) = Assessment.pulse a /\
  (Assessment.respiration a = Respiration.Absent <-> NRP.effort f = NRP.Apnea).

Theorem criterion_sound : forall a f,
  consistent a f -> ventilation_criterion a = true ->
  NRP.ventilation_indicated f = true.
Proof.
  intros [ap pu gr ac re] [ef hb cy] [Hp Hr].
  unfold ventilation_criterion, NRP.ventilation_indicated. simpl in *.
  destruct re, pu, hb, ef; simpl in *; intro Hc;
    first [ reflexivity | discriminate
          | (destruct Hr as [Hr _]; specialize (Hr eq_refl); discriminate) ].
Qed.

Theorem totals_up_to_2_meet_criterion : forall a,
  Assessment.total a <= 2 -> ventilation_criterion a = true.
Proof.
  intros [[] [] [] [] []] H; first [reflexivity | (cbv in H; lia)].
Qed.

Theorem total_10_excludes_criterion : forall a,
  Assessment.total a = 10 -> ventilation_criterion a = false.
Proof.
  intros a H. apply Assessment.total_ten_iff in H. subst a. reflexivity.
Qed.

(** Grades of color, reflex irritability and muscle tone summing to [n],
    for [n] up to 6. *)
Definition fill (n : nat) : Appearance.t * Grimace.t * Activity.t :=
  match n with
  | 0 => (Appearance.BlueOrPale, Grimace.NoResponse, Activity.Limp)
  | 1 => (Appearance.Acrocyanotic, Grimace.NoResponse, Activity.Limp)
  | 2 => (Appearance.CompletelyPink, Grimace.NoResponse, Activity.Limp)
  | 3 => (Appearance.CompletelyPink, Grimace.GrimaceOnly, Activity.Limp)
  | 4 => (Appearance.CompletelyPink, Grimace.CryOrWithdrawal, Activity.Limp)
  | 5 => (Appearance.CompletelyPink, Grimace.CryOrWithdrawal,
          Activity.SomeFlexion)
  | _ => (Appearance.CompletelyPink, Grimace.CryOrWithdrawal,
          Activity.ActiveMotion)
  end.

(** An assessment with total [n] and heart rate below 100. *)
Definition meeting (n : nat) : Assessment.t :=
  let '(ap, gr, ac) := fill (n - 3) in
  Assessment.mk ap Pulse.Below100 gr ac Respiration.GoodCry.

(** An assessment with total [n], heart rate of at least 100 and
    respiratory effort present. *)
Definition not_meeting (n : nat) : Assessment.t :=
  let '(ap, gr, ac) := fill (n - 3) in
  Assessment.mk ap Pulse.AtLeast100 gr ac Respiration.WeakCry.

Theorem interior_totals_undetermined : forall n,
  3 <= n <= 9 ->
  Assessment.total (meeting n) = n /\
  ventilation_criterion (meeting n) = true /\
  Assessment.total (not_meeting n) = n /\
  ventilation_criterion (not_meeting n) = false.
Proof.
  intros n [Hlo Hhi].
  do 10 (destruct n as [|n]; [try lia; repeat split; reflexivity|]). lia.
Qed.

(** No rule on the total reproduces the criterion. *)
Theorem no_threshold_rule :
  ~ exists rule : nat -> bool,
      forall a, rule (Assessment.total a) = ventilation_criterion a.
Proof.
  intros [rule H].
  pose proof (H (meeting 5)) as H1. pose proof (H (not_meeting 5)) as H2.
  cbv in H1, H2. rewrite H1 in H2. discriminate.
Qed.

(** A reassuring score does not exclude the criterion and a low score does
    not imply it. *)
Theorem class_does_not_determine :
  (exists a, Classification.of_assessment a = Classification.Reassuring /\
             ventilation_criterion a = true) /\
  (exists a, Classification.of_assessment a = Classification.Low /\
             ventilation_criterion a = false).
Proof.
  split; [exists (meeting 9) | exists (not_meeting 3)]; split; reflexivity.
Qed.

End ScoreAndResuscitation.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 11: EXPANDED APGAR FORM                         *)
(*                                                                            *)
(*  [AAP2015]: the expanded form records, with each score, the resuscitative  *)
(*  interventions in use at that time: oxygen, positive pressure ventilation  *)
(*  or nasal CPAP, endotracheal tube, chest compressions and epinephrine. A   *)
(*  score assigned during a resuscitation is not equivalent to a score        *)
(*  assigned to a spontaneously breathing infant, and the form places no      *)
(*  constraint between the two.                                               *)
(*                                                                            *)
(******************************************************************************)

Module ExpandedForm.

Record Interventions : Type := mkInterventions {
  oxygen : bool;
  ppv_ncpap : bool;
  ett : bool;
  chest_compressions : bool;
  epinephrine : bool
}.

Definition no_interventions : Interventions :=
  mkInterventions false false false false false.

(** Whether the score was assigned during a resuscitation. *)
Definition assisted (i : Interventions) : bool :=
  oxygen i || ppv_ncpap i || ett i || chest_compressions i || epinephrine i.

Record Column : Type := mkColumn {
  column_assessment : Assessment.t;
  column_interventions : Interventions
}.

(** The columns are held in the order of the standard times. *)
Record t : Type := mk {
  gestational_age : GestationalAge.t;
  columns : list Column
}.

(** The scores of the form with the times of their columns. *)
Definition timed (f : t) : list Timing.Timed :=
  map (fun p => Timing.mkTimed (fst p) (column_assessment (snd p)))
      (combine Timing.all (columns f)).

(** A form is well formed when it has at most five columns and its scores
    follow the timing rule. *)
Definition well_formed (f : t) : Prop :=
  length (columns f) <= 5 /\ Timing.Valid (timed f).

Definition well_formedb (f : t) : bool :=
  (length (columns f) <=? 5) && Timing.validb (timed f).

Theorem well_formedb_correct : forall f,
  well_formedb f = true <-> well_formed f.
Proof.
  intros f. unfold well_formedb, well_formed.
  rewrite andb_true_iff, Nat.leb_le, Timing.validb_correct. reflexivity.
Qed.

Lemma timed_length : forall f,
  length (columns f) <= 5 -> length (timed f) = length (columns f).
Proof.
  intros f H. unfold timed. rewrite length_map, length_combine.
  change (length Timing.all) with 5. lia.
Qed.

Theorem well_formed_columns : forall f,
  well_formed f -> 2 <= length (columns f) <= 5.
Proof.
  intros f [Hlen Hv]. destruct (Timing.valid_shape _ Hv) as [_ Hl].
  rewrite (timed_length f Hlen) in Hl. exact Hl.
Qed.

(** ** Construction from observations *)

Definition of_observations (ga : GestationalAge.t)
    (obs : Timing.Time -> Assessment.t)
    (interventions : Timing.Time -> Interventions) : t :=
  mk ga (map (fun x => mkColumn (Timing.assessment x)
                                (interventions (Timing.time x)))
             (Timing.series obs)).

Lemma timed_of_columns : forall (iv : Timing.Time -> Interventions) ts l,
  map Timing.time l = firstn (length l) ts ->
  map (fun p => Timing.mkTimed (fst p) (column_assessment (snd p)))
      (combine ts
         (map (fun x => mkColumn (Timing.assessment x) (iv (Timing.time x)))
              l)) = l.
Proof.
  intros iv ts l. revert ts.
  induction l as [|[t0 a] l' IH]; intros ts H.
  - destruct ts; reflexivity.
  - destruct ts as [|t ts']; simpl in H; [discriminate H|].
    injection H as Ht Hrest. subst t0. simpl. f_equal. apply IH. exact Hrest.
Qed.

(** A form built from observations is well formed. *)
Theorem of_observations_well_formed : forall ga obs iv,
  well_formed (of_observations ga obs iv).
Proof.
  intros ga obs iv.
  assert (Hv : Timing.Valid (Timing.series obs)).
  { apply Timing.valid_iff_series. exists obs. reflexivity. }
  destruct (Timing.valid_shape _ Hv) as [Ht Hl].
  unfold well_formed, of_observations, timed. cbn [columns]. split.
  - rewrite length_map. lia.
  - rewrite (timed_of_columns iv Timing.all (Timing.series obs) Ht). exact Hv.
Qed.

(** ** Reading the form *)

(** The class of the 5-minute score, for an infant of at least 34 weeks,
    where [AAP2015] defines the bands [Engle2007]. *)
Definition five_minute_class (f : t) : option Classification.t :=
  if 34 <=? GestationalAge.weeks (gestational_age f)
  then match columns f with
       | _ :: c5 :: _ =>
           Some (Classification.of_assessment (column_assessment c5))
       | _ => None
       end
  else None.

Theorem five_minute_class_defined : forall f,
  well_formed f ->
  ((exists c, five_minute_class f = Some c) <->
   34 <= GestationalAge.weeks (gestational_age f)).
Proof.
  intros f Hwf. pose proof (well_formed_columns f Hwf) as [Hlo _].
  unfold five_minute_class.
  destruct (columns f) as [|c1 [|c5 rest]]; simpl in Hlo; try lia.
  decide_thresholds; split;
    first [ intros [c H]; discriminate
          | intro; first [lia | eexists; reflexivity] ].
Qed.

(** Whether the 5-minute score calls for an umbilical arterial blood gas
    sample. *)
Definition gas_sample_indicated (f : t) : bool :=
  match columns f with
  | _ :: c5 :: _ =>
      CordBloodGas.sample_indicated (Assessment.total (column_assessment c5))
  | _ => false
  end.

(** When the sample is indicated, a 10-minute score is due as well. *)
Theorem gas_sample_implies_10_minute_score : forall f,
  well_formed f -> gas_sample_indicated f = true -> 3 <= length (columns f).
Proof.
  intros [ga cols] [Hlen Hv] Hg.
  rewrite <- (timed_length _ Hlen).
  unfold gas_sample_indicated, timed, Timing.Valid, Timing.all in *.
  cbn [columns] in *.
  destruct cols as [|c1 [|c5 rest]]; try discriminate Hg.
  apply CordBloodGas.sample_indicated_iff in Hg.
  cbn [combine map fst snd] in Hv.
  apply Timing.follows_cons_inv in Hv.
  destruct Hv as [_ [[Hnil _] | [_ Hr1]]]; [discriminate Hnil|].
  apply Timing.follows_cons_inv in Hr1.
  destruct Hr1 as [_ [[_ Hs] | [_ Hr2]]].
  - cbn [Timing.continues Timing.assessment] in Hs.
    apply Nat.ltb_ge in Hs. lia.
  - destruct (Timing.follows_shape _ _ Hr2) as [_ Hl].
    cbn [combine map fst snd length]. lia.
Qed.

End ExpandedForm.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 12: THERAPEUTIC HYPOTHERMIA                     *)
(*                                                                            *)
(*  Eligibility criteria of the NICHD whole-body hypothermia trial            *)
(*  [Shankaran2005]: gestational age of at least 36 weeks, evaluation by 6    *)
(*  hours of age, severe acidosis or an intermediate or missing blood gas     *)
(*  with an acute perinatal event and either a 10-minute score of 5 or less   *)
(*  or assisted ventilation from birth for at least 10 minutes, and           *)
(*  moderate or severe encephalopathy or seizures. [AHA2020] recommends       *)
(*  evaluation for therapeutic hypothermia from 36 weeks.                     *)
(*                                                                            *)
(******************************************************************************)

Module TherapeuticHypothermia.

(** ** Physiological criteria *)

(** pH in hundredths and base deficit in tenths of mmol/L, from cord blood
    or any blood sample in the first hour; either may be missing. *)

Definition ph_severe (ph : option nat) : bool :=
  match ph with
  | Some p => p <=? 7 * hundred
  | None => false
  end.

Definition bd_severe (bd : option nat) : bool :=
  match bd with
  | Some b => 16 * 10 <=? b
  | None => false
  end.

Definition ph_intermediate (ph : option nat) : bool :=
  match ph with
  | Some p => (7 * hundred + 1 <=? p) && (p <=? 7 * hundred + 15)
  | None => false
  end.

Definition bd_intermediate (bd : option nat) : bool :=
  match bd with
  | Some b => (hundred <=? b) && (b <=? 15 * 10 + 9)
  | None => false
  end.

Definition gas_missing (ph bd : option nat) : bool :=
  match ph, bd with
  | None, None => true
  | _, _ => false
  end.

(** pH of 7.0 or less, or base deficit of 16 mmol/L or more. *)
Definition severe_acidosis (ph bd : option nat) : bool :=
  ph_severe ph || bd_severe bd.

(** pH between 7.01 and 7.15, base deficit between 10 and 15.9 mmol/L, or
    no blood gas available. *)
Definition intermediate_or_missing (ph bd : option nat) : bool :=
  ph_intermediate ph || bd_intermediate bd || gas_missing ph bd.

(** An acute perinatal event and either a 10-minute score of 5 or less or
    assisted ventilation from birth for at least 10 minutes. *)
Definition additional_criteria (event : bool) (apgar10 : option nat)
    (ventilated : bool) : bool :=
  event
  && ((match apgar10 with Some s => s <=? 5 | None => false end) || ventilated).

Definition physiologic (ph bd : option nat) (event : bool)
    (apgar10 : option nat) (ventilated : bool) : bool :=
  severe_acidosis ph bd
  || (intermediate_or_missing ph bd
      && additional_criteria event apgar10 ventilated).

(** With severe acidosis the criteria are met whatever the perinatal
    course, the 10-minute score and the ventilation. *)
Theorem severe_acidosis_suffices : forall ph bd event apgar10 ventilated,
  severe_acidosis ph bd = true ->
  physiologic ph bd event apgar10 ventilated = true.
Proof.
  intros ph bd event apgar10 ventilated H. unfold physiologic.
  rewrite H. reflexivity.
Qed.

(** Without severe acidosis the criteria require the acute event and the
    10-minute score or ventilation. *)
Theorem additional_criteria_required : forall ph bd event apgar10 ventilated,
  severe_acidosis ph bd = false ->
  physiologic ph bd event apgar10 ventilated = true ->
  event = true /\
  ((exists s, apgar10 = Some s /\ s <= 5) \/ ventilated = true).
Proof.
  intros ph bd event apgar10 ventilated Hs. unfold physiologic.
  rewrite Hs. unfold additional_criteria.
  destruct (intermediate_or_missing ph bd), event, ventilated,
    apgar10 as [s|]; calc; decide_thresholds; intro H;
    try discriminate; split; try reflexivity;
    first [ right; reflexivity
          | left; exists s; split; [reflexivity | assumption] ].
Qed.

(** The criteria are monotone: a lower pH, a larger base deficit or a lower
    10-minute score never loses them. *)
Lemma ph_progress : forall p p',
  p' <= p ->
  (ph_severe (Some p) = true -> ph_severe (Some p') = true) /\
  (ph_intermediate (Some p) = true ->
     ph_severe (Some p') = true \/ ph_intermediate (Some p') = true).
Proof.
  intros p p' Hle. unfold ph_severe, ph_intermediate.
  decide_thresholds; calc; split; solve_cases.
Qed.

Lemma bd_progress : forall b b',
  b <= b' ->
  (bd_severe (Some b) = true -> bd_severe (Some b') = true) /\
  (bd_intermediate (Some b) = true ->
     bd_severe (Some b') = true \/ bd_intermediate (Some b') = true).
Proof.
  intros b b' Hle. unfold bd_severe, bd_intermediate.
  decide_thresholds; calc; split; solve_cases.
Qed.

Lemma gas_missing_some_l : forall p bd, gas_missing (Some p) bd = false.
Proof. intros p bd. reflexivity. Qed.

Lemma gas_missing_some_r : forall ph b, gas_missing ph (Some b) = false.
Proof. intros [p|] b; reflexivity. Qed.

Local Ltac boolean_cases :=
  let Hs := fresh "Hs" in
  let Hi := fresh "Hi" in
  let H := fresh "H" in
  simpl; intros Hs Hi H;
  first [ reflexivity | discriminate
        | (specialize (Hs eq_refl); discriminate)
        | (destruct (Hi eq_refl); discriminate) ].

Lemma additional_monotone_apgar : forall event s s' ventilated,
  s' <= s ->
  additional_criteria event (Some s) ventilated = true ->
  additional_criteria event (Some s') ventilated = true.
Proof.
  intros event s s' ventilated Hle. unfold additional_criteria.
  destruct event, ventilated; calc; decide_thresholds; calc; solve_cases.
Qed.

Theorem physiologic_monotone_ph : forall p p' bd event apgar10 ventilated,
  p' <= p ->
  physiologic (Some p) bd event apgar10 ventilated = true ->
  physiologic (Some p') bd event apgar10 ventilated = true.
Proof.
  intros p p' bd event apgar10 ventilated Hle.
  destruct (ph_progress p p' Hle) as [Hs Hi].
  unfold physiologic, severe_acidosis, intermediate_or_missing.
  rewrite !gas_missing_some_l. revert Hs Hi.
  destruct (ph_severe (Some p)), (ph_intermediate (Some p)),
    (ph_severe (Some p')), (ph_intermediate (Some p')),
    (bd_severe bd), (bd_intermediate bd),
    (additional_criteria event apgar10 ventilated); boolean_cases.
Qed.

Theorem physiologic_monotone_bd : forall ph b b' event apgar10 ventilated,
  b <= b' ->
  physiologic ph (Some b) event apgar10 ventilated = true ->
  physiologic ph (Some b') event apgar10 ventilated = true.
Proof.
  intros ph b b' event apgar10 ventilated Hle.
  destruct (bd_progress b b' Hle) as [Hs Hi].
  unfold physiologic, severe_acidosis, intermediate_or_missing.
  rewrite !gas_missing_some_r. revert Hs Hi.
  destruct (bd_severe (Some b)), (bd_intermediate (Some b)),
    (bd_severe (Some b')), (bd_intermediate (Some b')),
    (ph_severe ph), (ph_intermediate ph),
    (additional_criteria event apgar10 ventilated); boolean_cases.
Qed.

Theorem physiologic_monotone_apgar : forall ph bd event s s' ventilated,
  s' <= s ->
  physiologic ph bd event (Some s) ventilated = true ->
  physiologic ph bd event (Some s') ventilated = true.
Proof.
  intros ph bd event s s' ventilated Hle H. unfold physiologic in *.
  apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H].
  - left. exact H.
  - apply andb_true_iff in H. destruct H as [Hi Ha]. right.
    apply andb_true_iff. split; [exact Hi|].
    exact (additional_monotone_apgar event s s' ventilated Hle Ha).
Qed.

(** The trial counts a pH of exactly 7.00 as severe acidosis, while the
    sign of [ACOG2014] requires a pH below 7.0. *)
Theorem ph_7_00_thresholds : forall g,
  CordBloodGas.PH.value (CordBloodGas.ph g) = 700 ->
  severe_acidosis (Some (CordBloodGas.PH.value (CordBloodGas.ph g))) None
    = true /\
  CordBloodGas.ph_below_7 g = false.
Proof.
  intros g H. unfold CordBloodGas.ph_below_7. rewrite H. split; reflexivity.
Qed.

(** ** Candidate *)

Inductive Encephalopathy : Type :=
  | NoEncephalopathy : Encephalopathy
  | MildEncephalopathy : Encephalopathy
  | ModerateEncephalopathy : Encephalopathy
  | SevereEncephalopathy : Encephalopathy.

Definition encephalopathy_eq_dec : forall e1 e2 : Encephalopathy,
  {e1 = e2} + {e1 <> e2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Record Candidate : Type := mkCandidate {
  gestational_age : GestationalAge.t;
  age_hours : nat;
  ph : option CordBloodGas.PH.t;
  base_deficit : option CordBloodGas.BaseDeficit.t;
  acute_perinatal_event : bool;
  apgar_10 : option Assessment.t;
  ventilated_from_birth_10min : bool;
  encephalopathy : Encephalopathy;
  seizures : bool;
  major_congenital_abnormality : bool;
  birth_weight : BirthWeight.t;
  moribund : bool
}.

(** Moderate or severe encephalopathy, or seizures. *)
Definition neurologic (e : Encephalopathy) (seizing : bool) : bool :=
  (match e with
   | ModerateEncephalopathy | SevereEncephalopathy => true
   | NoEncephalopathy | MildEncephalopathy => false
   end) || seizing.

(** Exclusions: evaluation after 6 hours of age, a major congenital
    abnormality, a birth weight of 1,800 g or less, or a moribund infant. *)
Definition excluded (c : Candidate) : bool :=
  (6 <? age_hours c) || major_congenital_abnormality c
  || (BirthWeight.grams (birth_weight c) <=? 18 * hundred) || moribund c.

Definition eligible (c : Candidate) : bool :=
  (36 <=? GestationalAge.weeks (gestational_age c))
  && physiologic (option_map CordBloodGas.PH.value (ph c))
       (option_map CordBloodGas.BaseDeficit.value (base_deficit c))
       (acute_perinatal_event c)
       (option_map Assessment.total (apgar_10 c))
       (ventilated_from_birth_10min c)
  && neurologic (encephalopathy c) (seizures c)
  && negb (excluded c).

Theorem eligible_requires : forall c,
  eligible c = true ->
  36 <= GestationalAge.weeks (gestational_age c) /\
  age_hours c <= 6 /\
  1800 < BirthWeight.grams (birth_weight c) /\
  major_congenital_abnormality c = false /\
  moribund c = false /\
  (encephalopathy c = ModerateEncephalopathy \/
   encephalopathy c = SevereEncephalopathy \/ seizures c = true).
Proof.
  intros c H. unfold eligible in H.
  apply andb_true_iff in H. destruct H as [H Hex].
  apply andb_true_iff in H. destruct H as [H Hn].
  apply andb_true_iff in H. destruct H as [Hga _].
  apply Nat.leb_le in Hga.
  apply negb_true_iff in Hex. unfold excluded in Hex.
  apply orb_false_iff in Hex. destruct Hex as [Hex Hmor].
  apply orb_false_iff in Hex. destruct Hex as [Hex Hbw].
  apply orb_false_iff in Hex. destruct Hex as [Hage Hmca].
  apply Nat.ltb_ge in Hage. apply Nat.leb_gt in Hbw.
  split; [exact Hga|]. split; [exact Hage|]. split; [arith|].
  split; [exact Hmca|]. split; [exact Hmor|].
  unfold neurologic in Hn. destruct (encephalopathy c); simpl in Hn; auto.
Qed.

End TherapeuticHypothermia.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 13: SCORE TRAJECTORIES                          *)
(*                                                                            *)
(*  Successive totals of one infant. A trajectory is characterized by its     *)
(*  adjacent pairs; a chain under a reflexive and transitive relation         *)
(*  relates any earlier total to any later one, and the class follows the     *)
(*  total.                                                                    *)
(*                                                                            *)
(******************************************************************************)

Module Trajectory.

(** Adjacent pairs of a list. *)
Fixpoint pairs (l : list nat) : list (nat * nat) :=
  match l with
  | x :: ((y :: _) as rest) => (x, y) :: pairs rest
  | _ => []
  end.

(** [chain R l]: every element is related by [R] to its successor. *)
Definition chain (R : nat -> nat -> Prop) (l : list nat) : Prop :=
  forall p, In p (pairs l) -> R (fst p) (snd p).

Lemma chain_tail : forall R x l, chain R (x :: l) -> chain R l.
Proof.
  intros R x l H p Hp. apply H.
  destruct l as [|y l']; [contradiction|]. simpl. right. exact Hp.
Qed.

Lemma chain_head : forall R,
  (forall a b c, R a b -> R b c -> R a c) ->
  forall l x y, chain R (x :: l) -> In y l -> R x y.
Proof.
  intros R Htrans. induction l as [|z l' IH]; intros x y H Hy.
  - contradiction.
  - assert (Hxz : R x z) by (apply (H (x, z)); simpl; left; reflexivity).
    destruct Hy as [Hy|Hy].
    + subst y. exact Hxz.
    + apply (Htrans x z y Hxz). apply IH; [|exact Hy].
      apply (chain_tail R x). exact H.
Qed.

(** In a chain under a reflexive and transitive relation, each element is
    related to every later one. *)
Theorem chain_nth : forall R,
  (forall a, R a a) -> (forall a b c, R a b -> R b c -> R a c) ->
  forall l i j,
  chain R l -> i <= j -> j < length l -> R (nth i l 0) (nth j l 0).
Proof.
  intros R Hrefl Htrans. induction l as [|x l' IH]; intros i j H Hij Hj.
  - simpl in Hj. lia.
  - destruct i as [|i'], j as [|j']; simpl.
    + apply Hrefl.
    + apply (chain_head R Htrans l' x); [exact H|].
      apply nth_In. simpl in Hj. lia.
    + lia.
    + apply IH; [apply (chain_tail R x); exact H | lia | simpl in Hj; lia].
Qed.

Definition nondecreasing : list nat -> Prop := chain le.
Definition nonincreasing : list nat -> Prop := chain ge.
Definition constant : list nat -> Prop := chain eq.

(** ** Class along a trajectory *)

Theorem nondecreasing_class : forall l i j,
  nondecreasing l -> i <= j -> j < length l ->
  Classification.le (Classification.of_score (nth i l 0))
                    (Classification.of_score (nth j l 0)).
Proof.
  intros l i j H Hij Hj. apply Classification.of_score_monotone.
  apply (chain_nth le Nat.le_refl Nat.le_trans l i j H Hij Hj).
Qed.

Theorem nonincreasing_class : forall l i j,
  nonincreasing l -> i <= j -> j < length l ->
  Classification.le (Classification.of_score (nth j l 0))
                    (Classification.of_score (nth i l 0)).
Proof.
  intros l i j H Hij Hj. apply Classification.of_score_monotone.
  assert (Hge : nth i l 0 >= nth j l 0).
  { apply (chain_nth ge); [intro a; lia | intros a b c; lia | exact H
                          | exact Hij | exact Hj]. }
  exact Hge.
Qed.

(** Along a nondecreasing trajectory a reassuring score stays reassuring. *)
Theorem reassuring_persists : forall l i j,
  nondecreasing l -> i <= j -> j < length l ->
  Classification.of_score (nth i l 0) = Classification.Reassuring ->
  Classification.of_score (nth j l 0) = Classification.Reassuring.
Proof.
  intros l i j H Hij Hj Hr.
  pose proof (chain_nth le Nat.le_refl Nat.le_trans l i j H Hij Hj) as Hle.
  destruct (Classification.of_score_spec (nth i l 0)) as [_ [_ Ri]].
  destruct (Classification.of_score_spec (nth j l 0)) as [_ [_ Rj]].
  apply Rj. apply Ri in Hr. lia.
Qed.

(** ** Trend *)

Definition rises (p : nat * nat) : bool := fst p <? snd p.
Definition falls (p : nat * nat) : bool := snd p <? fst p.

Inductive Trend : Type :=
  | Stable : Trend
  | Improving : Trend
  | Declining : Trend
  | Mixed : Trend.

Definition trend_eq_dec : forall t1 t2 : Trend, {t1 = t2} + {t1 <> t2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition trend (l : list nat) : Trend :=
  match existsb rises (pairs l), existsb falls (pairs l) with
  | false, false => Stable
  | true, false => Improving
  | false, true => Declining
  | true, true => Mixed
  end.

Lemma rises_iff : forall l,
  existsb rises (pairs l) = true <->
  exists p, In p (pairs l) /\ fst p < snd p.
Proof.
  intros l. rewrite existsb_exists. unfold rises.
  split; intros [p [Hp H]]; exists p; (split; [exact Hp|]);
    apply Nat.ltb_lt; exact H.
Qed.

Lemma falls_iff : forall l,
  existsb falls (pairs l) = true <->
  exists p, In p (pairs l) /\ snd p < fst p.
Proof.
  intros l. rewrite existsb_exists. unfold falls.
  split; intros [p [Hp H]]; exists p; (split; [exact Hp|]);
    apply Nat.ltb_lt; exact H.
Qed.

Lemma no_rise_iff : forall l,
  existsb rises (pairs l) = false <-> nonincreasing l.
Proof.
  intros l. split.
  - intros H p Hp. destruct (le_lt_dec (snd p) (fst p)) as [Hle|Hlt];
      [exact Hle|].
    exfalso.
    assert (Ht : existsb rises (pairs l) = true).
    { apply rises_iff. exists p. split; assumption. }
    rewrite H in Ht. discriminate.
  - intros H. destruct (existsb rises (pairs l)) eqn:E; [|reflexivity].
    apply rises_iff in E. destruct E as [p [Hp Hr]].
    specialize (H p Hp). unfold ge in H. lia.
Qed.

Lemma no_fall_iff : forall l,
  existsb falls (pairs l) = false <-> nondecreasing l.
Proof.
  intros l. split.
  - intros H p Hp. destruct (le_lt_dec (fst p) (snd p)) as [Hle|Hlt];
      [exact Hle|].
    exfalso.
    assert (Ht : existsb falls (pairs l) = true).
    { apply falls_iff. exists p. split; assumption. }
    rewrite H in Ht. discriminate.
  - intros H. destruct (existsb falls (pairs l)) eqn:E; [|reflexivity].
    apply falls_iff in E. destruct E as [p [Hp Hr]].
    specialize (H p Hp). lia.
Qed.

Lemma constant_iff : forall l,
  constant l <->
  existsb rises (pairs l) = false /\ existsb falls (pairs l) = false.
Proof.
  intros l. rewrite no_rise_iff, no_fall_iff. split.
  - intros H. split; intros p Hp; specialize (H p Hp); unfold ge; lia.
  - intros [H1 H2] p Hp. specialize (H1 p Hp). specialize (H2 p Hp).
    unfold ge in H1. lia.
Qed.

(** A trajectory is stable when it never changes, improving when it rises
    and never falls, declining when it falls and never rises, and mixed
    when it does both. *)
Theorem trend_spec : forall l,
  (trend l = Stable <-> constant l) /\
  (trend l = Improving <->
     nondecreasing l /\ exists p, In p (pairs l) /\ fst p < snd p) /\
  (trend l = Declining <->
     nonincreasing l /\ exists p, In p (pairs l) /\ snd p < fst p) /\
  (trend l = Mixed <->
     (exists p, In p (pairs l) /\ fst p < snd p) /\
     (exists p, In p (pairs l) /\ snd p < fst p)).
Proof.
  intros l. unfold trend.
  rewrite constant_iff, <- !no_fall_iff, <- !no_rise_iff, <- !rises_iff,
    <- !falls_iff.
  destruct (existsb rises (pairs l)), (existsb falls (pairs l));
    split_conj; split; solve_cases.
Qed.

(** Totals of a series of timed assessments, in order. *)
Definition of_series (l : list Timing.Timed) : list nat :=
  map (fun x => Assessment.total (Timing.assessment x)) l.

End Trajectory.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 14: AUDIT LOG                                   *)
(*                                                                            *)
(*  An append-only record of the events on one assessment. A log opens        *)
(*  with its creation, runs forward in time and accepts nothing after it      *)
(*  is finalized. The guarded append preserves these properties and           *)
(*  reaches every log that has them.                                          *)
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

Record Event : Type := mkEvent {
  event_type : EventType;
  timestamp : nat;
  user : nat;
  snapshot : Assessment.t
}.

(** A log holds its events most recent first. *)
Definition Log : Type := list Event.

Definition is_created (e : Event) : bool :=
  match event_type e with
  | Created => true
  | _ => false
  end.

Definition is_finalized (e : Event) : bool :=
  match event_type e with
  | Finalized => true
  | _ => false
  end.

(** [guard e prev]: the event [e] may follow [prev]. *)
Definition guard (e prev : Event) : bool :=
  negb (is_created e) && negb (is_finalized prev)
  && (timestamp prev <=? timestamp e).

Lemma guard_iff : forall e prev,
  guard e prev = true <->
  is_created e = false /\ is_finalized prev = false /\
  timestamp prev <= timestamp e.
Proof.
  intros e prev. unfold guard.
  rewrite !andb_true_iff, !negb_true_iff, Nat.leb_le. tauto.
Qed.

Set Elimination Schemes.
Inductive WellFormed : Log -> Prop :=
  | wf_created : forall e, is_created e = true -> WellFormed [e]
  | wf_append : forall e prev rest,
      WellFormed (prev :: rest) ->
      guard e prev = true ->
      WellFormed (e :: prev :: rest).
Unset Elimination Schemes.

(** ** Operations *)

Definition create (ts u : nat) (a : Assessment.t) : Log :=
  [mkEvent Created ts u a].

Definition append (log : Log) (e : Event) : option Log :=
  match log with
  | [] => None
  | prev :: _ => if guard e prev then Some (e :: log) else None
  end.

Theorem create_well_formed : forall ts u a, WellFormed (create ts u a).
Proof. intros ts u a. apply wf_created. reflexivity. Qed.

Theorem append_preserves : forall log e log',
  WellFormed log -> append log e = Some log' -> WellFormed log'.
Proof.
  intros log e log' Hwf H. unfold append in H.
  destruct log as [|prev rest]; [discriminate|].
  destruct (guard e prev) eqn:G; [|discriminate].
  inversion H. apply wf_append; assumption.
Qed.

(** Every well-formed log of more than one event is the append of its
    latest event to the rest. *)
Theorem append_complete : forall e prev rest,
  WellFormed (e :: prev :: rest) ->
  append (prev :: rest) e = Some (e :: prev :: rest).
Proof.
  intros e prev rest H. inversion H; subst. unfold append.
  match goal with
  | G : guard _ _ = true |- _ => rewrite G
  end. reflexivity.
Qed.

(** ** Decision procedure *)

Fixpoint well_formedb (log : Log) : bool :=
  match log with
  | [] => false
  | e :: rest =>
      match rest with
      | [] => is_created e
      | prev :: _ => guard e prev && well_formedb rest
      end
  end.

Lemma well_formedb_step : forall e prev rest,
  well_formedb (e :: prev :: rest) =
  guard e prev && well_formedb (prev :: rest).
Proof. reflexivity. Qed.

Theorem well_formedb_correct : forall log,
  well_formedb log = true <-> WellFormed log.
Proof.
  induction log as [|e log' IH].
  - simpl. split; [discriminate | intro H; inversion H].
  - destruct log' as [|prev rest].
    + simpl. split.
      * intro H. apply wf_created. exact H.
      * intro H. inversion H. assumption.
    + rewrite well_formedb_step, andb_true_iff, IH. split.
      * intros [G Hwf]. apply wf_append; assumption.
      * intro H. inversion H; subst. split; assumption.
Qed.

(** ** Consequences *)

(** No event is recorded after a finalization. *)
Theorem finalized_only_latest : forall log e,
  WellFormed (e :: log) -> forall x, In x log -> is_finalized x = false.
Proof.
  induction log as [|prev rest IH]; intros e H x Hx.
  - contradiction.
  - inversion H; subst.
    match goal with
    | G : guard _ _ = true |- _ =>
        apply guard_iff in G; destruct G as [_ [Gf _]]
    end.
    destruct Hx as [Hx|Hx].
    + subst x. exact Gf.
    + eapply IH; eassumption.
Qed.

(** The latest event is not earlier than any other. *)
Theorem chronological : forall log e,
  WellFormed (e :: log) -> forall x, In x log -> timestamp x <= timestamp e.
Proof.
  induction log as [|prev rest IH]; intros e H x Hx.
  - contradiction.
  - inversion H; subst.
    match goal with
    | G : guard _ _ = true |- _ =>
        apply guard_iff in G; destruct G as [_ [_ Gt]]
    end.
    destruct Hx as [Hx|Hx].
    + subst x. exact Gt.
    + assert (Hle : timestamp x <= timestamp prev) by (eapply IH; eassumption).
      lia.
Qed.

(** The creation is the oldest event and the only creation. *)
Theorem created_only_first : forall log,
  WellFormed log ->
  exists e0 later,
    log = later ++ [e0] /\ is_created e0 = true /\
    forall x, In x later -> is_created x = false.
Proof.
  intros log H. induction H as [e He | e prev rest Hwf IH G].
  - exists e, []. split; [reflexivity|]. split; [exact He|].
    intros x Hx. contradiction.
  - destruct IH as [e0 [later [Heq [Hc Hl]]]].
    apply guard_iff in G. destruct G as [Gc _].
    exists e0, (e :: later). split; [rewrite Heq; reflexivity|].
    split; [exact Hc|].
    intros x [Hx|Hx]; [subst x; exact Gc | apply Hl; exact Hx].
Qed.

(** A finalized log accepts no further event. *)
Theorem finalized_terminal : forall e log e',
  is_finalized e = true -> append (e :: log) e' = None.
Proof.
  intros e log e' Hf. unfold append, guard. rewrite Hf.
  destruct (is_created e'); reflexivity.
Qed.

(** Totals recorded in the log, oldest first. *)
Definition score_history (log : Log) : list nat :=
  map (fun e => Assessment.total (snapshot e)) (rev log).

End AuditTrail.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 15: WORKED EXAMPLE                              *)
(*                                                                            *)
(*  One infant followed through the modules: scores of 2, 5 and 8 at 1, 5     *)
(*  and 10 minutes.                                                           *)
(*                                                                            *)
(******************************************************************************)

Module Examples.

Definition at_1 : Assessment.t :=
  Assessment.mk Appearance.BlueOrPale Pulse.Below100 Grimace.NoResponse
                Activity.Limp Respiration.WeakCry.

Definition at_5 : Assessment.t :=
  Assessment.mk Appearance.Acrocyanotic Pulse.AtLeast100 Grimace.GrimaceOnly
                Activity.Limp Respiration.WeakCry.

Definition at_10 : Assessment.t :=
  Assessment.mk Appearance.CompletelyPink Pulse.AtLeast100 Grimace.GrimaceOnly
                Activity.SomeFlexion Respiration.GoodCry.

Definition observed (t : Timing.Time) : Assessment.t :=
  match t with
  | Timing.Min1 => at_1
  | Timing.Min5 => at_5
  | _ => at_10
  end.

(** The series ends with the 10-minute score, the first of 7 or more. *)
Example totals : Trajectory.of_series (Timing.series observed) = [2; 5; 8].
Proof. reflexivity. Qed.

Example classes :
  map Classification.of_score [2; 5; 8] =
  [Classification.Low; Classification.ModeratelyAbnormal;
   Classification.Reassuring].
Proof. reflexivity. Qed.

Example trend : Trajectory.trend [2; 5; 8] = Trajectory.Improving.
Proof. reflexivity. Qed.

(** At 1 minute the heart rate below 100 meets the criterion for
    ventilation. *)
Example ventilation_at_1 :
  ScoreAndResuscitation.ventilation_criterion at_1 = true.
Proof. reflexivity. Qed.

Example step_after_30s_ventilation :
  NRP.step (NRP.mkState (NRP.mkFindings NRP.Apnea Pulse.BandBelow60 false)
                        30 0) = NRP.Compress.
Proof. reflexivity. Qed.

(** The expanded form, with oxygen and ventilation recorded at 1 minute. *)
Definition ga_39_2 : GestationalAge.t :=
  GestationalAge.mk (GestationalAge.Weeks.mk 39 eq_refl)
                    (GestationalAge.Days.mk 2 eq_refl).

Definition form : ExpandedForm.t :=
  ExpandedForm.of_observations ga_39_2 observed
    (fun t => match t with
              | Timing.Min1 =>
                  ExpandedForm.mkInterventions true true false false false
              | _ => ExpandedForm.no_interventions
              end).

Example form_well_formed : ExpandedForm.well_formedb form = true.
Proof. reflexivity. Qed.

Example form_class :
  ExpandedForm.five_minute_class form = Some Classification.ModeratelyAbnormal.
Proof. reflexivity. Qed.

Example form_gas_sample : ExpandedForm.gas_sample_indicated form = true.
Proof. reflexivity. Qed.

(** The 5-minute assessment with color not observed: the total lies
    between 4 and 6, and the class is determined. *)
Definition partial_5 : PartialAssessment.t :=
  PartialAssessment.mk None (Some Pulse.AtLeast100) (Some Grimace.GrimaceOnly)
                       (Some Activity.Limp) (Some Respiration.WeakCry).

Example partial_bounds :
  PartialAssessment.score_min partial_5 = 4 /\
  PartialAssessment.score_max partial_5 = 6 /\
  Classification.of_score 4 = Classification.of_score 6.
Proof. repeat split. Qed.

(** Grades outside 0 to 2 are rejected. *)
Example validated_input :
  Assessment.of_nats_opt 0 1 0 0 1 = Some at_1 /\
  Assessment.of_nats_opt 0 3 0 0 1 = None.
Proof. split; reflexivity. Qed.

(** A candidate for therapeutic hypothermia: 39 weeks, 3 hours of age,
    cord pH 6.95, moderate encephalopathy, 3,200 g. *)
Definition candidate : TherapeuticHypothermia.Candidate :=
  TherapeuticHypothermia.mkCandidate ga_39_2 3
    (Some (CordBloodGas.PH.mk 695 eq_refl)) None false (Some at_10) false
    TherapeuticHypothermia.ModerateEncephalopathy false false
    (BirthWeight.mk 3200 eq_refl) false.

Example candidate_eligible : TherapeuticHypothermia.eligible candidate = true.
Proof. reflexivity. Qed.

(** A log is created, finalized, and then accepts nothing further. *)
Definition log_1 : AuditTrail.Log := AuditTrail.create 60 7 at_1.

Definition finalization : AuditTrail.Event :=
  AuditTrail.mkEvent AuditTrail.Finalized 400 7 at_1.

Example log_finalized :
  AuditTrail.append log_1 finalization = Some (finalization :: log_1).
Proof. reflexivity. Qed.

Example log_closed :
  AuditTrail.append (finalization :: log_1)
    (AuditTrail.mkEvent AuditTrail.Modified 500 7 at_5) = None.
Proof. reflexivity. Qed.

End Examples.

(******************************************************************************)
(*                                                                            *)
(*                    SECTION 16: EXTRACTION                                  *)
(*                                                                            *)
(*  The computational content of each module is extracted to OCaml. Natural   *)
(*  numbers become OCaml int.                                                 *)
(*                                                                            *)
(******************************************************************************)

From Corelib Require Import Extraction ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Set Extraction Output Directory ".".

Extraction "apgar.ml"
  ScoreLevel Appearance Pulse Grimace Activity Respiration Assessment
  Classification PartialAssessment Timing Edition GestationalAge BirthWeight
  SpO2 Temperature CordBloodGas NRP ScoreAndResuscitation ExpandedForm
  TherapeuticHypothermia Trajectory AuditTrail.
