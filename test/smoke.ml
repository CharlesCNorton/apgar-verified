(* Checks on the OCaml code extracted from apgar.v. Exits non-zero when a
   check fails. *)

open Apgar

let failures = ref 0

let check name cond =
  if not cond then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let get = function
  | Some x -> x
  | None -> failwith "validated constructor rejected a test value"

let at_1 =
  { Assessment.appearance = Appearance.BlueOrPale;
    pulse = Pulse.Below100;
    grimace = Grimace.NoResponse;
    activity = Activity.Limp;
    respiration = Respiration.WeakCry }

let at_5 =
  { Assessment.appearance = Appearance.Acrocyanotic;
    pulse = Pulse.AtLeast100;
    grimace = Grimace.GrimaceOnly;
    activity = Activity.Limp;
    respiration = Respiration.WeakCry }

let at_10 =
  { Assessment.appearance = Appearance.CompletelyPink;
    pulse = Pulse.AtLeast100;
    grimace = Grimace.GrimaceOnly;
    activity = Activity.SomeFlexion;
    respiration = Respiration.GoodCry }

let observed = function
  | Timing.Min1 -> at_1
  | Timing.Min5 -> at_5
  | _ -> at_10

let range a b = List.init (b - a + 1) (fun i -> a + i)

let () =
  (* Assessment *)
  check "enumeration has 243 assessments" (List.length Assessment.all = 243);
  check "totals lie in 0..10"
    (List.for_all
       (fun a -> let s = Assessment.total a in 0 <= s && s <= 10)
       Assessment.all);
  check "distribution of totals"
    (List.map Assessment.count_with_total (range 0 10)
     = [1; 5; 15; 30; 45; 51; 45; 30; 15; 5; 1]);
  check "witness totals"
    (List.map (fun n -> Assessment.total (Assessment.witness n)) (range 0 10)
     = range 0 10);
  check "extremes"
    (Assessment.total Assessment.minimum = 0
     && Assessment.total Assessment.maximum = 10);
  check "validated construction"
    (Assessment.of_nats_opt 0 1 0 0 1 = Some at_1
     && Assessment.of_nats_opt 0 3 0 0 1 = None);
  check "hamming"
    (Assessment.hamming at_1 at_1 = 0 && Assessment.hamming at_1 at_5 = 3);

  (* Classification *)
  check "class bands"
    (List.map Classification.of_score [0; 3; 4; 6; 7; 10]
     = Classification.
         [Low; Low; ModeratelyAbnormal; ModeratelyAbnormal; Reassuring;
          Reassuring]);

  (* Partial assessment *)
  let partial =
    { PartialAssessment.appearance = None;
      pulse = Some Pulse.AtLeast100;
      grimace = Some Grimace.GrimaceOnly;
      activity = Some Activity.Limp;
      respiration = Some Respiration.WeakCry }
  in
  check "partial bounds"
    (PartialAssessment.score_min partial = 4
     && PartialAssessment.score_max partial = 6
     && PartialAssessment.missing partial = 1);

  (* Timing *)
  let series = Timing.series observed in
  check "series totals" (Trajectory.of_series series = [2; 5; 8]);
  check "series is valid" (Timing.validb series);
  check "a series without the 5-minute score is invalid"
    (not (Timing.validb [List.hd series]));
  check "trend" (Trajectory.trend [2; 5; 8] = Trajectory.Improving);

  (* Bounded quantities *)
  check "saturation range" (SpO2.make 100 <> None && SpO2.make 101 = None);
  check "temperature range"
    (Temperature.make 199 = None && Temperature.make 365 <> None);
  check "pH range"
    (CordBloodGas.PH.make 599 = None && CordBloodGas.PH.make 700 <> None);
  check "gestational age range"
    (GestationalAge.make 39 2 <> None && GestationalAge.make 39 7 = None
     && GestationalAge.make 19 0 = None);

  (* Physiological context *)
  check "saturation targets"
    (SpO2.target Edition.NRP8 1 = Some (60, 65)
     && SpO2.target Edition.NRP9 1 = None
     && SpO2.target Edition.NRP9 5 = Some (80, 85)
     && SpO2.target Edition.NRP9 10 = Some (85, 95));
  check "temperature bands"
    (Temperature.classify (get (Temperature.make 362))
     = Temperature.MildHypothermia
     && Temperature.is_hypothermic (get (Temperature.make 362))
     && Temperature.classify (get (Temperature.make 365)) = Temperature.Normal);
  check "cord gas sample" (CordBloodGas.sample_indicated 5
                           && not (CordBloodGas.sample_indicated 6));

  (* Resuscitation *)
  let state hr vent comp =
    { NRP.findings =
        { NRP.effort = NRP.Apnea; heart_rate = hr;
          persistent_cyanosis = false };
      effective_ventilation_secs = vent;
      compression_secs = comp }
  in
  check "indicated steps"
    (NRP.step (state Pulse.BandBelow60 0 0) = NRP.Ventilate
     && NRP.step (state Pulse.BandBelow60 30 0) = NRP.Compress
     && NRP.step (state Pulse.BandBelow60 30 60) = NRP.GiveEpinephrine);
  check "epinephrine for 3000 g"
    (NRP.dose_mcg 3000 (NRP.suggested_dose NRP.Intravenous) = 60
     && NRP.volume_ul 60 = 600
     && NRP.dose_mcg 3000 (NRP.suggested_dose NRP.Endotracheal) = 300);
  check "tube size by edition"
    (NRP.tube_by_weight Edition.NRP8 1100 = NRP.Tube30
     && NRP.tube_by_weight Edition.NRP9 1100 = NRP.Tube25
     && NRP.tube_by_weight Edition.NRP9 1200 = NRP.Tube30);
  check "tube depth"
    (NRP.depth_by_gestation 22 = None
     && NRP.depth_by_gestation 39 = Some 85);
  check "initial oxygen"
    (NRP.initial_fio2 Edition.NRP8 30 = (21, 30)
     && NRP.initial_fio2 Edition.NRP9 30 = (30, 100));

  (* Score and resuscitation *)
  check "criterion at totals 9 and 3"
    (ScoreAndResuscitation.ventilation_criterion
       (ScoreAndResuscitation.meeting 9)
     && not (ScoreAndResuscitation.ventilation_criterion
               (ScoreAndResuscitation.not_meeting 3)));

  (* Expanded form *)
  let ga = get (GestationalAge.make 39 2) in
  let form =
    ExpandedForm.of_observations ga observed
      (fun _ -> ExpandedForm.no_interventions)
  in
  check "form" (ExpandedForm.well_formedb form
                && List.length form.ExpandedForm.columns = 3
                && ExpandedForm.five_minute_class form
                   = Some Classification.ModeratelyAbnormal
                && ExpandedForm.gas_sample_indicated form);

  (* Therapeutic hypothermia *)
  let candidate ph =
    { TherapeuticHypothermia.gestational_age = ga;
      age_hours = 3;
      ph = CordBloodGas.PH.make ph;
      base_deficit = None;
      acute_perinatal_event = false;
      apgar_10 = Some at_10;
      ventilated_from_birth_10min = false;
      encephalopathy = TherapeuticHypothermia.ModerateEncephalopathy;
      seizures = false;
      major_congenital_abnormality = false;
      birth_weight = get (BirthWeight.make 3200);
      moribund = false }
  in
  check "hypothermia eligibility"
    (TherapeuticHypothermia.eligible (candidate 695)
     && TherapeuticHypothermia.eligible (candidate 700)
     && not (TherapeuticHypothermia.eligible (candidate 710)));

  (* Audit log *)
  let log = AuditTrail.create 60 7 at_1 in
  let finalization =
    { AuditTrail.event_type = AuditTrail.Finalized; timestamp = 400;
      user = 7; snapshot = at_1 }
  in
  let modification =
    { AuditTrail.event_type = AuditTrail.Modified; timestamp = 500;
      user = 7; snapshot = at_5 }
  in
  check "audit log"
    (AuditTrail.well_formedb log
     && AuditTrail.append log finalization = Some (finalization :: log)
     && AuditTrail.append (finalization :: log) modification = None
     && AuditTrail.append log { modification with timestamp = 30 } = None);

  if !failures > 0 then begin
    Printf.printf "%d checks failed\n" !failures;
    exit 1
  end
  else print_endline "smoke checks passed"
