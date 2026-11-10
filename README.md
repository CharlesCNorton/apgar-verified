# apgar-verified

`apgar.v` is a Rocq formalization of the Apgar score and of the delivery-room rules that surround it. Every definition, statement and proof is in that one file, and its computational content is extracted to OCaml. The scoring, classification, timing and reporting form follow the joint statement of the American Academy of Pediatrics and the American College of Obstetricians and Gynecologists (2015, reaffirmed 2025). The resuscitation rules follow the Neonatal Resuscitation Program, 8th edition, together with the values the 9th edition changes, and the cooling criteria follow the NICHD whole-body hypothermia trial. The reference list is at the head of the file, and each rule cites its entry.

## Contents

The file is divided into numbered sections of one or more modules each. The table gives what each section states.

| Section | Modules | Statements |
|---|---|---|
| 0, 1 | `ListHelpers`, `RangedNat` | Counting by injection and by involution; natural numbers confined to a range, with a validating constructor and its specification. |
| 2, 3 | `ScoreLevel`, `Appearance`, `Pulse`, `Grimace`, `Activity`, `Respiration` | The grades 0, 1, 2 and the five signs, whose shared theory comes from one functor; heart-rate bands at 60 and 100 per minute. |
| 4 | `Trinomial`, `Assessment` | The 243 assessments, each listed once; totals are exactly 0 to 10; the number of assessments with total k is the coefficient of x^k in (1 + x + x^2)^5, from a count proved for any number of signs; symmetry of that distribution by the complement involution; the total moves at most two points for each sign that differs. |
| 5 | `Classification` | The bands 0-3, 4-6 and 7-10; the class is monotone in the score and changes exactly at 3 and 6. |
| 6 | `PartialAssessment` | With some signs unobserved, the totals of the completions are exactly an interval, and the class is determined exactly when both ends of the interval fall in one class. |
| 7 | `Timing` | The rule for scores at 1, 5, 10, 15 and 20 minutes as a function of the scores observed, a declarative description of the series it produces, their equivalence, and a decision procedure. |
| 8 | `Edition`, `GestationalAge`, `BirthWeight`, `SpO2`, `Temperature`, `CordBloodGas` | Categories and thresholds with their characterizations; the saturation target table in both editions. |
| 9 | `NRP` | The decision points of the algorithm and the step they indicate, monotone in heart rate; ventilation, oxygen, compression, epinephrine, tube and cord parameters; where the two editions differ. |
| 10 | `ScoreAndResuscitation` | What the total determines about the criterion for ventilation: totals up to 2 meet it, the total 10 does not, every total from 3 to 9 is reached both ways, and no rule on the total reproduces it. |
| 11 | `ExpandedForm` | The expanded reporting form with its interventions; well-formedness and its decision procedure. |
| 12 | `TherapeuticHypothermia` | The trial's eligibility criteria, monotone in pH, base deficit and the 10-minute score. |
| 13 | `Trajectory` | Chains of successive totals, the class along them, and the characterization of the trend. |
| 14 | `AuditTrail` | An append-only log whose guarded append preserves its invariant and reaches every log that has it. |
| 15 | `Examples` | One infant followed through the modules. |

## Building

The file needs Rocq 9.0 and loads only the standard library; the extraction test also needs OCaml. One command compiles it and writes the extraction next to it as `apgar.ml` and `apgar.mli`:

```
rocq compile -Q . Apgar apgar.v
```

With GNU make, `make` does the same and fails on any compiler output, `make check` runs the proof checker, `make test` runs the OCaml test, and `make ci` runs all three. The tools are taken from `PATH` unless `ROCQ`, `ROCQCHK`, `OCAMLC` and `OCAMLRUN` are set.

## Verification

Compiling the file has the Rocq kernel check every proof. `make check` then runs `rocqchk` on the compiled library, which re-checks the proof terms with a separate checker and prints the axioms of the context it checked; the target fails if it lists any. `make test` compiles the extracted OCaml and runs `test/smoke.ml`, which exercises the extracted functions on the worked example and on boundary values of the thresholds. The workflow in `.github/workflows/ci.yml` runs `make ci` against Rocq 9.0.0 on each push to `main` and on each pull request.

## Extracted OCaml

Natural numbers become OCaml `int`, and each module of the file becomes a module of `Apgar`. A bounded quantity is a plain `int` in OCaml, so its range is enforced by its constructor: `SpO2.make`, `Temperature.make`, `BirthWeight.make`, `CordBloodGas.PH.make`, `CordBloodGas.BaseDeficit.make` and `GestationalAge.make` return `None` outside the range, and `Assessment.of_nats_opt` does the same for grades outside 0 to 2.

```ocaml
open Apgar

let () =
  match Assessment.of_nats_opt 1 2 1 0 1 with
  | None -> print_endline "grade out of range"
  | Some a ->
      Printf.printf "total %d, ventilation criterion %b\n"
        (Assessment.total a)
        (ScoreAndResuscitation.ventilation_criterion a)
```

## Scope

The file models published rules and proves properties of that model; it is not clinical decision support. The block headed "Scope of the model" at the top of `apgar.v` lists the readings the model fixes where a source leaves a choice, among them the score at a heart rate of exactly 100, the stopping rule for scores after 5 minutes, and the saturation target between the tabulated minutes. The repository is released under the MIT License, in `LICENSE`.
