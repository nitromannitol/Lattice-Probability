/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIgChi
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRadial
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLqgAreaApprox
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsVagueLimitC
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeScale
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRescaleField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRescaleCurve
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTBrownRescale
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTAffineReroot
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIgPullback
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTRestrictCircles
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTExcursionSegment
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSegmentsContainBalls
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDiamAreaSup
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDegInner
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDegOuter

/-!
# Frozen definition: `MatedCRT.IsMatingOfTreesCoupling`

The coupling records laws, independence and measurability together with SLE/LQG properties of the
field and curves. `areaParam` and `areaParam₀` quantify over every dyadic vague limit of the area
approximations. `boundaryLength` records the coordinate-change rule for quantum length.

In `igMap`, the same witness `Φ` ignores every radius `ρ ≤ 0`. The field `visitBound` bounds the
number of visits of `ηL` to any point, as in DMS Lemma 8.13 and (8.9) for `κ' > 4`.
The coupling has 24 fields.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **A mating-of-trees coupling for the γ-mated-CRT map** . On `(Ω, P)`:
* `X, B, B'` build the γ-quantum cone `h = coneField X (coneRadial γ γ B B')` and `X₀, B₀, B₀'` the 0-quantum cone `h₀`
  (SLE-free data with the laws of; [20] §4 uses the 0-cone, [20]);
* `hIG₀ + U` is the imaginary-geometry field, a whole-plane GFF modulo `2πχ` with uniform constant (MS17's definition,
  IG4; [18]), independent of both cones, with circle-average process `HIG`;
* `ηL` is whole-plane space-filling SLE_{16/γ²} from ∞ to ∞, parametrized by Lebesgue measure with `ηL 0 = 0`, a
  measurable function `Φ` of `HIG`;
* `η` (resp. `η₀`) is `ηL` reparametrized by `γ`-LQG area of `h` (resp. `h₀`) with `η 0 = 0`;
* `bm` is the boundary-length pair of `(h, η)` (normalized), given by a measurable functional `BL`.
Every field after the data is a literature statement that needs SLE (source line in its comment). -/
structure IsMatingOfTreesCoupling (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2) : Prop where
  /- SLE-free data: laws and independence of the fields (constructed, not input). -/
  isProbabilityMeasure : IsProbabilityMeasure P
  gff : LQGMetric.IsWholePlaneGFF X P
  gff₀ : LQGMetric.IsWholePlaneGFF X₀ P
  bm_B : IsBrownianReal B P
  bm_B' : IsBrownianReal B' P
  bm_B₀ : IsBrownianReal B₀ P
  bm_B₀' : IsBrownianReal B₀' P
  indep_cone : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P
  indep_cone₀ : IndepFun X₀ (fun ω => ((fun t => B₀ t ω), (fun t => B₀' t ω))) P ∧
    IndepFun (fun ω t => B₀ t ω) (fun ω t => B₀' t ω) P
  igField : LQGMetric.IsNormalizedWPGFF hIG₀ P ∧ P.map U = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)] ∧
    IndepFun hIG₀ U P
  indep_curve : IndepFun (fun ω => (hIG₀ ω, U ω))
    (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω, (fun t => B₀ t ω), (fun t => B₀' t ω))) P
  measurable_curves : Measurable ηL ∧ Measurable η ∧ Measurable η₀ ∧ Measurable bm
  /- (S6) whole-plane space-filling SLE ∞ → ∞ as a function of the IG field: [18] (MS17 Thm 1.16 and
  DMS footnote 4, DMS); IG1, (1.4) = IG4, (1.2) (flow lines of `h ∘ ψ − χ arg ψ′` are
  `ψ⁻¹` of those of `h`); whole-plane flow lines: IG4 Theorems 1.1–1.2 (IG4). -/
  igMap : ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
    /-  `Φ` reads only the circle averages at positive radii: the IG field
    determines the curve and its positive-radius circle averages determine the field (S1Z §A), so one witness `Φ`
    ignores every radius `ρ ≤ 0` (the junk coordinate of IA5's counterexample, `IGLaw/OCounter.lean`). -/
    (∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K') ∧
    (∀ᵐ ω ∂P, ηL ω = Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) ∧
    /- coordinate change (1.4), IG1, for `ψ w = z₀ + s e^{iφ} w`, whole-plane form; the curve is re-rooted at
    the first, a.s. only, hitting time of the fixed point `z₀` (GHM15; DMS), so at `ψ = id`, with
    `spaceFilling`'s transience, this clause gives `firstHit (ηL ω) 0 = 0` a.s. -/
    (∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (igPullback γ z₀ s φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) =
        affineReroot z₀ s φ (ηL ω)) ∧
    /- (S7) locality, [18] Lemma 2.4: `h^IG|_{B_δ(U)}` determines the excursion segments in `U` -/
    (∀ (V : Set ℂ), IsOpen V → Bornology.IsBounded V → ∀ δ : ℝ, 0 < δ →
      ∃ g : (ℝ → ℂ → ℝ) → (ℚ × ℚ → ℝ → ℂ), Measurable g ∧ ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ,
        ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ V →
          excursionSegment (ηL ω) V ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) =
            g (restrictCircles (thickening δ V)
              (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) q)
  /- (S6) continuous (by type), surjective, transient (DMS Lemma 8.11, DMS), rooted at `0`,
  parametrized by Lebesgue measure ([18]; [20]). -/
  spaceFilling : ∀ᵐ ω ∂P, Function.Surjective (ηL ω) ∧
    Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) ∧ ηL ω 0 = 0 ∧
    ∀ s t : ℝ, s ≤ t → volume (ηL ω '' Icc s t) = ENNReal.ofReal (t - s)
  /- (S6) parametrization by γ-LQG area (DMS; GHMS; [16]), stated for every
  dyadic vague limit `μ` of the area approximations of `h`. The clause is conditional: it binds only the vague
  limits `μ` that exist (the structure does not assert that one exists; if none exists, the clause holds vacuously).
  That existence is SLE-free and is not proved here. -/
  areaParam : ∀ᵐ ω ∂P,
    (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, η ω t = ηL ω (φ t)) ∧
      ∀ μ : Measure ℂ,
        IsVagueLimitC (lqgAreaApprox γ (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))) μ →
          ∀ s t : ℝ, s ≤ t → μ (η ω '' Icc s t) = ENNReal.ofReal (t - s)
  /- (S6) the same for the 0-cone. -/
  areaParam₀ : ∀ᵐ ω ∂P,
    (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, η₀ ω t = ηL ω (φ t)) ∧
      ∀ μ : Measure ℂ,
        IsVagueLimitC (lqgAreaApprox γ (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))) μ →
          ∀ s t : ℝ, s ≤ t → μ (η₀ ω '' Icc s t) = ENNReal.ofReal (t - s)
  /- (S8a) GHM15 Prop 3.4 with Remark 3.9 (GHM15): `P(E_ε(R, r)ᶜ) = o^∞(ε)`. -/
  segmentsContainBalls : ∀ R : ℝ, 0 < R → ∀ r ∈ Ioo (0 : ℝ) 1, ∀ N : ℕ, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
    P {ω | ¬ SegmentsContainBalls (ηL ω) R r ε} ≤ ENNReal.ofReal (C * ε ^ N)
  /- (S8b) [16] Lemma A.4 for the γ-cone: `P[𝔻 ⊂ η([−M, M])] ≥ 1 − O(M^{−c})`. -/
  coverage : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ M : ℝ, 1 < M →
    P {ω | ¬ ball (0 : ℂ) 1 ⊆ η ω '' Icc (-M) M} ≤ ENNReal.ofReal (C * M ^ (-c))
  /- (S8c) [20] Prop 4.4 and Prop 4.6, 0-cone, `η₀(0) = 0`. -/
  cellMoments :
    (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, diamAreaSup (η₀ ω) ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∫⁻ ω, ((degInner (η₀ ω) : ℝ≥0∞)) ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ((degOuter (η₀ ω) : ℝ≥0∞)) ^ p ∂P < ⊤)
  /- (M) DMS Theorem 1.9 (DMS; Theorem 8.1, DMS) for `κ' ≤ 8`, GHMS Theorem 1.1
  (GHMS; DMS Remark 1.10, DMS) for `κ' > 8`; for every `κ' > 4` a two-sided planar Brownian motion
  (DMS Lemma 8.2, DMS) with equal variances (DMS); after the positive normalization of the variance
  . The cited DMS proof leaves the case `κ' = 8` unresolved. -/
  boundaryLawBM : IsCorrelatedBM2 γ (P.map bm)
  /- (M) `bm` is the normalized boundary-length pair of `(h, η)` (DMS; [20]), a measurable
  functional `BL` of `(h, η)`; and, for each `b > 0`, the boundary-length pair of `(h_b, η^b)` is
  `b^{-1/2} bm(b·)`: the coordinate-change rule `f_* ν_{h̃} = ν_h` ([20]; DMS) at the dilation
  `z ↦ R_b z` and `ν_{h+c} = e^{γc/2} ν_h` (DMS (1.2), DMS); the pathwise random-dilation covariance of quantum
  length, used implicitly at DMS. Not a numbered theorem (see disclosure 3 of the guide). -/
  boundaryLength : ∃ BL : Field × C(ℝ, ℂ) → Path2, Measurable BL ∧
    (∀ᵐ ω ∂P, bm ω = BL (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)), η ω)) ∧
    ∀ b₀ : ℝ, 0 < b₀ → ∀ᵐ ω ∂P,
      BL (coneRescaleField γ (coneScale γ γ (fun u => B u ω) (fun u => B' u ω) b₀) b₀
            (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))),
          coneRescaleCurve (coneScale γ γ (fun u => B u ω) (fun u => B' u ω) b₀) b₀ (η ω)) =
        brownRescale b₀ (bm ω)
  /- (P1) DMS Lemma 8.8 (DMS): a direct L- or R-identification of `s < t` gives `η(s) = η(t)`. -/
  merge : ∀ᵐ ω ∂P, ∀ s t : ℝ,
    (DirectRel (fun u => lrCoord 0 u (bm ω)) s t ∨ DirectRel (fun u => lrCoord 1 u (bm ω)) s t) →
      η ω s = η ω t
  /- (P2) DMS Lemma 8.14 (DMS; "R_s = L_t" there is a typo for `R_s = R_t`): `η(s) = η(t)` only if
  `s ≡ t` for the equivalence generated by the direct identifications (DMS Lemma 8.9, DMS). -/
  onlyMerge : ∀ᵐ ω ∂P, ∀ s t : ℝ, η ω s = η ω t →
    Relation.EqvGen (fun a c => DirectRel (fun u => lrCoord 0 u (bm ω)) a c ∨
      DirectRel (fun u => lrCoord 1 u (bm ω)) a c) s t
  /- (B; v4) DMS Lemma 8.13 with (8.9), DMS, all κ' > 4 (S1Z); : a deterministic
  bound on the number of times `ηL` visits any point (`encard` counts distinct times; S1Z §B). -/
  visitBound : ∃ k : ℕ, ∀ᵐ ω ∂P, ∀ z : ℂ, ((ηL ω) ⁻¹' {z}).encard ≤ k

end MatedCRT

end MatedCRTHarmonic
