/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18T1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Law transfer for circle-average processes (DG:1774–1777, the law step)

DG (proof of Prop 3.18, DG:1774–1777) passes from one realisation of the field to "a whole-plane
GFF": the statements only depend on the law. In the project the nodes `DGProp3_18Sq`,
`DGProp3_17Sq` quantify over an arbitrary process `hc` with
`LQGDimension.IsGFFCircleAverage hc P`. The law of countably many coordinates
`(hc δ (ι t))_{t ∈ T}` is determined by this predicate: it is a centred Gaussian process with the
covariance `gffCircleCov`, and two Gaussian processes with equal means and covariances have equal
laws (`KilledHeat.map_eq_of_gaussian`, the argument of mathlib's
`IsGaussianProcess.isPreBrownianReal_of_covariance`).

* `t18T_map_eq` — equality of the laws of `ω ↦ (hc δ (ι t) ω)_t`.
* **`t18T_measure_eq`** — the general transfer lemma: for an event measurable in these
  coordinates, `P(E(hc)) = P'(E(hc'))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric.DG

/-- the coordinates `(hc δ (ι t))_{t ∈ T}` -/
def t18Coord {Ω : Type*} {T : Type*} (hc : ℝ → ℂ → Ω → ℝ) (δ : ℝ) (ι : T → ℂ) (ω : Ω) :
    T → ℝ := fun t => hc δ (ι t) ω

lemma t18T_gp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) {δ : ℝ} (hδ : 0 < δ) {T : Type*} (ι : T → ℂ) :
    IsGaussianProcess (fun t => hc δ (ι t)) P :=
  hG.isGaussianProcess.comp_right (fun t => ((⟨δ, hδ⟩ : Ioi (0 : ℝ)), ι t))

lemma t18T_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hc : ℝ → ℂ → Ω → ℝ} (hG : LQGDimension.IsGFFCircleAverage hc P) {δ : ℝ} (hδ : 0 < δ)
    {T : Type*} [Countable T] (ι : T → ℂ) : AEMeasurable (t18Coord hc δ ι) P :=
  .of_eval fun t => (t18T_gp hG hδ ι).aemeasurable t

/-- the law of the coordinates is determined by `IsGFFCircleAverage` -/
theorem t18T_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {hc : ℝ → ℂ → Ω → ℝ} {hc' : ℝ → ℂ → Ω' → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) (hG' : LQGDimension.IsGFFCircleAverage hc' P')
    {δ : ℝ} (hδ : 0 < δ) {T : Type*} [Countable T] (ι : T → ℂ) :
    P.map (t18Coord hc δ ι) = P'.map (t18Coord hc' δ ι) :=
  KilledHeat.map_eq_of_gaussian (t18T_gp hG hδ ι) (t18T_gp hG' hδ ι)
    (fun t => (hG.integral_eq_zero δ hδ (ι t)).trans (hG'.integral_eq_zero δ hδ (ι t)).symm)
    (fun s t => (hG.covariance_eq δ hδ δ hδ (ι s) (ι t)).trans
      (hG'.covariance_eq δ hδ δ hδ (ι s) (ι t)).symm)

/-- **Law transfer**: for events measurable in the countably many coordinates
`(hc δ (ι t))_{t ∈ T}`, the probability does not depend on the process `hc`. -/
theorem t18T_measure_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {hc : ℝ → ℂ → Ω → ℝ} {hc' : ℝ → ℂ → Ω' → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) (hG' : LQGDimension.IsGFFCircleAverage hc' P')
    {δ : ℝ} (hδ : 0 < δ) {T : Type*} [Countable T] (ι : T → ℂ) {B : Set (T → ℝ)}
    (hB : MeasurableSet B) :
    P {ω | t18Coord hc δ ι ω ∈ B} = P' {ω | t18Coord hc' δ ι ω ∈ B} := by
  have h1 := Measure.map_apply_of_aemeasurable (t18T_aemeasurable hG hδ ι) hB
  have h2 := Measure.map_apply_of_aemeasurable (t18T_aemeasurable hG' hδ ι) hB
  rw [t18T_map_eq hG hG' hδ ι] at h1
  exact h1.symm.trans h2

end LQGMetric.DG
