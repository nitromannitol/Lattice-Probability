/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFMod
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import Mathlib.Probability.ConditionalProbability

/-!
# Whole-plane LQG area and the canonical representative of plane-like surfaces

DMS (arXiv:1409.7055v4) (the measure `μ_h = lim ε^{γ²/2} e^{γ h_ε(z)} dz`,
Duplantier–Sheffield arXiv:0808.1560 Prop. 1.1 / (1.1)) on a plane domain.

* `areaApproxC γ h k = 2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz` on all of `ℂ`, with LM's circle average
  `LQGMetric.circleAvg` (unfolded circles). This is QZ's `areaApprox` (QZ/LQG/Measures.lean) with the
  folded circle average `avgReg` replaced by LM's whole-plane `circleAvg` and `volume.restrict H` by
  `volume`.
* `qAreaC γ h`: a chosen vague limit on `ℂ` (QZ's `IsVagueLimitOn Set.univ`), junk `0` if none
  exists — the shape of QZ's `qAreaMeasure`.
* `scaleC`, `canonicalC` (unit `qAreaC`-area of `𝔻`), `unifAngle`, `surfLawC` (law of the rotation
  orbit of the canonical representative).

Proved here (deterministic): measurability of the approximants, that `qAreaC` is *the* vague limit
whenever one exists (QZ `isVagueLimitOn_unique`), local finiteness, and the additive-constant rule
`μ_{h+c} = e^{γc} μ_h` (DMS / QZ `FiniteArea.ae_qAreaMeasure_add_ofFun` for constants).
The almost-sure existence and positivity results are established in later modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort

open LQGMetric

/-- the whole-plane area approximation `2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz` (QZ `areaApprox` with
unfolded circle averages, on all of `ℂ`) -/
def areaApproxC (γ : ℝ) (h : Field) (k : ℕ) : Measure ℂ :=
  volume.withDensity fun z : ℂ =>
    ENNReal.ofReal (QuantumZipper.radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * circleAvg h (QuantumZipper.radius k) z))

open Classical in
/-- the whole-plane `γ`-LQG area measure: a chosen vague limit on `ℂ` of
`areaApproxC γ h`, or the junk measure `0` if none exists -/
def qAreaC (γ : ℝ) (h : Field) : Measure ℂ :=
  if hx : ∃ μ, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ h) μ then hx.choose else 0

namespace ConeArea

theorem measurable_areaApproxC (γ : ℝ) (k : ℕ) :
    Measurable fun h : Field => areaApproxC γ h k := by
  unfold areaApproxC
  apply MeasureTheory.measurable_withDensity
  have h1 : Measurable fun p : Field × ℂ => circleAvg p.1 (QuantumZipper.radius k) p.2 :=
    measurable_circleAvg.comp (f := fun p : Field × ℂ => (p.1, QuantumZipper.radius k, p.2))
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (h1.const_mul γ)).const_mul _)

/-- `qAreaC` is a vague limit whenever one exists -/
theorem isVagueLimitOn_qAreaC {γ : ℝ} {h : Field}
    (hx : ∃ μ, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ h) μ) :
    QuantumZipper.IsVagueLimitOn univ (areaApproxC γ h) (qAreaC γ h) := by
  rw [qAreaC, dite_eq_left_of_eq_true (eq_true hx)]; exact hx.choose_spec

/-- `qAreaC` is *the* vague limit whenever one exists (uniqueness, QZ `isVagueLimitOn_unique`) -/
theorem qAreaC_eq_of_isVagueLimitOn {γ : ℝ} {h : Field} {μ : Measure ℂ}
    (hμ : QuantumZipper.IsVagueLimitOn univ (areaApproxC γ h) μ) : qAreaC γ h = μ :=
  QuantumZipper.isVagueLimitOn_unique isOpen_univ (isVagueLimitOn_qAreaC ⟨μ, hμ⟩) hμ

/-- `qAreaC γ h` is finite on compact sets (always: junk `0` otherwise) -/
theorem qAreaC_compact_lt_top (γ : ℝ) (h : Field) {K : Set ℂ} (hK : IsCompact K) :
    qAreaC γ h K < ⊤ := by
  by_cases hx : ∃ μ, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ h) μ
  · exact (isVagueLimitOn_qAreaC hx).2.1 K hK (subset_univ K)
  · rw [qAreaC, dite_eq_right_of_eq_false (eq_false hx)]; simp

/-- the circle averages of `h` exist (as limits of the mollified averages) at a.e. point at
every dyadic scale -/
def HasCircleAvgs (h : Field) : Prop :=
  ∀ k : ℕ, ∀ᵐ z ∂(volume : Measure ℂ), ∃ a : ℝ,
    Tendsto (fun n => CircleAvg.mollAvg h n z (QuantumZipper.radius k)) atTop (𝓝 a)

/-- adding a constant multiplies the approximations by `e^{γc}` -/
theorem areaApproxC_addConst {γ : ℝ} {h : Field} (hh : HasCircleAvgs h) (c : ℝ) (k : ℕ) :
    areaApproxC γ (addConst h c) k = ENNReal.ofReal (Real.exp (γ * c)) • areaApproxC γ h k := by
  unfold areaApproxC
  refine Eq.trans ?_ (withDensity_smul' _ _ ENNReal.ofReal_ne_top)
  refine withDensity_congr_ae ?_
  filter_upwards [hh k] with z ⟨a, ha⟩
  rw [CircleAvg.circleAvg_addConst_of_tendsto ha, Pi.smul_apply, smul_eq_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]; ring

/-- vague limits are compatible with multiplication by a finite constant -/
theorem isVagueLimitOn_smul {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hμ : QuantumZipper.IsVagueLimitOn univ μs μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    QuantumZipper.IsVagueLimitOn univ (fun k => c • μs k) (c • μ) := by
  obtain ⟨h0, hK, hf⟩ := hμ
  refine ⟨by simp, fun K hKc hKU => ?_, fun f hf1 hf2 hf3 => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hK K hKc hKU)
  · simp only [integral_smul_measure]
    exact (hf f hf1 hf2 hf3).const_smul _

/-- **additive constants** (`μ_{h+c} = e^{γc} μ_h`, DMS L321–337): if the vague limit exists for
`h`, it exists for `h + c` and is `e^{γc}` times the one of `h` -/
theorem qAreaC_addConst {γ : ℝ} {h : Field} (hh : HasCircleAvgs h)
    (hx : ∃ μ, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ h) μ) (c : ℝ) :
    qAreaC γ (addConst h c) = ENNReal.ofReal (Real.exp (γ * c)) • qAreaC γ h := by
  apply qAreaC_eq_of_isVagueLimitOn
  have := isVagueLimitOn_smul (isVagueLimitOn_qAreaC hx)
    (ENNReal.ofReal_ne_top (r := Real.exp (γ * c)))
  have e : areaApproxC γ (addConst h c) =
      fun k => ENNReal.ofReal (Real.exp (γ * c)) • areaApproxC γ h k :=
    funext (areaApproxC_addConst hh c)
  rw [e]; exact this

end ConeArea

end MatedCRTHarmonic.MoTPort
