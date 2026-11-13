/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.ConeRadialPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.WedgeFieldMol

/-!
# Paths of the cone's radial process: continuity, growth, local integrability

For the radial process `A = coneRadial γ γ b b'` of the γ-quantum cone (DMS Def 4.10 with Rem 4.4):

* `continuous_coneRadial`: `A` is continuous when `b` is continuous with `b(0) = 0` and the drifted path
  `c(u) = b'(u) + (Q − γ)u` is a good drift (`GoodDrift`; then `c(ℓ) = 0` at its last zero `ℓ`);
* `exists_abs_le_add_of_tendsto_div`: a continuous path with `b(t)/t → 0` satisfies `|b(t)| ≤ C + t`;
* `locallyIntegrable_radial_of_growth`: if `a` is continuous on `ℝ` with `|a(t)| ≤ C + Kt` for `t ≥ 0`, then
  `z ↦ a(−log|z|)` is locally integrable on `ℂ` (ported MoT `WedgeFieldMol.locallyIntegrable_rp`).

These are the pathwise facts behind `h = X̃ + g` with `g = −γ log|·|` on `𝔻` (`ConeCompare.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMCFacts

open MatedCRTHarmonic.CellScaling

/-- `coneRadial` on `t ≥ 0`. -/
lemma coneRadial_of_nonneg (γ α : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    coneRadial γ α b b' t = b t.toNNReal + α * t := by
  simp [coneRadial, ht]

/-- **The cone's radial process is continuous** (for continuous `b` with `b(0) = 0` and a good drift). -/
theorem continuous_coneRadial {γ : ℝ} {b b' : ℝ≥0 → ℝ} (hb : Continuous b) (hb0 : b 0 = 0)
    {μ : ℝ} (hc : GoodDrift (coneDrift γ γ b') μ) : Continuous (coneRadial γ γ b b') := by
  have e : coneRadial γ γ b b' = fun t => if (0 : ℝ) ≤ t then b t.toNNReal + γ * t else
      coneDrift γ γ b' (lastZeroR (coneDrift γ γ b') - t) + lqgQ γ * t := by
    funext t
    rfl
  rw [e]
  refine Continuous.if_le ((hb.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id))
    ((hc.cont.comp (continuous_const.sub continuous_id)).add (continuous_const.mul continuous_id))
    continuous_const continuous_id fun t ht => ?_
  subst ht
  simp only [Real.toNNReal_zero, hb0, mul_zero, add_zero, sub_zero]
  exact hc.lastZeroR_mem.2.symm

/-- A continuous path with `b(t)/t → 0` grows at most linearly: `|b(t)| ≤ C + t`. -/
theorem exists_abs_le_add_of_tendsto_div {b : ℝ≥0 → ℝ} (hb : Continuous b)
    (hlln : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * b t) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ t : ℝ≥0, |b t| ≤ C + t := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlln.eventually (Metric.ball_mem_nhds 0 one_pos))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := max T 1)).exists_bound_of_continuousOn
    hb.continuousOn
  refine ⟨max M 0, fun t => ?_⟩
  rcases le_total t (max T 1) with h | h
  · have := hM t ⟨zero_le, h⟩
    rw [Real.norm_eq_abs] at this
    have : (0 : ℝ) ≤ t := t.2
    linarith [le_max_left M 0]
  · have hTt : T ≤ t := (le_max_left T 1).trans h
    have h1 : (1 : ℝ) ≤ t := by exact_mod_cast (le_max_right T 1).trans h
    have := hT t hTt
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul,
      abs_inv, abs_of_pos (by linarith : (0 : ℝ) < t)] at this
    have hpos : (0 : ℝ) < t := by linarith
    rw [inv_mul_lt_iff₀ hpos, mul_one] at this
    linarith [le_max_right M 0]

/-- **Local integrability of radial profiles with linear growth**: if `a` is continuous and `|a(t)| ≤ C + K t` for
`t ≥ 0`, then `z ↦ a(−log|z|)` is locally integrable on `ℂ`. -/
theorem locallyIntegrable_radial_of_growth {a : ℝ → ℝ} (ha : Continuous a) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hgr : ∀ t, 0 ≤ t → |a t| ≤ C + K * t) :
    LocallyIntegrable (fun z : ℂ => a (-Real.log ‖z‖)) volume := by
  have hgm : Measurable fun r : ℝ => a (-Real.log r) := ha.measurable.comp Real.measurable_log.neg
  have hgc : ContinuousOn (fun r : ℝ => a (-Real.log r)) (Ioi 0) :=
    ha.comp_continuousOn (Real.continuousOn_log.mono fun r hr => ne_of_gt hr).neg
  have hbd : ∀ t : ℝ, 0 < t → t ≤ 1 → |a (-Real.log t)| ≤ (C + K) * (1 - Real.log t) := by
    intro t ht ht1
    have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
    refine (hgr _ (by linarith)).trans ?_
    nlinarith
  exact MoTPort.WedgeFieldMol.locallyIntegrable_rp hgm hgc hbd

end MatedCRTHarmonic.GMCFacts
