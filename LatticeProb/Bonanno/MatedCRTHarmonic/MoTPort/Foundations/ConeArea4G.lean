/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4G at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4F
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.WedgeFieldMol
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN

/-!
**`ae_locallyIntegrable_coneProfile`**: for a cone process `A` (`IsConeProcess α Q A P`), a.s.
`z ↦ Q(−log|z|) + A_{−log|z|}` is locally integrable on `ℂ` — radial integrability statement (R3), in the exact form of the hypothesis `hR3` of
`ConeArea3.ae_isVagueLimitOn_coneField_punctured_of`.

Proof: for `t ≥ 0`, `A_t = B_t + (α − Q)t` (`conePath_of_nonneg`, DMS Definition 4.9: the
`0`-side of the cone process is `B_t + αt` minus the `Q t` of the profile); a.s. `B_t/t → 0`
(QZ `BMLLN.ae_tendsto_div_atTop`, Le Gall Exercise 2.25) and `B` is continuous, so
`|B_t| ≤ M + t`; with `t = −log|z|` the profile is bounded by `C(1 − log|z|)` on the unit disc
and continuous off `0` (a.s. continuity of `A`, ConeMeas2), and `WedgeFieldMol.locallyIntegrable_rp`
gives local integrability. Own elementary glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper

/-- on the `0`-side the cone path is the Brownian motion with drift `α − Q` -/
lemma conePath_of_nonneg (α Q : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    conePath α Q b b' t = b t.toNNReal + (α - Q) * t := by
  have h2 : (2 : ℝ≥0) * (t / 2).toNNReal = t.toNNReal := by
    ext
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal _ ht,
      Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ t / 2)]
    ring
  simp only [conePath, wedgePath]
  rw [if_pos (by positivity), h2]
  have hs : Real.sqrt 2 * (√2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc, hs, one_mul]
  ring

/-- a continuous path with `B_t / t → 0` grows at most linearly -/
lemma exists_abs_le_add {f : ℝ≥0 → ℝ} (hc : Continuous f)
    (hl : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * f t) atTop (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, |f t| ≤ M + t := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hl.eventually (closedBall_mem_nhds 0 one_pos))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases htT : t ≤ T
  · have := hM t ⟨t.2, htT⟩
    rw [Real.norm_eq_abs] at this
    linarith [le_max_left M 0, t.2]
  · have ht := hT t (le_of_lt (not_le.1 htT))
    have hpos : (0 : ℝ) < t := by
      have : (0 : ℝ≥0) < t := lt_of_le_of_lt T.2 (not_le.1 htT)
      exact_mod_cast this
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_pos hpos, inv_mul_le_iff₀ hpos, mul_one] at ht
    linarith [le_max_right M 0]

/-- **node (R3) / C.loc**: a.s. the cone profile `Q(−log|·|) + A_{−log|·|}` is locally
integrable -/
theorem ae_locallyIntegrable_coneProfile {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsConeProcess α Q A P) :
    ∀ᵐ ω ∂P,
      LocallyIntegrable (fun z : ℂ => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖) ω) volume := by
  have hcont := (ConeMeas2.aemeasurable_conePath hA).2
  obtain ⟨B, B', hB, -, -, hAe⟩ := hA
  filter_upwards [hcont, BMLLN.ae_tendsto_div_atTop hB, hB.cont] with ω hAc hlln hBc
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_add hBc hlln
  set g : ℝ → ℝ := fun r => Q * (-Real.log r) + A (-Real.log r) ω
  have hgm : Measurable g :=
    (measurable_const.mul Real.measurable_log.neg).add (hAc.measurable.comp Real.measurable_log.neg)
  have hgc : ContinuousOn g (Ioi 0) := by
    have hl : ContinuousOn (fun r : ℝ => -Real.log r) (Ioi 0) :=
      (Real.continuousOn_log.mono fun r (hr : 0 < r) => hr.ne').neg
    exact (continuousOn_const.mul hl).add (hAc.comp_continuousOn hl)
  have hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ (|α| + 1 + M) * (1 - Real.log t) := by
    intro t ht0 ht1
    have hs : 0 ≤ -Real.log t := neg_nonneg.2 (Real.log_nonpos ht0.le ht1)
    have hA' : A (-Real.log t) ω = B (-Real.log t).toNNReal ω + (α - Q) * (-Real.log t) := by
      rw [hAe ω, conePath_of_nonneg _ _ _ _ hs]
    have hBb := hM (-Real.log t).toNNReal
    rw [Real.coe_toNNReal _ hs] at hBb
    have e : g t = α * (-Real.log t) + B (-Real.log t).toNNReal ω := by
      simp only [g, hA']; ring
    rw [e]
    calc |α * (-Real.log t) + B (-Real.log t).toNNReal ω|
        ≤ |α| * (-Real.log t) + (M + -Real.log t) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ hBb)
          rw [abs_mul, abs_of_nonneg hs]
      _ ≤ (|α| + 1 + M) * (1 - Real.log t) := by
          nlinarith [abs_nonneg α]
  exact WedgeFieldMol.locallyIntegrable_rp hgm hgc hbd

end ConeArea4
end MatedCRTHarmonic.MoTPort
