import Mathlib
import LatticeProb.Prob.PaleyZygmundLaplace

/-!
# Laplace transform bound from a mean and a higher moment

Let `Z : Ω → [0, ∞]` be almost-everywhere measurable on a probability space, with `E Z = m ∈ (0, ∞)` and
`E Z^p ≤ C` for some `p > 1`. Then `E exp(-λ Z) ≤ 1 - η / 2` for every `λ ≥ 2 log 2 / m`, where
`η = (m/2)^{p/(p-1)} C^{-1/(p-1)}` depends only on `m`, `p` and `C`. This is Paley-Zygmund at half the mean
followed by the elementary bound `exp(-λ z) ≤ 1/2` on `{z > m/2}`.

* `LatticeProb.laplace_le_of_moments`: the statement above, for `[0, ∞]`-valued `Z` (the integrand uses `Z.toReal`).
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Laplace transform from a mean and a higher moment.** If `E Z = m > 0`, `E Z^p ≤ C` with `p > 1`, `C > 0`,
then `E exp(-λ Z) ≤ 1 - η/2` for `λ ≥ 2 log 2 / m`, `η = (m/2)^{p/(p-1)} C^{-1/(p-1)}`. -/
theorem laplace_le_of_moments [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : AEMeasurable Z P)
    {m C p : ℝ} (hm : 0 < m) (hp : 1 < p) (hC : 0 < C)
    (hmean : ∫⁻ ω, Z ω ∂P = ENNReal.ofReal m) (hmom : ∫⁻ ω, Z ω ^ p ∂P ≤ ENNReal.ofReal C)
    {lam : ℝ} (hlam : 2 * Real.log 2 / m ≤ lam) :
    ∫ ω, Real.exp (-(lam * (Z ω).toReal)) ∂P ≤
      1 - ((m / 2) ^ (p / (p - 1)) * C ^ (-(1 / (p - 1)))) / 2 := by
  have hfin : ∀ᵐ ω ∂P, Z ω < ⊤ :=
    ae_lt_top' hZ (by rw [hmean]; exact ENNReal.ofReal_ne_top)
  set Z' : Ω → ℝ := fun ω => (hZ.mk Z ω).toReal with hZ'
  have hZm : Measurable (hZ.mk Z) := hZ.measurable_mk
  have hZ'm : Measurable Z' := hZm.ennreal_toReal
  have hae : ∀ᵐ ω ∂P, Z ω = hZ.mk Z ω := hZ.ae_eq_mk
  have hfin' : ∀ᵐ ω ∂P, hZ.mk Z ω < ⊤ := by
    filter_upwards [hfin, hae] with ω h1 h2
    rwa [← h2]
  have hofr : ∀ᵐ ω ∂P, ENNReal.ofReal (Z' ω) = Z ω := by
    filter_upwards [hfin', hae] with ω h1 h2
    rw [hZ', h2]
    exact ENNReal.ofReal_toReal h1.ne
  have hmean' : ∫⁻ ω, ENNReal.ofReal (Z' ω) ∂P = ENNReal.ofReal m := by
    rw [← hmean]; exact lintegral_congr_ae hofr
  have hmom' : ∫⁻ ω, ENNReal.ofReal (Z' ω) ^ p ∂P ≤ ENNReal.ofReal C := by
    refine le_trans (le_of_eq ?_) hmom
    exact lintegral_congr_ae (hofr.mono fun ω h => by simp only [h])
  have hη := measure_gt_half_ge hZ'm hm hp hC hmean' hmom'
  have h0 : ∀ ω, 0 ≤ Z' ω := fun ω => ENNReal.toReal_nonneg
  have key := integral_exp_neg_le_of_measure_gt_half hZ'm h0 hm hη hlam
  refine le_trans (le_of_eq ?_) key
  refine integral_congr_ae ?_
  filter_upwards [hae] with ω h2
  rw [hZ', h2]

end LatticeProb
