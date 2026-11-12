/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.FractionalMoments at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (GaussTK, KernelId). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
Blueprint `M4_BLUEPRINT.md`, node M4-P3.

Fix a centre `t ∈ ℝ`, a scale `δ > 0` and `R` with `|t| + δ ≤ R`. For the normalized field
`Z = zField X R` we split `Z` inside `B(t, δ)` as
`Z_ρ(s) = Ω + Y_ρ(s)`, where `Ω = Z(fc(t,δ))` is the semicircle average at `(t, δ)` and
`Y = X − X(fc(t,δ))` is the *inner field*.

* (a) `innerProc X t δ` is the inner process indexed by `InnerQ` (coordinates
  `X(fc(t+δu, δr)) − X(fc(t,δ))`, `|u| + r ≤ 1`); it is independent of `Ω`
  (`indepFun_omega_innerSample`), and its law does not depend on `(t, δ)`:
  `map_innerProc_eq` (exact scaling, at the level of the Gaussian coordinates). The field
  `innerSample X t δ` rebuilt from it satisfies, almost surely, for every `k` and every `s` with
  `|s − t| + 2^{-k} < δ`, `Z_{2^{-k}}(s) = Ω + avgReg (innerSample) k s`
  (`ae_avgReg_zField_eq_inner`), hence
  `ν_{2^{-k}}(S) = e^{(γ/2)Ω} δ^{γ²/4} W_k(S)` (`ae_bdryApprox_eq_omega_mul`), where `W_k` is the
  rescaled inner mass, a function of the inner process only.
* (b) fractional moments of `ν_{2^{-k}}(S)`, `S = [t − δ/2, t + δ/2]`, for fixed `k` and with
  `sup_k` inside the expectation.
* (c) the same for the limit measure `qBoundaryMeasure` (open interval, Fatou).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace FracMom

open TwoRadius BdryExist

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ### Covariances -/

/-! ### The two-radius hypotheses for the inner field -/

/-! ### Multiplicative decomposition `ν_{2^{-k}}(S) = e^{(γ/2)Ω} δ^{γ²/4} W_k` -/

/-! ### Moments -/

/-- Jensen for `x ↦ x^p`, `p ∈ (0,1]`, on a probability space. -/
theorem lintegral_rpow_le_rpow_lintegral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫⁻ ω, f ω ^ p ∂μ ≤ (∫⁻ ω, f ω ∂μ) ^ p := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le hp0 hp1 μ hf.aestronglyMeasurable
  simp only [eLpNorm', enorm_eq_self, ENNReal.rpow_one, div_one] at h
  calc ∫⁻ ω, f ω ^ p ∂μ = ((∫⁻ ω, f ω ^ p ∂μ) ^ (1 / p)) ^ p := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow h hp0.le

/-! ### Increments of the inner masses (two-radius lemma) and the `sup` bound -/

/-- Telescoping in `ℝ≥0∞`: `sup_m a_m ≤ a_0 + Σ |a_i − a_{i+1}|` for finite `a`. -/
theorem iSup_le_add_tsum_abs_sub {a : ℕ → ℝ≥0∞} (ha : ∀ m, a m ≠ ⊤) :
    ⨆ m, a m ≤ a 0 + ∑' i, ENNReal.ofReal |(a i).toReal - (a (i + 1)).toReal| := by
  refine iSup_le fun m => ?_
  have key : ∀ m, (a m).toReal ≤
      (a 0).toReal + ∑ i ∈ Finset.range m, |(a i).toReal - (a (i + 1)).toReal| := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have := le_abs_self ((a (m + 1)).toReal - (a m).toReal)
      rw [abs_sub_comm] at this
      linarith
  calc a m = ENNReal.ofReal (a m).toReal := (ENNReal.ofReal_toReal (ha m)).symm
    _ ≤ ENNReal.ofReal ((a 0).toReal +
          ∑ i ∈ Finset.range m, |(a i).toReal - (a (i + 1)).toReal|) :=
        ENNReal.ofReal_le_ofReal (key m)
    _ = a 0 + ∑ i ∈ Finset.range m, ENNReal.ofReal |(a i).toReal - (a (i + 1)).toReal| := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
          (Finset.sum_nonneg fun _ _ => abs_nonneg _), ENNReal.ofReal_toReal (ha 0),
          ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]
    _ ≤ _ := add_le_add le_rfl (ENNReal.sum_le_tsum _)

/-- Subadditivity of `x ↦ x^p` (`p ∈ (0,1]`) over countable sums in `ℝ≥0∞`. -/
theorem rpow_tsum_le_tsum_rpow (D : ℕ → ℝ≥0∞) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑' i, D i) ^ p ≤ ∑' i, D i ^ p := by
  have hfin : ∀ n, (∑ i ∈ Finset.range n, D i) ^ p ≤ ∑ i ∈ Finset.range n, D i ^ p := by
    intro n
    induction n with
    | zero => simp [ENNReal.zero_rpow_of_pos hp0]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add ih le_rfl)
  have ht : Tendsto (fun n => (∑ i ∈ Finset.range n, D i) ^ p) atTop
      (𝓝 ((∑' i, D i) ^ p)) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.tendsto_nat_tsum D)
  exact le_of_tendsto' ht fun n => (hfin n).trans (ENNReal.sum_le_tsum _)

/-! ### (c) The limit measure -/

/-! ### Dyadic form of (b), (c) -/

/-! ### (a) Exact scaling of the inner process (finite-dimensional laws) -/

end FracMom
end QuantumZipper
