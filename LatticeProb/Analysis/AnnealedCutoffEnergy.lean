import LatticeProb.Analysis.CriticalCutoffEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Annealed critical cutoff energy

Expectation estimates for the critical jump kernel with mean-one conductances.
-/

noncomputable section

open MeasureTheory ENNReal LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell
open LatticeProb.Analysis.CriticalCutoffEnergy

namespace LatticeProb.Analysis.AnnealedCutoffEnergy

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The unordered pairs of distinct lattice sites. -/
abbrev Edge (d : ℕ) := {e : Sym2 (Site d) // ¬ e.IsDiag}

/-- The edge between a site and its translate by a nonzero lattice vector. -/
def edgeAdd (x : Site d) (z : {z : Site d // z ≠ 0}) : Edge d :=
  ⟨s(x, x + z.val), by
    simp only [Sym2.mk_isDiag_iff]
    intro h
    apply z.property
    have hz : x + 0 = x + z.val := by simpa using h
    exact (add_left_cancel hz).symm⟩

/-- The deterministic cutoff-weighted critical kernel. -/
def weight (r : ℝ) (z : {z : Site d // z ≠ 0}) : ℝ :=
  min 1 (radius (physical 1 z.val) ^ 2 / r ^ 2) *
    (radius (physical 1 z.val) ^ (d + 2))⁻¹

lemma weight_nonneg (r : ℝ) (z : {z : Site d // z ≠ 0}) : 0 ≤ weight r z := by
  exact mul_nonneg (le_min zero_le_one (div_nonneg (sq_nonneg _) (sq_nonneg _)))
    (inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))

/-- A series of integrable functions with summable integral norms converges almost
surely and has an integrable pointwise sum. -/
theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (hi : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ ω, ‖f i ω‖ ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => f i ω)) ∧
      Integrable (fun ω => ∑' i, f i ω) μ := by
  have he (i : ι) : ∫⁻ ω, ‖f i ω‖ₑ ∂μ = ‖∫ ω, ‖f i ω‖ ∂μ‖ₑ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi i),
      Real.enorm_eq_ofReal (integral_nonneg (fun ω => norm_nonneg (f i ω)))]
  have ht : ∑' i, ∫⁻ ω, ‖f i ω‖ₑ ∂μ ≠ ⊤ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hs.abs
  have hm (i : ι) : AEMeasurable (fun ω => ‖f i ω‖ₑ) μ := (hi i).1.enorm
  have hb : ∀ᵐ ω ∂μ, Summable fun i => (‖f i ω‖₊ : ℝ) := by
    rw [← lintegral_tsum hm] at ht
    refine (ae_lt_top' (AEMeasurable.tsum hm) ht).mono ?_
    intro ω hω
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hω.ne
  have hbound : Integrable (fun ω => ∑' i, (‖f i ω‖₊ : ℝ)) μ := by
    constructor
    · fun_prop
    · dsimp [HasFiniteIntegral]
      have h : ∫⁻ ω, ∑' i, ‖f i ω‖ₑ ∂μ < ⊤ := by
        rwa [lintegral_tsum hm, lt_top_iff_ne_top]
      convert! h using 1
      apply lintegral_congr_ae
      filter_upwards [hb] with ω hω
      rw [Real.enorm_eq_ofReal (tsum_nonneg (fun i => abs_nonneg (f i ω))),
        ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg (f i ω)) hω]
      congr 1
      funext i
      rw [← Real.enorm_eq_ofReal (abs_nonneg (f i ω))]
      simp
  constructor
  · filter_upwards [hb] with ω hω
    exact hω.of_norm
  · apply hbound.mono' ?_ ?_
    · fun_prop
    · filter_upwards [hb] with ω hω
      exact norm_tsum_le_tsum_norm hω

/-- Averaging the conductance-weighted series gives the deterministic kernel sum. -/
theorem integral_cutoff_energy_eq (μ : Measure Ω) (hd : 1 ≤ d)
    (a : Ω → Edge d → ℝ)
    (hn : ∀ e, ∀ᵐ ω ∂μ, 0 ≤ a ω e)
    (hm : ∀ e, ∫ ω, a ω e ∂μ = 1) (x : Site d) (r : ℝ) :
    (∫ ω, ∑' z : {z : Site d // z ≠ 0}, weight r z * a ω (edgeAdd x z) ∂μ) =
      ∑' z : {z : Site d // z ≠ 0}, weight r z := by
  have ha (e : Edge d) : Integrable (fun ω => a ω e) μ :=
    Integrable.of_integral_ne_zero (by rw [hm e]; norm_num)
  have hi (z : {z : Site d // z ≠ 0}) :
      Integrable (fun ω => weight r z * a ω (edgeAdd x z)) μ :=
    (ha _).const_mul _
  have hnorm (z : {z : Site d // z ≠ 0}) :
      (∫ ω, ‖weight r z * a ω (edgeAdd x z)‖ ∂μ) = weight r z := by
    calc
      _ = ∫ ω, weight r z * a ω (edgeAdd x z) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hn (edgeAdd x z)] with ω hω
        exact Real.norm_of_nonneg (mul_nonneg (weight_nonneg r z) hω)
      _ = weight r z := by rw [integral_const_mul, hm]; simp
  have hs : Summable (fun z : {z : Site d // z ≠ 0} =>
      ∫ ω, ‖weight r z * a ω (edgeAdd x z)‖ ∂μ) := by
    simp_rw [hnorm]
    exact summable_cutoff_energy d hd r
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  congr 1
  funext z
  rw [integral_const_mul, hm]
  simp

/-- The weighted series converges almost surely and defines an integrable random variable. -/
theorem cutoff_energy_integrable (μ : Measure Ω) (hd : 1 ≤ d)
    (a : Ω → Edge d → ℝ)
    (hn : ∀ e, ∀ᵐ ω ∂μ, 0 ≤ a ω e)
    (hm : ∀ e, ∫ ω, a ω e ∂μ = 1) (x : Site d) (r : ℝ) :
    (∀ᵐ ω ∂μ, Summable (fun z : {z : Site d // z ≠ 0} =>
      weight r z * a ω (edgeAdd x z))) ∧
    Integrable (fun ω => ∑' z : {z : Site d // z ≠ 0},
      weight r z * a ω (edgeAdd x z)) μ := by
  have ha (e : Edge d) : Integrable (fun ω => a ω e) μ :=
    Integrable.of_integral_ne_zero (by rw [hm e]; norm_num)
  apply integrable_tsum_of_summable_integral_norm μ
  · intro z
    exact (ha _).const_mul _
  · have hnorm (z : {z : Site d // z ≠ 0}) :
        (∫ ω, ‖weight r z * a ω (edgeAdd x z)‖ ∂μ) = weight r z := by
      calc
        _ = ∫ ω, weight r z * a ω (edgeAdd x z) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hn (edgeAdd x z)] with ω hω
          exact Real.norm_of_nonneg (mul_nonneg (weight_nonneg r z) hω)
        _ = weight r z := by rw [integral_const_mul, hm]; simp
    simp_rw [hnorm]
    exact summable_cutoff_energy d hd r

/-- The annealed cutoff energy has the dimension-only logarithmic bound. -/
theorem integral_cutoff_energy_le_log (μ : Measure Ω) (hd : 1 ≤ d)
    (a : Ω → Edge d → ℝ)
    (hn : ∀ e, ∀ᵐ ω ∂μ, 0 ≤ a ω e)
    (hm : ∀ e, ∫ ω, a ω e ∂μ = 1) (x : Site d) {r : ℝ} (hr : 1 ≤ r) :
    (∫ ω, ∑' z : {z : Site d // z ≠ 0}, weight r z * a ω (edgeAdd x z) ∂μ) ≤
      (shellConstant d * (1 + 25 / Real.log 3)) * Real.log (2 + r) / r ^ 2 := by
  rw [integral_cutoff_energy_eq μ hd a hn hm x r]
  exact cutoff_energy_le_log hd hr

/-- The annealed cutoff energy is bounded by the total critical jump rate. -/
theorem integral_cutoff_energy_le_total_rate (μ : Measure Ω) (hd : 1 ≤ d)
    (a : Ω → Edge d → ℝ)
    (hn : ∀ e, ∀ᵐ ω ∂μ, 0 ≤ a ω e)
    (hm : ∀ e, ∫ ω, a ω e ∂μ = 1) (x : Site d) (r : ℝ) :
    (∫ ω, ∑' z : {z : Site d // z ≠ 0}, weight r z * a ω (edgeAdd x z) ∂μ) ≤
      ∑' z : {z : Site d // z ≠ 0}, (radius (physical 1 z.val) ^ (d + 2))⁻¹ := by
  rw [integral_cutoff_energy_eq μ hd a hn hm x r]
  exact cutoff_energy_le_total_rate d hd r

end LatticeProb.Analysis.AnnealedCutoffEnergy
