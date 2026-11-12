/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3VarBdry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4Tail

/-!
# DZZ Lemma 3.7, variance inputs (P2-DZZ3D, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Lemma 3.7 (l. 975–986):
on `{M_{γ,s}(B) ≤ δ²} ∩ 𝓔_{δ,α}`, `M_{γ,ts}(B̃) ≤ δ² e^{2γα√L log L} t² e^{γ η^{ε²s}_{ts}(c̃) − γ²/2 Var}`.
Writing `η_{ts}(c̃) = η_{ε²s}(c̃) + η^{ε²s}_{ts}(c̃)` this uses, besides `𝓔_{δ,α}`, the UNSTATED fact
`Var η_s(c_B) − Var η_{ε²s}(c̃) ≤ O(α √L log L)` (DZZ do not state it; our `η` is killed at `∂𝕍`).

* `inner_etaKernelL2_Ioi_Ioo`, `etaVar_split`: `Var η_{ε'}(w) = Var η_ε(w) + Var η^ε_{ε'}(w)`
  (disjoint time supports); `etaVar_anti`: `Var η_ε(w) ≤ Var η_{ε'}(w)` for `ε' ≤ ε`.
* `etaVar_sub_le`: `Var η_ε(v) − Var η_ε(w) ≤ 2 √(1076 |v − w|/ε) √(log ε⁻¹ + 4)` from
  `‖a‖² − ‖b‖² ≤ ‖a − b‖ (‖a‖ + ‖b‖)` and DZZ Lemma 2.5 (kernel form).
* `etaVar_sub_fine_le` (**own lemma**, the unstated variance fact): for `0 < ε' ≤ ε ≤ 1`,
  `Var η_ε(v) − Var η_{ε'}(w) ≤ 2 √(1076 |v − w|/ε) √(log ε⁻¹ + 4)`. For `|v − w| = O(ε)` this is
  `O(√(log ε⁻¹)) = O(√L)`, well inside DZZ's error `O(α √L log L)`. Own elementary argument (no
  killed-heat-kernel lower bound is needed); DEVIATIONS.
* `hasLaw_eta`, `tail_eta_normalized`: `η^{ε}_{ε'}(w) ~ N(0, π‖K‖²)` and the exponential-martingale
  (Markov) bound `P(γ X − γ²/2 Var X ≥ a) ≤ e^{−a}`. DZZ (eq-berlin1) bound `η^{ε²s}_{ts} ≤ 1.5 log t⁻¹`
  and use `Var η^{ε²s}_{ts} ≈ log(ε²/t)` to get `t^{0.8}` in (eq-LQG-tilde-B-Phi); we threshold the
  normalized exponent `γ η − γ²/2 Var η` directly (needs no lower bound on the band variance near
  `∂𝕍`); DEVIATIONS: own elementary step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

/-- The kernels of `η_b` and of the band `η^b_a` are orthogonal (disjoint time supports). -/
lemma inner_etaKernelL2_Ioi_Ioo {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (w : ℂ) :
    ⟪etaKernelL2 (Ioi b) w, etaKernelL2 (Ioo a b) w⟫ = 0 := by
  have h1 := memLp_etaKernel (I := Ioi b) measurableSet_Ioi ha (Ioi_subset_Ioi hab) w
  have h2 := memLp_etaKernel (I := Ioo a b) measurableSet_Ioo ha Ioo_subset_Ioi_self w
  rw [etaKernelL2, etaKernelL2, dite_eq_left_of_eq_true (eq_true h1),
    dite_eq_left_of_eq_true (eq_true h2), L2.inner_def]
  refine (integral_congr_ae ?_).trans (integral_zero _ ℝ)
  filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with p e1 e2
  rw [e1, e2]
  simp only [etaKernel]
  by_cases hp : p.1 ∈ Ioi b
  · have : p.1 ∉ Ioo a b := fun h => absurd h.2 (not_lt.2 (le_of_lt hp))
    simp [indicator_of_notMem this]
  · simp [indicator_of_notMem hp]

/-- `Var η_{ε'}(w) = Var η_ε(w) + Var η^ε_{ε'}(w)` for `0 < ε' ≤ ε`. -/
theorem etaVar_split {ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε) (w : ℂ) :
    etaVar ε' w = etaVar ε w + Real.pi * ‖etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) w‖ ^ 2 := by
  have hsq : ε' ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hε'.le h 2
  unfold etaVar
  rw [etaKernelL2_split (a' := ε' ^ 2) (b := ε) (by positivity) hsq w, norm_add_sq_real,
    inner_etaKernelL2_Ioi_Ioo (by positivity) hsq]
  ring

/-- `Var η_ε(w) ≤ Var η_{ε'}(w)` for `0 < ε' ≤ ε`. -/
theorem etaVar_anti {ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε) (w : ℂ) :
    etaVar ε w ≤ etaVar ε' w := by
  rw [etaVar_split hε' h w]
  have := Real.pi_pos
  nlinarith [sq_nonneg ‖etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) w‖]

/-- `Var η_ε(v) − Var η_ε(w) ≤ 2 √(1076 |v − w|/ε) √(log ε⁻¹ + 4)` (`0 < ε ≤ 1`). -/
theorem etaVar_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (v w : ℂ) :
    etaVar ε v - etaVar ε w ≤
      2 * Real.sqrt (1076 * ‖v - w‖ / ε) * Real.sqrt (Real.log ε⁻¹ + 4) := by
  set a := etaKernelL2 (Ioi (ε ^ 2)) v
  set b := etaKernelL2 (Ioi (ε ^ 2)) w
  have hpi := Real.pi_pos
  set r := Real.sqrt Real.pi
  have hr : r ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hD := pi_sq_norm_etaKernelL2_sub_le hW hε v w
  have hVa := etaVar_le hε hε1 v
  have hVb := etaVar_le hε hε1 w
  unfold etaVar at hVa hVb ⊢
  -- x = r‖a − b‖, y = r‖a‖, z = r‖b‖
  have hx : r * ‖a - b‖ ≤ Real.sqrt (1076 * ‖v - w‖ / ε) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [mul_pow, hr]; exact hD))
  have hy : r * ‖a‖ ≤ Real.sqrt (Real.log ε⁻¹ + 4) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [mul_pow, hr]; exact hVa))
  have hz : r * ‖b‖ ≤ Real.sqrt (Real.log ε⁻¹ + 4) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [mul_pow, hr]; exact hVb))
  have hab : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := norm_sub_norm_le a b
  have e : Real.pi * ‖a‖ ^ 2 - Real.pi * ‖b‖ ^ 2 =
      (r * (‖a‖ - ‖b‖)) * (r * ‖a‖ + r * ‖b‖) := by rw [← hr]; ring
  rw [e]
  have h0 : 0 ≤ r * ‖a‖ + r * ‖b‖ := by positivity
  have h1 : r * (‖a‖ - ‖b‖) ≤ r * ‖a - b‖ := mul_le_mul_of_nonneg_left hab hr0
  have hs0 : 0 ≤ Real.sqrt (1076 * ‖v - w‖ / ε) := Real.sqrt_nonneg _
  calc (r * (‖a‖ - ‖b‖)) * (r * ‖a‖ + r * ‖b‖)
      ≤ Real.sqrt (1076 * ‖v - w‖ / ε) * (r * ‖a‖ + r * ‖b‖) :=
        mul_le_mul_of_nonneg_right (h1.trans hx) h0
    _ ≤ Real.sqrt (1076 * ‖v - w‖ / ε) *
        (Real.sqrt (Real.log ε⁻¹ + 4) + Real.sqrt (Real.log ε⁻¹ + 4)) :=
        mul_le_mul_of_nonneg_left (add_le_add hy hz) hs0
    _ = 2 * Real.sqrt (1076 * ‖v - w‖ / ε) * Real.sqrt (Real.log ε⁻¹ + 4) := by ring

/-- **Own lemma (the variance fact DZZ use unstated at l. 975)**: for `0 < ε' ≤ ε ≤ 1`,
`Var η_ε(v) − Var η_{ε'}(w) ≤ 2 √(1076 |v − w|/ε) √(log ε⁻¹ + 4)`. -/
theorem etaVar_sub_fine_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε)
    (hε1 : ε ≤ 1) (v w : ℂ) :
    etaVar ε v - etaVar ε' w ≤
      2 * Real.sqrt (1076 * ‖v - w‖ / ε) * Real.sqrt (Real.log ε⁻¹ + 4) := by
  have := etaVar_sub_le hW (hε'.trans_le h) hε1 v w
  have := etaVar_anti hε' h w
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The variance of the band `η^{ε}_{ε'}(w)`. -/
def etaBandVar (ε' ε : ℝ) (w : ℂ) : ℝ := Real.pi * ‖etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) w‖ ^ 2

lemma etaBandVar_nonneg (ε' ε : ℝ) (w : ℂ) : 0 ≤ etaBandVar ε' ε w := by
  unfold etaBandVar; positivity

/-- `η^{ε}_{ε'}(w) ~ N(0, Var η^ε_{ε'}(w))`. -/
theorem hasLaw_eta (hW : IsWhiteNoise P W) (ε' ε : ℝ) (w : ℂ) :
    HasLaw (eta W ε' ε w) (gaussianReal 0 (etaBandVar ε' ε w).toNNReal) P := by
  have h := hW.hasLaw (ι := Unit) (fun _ => etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) w)
    (fun _ => Real.sqrt Real.pi)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  have e : ‖Real.sqrt Real.pi • etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) w‖ ^ 2 =
      etaBandVar ε' ε w := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt Real.pi_pos.le, etaBandVar]
  rw [e] at h
  exact h

/-- Exponential-martingale bound: for `U ~ N(0, V)`, `P(a ≤ γ U − γ²/2 V) ≤ e^{−a}`. -/
lemma tail_normalized_of_hasLaw [IsProbabilityMeasure P] {U : Ω → ℝ} {V : ℝ} (hV : 0 ≤ V)
    (hU : HasLaw U (gaussianReal 0 V.toNNReal) P) (γ a : ℝ) :
    P.real {ω | a ≤ γ * U ω - γ ^ 2 / 2 * V} ≤ Real.exp (-a) := by
  have hint : Integrable (fun ω => Real.exp (γ * U ω)) P :=
    hU.integrable_comp (f := fun x => Real.exp (γ * x)) (integrable_exp_mul_gaussianReal γ)
  by_cases hγ : γ = 0
  · subst hγ
    by_cases ha : a ≤ 0
    · exact measureReal_le_one.trans (by
        have := Real.add_one_le_exp (-a); linarith)
    · have : {ω | a ≤ 0 * U ω - (0 : ℝ) ^ 2 / 2 * V} = ∅ := by
        ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; push Not
        simp; linarith
      rw [this]; simp; positivity
  -- reduce to a tail of `γ U` via Chernoff with parameter `1`
  have hset : {ω | a ≤ γ * U ω - γ ^ 2 / 2 * V} =
      {ω | a + γ ^ 2 / 2 * V ≤ (fun ω => γ * U ω) ω} := by
    ext ω; simp only [mem_ofPred_eq]; constructor <;> intro h <;> linarith
  rw [hset]
  have hint1 : Integrable (fun ω => Real.exp (1 * (γ * U ω))) P := by
    simpa using hint
  refine (measure_ge_le_exp_mul_mgf (a + γ ^ 2 / 2 * V) zero_le_one hint1).trans ?_
  have hm : mgf (fun ω => γ * U ω) P 1 = Real.exp (V * γ ^ 2 / 2) := by
    have : mgf (fun ω => γ * U ω) P 1 = mgf U P γ := by
      simp [mgf]
    rw [this, mgf_gaussianReal hU, Real.coe_toNNReal _ hV]
    ring_nf
  rw [hm, ← Real.exp_add]
  refine Real.exp_le_exp.mpr (le_of_eq ?_)
  ring

/-- `P(a ≤ γ η^ε_{ε'}(w) − γ²/2 Var) ≤ e^{−a}`. -/
theorem tail_eta_normalized (hW : IsWhiteNoise P W) (ε' ε : ℝ) (w : ℂ) (γ a : ℝ) :
    P.real {ω | a ≤ γ * eta W ε' ε w ω - γ ^ 2 / 2 * etaBandVar ε' ε w} ≤ Real.exp (-a) := by
  have := hW.isProbabilityMeasure
  exact tail_normalized_of_hasLaw (etaBandVar_nonneg _ _ _) (hasLaw_eta hW ε' ε w) γ a

/-- a.s. decomposition `η_{ε'}(w) = η_ε(w) + η^ε_{ε'}(w)` for `0 < ε' ≤ ε`. -/
theorem etaInf_eq_add_eta_ae (hW : IsWhiteNoise P W) {ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε)
    (w : ℂ) :
    etaInf W ε' w =ᵐ[P] fun ω => etaInf W ε w ω + eta W ε' ε w ω := by
  have hsq : ε' ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hε'.le h 2
  filter_upwards [hW.add_ae (etaKernelL2 (Ioi (ε ^ 2)) w)
    (etaKernelL2 (Ioo (ε' ^ 2) (ε ^ 2)) w)] with ω hω
  simp only [etaInf, eta, etaField]
  rw [etaKernelL2_split (a' := ε' ^ 2) (b := ε) (by positivity) hsq w, hω]
  ring

end DZZ
end LQGMetric
