/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L10Var at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7

/-!
# (eq-var-compare) for `h̃` and `η` (P2-DZZ3C, input of DZZ Lemma 3.10)

DZZ (arXiv:1807.00422) apply Lemma 3.8 to `ζ¹ = h̃`, `ζ² = η` (`a = 1`) in the proof of
Lemma 3.10 (l. 1263–1264), which needs (eq-var-compare) (l. 1222):
`sup_{v ∈ 𝕍, n ≥ 0} |Var h̃_{2^{-n}}(v) − Var η_{2^{-n}}(v)| ≤ b₁`. DZZ do not write this out; it is
the band computation of (eq-variance-truncation) (proof of Lemma 2.7, l. 556–559), reused here:
`Var h̃_ε(v) − Var η_ε(v) = π ∫_{ε²}^∞ (p_𝕍(s;v,v) − p_{𝕍∩B(v,r(s))}(s;v,v)) ds` (Chapman–Kolmogorov,
`inner_wndKernelL2`, `lintegral_etaKernel_sq`), split into the dyadic bands `(4^{-j-1}, 4^{-j})`
(each `≤ 2 e^{−(2/9)κ j} log 4`, `pi_integral_trunc_le`) and `(1, ∞)` (`≤ 4`).

* `tildeVar ε v = π ‖K^{h̃}_{ε,v}‖²` (`variance_tildeHInf`: `= Var h̃_ε(v)` under a white noise);
* **`dzz_var_compare`**: `∃ b₁, ∀ n v, |tildeVar 2^{-n} v − etaVar 2^{-n} v| ≤ b₁`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- `Var h̃_ε(v) = π ‖K^{h̃}_{ε,v}‖²` (deterministic; `variance_tildeHInf`). -/
def tildeVar (ε : ℝ) (v : ℂ) : ℝ := Real.pi * ‖wndKernelL2 openSquare (Ioi (ε ^ 2)) v‖ ^ 2

/-- `π (∫_I p_𝕍(s; v, v) ds − ∫_I p_{𝕍 ∩ B(v, r(s))}(s; v, v) ds)`. -/
def truncGap (I : Set ℝ) (v : ℂ) : ℝ :=
  Real.pi * ((∫ s in I, killedHeat openSquare s.toNNReal v v) -
    ∫ s in I, killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v)

lemma integrableOn_pK {I : Set ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀) (v : ℂ) :
    IntegrableOn (fun s : ℝ => killedHeat openSquare s.toNNReal v v) I :=
  integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball hc₀ hI0 v v

lemma tildeVar_sub_etaVar {ε : ℝ} (hε : 0 < ε) (v : ℂ) :
    tildeVar ε v - etaVar ε v = truncGap (Ioi (ε ^ 2)) v := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have h1 : ‖wndKernelL2 openSquare (Ioi (ε ^ 2)) v‖ ^ 2 =
      ∫ s in Ioi (ε ^ 2), killedHeat openSquare s.toNNReal v v := by
    rw [← real_inner_self_eq_norm_sq]
    exact inner_wndKernelL2 LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
      openSquare_subset_ball measurableSet_Ioi hε2 subset_rfl v v
  have h2 : ‖etaKernelL2 (Ioi (ε ^ 2)) v‖ ^ 2 =
      ∫ s in Ioi (ε ^ 2), killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v := by
    rw [← real_inner_self_eq_norm_sq, inner_etaKernelL2 measurableSet_Ioi hε2 subset_rfl v v]
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel measurableSet_Ioi v)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time v)
      (fun s => killedHeat_nonneg _ _ _ _)
      (lintegral_etaKernel_sq measurableSet_Ioi (Ioi_subset_Ioi hε2.le) v)
  rw [tildeVar, etaVar, h1, h2, truncGap]
  ring

lemma truncGap_nonneg {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (v : ℂ) : 0 ≤ truncGap I v := by
  unfold truncGap
  refine mul_nonneg Real.pi_pos.le (sub_nonneg.mpr (setIntegral_mono_on
    (integrableOn_killedHeat_eta hc₀ hI0 v) (integrableOn_pK hc₀ hI0 v) hI
    fun s _ => killedHeat_mono Set.inter_subset_left _ _ _))

lemma truncGap_split {a b : ℝ} (ha : 0 < a) (hab : a < b) (v : ℂ) :
    truncGap (Ioi a) v = truncGap (Ioo a b) v + truncGap (Ioi b) v := by
  have key : ∀ f : ℝ → ℝ, IntegrableOn f (Ioi a) →
      ∫ s in Ioi a, f s = (∫ s in Ioo a b, f s) + ∫ s in Ioi b, f s := by
    intro f hf
    rw [← Ioc_union_Ioi_eq_Ioi hab.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hab.le)),
      integral_Ioc_eq_integral_Ioo]
  unfold truncGap
  rw [key _ (integrableOn_pK ha subset_rfl v), key _ (integrableOn_killedHeat_eta ha subset_rfl v)]
  ring

/-- The band `(4^{-j-1}, 4^{-j})` (as `variance_dzzDelta_succ_le`). -/
lemma truncGap_band_le (j : ℕ) (v : ℂ) :
    truncGap (Ioo ((1 / 4 : ℝ) ^ (j + 1)) ((1 / 4 : ℝ) ^ j)) v ≤
      2 * Real.exp (-(2 / 9 * kappaBand * j)) * Real.log 4 := by
  have ha : (0 : ℝ) < (1 / 4) ^ (j + 1) := by positivity
  have hab : (1 / 4 : ℝ) ^ (j + 1) ≤ (1 / 4) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)
  have hlog : Real.log ((1 / 4 : ℝ) ^ j / (1 / 4) ^ (j + 1)) = Real.log 4 := by
    rw [pow_succ, div_mul_cancel_left₀ (by positivity)]
    norm_num
  unfold truncGap
  rw [← hlog]
  refine pi_integral_trunc_le ha hab (fun s hs => (etaRad_band j hs).1) (fun s hs => ?_) v
  have h := (etaRad_band j hs).2
  have e2 : 2 * (etaRad s / 3) ^ 2 / s = 2 / 9 * (etaRad s ^ 2 / s) := by ring
  rw [e2]
  nlinarith

/-- The top band `(1, ∞)` (as `variance_dzzDelta_zero_le`). -/
lemma truncGap_Ioi_one_le (v : ℂ) : truncGap (Ioi 1) v ≤ 4 := by
  have hiu := integrableOn_pK one_pos subset_rfl v
  have h0 : 0 ≤ ∫ s in Ioi (1 : ℝ),
      killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v :=
    setIntegral_nonneg measurableSet_Ioi fun s _ => killedHeat_nonneg _ _ _ _
  have hpow : IntegrableOn (fun s : ℝ => 2 ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  have h1 : ∫ s in Ioi (1 : ℝ), killedHeat openSquare s.toNNReal v v ≤ 4 / Real.pi := by
    calc ∫ s in Ioi (1 : ℝ), killedHeat openSquare s.toNNReal v v
        ≤ ∫ s in Ioi (1 : ℝ), 2 ^ 2 / Real.pi * s ^ (-2 : ℝ) :=
          setIntegral_mono_on hiu hpow measurableSet_Ioi fun s hs =>
            killedHeat_le_rpow (by norm_num) openSquare_subset_ball (one_pos.trans hs) v v
      _ = 4 / Real.pi := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
          norm_num
  have := Real.pi_pos
  unfold truncGap
  calc Real.pi * ((∫ s in Ioi (1 : ℝ), killedHeat openSquare s.toNNReal v v) -
        ∫ s in Ioi (1 : ℝ), killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v)
      ≤ Real.pi * (4 / Real.pi) := mul_le_mul_of_nonneg_left (by linarith) this.le
    _ = 4 := by field_simp

lemma truncGap_dyadic_le (n : ℕ) (v : ℂ) :
    truncGap (Ioi ((1 / 4 : ℝ) ^ n)) v ≤ 4 + 2 * Real.log 4 *
      ∑ j ∈ range n, Real.exp (-(2 / 9 * kappaBand)) ^ j := by
  induction n with
  | zero => simpa using truncGap_Ioi_one_le v
  | succ n ih =>
    have hlt : (1 / 4 : ℝ) ^ (n + 1) < (1 / 4) ^ n :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self n)
    rw [truncGap_split (by positivity) hlt, sum_range_succ]
    have hb := truncGap_band_le n v
    have e : Real.exp (-(2 / 9 * kappaBand * n)) = Real.exp (-(2 / 9 * kappaBand)) ^ n := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [e] at hb
    nlinarith

/-- **(eq-var-compare) for `(h̃, η)`, `a = 1`**: `|Var h̃_{2^{-n}}(v) − Var η_{2^{-n}}(v)| ≤ b₁`
for all `n ≥ 0` and all `v` (DZZ l. 1222, used in l. 1263–1264). -/
theorem dzz_var_compare : ∃ b₁ : ℝ, 0 ≤ b₁ ∧ ∀ (n : ℕ) (v : ℂ),
    |tildeVar ((1 / 2 : ℝ) ^ n) v - etaVar ((1 / 2 : ℝ) ^ n) v| ≤ b₁ := by
  set ρ := Real.exp (-(2 / 9 * kappaBand)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by have := kappaBand_pos; linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4 + 2 * Real.log 4 / (1 - ρ), by
    have : 0 < 1 - ρ := by linarith
    positivity, fun n v => ?_⟩
  have hsq : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [tildeVar_sub_etaVar (by positivity), hsq]
  have h0 := truncGap_nonneg measurableSet_Ioi (by positivity : (0 : ℝ) < (1 / 4) ^ n)
    subset_rfl v
  have hgeom : ∑ j ∈ range n, ρ ^ j ≤ 1 / (1 - ρ) := by
    have h1ρ : 0 < 1 - ρ := by linarith
    rw [geom_sum_eq hρ1.ne n, ← neg_div_neg_eq, neg_sub, neg_sub,
      div_le_div_iff₀ h1ρ h1ρ]
    have : 0 < ρ ^ n := by positivity
    nlinarith
  have h1 := truncGap_dyadic_le n v
  rw [abs_le]
  constructor
  · have : 0 < 1 - ρ := by linarith
    have : 0 ≤ 2 * Real.log 4 / (1 - ρ) := by positivity
    linarith
  · have := mul_le_mul_of_nonneg_left hgeom (by positivity : (0 : ℝ) ≤ 2 * Real.log 4)
    rw [mul_one_div] at this
    linarith

end DZZ
end LQGMetric
