/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L1Var at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6EtaVar

/-!
# DZZ Lemma 3.1, inputs: variance and tails of the approximate LQG mass (P2-DZZ3A, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422) proof of Lemma 3.1 (l. 833–848) uses
`Var η_ε(v) ≤ log ε⁻¹ + O(1)` and Gaussian tails of `η_ε(v)` ("a straightforward union bound").

* `etaVar_le`: `Var η_ε(v) = π ∫_{ε²}^∞ p_{𝕍 ∩ B(v, r(s))}(s; v, v) ds ≤ log ε⁻¹ + 4` for
  `0 < ε ≤ 1` (heat-kernel bound `(2πs)⁻¹` on `(ε², 1]`, `4/(π s²)` on `(1, ∞)`).
* `hasLaw_etaInf`: `η_ε(v) ~ N(0, Var η_ε(v))` under a white noise.
* `approxLQG_ge_tail` / `approxLQG_lt_tail`: exponential-moment (Chernoff) bounds for
  `P(M_{γ,s}(B) ≥ δ²)` and `P(M_{γ,s}(B) < δ²)`. DZZ write the union bound with a Gaussian tail
  of `η`; we use the exponential moment of `η` instead (same Gaussian computation, avoids
  optimising the tail in `Var η`; DEVIATIONS: own elementary step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

lemma etaVar_nonneg (ε : ℝ) (v : ℂ) : 0 ≤ etaVar ε v := by
  unfold etaVar; positivity

/-- `Var η_ε(v) ≤ log ε⁻¹ + 4` for `0 < ε ≤ 1`. -/
theorem etaVar_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (v : ℂ) :
    etaVar ε v ≤ Real.log ε⁻¹ + 4 := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε21 : ε ^ 2 ≤ 1 := by nlinarith
  set f : ℝ → ℝ := fun s => killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v
    with hf
  have nv : ∫ p, etaKernel (Ioi (ε ^ 2)) v p * etaKernel (Ioi (ε ^ 2)) v p =
      ∫ s in Ioi (ε ^ 2), f s := by
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel measurableSet_Ioi v)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time v)
      (fun s => killedHeat_nonneg _ _ _ _)
      (lintegral_etaKernel_sq measurableSet_Ioi (Ioi_subset_Ioi hε2.le) v)
  have hfi : IntegrableOn f (Ioi (ε ^ 2)) := integrableOn_killedHeat_eta hε2 subset_rfl v
  have hsplit : ∫ s in Ioi (ε ^ 2), f s =
      (∫ s in Ioc (ε ^ 2) 1, f s) + ∫ s in Ioi 1, f s := by
    rw [← Ioc_union_Ioi_eq_Ioi hε21, setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hfi.mono_set Ioc_subset_Ioi_self) (hfi.mono_set (Ioi_subset_Ioi hε21))]
  have hinv : IntegrableOn (fun s : ℝ => (2 * Real.pi)⁻¹ * s⁻¹) (Ioc (ε ^ 2) 1) :=
    (((continuousOn_inv₀.mono fun x hx => mem_compl_singleton_iff.mpr
      (ne_of_gt (hε2.trans_le hx.1))).integrableOn_Icc).mono_set Ioc_subset_Icc_self).const_mul _
  have h1 : ∫ s in Ioc (ε ^ 2) 1, f s ≤ Real.log ε⁻¹ / Real.pi := by
    calc ∫ s in Ioc (ε ^ 2) 1, f s ≤ ∫ s in Ioc (ε ^ 2) 1, (2 * Real.pi)⁻¹ * s⁻¹ := by
          refine setIntegral_mono_on (hfi.mono_set Ioc_subset_Ioi_self) hinv measurableSet_Ioc
            fun s hs => ?_
          have hs0 : 0 < s := hε2.trans hs.1
          refine (killedHeat_le_heatKernel _ _ _ _).trans ?_
          refine (heatKernel_le_inv _ (NNReal.coe_nonneg _) v v).trans (le_of_eq ?_)
          rw [Real.coe_toNNReal _ hs0.le, mul_inv]
      _ = Real.log ε⁻¹ / Real.pi := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hε21,
            integral_inv_of_pos hε2 one_pos, one_div, Real.log_inv, Real.log_pow, Real.log_inv]
          have := Real.pi_pos
          field_simp
          push_cast
          ring
  have hpow : IntegrableOn (fun s : ℝ => 2 ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  have h2 : ∫ s in Ioi (1 : ℝ), f s ≤ 4 / Real.pi := by
    calc ∫ s in Ioi (1 : ℝ), f s ≤ ∫ s in Ioi (1 : ℝ), 2 ^ 2 / Real.pi * s ^ (-2 : ℝ) :=
          setIntegral_mono_on (hfi.mono_set (Ioi_subset_Ioi hε21)) hpow measurableSet_Ioi
            fun s hs => killedHeat_le_rpow (by norm_num)
              (inter_subset_left.trans openSquare_subset_ball) (one_pos.trans hs) v v
      _ = 4 / Real.pi := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
          norm_num
  have hpi := Real.pi_pos
  rw [etaVar, ← real_inner_self_eq_norm_sq,
    inner_etaKernelL2 measurableSet_Ioi hε2 subset_rfl v v, nv, hsplit]
  calc Real.pi * ((∫ s in Ioc (ε ^ 2) 1, f s) + ∫ s in Ioi 1, f s)
      ≤ Real.pi * (Real.log ε⁻¹ / Real.pi + 4 / Real.pi) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hpi.le
    _ = Real.log ε⁻¹ + 4 := by field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `η_ε(v) ~ N(0, Var η_ε(v))` under a white noise. -/
theorem hasLaw_etaInf (hW : IsWhiteNoise P W) (ε : ℝ) (v : ℂ) :
    HasLaw (etaInf W ε v) (gaussianReal 0 (etaVar ε v).toNNReal) P := by
  have h := hW.hasLaw (ι := Unit) (fun _ => etaKernelL2 (Ioi (ε ^ 2)) v)
    (fun _ => Real.sqrt Real.pi)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  have e : ‖Real.sqrt Real.pi • etaKernelL2 (Ioi (ε ^ 2)) v‖ ^ 2 = etaVar ε v := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt Real.pi_pos.le, etaVar]
  rw [e] at h
  exact h

lemma integrable_exp_etaInf (hW : IsWhiteNoise P W) (ε : ℝ) (v : ℂ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * etaInf W ε v ω)) P :=
  (hasLaw_etaInf hW ε v).integrable_comp (f := fun x => Real.exp (t * x))
    (integrable_exp_mul_gaussianReal t)

lemma mgf_etaInf (hW : IsWhiteNoise P W) (ε : ℝ) (v : ℂ) (t : ℝ) :
    mgf (etaInf W ε v) P t = Real.exp (etaVar ε v * t ^ 2 / 2) := by
  rw [mgf_gaussianReal (hasLaw_etaInf hW ε v), Real.coe_toNNReal _ (etaVar_nonneg _ _)]
  ring_nf

omit [MeasurableSpace Ω] in
/-- `M ≥ δ²` iff `η ≥ (2 log δ − 2 log s + γ²V/2)/γ`. -/
lemma le_approxLQG_iff {γ : ℝ} (hγ : 0 < γ) {δ : ℝ} (hδ : 0 < δ) (ω : Ω) (b : DyBox) :
    δ ^ 2 ≤ approxLQG γ W ω b ↔
      (2 * Real.log δ - 2 * Real.log b.side + γ ^ 2 / 2 * etaVar b.side b.center) / γ ≤
        etaInf W b.side b.center ω := by
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  rw [approxLQG, div_le_iff₀ hγ, ← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow, Real.log_pow]
  push_cast
  constructor <;> intro h <;> linarith

variable [IsProbabilityMeasure P]

/-- Chernoff bound for `M_{γ,s}(B) ≥ δ²` with exponent `p ≥ 1`:
`P ≤ exp(2p(log s − log δ) + p(p−1)γ²/2 (log s⁻¹ + 4))`. -/
theorem approxLQG_ge_tail (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {δ : ℝ} (hδ : 0 < δ)
    {p : ℝ} (hp : 1 ≤ p) (b : DyBox) :
    P.real {ω | δ ^ 2 ≤ approxLQG γ W ω b} ≤
      Real.exp (2 * p * (Real.log b.side - Real.log δ) +
        p * (p - 1) * γ ^ 2 / 2 * (Real.log b.side⁻¹ + 4)) := by
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  have hs1 : b.side ≤ 1 := by unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  set V := etaVar b.side b.center
  set t := (2 * Real.log δ - 2 * Real.log b.side + γ ^ 2 / 2 * V) / γ
  have hset : {ω | δ ^ 2 ≤ approxLQG γ W ω b} = {ω | t ≤ etaInf W b.side b.center ω} := by
    ext ω; exact le_approxLQG_iff hγ hδ ω b
  rw [hset]
  refine (measure_ge_le_exp_mul_mgf t (by positivity : 0 ≤ p * γ)
    (integrable_exp_etaInf hW _ _ _)).trans ?_
  rw [mgf_etaInf hW, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hV := etaVar_le hs hs1 b.center
  have hpp : 0 ≤ p * (p - 1) * γ ^ 2 / 2 := by
    have : 0 ≤ p - 1 := by linarith
    positivity
  have e : -(p * γ) * t + V * (p * γ) ^ 2 / 2 =
      2 * p * (Real.log b.side - Real.log δ) + p * (p - 1) * γ ^ 2 / 2 * V := by
    simp only [t]; field_simp; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hV hpp]

/-- Chernoff bound for `M_{γ,s}(B) < δ²`:
`P ≤ exp(2(log δ − log s) + γ²(log s⁻¹ + 4))`. -/
theorem approxLQG_lt_tail (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {δ : ℝ} (hδ : 0 < δ)
    (b : DyBox) :
    P.real {ω | approxLQG γ W ω b < δ ^ 2} ≤
      Real.exp (2 * (Real.log δ - Real.log b.side) + γ ^ 2 * (Real.log b.side⁻¹ + 4)) := by
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  have hs1 : b.side ≤ 1 := by unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  set V := etaVar b.side b.center
  set t := (2 * Real.log δ - 2 * Real.log b.side + γ ^ 2 / 2 * V) / γ
  have hset : {ω | approxLQG γ W ω b < δ ^ 2} ⊆ {ω | etaInf W b.side b.center ω ≤ t} := by
    intro ω hω
    have := (le_approxLQG_iff hγ hδ ω b).not.mp (not_le.mpr hω)
    exact (not_le.mp this).le
  refine (measureReal_mono hset).trans ?_
  refine (measure_le_le_exp_mul_mgf t (by linarith : -γ ≤ 0)
    (integrable_exp_etaInf hW _ _ _)).trans ?_
  rw [mgf_etaInf hW, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hV := etaVar_le hs hs1 b.center
  have e : -(-γ) * t + V * (-γ) ^ 2 / 2 =
      2 * (Real.log δ - Real.log b.side) + γ ^ 2 * V := by
    simp only [t]; field_simp; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hV (sq_nonneg γ)]

end DZZ
end LQGMetric
