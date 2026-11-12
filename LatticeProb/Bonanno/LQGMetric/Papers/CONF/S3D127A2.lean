/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127A2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127A1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N1, part 2: Dynkin's formula for planar Brownian motion against the past (P-127A)

For a bounded functional `ξ = F((B_{r_i})_i)` of the path at times `r_i ≤ s ≤ t` and `g ∈ C³` with
bounded `g, Dg, D²g` and Lipschitz `D²g`:

  `E[ξ g(z + B_t)] − E[ξ g(z + B_s)] = ½ ∫_s^t E[ξ Δg(z + B_u)] du`   (`HeatA.dynkin_past`).

Telescoping of the one-step estimate `HeatA.step_bound` with QZ's
`QuantumZipper.Dynkin.eq_of_step_bound` (the same scheme as QZ `Dynkin.dynkin_additive`, here for
the planar Brownian motion and without drift). Also `HeatA.exists_bounds`: the needed constants
for a compactly supported smooth `g`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Laplacian
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM
namespace HeatA

open KilledHeat KilledHeatSq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

lemma abs_lap_le {g : ℂ → ℝ} {C : ℝ} (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C) (x : ℂ) :
    |Δ g x| ≤ 2 * C := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  refine (abs_add_le _ _).trans ?_
  have h1 := QuantumZipper.Dynkin.abs_iteratedFDeriv_two_vec_le g x 1
  have h2 := QuantumZipper.Dynkin.abs_iteratedFDeriv_two_vec_le g x Complex.I
  simp only [norm_one, one_pow, mul_one, Complex.norm_I] at h1 h2
  linarith [hD2 x]

lemma abs_lap_sub_le {g : ℂ → ℝ} {C : ℝ}
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖) (x y : ℂ) :
    |Δ g x - Δ g y| ≤ 2 * C * ‖x - y‖ := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  have h1 := QuantumZipper.Dynkin.abs_sub_apply_two_le (iteratedFDeriv ℝ 2 g x)
    (iteratedFDeriv ℝ 2 g y) 1
  have h2 := QuantumZipper.Dynkin.abs_sub_apply_two_le (iteratedFDeriv ℝ 2 g x)
    (iteratedFDeriv ℝ 2 g y) Complex.I
  simp only [norm_one, one_pow, mul_one, Complex.norm_I] at h1 h2
  have e : iteratedFDeriv ℝ 2 g x ![1, 1] + iteratedFDeriv ℝ 2 g x ![Complex.I, Complex.I] -
      (iteratedFDeriv ℝ 2 g y ![1, 1] + iteratedFDeriv ℝ 2 g y ![Complex.I, Complex.I]) =
      (iteratedFDeriv ℝ 2 g x ![1, 1] - iteratedFDeriv ℝ 2 g y ![1, 1]) +
      (iteratedFDeriv ℝ 2 g x ![Complex.I, Complex.I] -
        iteratedFDeriv ℝ 2 g y ![Complex.I, Complex.I]) := by ring
  simp only
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith [hLip2 x y]

lemma integral_abs_incr_le (hB : IsPlanarBM B P) (a h : ℝ≥0) (b : Bool) :
    ∫ ω, |incVec B a (a + h) ω b| ∂P ≤ QuantumZipper.gaussianAbsMoment 1 * Real.sqrt h := by
  have := integral_abs_pow_le_of_hasLaw (hasLaw_incr hB a h b) 1
  rw [QuantumZipper.Dynkin.rpow_one_half_eq] at this
  simpa using this

/-- Hölder-½ continuity in time of `E[ξ Φ(z + B_u)]` for Lipschitz bounded `Φ`. -/
lemma abs_integral_sub_le (hB : IsPlanarBM B P) {ξ : Ω → ℝ} (hξ : AEStronglyMeasurable ξ P)
    (hξb : ∀ ω, |ξ ω| ≤ 1) {Φ : ℂ → ℝ} {L M : ℝ} (hΦc : Continuous Φ) (hΦb : ∀ x, |Φ x| ≤ M)
    (hΦL : ∀ x y, |Φ x - Φ y| ≤ L * ‖x - y‖) (z : ℂ) (a h : ℝ≥0) :
    |∫ ω, ξ ω * Φ (z + B (a + h) ω) ∂P - ∫ ω, ξ ω * Φ (z + B a ω) ∂P| ≤
      L * (2 * QuantumZipper.gaussianAbsMoment 1) * Real.sqrt h := by
  have := hB.gauss.isProbabilityMeasure
  have hL : 0 ≤ L := by
    have := hΦL 1 0
    by_contra hneg
    push Not at hneg
    have : L * ‖(1 : ℂ) - 0‖ < 0 := by simp [hneg]
    linarith [abs_nonneg (Φ 1 - Φ 0)]
  have ib : ∀ Y : Ω → ℂ, AEMeasurable Y P → Integrable (fun ω ↦ ξ ω * Φ (Y ω)) P := fun Y hY ↦
    (integrable_const M).mono' (hξ.mul (hΦc.measurable.comp_aemeasurable hY).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        calc |ξ ω| * |Φ (Y ω)| ≤ 1 * M := mul_le_mul (hξb ω) (hΦb _) (abs_nonneg _) zero_le_one
          _ = M := one_mul M)
  have hDi : ∀ b, Integrable (fun ω ↦ |incVec B a (a + h) ω b|) P := fun b ↦
    ((memLp_incr hB a h b).integrable one_le_two).abs
  have i1 : Integrable (fun ω ↦ ξ ω * Φ (z + B (a + h) ω)) P :=
    ib _ (aemeasurable_const.add (aemeasurable_B hB _))
  have i0 : Integrable (fun ω ↦ ξ ω * Φ (z + B a ω)) P :=
    ib _ (aemeasurable_const.add (aemeasurable_B hB _))
  rw [← integral_sub i1 i0]
  refine (abs_integral_le_integral_abs).trans ?_
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
    (((hDi false).add (hDi true)).const_mul L) (ae_of_all _ fun ω ↦ ?_)).trans ?_
  · simp only [Pi.add_apply]
    rw [← mul_sub, abs_mul]
    calc |ξ ω| * |Φ (z + B (a + h) ω) - Φ (z + B a ω)|
        ≤ 1 * (L * ‖z + B (a + h) ω - (z + B a ω)‖) :=
          mul_le_mul (hξb ω) (hΦL _ _) (abs_nonneg _) zero_le_one
      _ ≤ L * (|incVec B a (a + h) ω false| + |incVec B a (a + h) ω true|) := by
          rw [one_mul, add_incr B a h ω, show z + (B a ω + toC (incVec B a (a + h) ω)) -
            (z + B a ω) = toC (incVec B a (a + h) ω) by ring]
          exact mul_le_mul_of_nonneg_left (norm_toC_le _) hL
  · simp only [Pi.add_apply]
    rw [integral_const_mul, integral_add (hDi false) (hDi true)]
    have := add_le_add (integral_abs_incr_le hB a h false) (integral_abs_incr_le hB a h true)
    have h2 : L * (∫ ω, |incVec B a (a + h) ω false| ∂P + ∫ ω, |incVec B a (a + h) ω true| ∂P) ≤
        L * (QuantumZipper.gaussianAbsMoment 1 * Real.sqrt h +
          QuantumZipper.gaussianAbsMoment 1 * Real.sqrt h) :=
      mul_le_mul_of_nonneg_left this hL
    linarith

lemma lipschitz_lap {g : ℂ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖) :
    LipschitzWith (Real.toNNReal (2 * C)) (Δ g) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact abs_lap_sub_le hLip2 x y

lemma toNNReal_sub_le {u v : ℝ} (huv : u ≤ v) : ((v.toNNReal - u.toNNReal : ℝ≥0) : ℝ) ≤ v - u := by
  rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal huv), Real.coe_toNNReal', Real.coe_toNNReal']
  have : max v 0 ≤ max u 0 + (v - u) :=
    max_le (by linarith [le_max_left u 0]) (by linarith [le_max_right u 0])
  linarith

variable {ι : Type*} [Countable ι]

/-- **Dynkin's formula against the past** for planar Brownian motion. -/
theorem dynkin_past (hB : IsPlanarBM B P) {r : ι → ℝ≥0} {s t : ℝ≥0} (hr : ∀ i, r i ≤ s)
    (hst : s ≤ t) {F : (Bool × ι → ℝ) → ℝ} (hF : Measurable F) (hFb : ∀ y, |F y| ≤ 1)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ} (hC : 0 ≤ C)
    (hg0 : ∀ x, |g x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C)
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖) (z : ℂ) :
    ∫ ω, F (pastVec B r ω) * g (z + B t ω) ∂P - ∫ ω, F (pastVec B r ω) * g (z + B s ω) ∂P =
      1 / 2 * ∫ u in (s : ℝ)..t, ∫ ω, F (pastVec B r ω) * Δ g (z + B u.toNNReal ω) ∂P := by
  have := hB.gauss.isProbabilityMeasure
  set ξ : Ω → ℝ := fun ω ↦ F (pastVec B r ω) with hξ
  have hξm : AEStronglyMeasurable ξ P :=
    (hF.comp_aemeasurable (aemeasurable_pastVec hB r)).aestronglyMeasurable
  have hξb : ∀ ω, |ξ ω| ≤ 1 := fun ω ↦ hFb _
  set K := 2 * C * (2 * QuantumZipper.gaussianAbsMoment 1) with hK
  have hK0 : 0 ≤ K := by have := QuantumZipper.gaussianAbsMoment_nonneg 1; positivity
  set f : ℝ → ℝ := fun u ↦ ∫ ω, ξ ω * Δ g (z + B u.toNNReal ω) ∂P with hf
  have hΔc : Continuous (Δ g) := (lipschitz_lap hC hLip2).continuous
  have hfb : ∀ u v : ℝ, u ≤ v → |f v - f u| ≤ K * Real.sqrt (v - u) := by
    intro u v huv
    have hv : v.toNNReal = u.toNNReal + (v.toNNReal - u.toNNReal) :=
      (add_tsub_cancel_of_le (Real.toNNReal_le_toNNReal huv)).symm
    have h1 := abs_integral_sub_le hB hξm hξb hΔc (abs_lap_le hD2) (abs_lap_sub_le hLip2) z
      u.toNNReal (v.toNNReal - u.toNNReal)
    rw [← hv] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (toNNReal_sub_le huv)) hK0)
  have hfc : Continuous f := by
    rw [Metric.continuous_iff]
    intro b ε hε
    refine ⟨(ε / (K + 1)) ^ 2, by positivity, fun a hab ↦ ?_⟩
    rw [Real.dist_eq] at hab ⊢
    have hsq : Real.sqrt |a - b| < ε / (K + 1) := by
      rw [show ε / (K + 1) = Real.sqrt ((ε / (K + 1)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_lt_sqrt (abs_nonneg _) hab
    have hle : |f a - f b| ≤ K * Real.sqrt |a - b| := by
      rcases le_total a b with h | h
      · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr h)]
        exact hfb a b h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        exact hfb b a h
    calc |f a - f b| ≤ K * Real.sqrt |a - b| := hle
      _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hsq.le hK0
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  set ψ : ℝ → ℝ := fun u ↦ ∫ ω, ξ ω * g (z + B u.toNNReal ω) ∂P -
    1 / 2 * ∫ v in (s : ℝ)..u, f v with hψ
  have hstep : ∀ a h : ℝ, (s : ℝ) ≤ a → 0 ≤ h → a + h ≤ t →
      |ψ (a + h) - ψ a| ≤ (8 * C * QuantumZipper.gaussianAbsMoment 3 + K / 2) *
        (h * Real.sqrt h) := by
    intro a h hsa h0 _
    have ha0 : 0 ≤ a := s.coe_nonneg.trans hsa
    have e1 : (a + h).toNNReal = a.toNNReal + h.toNNReal := Real.toNNReal_add ha0 h0
    have hr' : ∀ i, r i ≤ a.toNNReal := fun i ↦ (hr i).trans (by
      rw [← Real.toNNReal_coe (r := s)]; exact Real.toNNReal_le_toNNReal hsa)
    have hstp := step_bound hB hr' h.toNNReal hF hFb hg hC hg0 hD1 hD2 hLip2 z
    rw [Real.coe_toNNReal _ h0, ← e1] at hstp
    have hint : (∫ v in (s : ℝ)..(a + h), f v) - (∫ v in (s : ℝ)..a, f v) = ∫ v in a..(a + h), f v :=
      intervalIntegral.integral_interval_sub_left (hfc.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _)
    have hsplit : ∫ v in a..(a + h), f v = h * f a + ∫ v in a..(a + h), (f v - f a) := by
      rw [intervalIntegral.integral_sub (hfc.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hrem : |∫ v in a..(a + h), (f v - f a)| ≤ K * Real.sqrt h * h := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h)
        (f := fun v ↦ f v - f a) (C := K * Real.sqrt h) (fun v hv ↦ by
          rw [Set.uIoc_of_le (by linarith)] at hv
          rw [Real.norm_eq_abs]
          refine (hfb a v hv.1.le).trans (mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (by linarith [hv.2])) hK0))
      rwa [Real.norm_eq_abs, show a + h - a = h by ring, abs_of_nonneg h0] at this
    have e2 : ψ (a + h) - ψ a = (∫ ω, ξ ω * g (z + B (a + h).toNNReal ω) ∂P -
        ∫ ω, ξ ω * g (z + B a.toNNReal ω) ∂P - h / 2 * f a) -
        1 / 2 * ∫ v in a..(a + h), (f v - f a) := by
      simp only [hψ]
      rw [show ∀ x y z w : ℝ, x - 1 / 2 * y - (z - 1 / 2 * w) = x - z - 1 / 2 * (y - w) by
        intros; ring, hint, hsplit]
      ring
    rw [e2]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := QuantumZipper.gaussianAbsMoment_nonneg 3
    nlinarith [hstp, hrem, Real.sqrt_nonneg h]
  have hfin := QuantumZipper.Dynkin.eq_of_step_bound (ψ := ψ) (NNReal.coe_le_coe.mpr hst) hstep
  simp only [hψ, Real.toNNReal_coe, intervalIntegral.integral_same, mul_zero, sub_zero] at hfin
  linarith

end HeatA
end ZBM
end CONF
end LQGMetric
