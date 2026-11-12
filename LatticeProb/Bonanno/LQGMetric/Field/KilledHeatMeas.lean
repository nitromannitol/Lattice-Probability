/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatMeas at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatCK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 15: Brownian scaling of the bridge and joint measurability
(task P2-KILLED, D-KHK1)

* `IsPlanarBridge.scale`: if `X` is a planar bridge of length `1`, `s ↦ √t X_{s/t}` is one of
  length `t` (Brownian scaling; Gaussian covariance check).
* `measurable_killedHeat`: `(t, z, w) ↦ p_A(t; z, w)` is jointly measurable for open `A`
  (needed for the Bochner integrals `∫ p_A(s; ·, ·) ds` of DZZ / Green function).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The rescaled process `s ↦ √t X_{s/t}`. -/
def scaleBr (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ :=
  fun s ω ↦ ((Real.sqrt t : ℝ) : ℂ) * X (s / t) ω

lemma coordProc_scaleBr (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) (p : Bool × ℝ≥0) :
    coordProc (scaleBr t X) p = fun ω ↦ Real.sqrt t • coordProc X (p.1, p.2 / t) ω := by
  ext ω
  rcases p with ⟨b, s⟩
  cases b <;> simp [coordProc, scaleBr]

theorem IsPlanarBridge.scale {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω} (hX : IsPlanarBridge 1 X P)
    {t : ℝ≥0} (ht : t ≠ 0) : IsPlanarBridge t (scaleBr t X) P := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hle : ∀ s : ℝ≥0, s ≤ t → s / t ≤ 1 := fun s hs ↦ by
    rw [div_le_one (pos_iff_ne_zero.mpr ht)]; exact hs
  refine ⟨?_, ?_, fun p ↦ ?_, fun p q hp hq ↦ ?_⟩
  · filter_upwards [hX.cont] with ω hω
    unfold scaleBr
    exact continuous_const.mul (hω.comp (continuous_id.div_const _))
  · have h0 : IsGaussianProcess (fun p : Bool × ℝ≥0 ↦ fun ω ↦ coordProc X (p.1, p.2 / t) ω) P :=
      hX.gauss.comp_right (fun p : Bool × ℝ≥0 ↦ (p.1, p.2 / t))
    have := h0.smul (fun _ : Bool × ℝ≥0 ↦ Real.sqrt t)
    have e : coordProc (scaleBr t X) = fun p ω ↦ Real.sqrt t • coordProc X (p.1, p.2 / t) ω :=
      funext (coordProc_scaleBr t X)
    rw [e]
    exact this
  · rw [coordProc_scaleBr]
    simp only [smul_eq_mul]
    rw [integral_const_mul, hX.mean, mul_zero]
  · rw [coordProc_scaleBr, coordProc_scaleBr]
    simp only [smul_eq_mul]
    rw [covariance_const_mul_left, covariance_const_mul_right, hX.cov _ _ (hle _ hp) (hle _ hq)]
    rcases p with ⟨b, s⟩
    rcases q with ⟨b', r⟩
    simp only [bridgeCov]
    split_ifs
    · have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht'.le
      rw [min_div_div_right zero_le, NNReal.coe_div, NNReal.coe_div, NNReal.coe_div,
        NNReal.coe_one, ← mul_assoc, hst]
      field_simp
    · ring

lemma bridgeEvent_scaleBr {t : ℝ≥0} (ht : t ≠ 0) (A : Set ℂ) (z w : ℂ) (Y : ℝ≥0 → Ω → ℂ) :
    bridgeEvent A t z w (scaleBr t Y) =
      bridgeEvent A 1 z w (fun u ω ↦ ((Real.sqrt t : ℝ) : ℂ) * Y u ω) := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  ext ω
  simp only [bridgeEvent, bridgePath, scaleBr, Set.mem_ofPred_eq, NNReal.coe_one, div_one]
  constructor
  · intro h u hu
    have := h (u * t) (by simpa using mul_le_mul_of_nonneg_right hu (zero_le : (0 : ℝ≥0) ≤ t))
    rwa [mul_div_cancel_right₀ _ ht, NNReal.coe_mul, mul_div_cancel_right₀ _ ht'] at this
  · intro h s hs
    have := h (s / t) (by rw [div_le_one (pos_iff_ne_zero.mpr ht)]; exact hs)
    rwa [NNReal.coe_div] at this

/-- The bridge probability through the length-`1` bridge (scaling). -/
lemma bridgeStay_eq_scale {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (z w : ℂ) :
    bridgeStay A t z w = ((P2.map (fun ω p ↦ sampled 1 (stdBridge 1) p ω))
      {g | (fun p ↦ Real.sqrt t * g p) ∈ cEvent A 1 z w}).toReal := by
  have h1 := isPlanarBridge_stdBridge (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  rw [← bridgeStay_eq_of_isPlanarBridge hA ht (h1.scale ht) z w, bridgeEvent_scaleBr ht]
  have hm : AEMeasurable (fun ω p ↦ sampled 1 (stdBridge 1) p ω) P2 :=
    .of_eval fun p ↦ (sampled_isGaussianProcess h1).aemeasurable p
  have hS : MeasurableSet {g : Bool × ℚ → ℝ | (fun p ↦ Real.sqrt t * g p) ∈ cEvent A 1 z w} :=
    measurableSet_cEvent_gen A 1 (g := fun g : Bool × ℚ → ℝ ↦ fun p ↦ Real.sqrt t * g p)
      (by fun_prop) measurable_const measurable_const
  rw [Measure.map_apply_of_aemeasurable hm hS]
  congr 1
  refine measure_congr ?_
  filter_upwards [h1.cont] with ω hω
  have hc : Continuous fun u ↦ ((Real.sqrt t : ℝ) : ℂ) * stdBridge 1 u ω :=
    continuous_const.mul hω
  apply propext
  rw [mem_bridgeEvent_iff A hA 1 z w _ hc]
  have e : (fun p ↦ sampled 1 (fun u ω ↦ ((Real.sqrt t : ℝ) : ℂ) * stdBridge 1 u ω) p ω) =
      fun p ↦ Real.sqrt t * sampled 1 (stdBridge 1) p ω := by
    funext p
    rcases p with ⟨b, q⟩
    cases b <;> simp [sampled, coordProc]
  rw [e]
  rfl

/-- **Joint measurability** of `(t, z, w) ↦ p_A(t; z, w)` for open `A`. -/
theorem measurable_killedHeat {A : Set ℂ} (hA : IsOpen A) :
    Measurable fun x : ℝ≥0 × ℂ × ℂ ↦ killedHeat A x.1 x.2.1 x.2.2 := by
  set μ1 := P2.map (fun ω p ↦ sampled 1 (stdBridge 1) p ω)
  have hS : MeasurableSet {q : (ℝ≥0 × ℂ × ℂ) × (Bool × ℚ → ℝ) |
      (fun p ↦ Real.sqrt q.1.1 * q.2 p) ∈ cEvent A 1 q.1.2.1 q.1.2.2} :=
    measurableSet_cEvent_gen A 1 (by fun_prop) (by fun_prop) (by fun_prop)
  have hF : Measurable fun x : ℝ≥0 × ℂ × ℂ ↦
      (μ1 {g | (fun p ↦ Real.sqrt x.1 * g p) ∈ cEvent A 1 x.2.1 x.2.2}).toReal :=
    (measurable_measure_prodMk_left hS).ennreal_toReal
  have hH : Measurable fun x : ℝ≥0 × ℂ × ℂ ↦ heatKernel x.1 x.2.1 x.2.2 := by
    unfold heatKernel
    fun_prop
  have e : (fun x : ℝ≥0 × ℂ × ℂ ↦ killedHeat A x.1 x.2.1 x.2.2) = fun x ↦
      heatKernel x.1 x.2.1 x.2.2 *
        (μ1 {g | (fun p ↦ Real.sqrt x.1 * g p) ∈ cEvent A 1 x.2.1 x.2.2}).toReal := by
    funext x
    rcases eq_or_ne x.1 0 with h0 | h0
    · simp [killedHeat, heatKernel, h0]
    · rw [killedHeat, bridgeStay_eq_scale hA h0]
  rw [e]
  exact hH.mul hF

end KilledHeat
end LQGMetric
