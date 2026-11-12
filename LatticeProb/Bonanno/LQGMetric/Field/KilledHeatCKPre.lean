/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatCKPre at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
* `measurableSet_cEvent_param`, `measurable_bridgeStay_left/right`: measurability of the bridge
  probability in its endpoints.
* `bridgeEvent_split`: pathwise, the bridge from `z` to `w` of length `t + s` stays in `A` iff its
  first piece (`bridgeOf t β`, from `z` to the midpoint `y'`) and its second piece
  (`bridgeTail (t+s) s β`, from `y'` to `w`) do.
* `heatKernel_mul_heatKernel_mid`: `p_{t+s}(z,w) p_{ts/(t+s)}(m, y) = p_t(z,y) p_s(y,w)` with
  `m = z + (t/(t+s))(w − z)` (completing the square; cf. `HeatSq.heatKernel_mul_heatKernel_ck`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `{(x, g) | g ∈ cEvent A t (f x) (h x)}` is measurable for measurable `f, h`. -/
lemma measurableSet_cEvent_param {α : Type*} {mα : MeasurableSpace α} (A : Set ℂ) (t : ℝ≥0)
    {f h : α → ℂ} (hf : Measurable f) (hh : Measurable h) :
    MeasurableSet {p : α × (Bool × ℚ → ℝ) | p.2 ∈ cEvent A t (f p.1) (h p.1)} := by
  have : {p : α × (Bool × ℚ → ℝ) | p.2 ∈ cEvent A t (f p.1) (h p.1)} = ⋃ n : ℕ, ⋂ q : ℚ,
      {p | f p.1 + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (h p.1 - f p.1) + cpt p.2 q ∈
        innerSet A n} := by
    ext p
    simp [cEvent]
  rw [this]
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.iInter fun q ↦ ?_
  have hm : Measurable fun p : α × (Bool × ℚ → ℝ) ↦
      f p.1 + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (h p.1 - f p.1) + cpt p.2 q := by
    unfold cpt
    fun_prop
  exact hm (isClosed_innerSet A n).measurableSet

lemma bridgeStay_eq_map {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (z w : ℂ) :
    bridgeStay A t z w =
      ((P2.map (fun ω p ↦ sampled t (stdBridge t) p ω)) (cEvent A t z w)).toReal := by
  rw [bridgeStay, measure_bridgeEvent_eq_map (isPlanarBridge_stdBridge ht) hA]

lemma measurable_bridgeStay_right {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (z : ℂ) :
    Measurable fun w ↦ bridgeStay A t z w := by
  simp_rw [bridgeStay_eq_map hA ht]
  exact (measurable_measure_prodMk_left (measurableSet_cEvent_param A t
    (f := fun _ : ℂ ↦ z) measurable_const measurable_id)).ennreal_toReal

lemma measurable_bridgeStay_left {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (w : ℂ) :
    Measurable fun z ↦ bridgeStay A t z w := by
  simp_rw [bridgeStay_eq_map hA ht]
  exact (measurable_measure_prodMk_left (measurableSet_cEvent_param A t
    (h := fun _ : ℂ ↦ w) measurable_id measurable_const)).ennreal_toReal

lemma measurable_heatKernel_right (t : ℝ) (z : ℂ) : Measurable fun w ↦ heatKernel t z w :=
  Continuous.measurable (by unfold heatKernel; fun_prop)

lemma measurable_heatKernel_left (t : ℝ) (w : ℂ) : Measurable fun z ↦ heatKernel t z w :=
  Continuous.measurable (by unfold heatKernel; fun_prop)

lemma measurable_killedHeat_right {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (z : ℂ) :
    Measurable fun w ↦ killedHeat A t z w :=
  (measurable_heatKernel_right t z).mul (measurable_bridgeStay_right hA ht z)

lemma measurable_killedHeat_left {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (w : ℂ) :
    Measurable fun z ↦ killedHeat A t z w :=
  (measurable_heatKernel_left t w).mul (measurable_bridgeStay_left hA ht w)

/-- The midpoint `m + β_t` of the bridge from `z` to `w` of length `t + s`. -/
def midPt (t s : ℝ≥0) (z w : ℂ) : ℂ := z + (((t : ℝ) / ((t + s : ℝ≥0) : ℝ) : ℝ) : ℂ) * (w - z)

lemma bridgePath_head {t s : ℝ≥0} (ht : t ≠ 0) (z w : ℂ) (β : ℝ≥0 → Ω → ℂ) (a : ℝ≥0)
    (ω : Ω) :
    bridgePath t z (midPt t s z w + β t ω) (bridgeOf t β) a ω =
      bridgePath (t + s) z w β a ω := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hT : ((t + s : ℝ≥0) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm ht')
    exact ne_of_gt (by push_cast; positivity)
  have hc : (((a : ℝ) / t : ℝ) : ℂ) * (((t : ℝ) / ((t + s : ℝ≥0) : ℝ) : ℝ) : ℂ) =
      (((a : ℝ) / ((t + s : ℝ≥0) : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  simp only [bridgePath, bridgeOf, midPt]
  linear_combination (w - z) * hc

lemma bridgePath_tail {t s : ℝ≥0} (ht : t ≠ 0) (hs : s ≠ 0) (z w : ℂ) (β : ℝ≥0 → Ω → ℂ)
    {r : ℝ≥0} (hr : r ≤ s) (ω : Ω) :
    bridgePath s (midPt t s z w + β t ω) w (bridgeTail (t + s) s β) r ω =
      bridgePath (t + s) z w β (t + r) ω := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  have ht0 : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hT : (t : ℝ) + s ≠ 0 := by positivity
  have h1 : (((s - r : ℝ≥0) : ℝ) / s) = 1 - (r : ℝ) / s := by
    rw [NNReal.coe_sub hr]
    field_simp
  have h2 : ((t : ℝ) / (t + s)) * (1 - (r : ℝ) / s) + (r : ℝ) / s = ((t : ℝ) + r) / (t + s) := by
    field_simp
    ring
  have h2c : ((((t : ℝ) / (t + s) : ℝ)) : ℂ) * (1 - (((r : ℝ) / s : ℝ) : ℂ)) +
      (((r : ℝ) / s : ℝ) : ℂ) = ((((t : ℝ) + r) / (t + s) : ℝ) : ℂ) := by
    rw [← h2]
    push_cast
    ring
  rw [bridgePath, bridgeTail_apply, add_tsub_tsub_eq t s r hr, add_tsub_cancel_right, h1]
  simp only [bridgePath, midPt, NNReal.coe_add]
  push_cast at h2c ⊢
  linear_combination (w - z) * h2c

/-- Pathwise splitting of the "stays in `A`" event at time `t`. -/
lemma bridgeEvent_split {t s : ℝ≥0} (ht : t ≠ 0) (hs : s ≠ 0) (A : Set ℂ) (z w : ℂ)
    (β : ℝ≥0 → Ω → ℂ) (ω : Ω) :
    ω ∈ bridgeEvent A (t + s) z w β ↔
      ω ∈ bridgeEvent A t z (midPt t s z w + β t ω) (bridgeOf t β) ∧
        ω ∈ bridgeEvent A s (midPt t s z w + β t ω) w (bridgeTail (t + s) s β) := by
  simp only [bridgeEvent, Set.mem_ofPred_eq, bridgePath_head ht]
  constructor
  · intro h
    refine ⟨fun a ha ↦ h a (ha.trans le_self_add), fun r hr ↦ ?_⟩
    rw [bridgePath_tail ht hs z w β hr]
    exact h _ (add_le_add_right hr t)
  · rintro ⟨h1, h2⟩ u hu
    rcases le_total u t with hut | htu
    · exact h1 u hut
    · have hr : u - t ≤ s := by
        rw [tsub_le_iff_left]
        exact hu
      have := h2 (u - t) hr
      rwa [bridgePath_tail ht hs z w β hr, add_tsub_cancel_of_le htu] at this

lemma sq_norm_complex' (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- Gaussian identity behind Chapman–Kolmogorov for the bridge formula. -/
lemma heatKernel_mul_heatKernel_mid {t s : ℝ≥0} (ht : t ≠ 0) (hs : s ≠ 0) (z w y : ℂ) :
    heatKernel ((t + s : ℝ≥0) : ℝ) z w * heatKernel ((t * s / (t + s) : ℝ≥0) : ℝ) (midPt t s z w) y =
      heatKernel t z y * heatKernel s y w := by
  have ht0 : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hs0 : (0 : ℝ) < s := lt_of_le_of_ne (NNReal.coe_nonneg s) (Ne.symm (by exact_mod_cast hs))
  unfold heatKernel midPt
  rw [mul_mul_mul_comm, ← Real.exp_add, mul_mul_mul_comm (2 * Real.pi * t)⁻¹, ← Real.exp_add]
  congr 1
  · push_cast
    field_simp
  · congr 1
    simp only [sq_norm_complex', Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    push_cast
    field_simp
    ring

end KilledHeat
end LQGMetric
