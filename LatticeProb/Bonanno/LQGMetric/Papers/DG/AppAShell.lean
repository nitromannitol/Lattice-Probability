/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppAShell at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel

/-!
# Ding–Gwynne App. A: the integrated shell estimate for a change of domain (task P2-DG3B)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma A.1 (DG:2207–2216):
moving the centre of the killing ball `B_{1/10}(z)` by `ε` changes the killed kernel only on the
event that the bridge "exits `B_{1/10}(z)` without exiting `B_{1/10+4ε}(z)`", whose probability
DG bound by `O(ε)` "uniformly over `w`". That pointwise claim fails for `w` near the circle
(handoff/P2-DG3A.md); only an integrated form is true. This file proves the integrated form in
the shape needed for `Var((ĥ − ĥ^tr)(z₁) − (ĥ − ĥ^tr)(z₂)) ≲ |z₁ − z₂|`:

* `integral_sq_killedHeat_sub_le` — for open `A₁ ⊆ A₂`,
  `∫ (p_{A₂}(τ; x, w) − p_{A₁}(τ; x, w))² dw ≤ p_{A₂}(2τ; x, x) − p_{A₁}(2τ; x, x)`
  (Chapman–Kolmogorov `integral_killedHeat_mul_killedHeat` and `p_{A₁} ≤ p_{A₂}`);
* `killedHeat_ball_diag` — `p_{B(c,ρ)}(s; c, c) = ρ⁻² K(s/ρ²)`, `K = DZZ.unitDiscK`
  (translation + Brownian scaling, `bridgeStay_ball_eq_unitDiscG`);
* `integral_killedHeat_ball_diag_sub_le` — for `0 < ρ₁ ≤ ρ₂`, `0 < a ≤ b`,
  `∫_a^b (p_{B(c,ρ₂)}(s; c, c) − p_{B(c,ρ₁)}(s; c, c)) ds ≤ π⁻¹ log(ρ₂/ρ₁)`.

The last bound is an own argument (DEVIATIONS: DG3B-1): after the substitution `u = s/ρᵢ²` the
two integrals are `∫ K` over `[a/ρ₂², b/ρ₂²]` and `[a/ρ₁², b/ρ₁²]`; their difference is
`∫_{a/ρ₂²}^{a/ρ₁²} K − ∫_{b/ρ₂²}^{b/ρ₁²} K ≤ ∫_{a/ρ₂²}^{a/ρ₁²} (2πu)⁻¹ du = π⁻¹ log(ρ₂/ρ₁)`,
using only `0 ≤ K(u) ≤ (2πu)⁻¹`. (This is the time-integrated version of the Green-function
identity `G_{B(0,ρ₂)} − G_{B(0,ρ₁)} = π⁻¹ log(ρ₂/ρ₁)`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace LQGMetric
namespace DG

open KilledHeat

/-! ### Translation -/

/-- Translation: `q_{B(c,ρ)}(t; c, w) = q_{B(0,ρ)}(t; 0, w − c)`. -/
theorem bridgeStay_ball_translate (t : ℝ≥0) (c w : ℂ) (ρ : ℝ) :
    bridgeStay (Metric.ball c ρ) t c w = bridgeStay (Metric.ball 0 ρ) t 0 (w - c) := by
  unfold bridgeStay
  congr 2
  ext ω
  simp only [bridgeEvent, bridgePath, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
  refine forall₂_congr fun s _ => ?_
  rw [show c + (((s : ℝ) / t : ℝ) : ℂ) * (w - c) + stdBridge t s ω - c =
    0 + (((s : ℝ) / t : ℝ) : ℂ) * (w - c - 0) + stdBridge t s ω - 0 by ring]

/-- The centred diagonal killed kernel of a ball: `p_{B(c,ρ)}(s; c, c) = ρ⁻² K(s/ρ²)`. -/
theorem killedHeat_ball_diag {s : ℝ} (hs : 0 < s) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    killedHeat (Metric.ball c ρ) s.toNNReal c c = (ρ ^ 2)⁻¹ * DZZ.unitDiscK (s / ρ ^ 2) := by
  have hs' : s.toNNReal ≠ 0 := by simpa using hs
  have hx : 0 < s / ρ ^ 2 := by positivity
  rw [killedHeat, bridgeStay_ball_translate, sub_self,
    DZZ.bridgeStay_ball_eq_unitDiscG hs' hρ, DZZ.unitDiscG_eq (by rwa [Real.coe_toNNReal _ hs.le]),
    Real.coe_toNNReal _ hs.le]
  unfold heatKernel
  simp only [sub_self, norm_zero]
  have := Real.pi_pos
  field_simp
  simp

/-! ### The integrated shell estimate -/

lemma measurable_unitDiscK : Measurable DZZ.unitDiscK := by
  have h := measurable_killedHeat (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1))
  exact h.comp (measurable_real_toNNReal.prodMk (measurable_const.prodMk measurable_const))

lemma intervalIntegrable_unitDiscK {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntervalIntegrable DZZ.unitDiscK volume α β := by
  have key : ∀ {a b : ℝ}, 0 < a → a ≤ b → IntervalIntegrable DZZ.unitDiscK volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      measurable_unitDiscK.aestronglyMeasurable (2 * Real.pi * a)⁻¹ ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
    have hx0 : 0 < x := ha.trans hx.1
    rw [Real.norm_of_nonneg (DZZ.unitDiscK_nonneg x)]
    refine (DZZ.unitDiscK_le_inv hx0).trans ?_
    have := Real.pi_pos
    exact inv_anti₀ (by positivity) (by nlinarith [hx.1])
  rcases le_total α β with h | h
  · exact key hα h
  · exact (key hβ h).symm

lemma intervalIntegrable_unitDiscK_scale {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun s => (ρ ^ 2)⁻¹ * DZZ.unitDiscK (s / ρ ^ 2)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    ((measurable_const.mul (measurable_unitDiscK.comp
      (measurable_id.div_const _)))).aestronglyMeasurable
    ((ρ ^ 2)⁻¹ * (2 * Real.pi * (a / ρ ^ 2))⁻¹) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
  have hx0 : 0 < x / ρ ^ 2 := div_pos (ha.trans hx.1) (by positivity)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (DZZ.unitDiscK_nonneg _))]
  refine mul_le_mul_of_nonneg_left ((DZZ.unitDiscK_le_inv hx0).trans ?_) (by positivity)
  have := Real.pi_pos
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hx.1.le (by positivity)) (by positivity))

/-- `∫_a^b ρ⁻² K(s/ρ²) ds = ∫_{a/ρ²}^{b/ρ²} K`. -/
lemma integral_unitDiscK_scale (a b : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ s in a..b, (ρ ^ 2)⁻¹ * DZZ.unitDiscK (s / ρ ^ 2) =
      ∫ u in a / ρ ^ 2..b / ρ ^ 2, DZZ.unitDiscK u := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (f := DZZ.unitDiscK) (by positivity : ρ ^ 2 ≠ 0),
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- **Integrated shell estimate** (own argument, DG3B-1): for `0 < ρ₁ ≤ ρ₂` and `0 < a ≤ b`,
`∫_a^b (p_{B(c,ρ₂)}(s; c, c) − p_{B(c,ρ₁)}(s; c, c)) ds ≤ π⁻¹ log(ρ₂/ρ₁)`. -/
theorem integral_killedHeat_ball_diag_sub_le (c : ℂ) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ : ρ₁ ≤ ρ₂) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ s in a..b, (killedHeat (Metric.ball c ρ₂) s.toNNReal c c -
      killedHeat (Metric.ball c ρ₁) s.toNNReal c c) ≤ Real.log (ρ₂ / ρ₁) / Real.pi := by
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le hρ
  have hpi := Real.pi_pos
  have e : ∀ s ∈ uIcc a b, killedHeat (Metric.ball c ρ₂) s.toNNReal c c -
      killedHeat (Metric.ball c ρ₁) s.toNNReal c c =
      (ρ₂ ^ 2)⁻¹ * DZZ.unitDiscK (s / ρ₂ ^ 2) - (ρ₁ ^ 2)⁻¹ * DZZ.unitDiscK (s / ρ₁ ^ 2) := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le (by rw [uIcc_of_le hab] at hs; exact hs.1)
    rw [killedHeat_ball_diag hs0 c hρ₂, killedHeat_ball_diag hs0 c hρ₁]
  set a₁ := a / ρ₁ ^ 2
  set a₂ := a / ρ₂ ^ 2
  set b₁ := b / ρ₁ ^ 2
  set b₂ := b / ρ₂ ^ 2
  have ha₁ : 0 < a₁ := div_pos ha (pow_pos hρ₁ 2)
  have ha₂ : 0 < a₂ := div_pos ha (pow_pos hρ₂ 2)
  have hb₁ : 0 < b₁ := div_pos (ha.trans_le hab) (pow_pos hρ₁ 2)
  have hb₂ : 0 < b₂ := div_pos (ha.trans_le hab) (pow_pos hρ₂ 2)
  have hsq : ρ₁ ^ 2 ≤ ρ₂ ^ 2 := pow_le_pow_left₀ hρ₁.le hρ 2
  have ha12 : a₂ ≤ a₁ := div_le_div_of_nonneg_left ha.le (by positivity) hsq
  have hb12 : b₂ ≤ b₁ := div_le_div_of_nonneg_left (ha.le.trans hab) (by positivity) hsq
  have hI : ∀ {x y : ℝ}, 0 < x → 0 < y → IntervalIntegrable DZZ.unitDiscK volume x y :=
    fun hx hy => intervalIntegrable_unitDiscK hx hy
  have hsc : ∀ ρ : ℝ, 0 < ρ →
      IntervalIntegrable (fun s => (ρ ^ 2)⁻¹ * DZZ.unitDiscK (s / ρ ^ 2)) volume a b :=
    fun ρ hρ0 => intervalIntegrable_unitDiscK_scale hρ0 ha hab
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub (hsc ρ₂ hρ₂) (hsc ρ₁ hρ₁),
    integral_unitDiscK_scale a b hρ₂, integral_unitDiscK_scale a b hρ₁]
  -- `∫_{a₂}^{b₂} K − ∫_{a₁}^{b₁} K = ∫_{a₂}^{a₁} K − ∫_{b₂}^{b₁} K`
  have hsplit : (∫ u in a₂..b₂, DZZ.unitDiscK u) - ∫ u in a₁..b₁, DZZ.unitDiscK u =
      (∫ u in a₂..a₁, DZZ.unitDiscK u) - ∫ u in b₂..b₁, DZZ.unitDiscK u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI ha₂ ha₁) (hI ha₁ hb₂),
      ← intervalIntegral.integral_add_adjacent_intervals (hI ha₁ hb₂) (hI hb₂ hb₁)]
    ring
  rw [hsplit]
  have hnn : 0 ≤ ∫ u in b₂..b₁, DZZ.unitDiscK u :=
    intervalIntegral.integral_nonneg hb12 fun u _ => DZZ.unitDiscK_nonneg u
  have hle : ∫ u in a₂..a₁, DZZ.unitDiscK u ≤ ∫ u in a₂..a₁, (2 * Real.pi)⁻¹ * u⁻¹ := by
    refine intervalIntegral.integral_mono_on ha12 (hI ha₂ ha₁) ?_ fun u hu => ?_
    · exact (intervalIntegral.intervalIntegrable_inv (fun x hx => by
        rw [uIcc_of_le ha12] at hx; exact (ha₂.trans_le hx.1).ne') (continuousOn_id)).const_mul _
    · have hu0 : 0 < u := ha₂.trans_le hu.1
      refine (DZZ.unitDiscK_le_inv hu0).trans (le_of_eq ?_)
      rw [mul_inv]
  have hval : ∫ u in a₂..a₁, (2 * Real.pi)⁻¹ * u⁻¹ = Real.log (ρ₂ / ρ₁) / Real.pi := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha₂ ha₁]
    have : a₁ / a₂ = (ρ₂ / ρ₁) ^ 2 := by
      simp only [a₁, a₂]
      field_simp
    rw [this, Real.log_pow]
    field_simp
    push_cast
    ring
  linarith

lemma integrable_killedHeat_mul {A A' : Set ℂ} (hA : IsOpen A) (hA' : IsOpen A') {τ : ℝ≥0}
    (hτ : τ ≠ 0) (x : ℂ) :
    Integrable (fun w => killedHeat A τ x w * killedHeat A' τ x w) := by
  have hτ' : (0 : ℝ) < τ := lt_of_le_of_ne (NNReal.coe_nonneg τ) (Ne.symm (by exact_mod_cast hτ))
  refine (WhiteNoise.integrable_heatKernel_mul_heatKernel (τ : ℝ) hτ' x x).mono'
    ((measurable_killedHeat_right hA hτ x).mul
      (measurable_killedHeat_right hA' hτ x)).aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _))]
  exact mul_le_mul (killedHeat_le_heatKernel _ _ _ _) (killedHeat_le_heatKernel _ _ _ _)
    (killedHeat_nonneg _ _ _ _) (heatKernel_nonneg' _ _ _)

/-- **Change of domain in `L²`**: for open `A₁ ⊆ A₂` and `τ > 0`,
`∫ (p_{A₂}(τ; x, w) − p_{A₁}(τ; x, w))² dw ≤ p_{A₂}(2τ; x, x) − p_{A₁}(2τ; x, x)`. -/
theorem integral_sq_killedHeat_sub_le {A₁ A₂ : Set ℂ} (hA₁ : IsOpen A₁) (hA₂ : IsOpen A₂)
    (h12 : A₁ ⊆ A₂) {τ : ℝ≥0} (hτ : τ ≠ 0) (x : ℂ) :
    ∫ w, (killedHeat A₂ τ x w - killedHeat A₁ τ x w) ^ 2 ≤
      killedHeat A₂ (τ + τ) x x - killedHeat A₁ (τ + τ) x x := by
  have hint : ∀ {A A' : Set ℂ}, IsOpen A → IsOpen A' →
      Integrable (fun w => killedHeat A τ x w * killedHeat A' τ x w) :=
    fun hA hA' => integrable_killedHeat_mul hA hA' hτ x
  have e : (fun w => (killedHeat A₂ τ x w - killedHeat A₁ τ x w) ^ 2) = fun w =>
      (killedHeat A₂ τ x w * killedHeat A₂ τ x w - killedHeat A₂ τ x w * killedHeat A₁ τ x w) -
      (killedHeat A₂ τ x w * killedHeat A₁ τ x w - killedHeat A₁ τ x w * killedHeat A₁ τ x w) := by
    funext w; ring
  have h22 := hint hA₂ hA₂
  have h21 := hint hA₂ hA₁
  have h11 := hint hA₁ hA₁
  have hs1 := integral_sub (h22.sub h21) (h21.sub h11)
  have hs2 := integral_sub h22 h21
  have hs3 := integral_sub h21 h11
  simp only [Pi.sub_apply] at hs1 hs2 hs3
  rw [e, hs1, hs2, hs3,
    integral_killedHeat_mul_killedHeat hA₂ hτ x x, integral_killedHeat_mul_killedHeat hA₁ hτ x x]
  have hmono : ∫ w, killedHeat A₁ τ x w * killedHeat A₁ τ x w ≤
      ∫ w, killedHeat A₂ τ x w * killedHeat A₁ τ x w := by
    refine integral_mono h11 h21 fun w => ?_
    exact mul_le_mul_of_nonneg_right (killedHeat_mono h12 _ _ _) (killedHeat_nonneg _ _ _ _)
  rw [integral_killedHeat_mul_killedHeat hA₁ hτ x x] at hmono
  linarith

/-- **Recentring the killing ball** (the integrated form of DG:2207–2216): if `‖z₁ − z₂‖ ≤ δ < r`,
then `∫ (p_{B(z₁,r)}(τ; z₂, w) − p_{B(z₂,r)}(τ; z₂, w))² dw ≤
p_{B(z₂,r+δ)}(2τ; z₂, z₂) − p_{B(z₂,r−δ)}(2τ; z₂, z₂)`: both kernels lie between
`p_{B(z₂,r−δ)}` and `p_{B(z₂,r+δ)}`. -/
theorem integral_sq_recentre_le {r δ : ℝ} {z₁ z₂ : ℂ} (hz : ‖z₁ - z₂‖ ≤ δ)
    {τ : ℝ≥0} (hτ : τ ≠ 0) :
    ∫ w, (killedHeat (Metric.ball z₁ r) τ z₂ w - killedHeat (Metric.ball z₂ r) τ z₂ w) ^ 2 ≤
      killedHeat (Metric.ball z₂ (r + δ)) (τ + τ) z₂ z₂ -
        killedHeat (Metric.ball z₂ (r - δ)) (τ + τ) z₂ z₂ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hz
  have hdist : dist z₁ z₂ ≤ δ := by rwa [dist_eq_norm]
  have s1 : Metric.ball z₂ (r - δ) ⊆ Metric.ball z₁ r := fun w hw => by
    rw [Metric.mem_ball] at hw ⊢
    linarith [dist_triangle w z₂ z₁, dist_comm z₁ z₂]
  have s2 : Metric.ball z₁ r ⊆ Metric.ball z₂ (r + δ) := fun w hw => by
    rw [Metric.mem_ball] at hw ⊢
    linarith [dist_triangle w z₁ z₂]
  have s3 : Metric.ball z₂ (r - δ) ⊆ Metric.ball z₂ r := Metric.ball_subset_ball (by linarith)
  have s4 : Metric.ball z₂ r ⊆ Metric.ball z₂ (r + δ) := Metric.ball_subset_ball (by linarith)
  set pm := fun w => killedHeat (Metric.ball z₂ (r - δ)) τ z₂ w
  set pp := fun w => killedHeat (Metric.ball z₂ (r + δ)) τ z₂ w
  have hb : ∀ w, (killedHeat (Metric.ball z₁ r) τ z₂ w - killedHeat (Metric.ball z₂ r) τ z₂ w) ^ 2
      ≤ (pp w - pm w) ^ 2 := by
    intro w
    have a1 := killedHeat_mono s1 τ z₂ w
    have a2 := killedHeat_mono s2 τ z₂ w
    have a3 := killedHeat_mono s3 τ z₂ w
    have a4 := killedHeat_mono s4 τ z₂ w
    exact sq_le_sq' (by simp only [pp, pm]; linarith) (by simp only [pp, pm]; linarith)
  have hI : Integrable (fun w => (pp w - pm w) ^ 2) := by
    refine (integrable_killedHeat_mul Metric.isOpen_ball Metric.isOpen_ball hτ z₂
      (A := Metric.ball z₂ (r + δ)) (A' := Metric.ball z₂ (r + δ))).mono'
      (((measurable_killedHeat_right Metric.isOpen_ball hτ z₂).sub
        (measurable_killedHeat_right Metric.isOpen_ball hτ z₂)).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)
    have a := killedHeat_mono s3 τ z₂ w
    have a' := killedHeat_mono s4 τ z₂ w
    have h0 := killedHeat_nonneg (Metric.ball z₂ (r - δ)) τ z₂ w
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    simp only [pp, pm]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (killedHeat_nonneg _ _ _ _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun w => sq_nonneg _) hI
    (ae_of_all _ hb)).trans ?_
  exact integral_sq_killedHeat_sub_le Metric.isOpen_ball Metric.isOpen_ball
    (Metric.ball_subset_ball (by linarith)) hτ z₂

end DG
end LQGMetric
