/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatMeas
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Killed heat kernel, part 17: Brownian scaling and log-convexity in time
(task P2-DZZPRE2; open item 2 of `handoff/P2-KILLED.md`; decision D62 route (1))

* `bridgeStay_scale`, `killedHeat_scale`: Brownian scaling
  `q_A(t; z, w) = q_{t^{-1/2} A}(1; t^{-1/2} z, t^{-1/2} w)` and
  `p_A(t; z, w) = t⁻¹ p_{t^{-1/2} A}(1; t^{-1/2} z, t^{-1/2} w)`, from `IsPlanarBridge.scale`.
* `bridgeStay_ball_scale`: `q_{B(0,ρ)}(t; 0, 0) = q_{B(0, ρ/√t)}(1; 0, 0)`.
* `nullMeasurableSet_bridgeEvent`.
* `killedHeat_sq_le`: `p_A(a + b; z, z)² ≤ p_A(2a; z, z) p_A(2b; z, z)` (Chapman–Kolmogorov
  `ofReal_killedHeat_add`, symmetry, Cauchy–Schwarz `ENNReal.lintegral_mul_le_Lp_mul_Lq`):
  `t ↦ p_A(t; z, z)` is log-convex (midpoint form). Standard (e.g. it is the Laplace transform
  `Σ e^{−λ_k t} φ_k(z)²`); the Chapman–Kolmogorov + Cauchy–Schwarz derivation is an own
  elementary argument (D62 route (1)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Pointwise

namespace LQGMetric
namespace KilledHeat

/-- **Brownian scaling** of the bridge probability: with `c = √t`,
`q_A(t; z, w) = q_{c⁻¹ A}(1; c⁻¹ z, c⁻¹ w)`. -/
theorem bridgeStay_scale {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0) (z w : ℂ) :
    bridgeStay A t z w = bridgeStay (((Real.sqrt t : ℝ) : ℂ)⁻¹ • A) 1
      (((Real.sqrt t : ℝ) : ℂ)⁻¹ * z) (((Real.sqrt t : ℝ) : ℂ)⁻¹ * w) := by
  have h1 := isPlanarBridge_stdBridge (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  set c : ℂ := ((Real.sqrt t : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.sqrt_pos.mpr ht').ne'
  rw [← bridgeStay_eq_of_isPlanarBridge hA ht (h1.scale ht) z w, bridgeEvent_scaleBr ht]
  unfold bridgeStay
  congr 2
  ext ω
  simp only [bridgeEvent, Set.mem_ofPred_eq]
  refine forall₂_congr fun s _ ↦ ?_
  rw [Set.mem_inv_smul_set_iff₀ hc0]
  have e : c • bridgePath 1 (c⁻¹ * z) (c⁻¹ * w) (stdBridge 1) s ω =
      bridgePath 1 z w (fun u ω ↦ c * stdBridge 1 u ω) s ω := by
    simp only [bridgePath, smul_eq_mul]
    field_simp
  rw [e]

/-- Scaling for centred balls: `q_{B(0,ρ)}(t; 0, 0) = q_{B(0,ρ/√t)}(1; 0, 0)`. -/
theorem bridgeStay_ball_scale {t : ℝ≥0} (ht : t ≠ 0) (ρ : ℝ) :
    bridgeStay (Metric.ball 0 ρ) t 0 0 = bridgeStay (Metric.ball 0 (ρ / Real.sqrt t)) 1 0 0 := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hs := Real.sqrt_pos.mpr ht'
  rw [bridgeStay_scale Metric.isOpen_ball ht, mul_zero]
  congr 1
  ext x
  have hc0 : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Set.mem_inv_smul_set_iff₀ hc0, Metric.mem_ball, Metric.mem_ball, dist_zero_right,
    dist_zero_right, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, lt_div_iff₀ hs, mul_comm]

/-- Bridge events of open sets are null-measurable. -/
theorem nullMeasurableSet_bridgeEvent {Ω : Type*} {mΩ : MeasurableSpace Ω} {t : ℝ≥0}
    {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω} (hX : IsPlanarBridge t X P) {A : Set ℂ} (hA : IsOpen A)
    (z w : ℂ) : NullMeasurableSet (bridgeEvent A t z w X) P := by
  have hm : AEMeasurable (fun ω p ↦ sampled t X p ω) P :=
    .of_eval fun p ↦ (sampled_isGaussianProcess hX).aemeasurable p
  refine (hm.nullMeasurable (measurableSet_cEvent A t z w)).congr ?_
  filter_upwards [hX.cont] with ω hω
  exact propext (mem_bridgeEvent_iff A hA t z w X hω).symm

/-- **Log-convexity in time** (midpoint form):
`p_A(a + b; z, z)² ≤ p_A(a + a; z, z) · p_A(b + b; z, z)`. -/
theorem killedHeat_sq_le {A : Set ℂ} (hA : IsOpen A) {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (z : ℂ) :
    killedHeat A (a + b) z z ^ 2 ≤ killedHeat A (a + a) z z * killedHeat A (b + b) z z := by
  set F : ℂ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (killedHeat A a z y)
  set G : ℂ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (killedHeat A b y z)
  have hF : AEMeasurable F := (measurable_killedHeat_right hA ha z).ennreal_ofReal.aemeasurable
  have hG : AEMeasurable G := (measurable_killedHeat_left hA hb z).ennreal_ofReal.aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hF hG
  have hFF : ∫⁻ y, F y ^ (2 : ℝ) = ENNReal.ofReal (killedHeat A (a + a) z z) := by
    rw [ofReal_killedHeat_add hA ha ha]
    refine lintegral_congr fun y ↦ ?_
    simp only [F, ENNReal.rpow_two, sq]
    rw [killedHeat_symm hA a y z]
  have hGG : ∫⁻ y, G y ^ (2 : ℝ) = ENNReal.ofReal (killedHeat A (b + b) z z) := by
    rw [ofReal_killedHeat_add hA hb hb]
    refine lintegral_congr fun y ↦ ?_
    simp only [G, ENNReal.rpow_two, sq]
    rw [killedHeat_symm hA b z y]
  have hFG : ∫⁻ y, (F * G) y = ENNReal.ofReal (killedHeat A (a + b) z z) :=
    (ofReal_killedHeat_add hA ha hb z z).symm
  rw [hFF, hGG, hFG] at hH
  set x := ENNReal.ofReal (killedHeat A (a + a) z z)
  set y := ENNReal.ofReal (killedHeat A (b + b) z z)
  have h2 := pow_le_pow_left₀ zero_le hH 2
  have e : (x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) ^ 2 = x * y := by
    rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    norm_num
  rw [e, ← ENNReal.ofReal_pow (killedHeat_nonneg _ _ _ _),
    ← ENNReal.ofReal_mul (killedHeat_nonneg _ _ _ _)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _))).mp h2

/-- Real-time form: for `p, q > 0`, `K((p+q)/2)² ≤ K(p) K(q)` with `K x = p_A(x; z, z)`. -/
theorem killedHeat_sq_le_real {A : Set ℂ} (hA : IsOpen A) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (z : ℂ) :
    killedHeat A ((p + q) / 2).toNNReal z z ^ 2 ≤
      killedHeat A p.toNNReal z z * killedHeat A q.toNNReal z z := by
  have ha : (p / 2).toNNReal ≠ 0 := by simpa using (by linarith : 0 < p / 2)
  have hb : (q / 2).toNNReal ≠ 0 := by simpa using (by linarith : 0 < q / 2)
  have h := killedHeat_sq_le hA ha hb z
  rw [← Real.toNNReal_add (by linarith) (by linarith), ← Real.toNNReal_add (by linarith)
    (by linarith), ← Real.toNNReal_add (by linarith) (by linarith)] at h
  rw [show (p + q) / 2 = p / 2 + q / 2 by ring]
  rwa [show p / 2 + p / 2 = p by ring, show q / 2 + q / 2 = q by ring] at h

end KilledHeat
end LQGMetric
