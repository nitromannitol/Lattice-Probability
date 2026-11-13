/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.L1SquareDynkin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1ResolventSeparation
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1SemigroupTimeIntegral

/-!
# Pointwise L1 Dynkin evolution for a squared vertex potential

The weak square Dynkin identity is upgraded here to a pointwise identity in
speed `L¹`.  No `L²` membership is imposed on the square-generator.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace NNReal
open MeasureTheory Set

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V] [Nontrivial V]

theorem integrable_vertexSpeedMeasure_of_summable_speed_mul
    (m : V → ℝ) (hm : ∀ x, 0 < m x) (f : V → ℝ)
    (hf : Summable (fun x ↦ m x * f x)) :
    Integrable f (vertexSpeedMeasure m) := by
  change Integrable f
    (Measure.sum (fun x ↦ ENNReal.ofReal (m x) • Measure.dirac x))
  apply integrable_sum_dirac (fun x ↦ ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (hm _).le, norm_mul,
    Real.norm_of_nonneg (hm _).le] using hf.norm

private theorem integral_vertexSpeedMeasure_eq_tsum
    (m : V → ℝ) (hm : ∀ x, 0 < m x) (f : V → ℝ)
    (hf : Integrable f (vertexSpeedMeasure m)) :
    (∫ x, f x ∂vertexSpeedMeasure m) = ∑' x, m x * f x := by
  rw [integral_countable hf]
  apply tsum_congr
  intro x
  simp only [measureReal_def, vertexSpeedMeasure_singleton,
    ENNReal.toReal_ofReal (hm x).le, smul_eq_mul]

private theorem integrable_mul_of_bounded_left
    (m : V → ℝ) (v f : V → ℝ) (hf : Integrable f (vertexSpeedMeasure m))
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ x, ‖v x‖ ≤ C) :
    Integrable (fun x ↦ v x * f x) (vertexSpeedMeasure m) := by
  apply Integrable.mono (hf.norm.const_mul C)
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with x
  simp only [norm_mul, norm_norm, Real.norm_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hv x) (norm_nonneg (f x))

/-- Resolvent-tested weak Dynkin identities determine the pointwise
speed-`L¹` semigroup evolution. -/
theorem l1_dynkin_of_vertexResolvent_weak_dynkin
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (wFun g : V → ℝ)
    (hwL2 : HasSpeedL2 m wFun)
    (hw : Integrable wFun (vertexSpeedMeasure m))
    (hg : Integrable g (vertexSpeedMeasure m))
    (hweak : ∀ {beta : ℝ}, 0 < beta → ∀ (s : ℝ≥0) (a : V),
      ⟪vertexOccupationPotentialValue G m beta a,
        fullFormSemigroup G m s (weightedValue m wFun hwL2) -
          weightedValue m wFun hwL2⟫_ℝ =
        ∫ r : ℝ in (0 : ℝ)..(s : ℝ),
          ∑' z : V, m z * g z *
            unweight m (fullFormSemigroup G m (Real.toNNReal r)
              (vertexOccupationPotentialValue G m beta a)) z)
    (t : ℝ≥0) (x : V) :
    weightedL1SemigroupAction G m hm hmsum t wFun x - wFun x =
      weightedL1SemigroupTimeIntegral G m hm hmsum t g x := by
  classical
  let w : ValueSpace V := weightedValue m wFun hwL2
  have hPt := integrable_weightedL1SemigroupAction
    G m hm hmsum t wFun hw
  have htime := integrable_weightedL1SemigroupTimeIntegral
    h hG hm hmsum hg t
  let f : V → ℝ := fun z ↦
    weightedL1SemigroupAction G m hm hmsum t wFun z - wFun z -
      weightedL1SemigroupTimeIntegral G m hm hmsum t g z
  have hf : Integrable f (vertexSpeedMeasure m) := (hPt.sub hw).sub htime
  have hzero : ∀ (beta : ℝ), 0 < beta → ∀ a : V,
      (∫ z, f z * vertexOccupationPotential G m beta z a
        ∂vertexSpeedMeasure m) = 0 := by
    intro beta hb a
    let q : V → ℝ := (vertexOccupationPotential G m beta · a)
    let hqL2 : HasSpeedL2 m q := hasSpeedL2_of_abs_le hm hmsum (fun z ↦ by
      rw [abs_of_nonneg (vertexOccupationPotential_nonneg G m hm hb z a)]
      exact vertexOccupationPotential_le_inv G m hm hb z a)
    let vValue : ValueSpace V := vertexOccupationPotentialValue G m beta a
    have hqBound (z : V) : ‖q z‖ ≤ 1 / beta := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (vertexOccupationPotential_nonneg G m hm hb z a)]
      exact vertexOccupationPotential_le_inv G m hm hb z a
    have hqPt : Integrable (fun z ↦ q z *
        weightedL1SemigroupAction G m hm hmsum t wFun z)
        (vertexSpeedMeasure m) :=
      integrable_mul_of_bounded_left m q _ hPt (1 / beta)
        (one_div_nonneg.mpr hb.le) hqBound
    have hqw : Integrable (fun z ↦ q z * wFun z)
        (vertexSpeedMeasure m) :=
      integrable_mul_of_bounded_left m q _ hw (1 / beta)
        (one_div_nonneg.mpr hb.le) hqBound
    have hqtime : Integrable (fun z ↦ q z *
        weightedL1SemigroupTimeIntegral G m hm hmsum t g z)
        (vertexSpeedMeasure m) :=
      integrable_mul_of_bounded_left m q _ htime (1 / beta)
        (one_div_nonneg.mpr hb.le) hqBound
    have hwq : weightedValue m q hqL2 = vValue := by
      calc
        weightedValue m q hqL2 =
            weightedValue m (unweight m vValue)
              (hasSpeedL2_unweight m hm vValue) := by
          apply Subtype.ext
          funext z
          simp only [weightedValue_apply, q]
          rw [unweight_vertexOccupationPotentialValue G m hb z a]
        _ = vValue := weightedValue_unweight m hm vValue
    let pt : V → ℝ := unweight m (fullFormSemigroup G m t w)
    let hptL2 : HasSpeedL2 m pt := hasSpeedL2_unweight m hm _
    have hwpt : weightedValue m pt hptL2 = fullFormSemigroup G m t w :=
      weightedValue_unweight m hm _
    have hPtPoint : weightedL1SemigroupAction G m hm hmsum t wFun = pt := by
      funext z
      unfold weightedL1SemigroupAction
      rw [show wFun = unweight m w by
        exact (unweight_weightedValue m hm wFun hwL2).symm]
      exact integral_unweight_semigroupProbabilityKernel G m hm hmsum t z w
    have hleft : (∫ z, q z *
        (weightedL1SemigroupAction G m hm hmsum t wFun z - wFun z)
          ∂vertexSpeedMeasure m) =
        ⟪vValue, fullFormSemigroup G m t w - w⟫_ℝ := by
      simp_rw [mul_sub]
      rw [integral_sub hqPt hqw, inner_sub_right, ← hwq, ← hwpt]
      rw [inner_weightedValue_eq_tsum m hm q pt hqL2 hptL2,
        inner_weightedValue_eq_tsum m hm q wFun hqL2 hwL2]
      rw [integral_vertexSpeedMeasure_eq_tsum m hm _ hqPt,
        integral_vertexSpeedMeasure_eq_tsum m hm _ hqw]
      simp only [hPtPoint]
      congr 1 <;> apply tsum_congr <;> intro z <;> ring
    have htimePair : (∫ z, q z *
        weightedL1SemigroupTimeIntegral G m hm hmsum t g z
          ∂vertexSpeedMeasure m) =
        ∫ r in Icc 0 (t : ℝ), ∫ z, g z *
          unweight m (fullFormSemigroup G m (Real.toNNReal r) vValue) z
            ∂vertexSpeedMeasure m := by
      rw [integral_mul_weightedL1SemigroupTimeIntegral
        h hG hm hmsum hg t q (1 / beta) (one_div_nonneg.mpr hb.le) hqBound]
      apply integral_congr_ae
      filter_upwards with r
      rw [integral_mul_weightedL1SemigroupAction_comm
        G m hm hmsum (Real.toNNReal r) g q hg
          (1 / beta) (one_div_nonneg.mpr hb.le) hqBound]
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      unfold weightedL1SemigroupAction
      rw [show q = unweight m vValue by
        rw [← hwq, unweight_weightedValue m hm]]
      exact integral_unweight_semigroupProbabilityKernel G m hm hmsum
        (Real.toNNReal r) z vValue
    have hweak' : ⟪vValue, fullFormSemigroup G m t w - w⟫_ℝ =
        ∫ r in Icc 0 (t : ℝ), ∫ z, g z *
          unweight m (fullFormSemigroup G m (Real.toNNReal r) vValue) z
            ∂vertexSpeedMeasure m := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) by positivity)]
      rw [hweak hb t a]
      apply intervalIntegral.integral_congr
      intro r _
      change (∑' z : V, m z * g z *
          unweight m (fullFormSemigroup G m (Real.toNNReal r) vValue) z) =
        ∫ z, g z * unweight m
          (fullFormSemigroup G m (Real.toNNReal r) vValue) z
            ∂vertexSpeedMeasure m
      rw [integral_vertexSpeedMeasure_eq_tsum m hm _]
      · apply tsum_congr
        intro z
        ring
      · simpa only [mul_comm] using integrable_mul_of_bounded_left m
          (fun z ↦ unweight m
            (fullFormSemigroup G m (Real.toNNReal r) vValue) z) g hg
          (1 / beta) (one_div_nonneg.mpr hb.le) (fun z ↦ by
            rw [← integral_unweight_semigroupProbabilityKernel
              G m hm hmsum (Real.toNNReal r) z vValue]
            have hbound : ∀ qz : V, ‖unweight m vValue qz‖ ≤ 1 / beta := by
              intro qz
              rw [unweight_vertexOccupationPotentialValue G m hb qz a,
                Real.norm_eq_abs,
                abs_of_nonneg (vertexOccupationPotential_nonneg G m hm hb qz a)]
              exact vertexOccupationPotential_le_inv G m hm hb qz a
            simpa using norm_integral_le_of_norm_le_const
              (μ := semigroupProbabilityKernel G m hm hmsum
                (Real.toNNReal r) z) (ae_of_all _ hbound))
    rw [show f = fun z ↦
        (weightedL1SemigroupAction G m hm hmsum t wFun z - wFun z) -
          weightedL1SemigroupTimeIntegral G m hm hmsum t g z by rfl]
    rw [show (fun z ↦ ((weightedL1SemigroupAction G m hm hmsum t wFun z -
        wFun z) - weightedL1SemigroupTimeIntegral G m hm hmsum t g z) * q z) =
        fun z ↦ q z * (weightedL1SemigroupAction G m hm hmsum t wFun z - wFun z) -
          q z * weightedL1SemigroupTimeIntegral G m hm hmsum t g z by
      funext z; ring]
    rw [integral_sub]
    · rw [hleft, htimePair, hweak', sub_self]
    · exact integrable_mul_of_bounded_left m q _ (hPt.sub hw)
        (1 / beta) (one_div_nonneg.mpr hb.le) hqBound
    · exact hqtime
  have hfzero := eq_zero_of_integral_mul_vertexOccupationPotential_eq_zero
    G m hm f hf hzero
  have hx := congrFun hfzero x
  change weightedL1SemigroupAction G m hm hmsum t wFun x - wFun x -
    weightedL1SemigroupTimeIntegral G m hm hmsum t g x = 0 at hx
  exact sub_eq_zero.mp hx

end ReflectedGMS
