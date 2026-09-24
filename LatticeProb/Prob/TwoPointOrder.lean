/-
A lower bound in convex order for a near-family of mean-zero integer laws recentred to the
real line (`shiftLaw`, `NearFamily` of `LatticeProb.Prob.NearFamily`), matching a companion
upper bound by a fixed exponential reference law (`LatticeProb.ConvexOrder.convex_integral_le_refLaw`
of `LatticeProb/Prob/ConvexOrder.lean`): there is a symmetric two-point law at `±a₀` and a
horizon `δ₁ > 0` such that every law of the family at parameter `δ ∈ (0, δ₁]` dominates that
two-point law in convex order, tested against every convex Lipschitz function.

`twoPointLaw a` is the law of `a χ` for a symmetric random sign `χ`. The comparison rests on
one elementary fact about a mean-zero law `μ` on the line: if its positive part carries mass
`p = E X⁺ > 0`, then the two-point law at `±a` is below `μ` in convex order for every `a ≤ p/2`.
Writing a convex `f` as `f(0) + βx + h(x)` for a supporting slope `β` at the origin leaves `h`
convex, nonnegative and vanishing at the origin, so `h(x) ≥ (x/a)h(a)` beyond `a` and
`h(x) ≥ (-x/a)h(-a)` below `-a`, while the middle contributes nothing. Both tails still carry
mass at least `a/2` because at most `a` of `p` sits in `(0,a)`, which is where `a ≤ p/2` is
used. The mean-zero property turns the positive mass into the negative mass.

The uniformity in `δ` is the coupling clause of `NearFamily`: the positive mass of the
parameter-`δ` law is within `(K+1)δ` of the positive mass of the base law, because `x ↦ x⁺` is
`1`-Lipschitz, and the positive mass of the base law is positive because it has mean zero and
is not a point mass. So `a₀` is a quarter of that mass and serves every small `δ`.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.NearFamily
import LatticeProb.Prob.ConvexProduct
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace LatticeProb.ConvexOrder

/-- The symmetric two point law at `±a`: the law of `a χ` for a symmetric random sign. -/
def twoPointLaw (a : ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac a + Measure.dirac (-a))

/-- Every function is integrable for the two-point law, which is a finite combination of Dirac
masses. -/
theorem integrable_twoPointLaw (a : ℝ) (f : ℝ → ℝ) : Integrable f (twoPointLaw a) := by
  rw [twoPointLaw]
  exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
    (by simp)

/-- The two-point law is a probability measure. -/
instance isProbabilityMeasure_twoPointLaw (a : ℝ) : IsProbabilityMeasure (twoPointLaw a) := by
  constructor
  rw [twoPointLaw]
  simp only [Measure.smul_apply, Measure.coe_add, Pi.add_apply, measure_univ, smul_eq_mul]
  rw [mul_add, mul_one, ENNReal.inv_two_add_inv_two]

/-- The two-point-law integral of `f` is the average of `f` at `a` and at `-a`. -/
theorem integral_twoPointLaw (a : ℝ) (f : ℝ → ℝ) :
    ∫ z, f z ∂(twoPointLaw a) = (f a + f (-a)) / 2 := by
  rw [twoPointLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  simp
  ring

/-- The two-point law has mean zero. -/
theorem integral_twoPointLaw_id (a : ℝ) : ∫ z, z ∂(twoPointLaw a) = 0 := by
  rw [integral_twoPointLaw a (fun z => z)]
  ring

/-- The second moment of the two-point law is `a²`. -/
theorem integral_twoPointLaw_sq (a : ℝ) : ∫ z, z ^ 2 ∂(twoPointLaw a) = a ^ 2 := by
  rw [integral_twoPointLaw a (fun z => z ^ 2)]
  ring

/-- The two-point law has finite variance. -/
theorem evariance_twoPointLaw_lt_top (a : ℝ) :
    evariance (id : ℝ → ℝ) (twoPointLaw a) < ⊤ :=
  evariance_lt_top ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
    (integrable_twoPointLaw a _))

/-- The two-point law at a nonzero point has strictly positive variance. -/
theorem evariance_twoPointLaw_pos {a : ℝ} (ha : 0 < a) :
    0 < evariance (id : ℝ → ℝ) (twoPointLaw a) := by
  refine pos_iff_ne_zero.mpr fun hz => ?_
  have hae := (evariance_eq_zero_iff (X := (id : ℝ → ℝ)) (μ := twoPointLaw a)
    measurable_id.aemeasurable).mp hz
  rw [show ∫ x, (id x : ℝ) ∂(twoPointLaw a) = 0 from integral_twoPointLaw_id a] at hae
  have heq : (fun x : ℝ => x ^ 2) =ᵐ[twoPointLaw a] fun _ => 0 := by
    filter_upwards [hae] with x hx
    change x = 0 at hx
    simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have h := integral_congr_ae heq
  rw [integral_twoPointLaw_sq, integral_zero] at h
  nlinarith [h]

/-- The two-point law is almost everywhere bounded below by `-|a|`. -/
theorem ae_neg_le_twoPointLaw (a : ℝ) : ∀ᵐ z ∂(twoPointLaw a), -|a| ≤ z := by
  have hs : MeasurableSet {z : ℝ | ¬ (-|a| ≤ z)} := by
    have : {z : ℝ | ¬ (-|a| ≤ z)} = Set.Iio (-|a|) := by
      ext z; simp [Set.mem_Iio, not_le]
    rw [this]; exact measurableSet_Iio
  rw [ae_iff, twoPointLaw, Measure.smul_apply, Measure.coe_add, Pi.add_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs]
  have h1 : a ∉ {z : ℝ | ¬ (-|a| ≤ z)} := by
    simp only [Set.mem_setOf_eq, not_not]
    exact neg_abs_le a
  have h2 : -a ∉ {z : ℝ | ¬ (-|a| ≤ z)} := by
    simp only [Set.mem_setOf_eq, not_not]
    have := le_abs_self a
    linarith
  rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  simp

/-- A convex function vanishing at the origin grows at least linearly beyond `a`. -/
theorem convex_ray_right {h : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ h) (h0 : h 0 = 0)
    {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) : (x / a) * h a ≤ h x := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le ha hx
  have ht0 : (0:ℝ) ≤ a / x := by positivity
  have ht1 : (0:ℝ) ≤ 1 - a / x := by
    rw [sub_nonneg, div_le_one hx0]; linarith
  have key := hc.2 (Set.mem_univ x) (Set.mem_univ (0:ℝ)) ht0 ht1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, h0] at key
  rw [div_mul_cancel₀ a (ne_of_gt hx0)] at key
  have hfin : (x / a) * (a / x * h x) = h x := by field_simp
  nlinarith [key, hfin, div_pos hx0 ha]

/-- A convex function vanishing at the origin grows at least linearly below `-a`. -/
theorem convex_ray_left {h : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ h) (h0 : h 0 = 0)
    {a x : ℝ} (ha : 0 < a) (hx : x ≤ -a) : (-x / a) * h (-a) ≤ h x := by
  have hx0 : x < (0:ℝ) := lt_of_le_of_lt hx (by linarith)
  have ht0 : (0:ℝ) ≤ (-a) / x := by
    rw [div_nonneg_iff]
    exact Or.inr ⟨by linarith, by linarith⟩
  have ht1 : (0:ℝ) ≤ 1 - (-a) / x := by
    rw [sub_nonneg, div_le_one_of_neg hx0]
    linarith
  have key := hc.2 (Set.mem_univ x) (Set.mem_univ (0:ℝ)) ht0 ht1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, h0] at key
  rw [div_mul_cancel₀ (-a) (ne_of_lt hx0)] at key
  have hfin : ((-x) / a) * ((-a) / x * h x) = h x := by
    field_simp
    exact mul_div_cancel_left₀ (h x) (ne_of_lt hx0)
  nlinarith [key, hfin, div_pos (by linarith : (0:ℝ) < -x) ha]

/-- A convex function on the line has a supporting line at the origin. -/
theorem exists_supporting_line {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∃ β : ℝ, ∀ y : ℝ, f 0 + β * y ≤ f y := by
  classical
  set S : Set ℝ := (fun y : ℝ => (f y - f 0) / (y - 0)) '' Set.Iio 0 with hS
  have hne : S.Nonempty := ⟨(f (-1) - f 0) / ((-1 : ℝ) - 0), ⟨-1, by norm_num, rfl⟩⟩
  have hbdd : BddAbove S := by
    refine ⟨(f 1 - f 0) / ((1 : ℝ) - 0), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y < 0 := Set.mem_Iio.mp hy
    exact hf.secant_mono (Set.mem_univ (0 : ℝ)) (Set.mem_univ y) (Set.mem_univ (1 : ℝ))
      (ne_of_lt hy') one_ne_zero (by linarith)
  refine ⟨sSup S, fun y => ?_⟩
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hmem : (f y - f 0) / (y - 0) ∈ S := ⟨y, hy, rfl⟩
    have hle := le_csSup hbdd hmem
    have := (div_le_iff_of_neg (show y - 0 < (0:ℝ) by linarith)).mp hle
    linarith
  · subst hy; simp
  · have hge : sSup S ≤ (f y - f 0) / (y - 0) := by
      refine csSup_le hne ?_
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z < 0 := Set.mem_Iio.mp hz
      exact hf.secant_mono (Set.mem_univ (0 : ℝ)) (Set.mem_univ z) (Set.mem_univ y)
        (ne_of_lt hz') (ne_of_gt hy) (by linarith)
    have := (le_div_iff₀ (show (0:ℝ) < y - 0 by linarith)).mp hge
    linarith

/-- The right tail beyond `a` still carries mass when `a` is below half the positive mass. -/
theorem half_le_setIntegral_Ici {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) {a p : ℝ} (ha : 0 < a)
    (hp : p ≤ ∫ z in Set.Ioi (0:ℝ), z ∂μ) (hap : a ≤ p / 2) :
    a / 2 ≤ ∫ z in Set.Ici a, z ∂μ := by
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioo 0 a ∪ Set.Ici a := by
    ext z
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro hz
      by_cases hza : z < a
      · exact Or.inl ⟨hz, hza⟩
      · exact Or.inr (not_lt.mp hza)
    · rintro (⟨h1, -⟩ | h1)
      · exact h1
      · linarith
  have hdisj : Disjoint (Set.Ioo (0:ℝ) a) (Set.Ici a) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd (Set.mem_Ici.mp hz') (not_le.mpr (Set.mem_Ioo.mp hz).2)
  have hA : IntegrableOn (fun z : ℝ => z) (Set.Ioo (0:ℝ) a) μ := hid.integrableOn
  have hB : IntegrableOn (fun z : ℝ => z) (Set.Ici a) μ := hid.integrableOn
  have hadd : ∫ z in Set.Ioi (0:ℝ), z ∂μ
      = (∫ z in Set.Ioo (0:ℝ) a, z ∂μ) + ∫ z in Set.Ici a, z ∂μ := by
    rw [hsplit]
    exact setIntegral_union hdisj measurableSet_Ici hA hB
  have hsmall : ∫ z in Set.Ioo (0:ℝ) a, z ∂μ ≤ a := by
    have h1 : ∫ z in Set.Ioo (0:ℝ) a, z ∂μ ≤ ∫ _z in Set.Ioo (0:ℝ) a, a ∂μ :=
      setIntegral_mono_on hA (integrable_const a).integrableOn measurableSet_Ioo
        (fun z hz => le_of_lt (Set.mem_Ioo.mp hz).2)
    have h2 : ∫ _z in Set.Ioo (0:ℝ) a, a ∂μ = μ.real (Set.Ioo (0:ℝ) a) * a := by
      rw [setIntegral_const, smul_eq_mul]
    have h3 : μ.real (Set.Ioo (0:ℝ) a) ≤ 1 := by
      simp
    have h5 : (0:ℝ) ≤ μ.real (Set.Ioo (0:ℝ) a) := measureReal_nonneg
    nlinarith [h1, h2, h3, h5, ha.le]
  linarith

/-- The positive and negative parts of a mean zero law carry the same mass. -/
theorem setIntegral_Iic_neg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) (hmean : ∫ z, z ∂μ = 0) :
    ∫ z in Set.Iic (0:ℝ), (-z) ∂μ = ∫ z in Set.Ioi (0:ℝ), z ∂μ := by
  have hdisj : Disjoint (Set.Iic (0:ℝ)) (Set.Ioi (0:ℝ)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd (Set.mem_Ioi.mp hz') (not_lt.mpr (Set.mem_Iic.mp hz))
  have hA : IntegrableOn (fun z : ℝ => z) (Set.Iic (0:ℝ)) μ := hid.integrableOn
  have hB : IntegrableOn (fun z : ℝ => z) (Set.Ioi (0:ℝ)) μ := hid.integrableOn
  have hsplit : ∫ z, z ∂μ = (∫ z in Set.Iic (0:ℝ), z ∂μ) + ∫ z in Set.Ioi (0:ℝ), z ∂μ := by
    rw [← setIntegral_univ (μ := μ) (f := fun z : ℝ => z), ← Set.Iic_union_Ioi (a := (0:ℝ))]
    exact setIntegral_union hdisj measurableSet_Ioi hA hB
  have hneg : ∫ z in Set.Iic (0:ℝ), (-z) ∂μ = -∫ z in Set.Iic (0:ℝ), z ∂μ := integral_neg _
  rw [hneg]
  linarith [hsplit, hmean]

/-- The left tail below `-a` still carries mass when `a` is below half the positive mass. -/
theorem half_le_setIntegral_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) (hmean : ∫ z, z ∂μ = 0) {a p : ℝ} (ha : 0 < a)
    (hp : p ≤ ∫ z in Set.Ioi (0:ℝ), z ∂μ) (hap : a ≤ p / 2) :
    a / 2 ≤ ∫ z in Set.Iic (-a), (-z) ∂μ := by
  have hsplit : Set.Iic (0:ℝ) = Set.Ioc (-a) 0 ∪ Set.Iic (-a) := by
    ext z
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hz
      by_cases hza : -a < z
      · exact Or.inl ⟨hza, hz⟩
      · exact Or.inr (not_lt.mp hza)
    · rintro (⟨-, h1⟩ | h1)
      · exact h1
      · linarith
  have hdisj : Disjoint (Set.Ioc (-a) (0:ℝ)) (Set.Iic (-a)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd (Set.mem_Iic.mp hz') (not_le.mpr (Set.mem_Ioc.mp hz).1)
  have hA : IntegrableOn (fun z : ℝ => -z) (Set.Ioc (-a) (0:ℝ)) μ := hid.neg.integrableOn
  have hB : IntegrableOn (fun z : ℝ => -z) (Set.Iic (-a)) μ := hid.neg.integrableOn
  have hadd : ∫ z in Set.Iic (0:ℝ), (-z) ∂μ
      = (∫ z in Set.Ioc (-a) (0:ℝ), (-z) ∂μ) + ∫ z in Set.Iic (-a), (-z) ∂μ := by
    rw [hsplit]
    exact setIntegral_union hdisj measurableSet_Iic hA hB
  have hsmall : ∫ z in Set.Ioc (-a) (0:ℝ), (-z) ∂μ ≤ a := by
    have h1 : ∫ z in Set.Ioc (-a) (0:ℝ), (-z) ∂μ ≤ ∫ _z in Set.Ioc (-a) (0:ℝ), a ∂μ :=
      setIntegral_mono_on hA (integrable_const a).integrableOn measurableSet_Ioc
        (fun z hz => by have := (Set.mem_Ioc.mp hz).1; linarith)
    have h2 : ∫ _z in Set.Ioc (-a) (0:ℝ), a ∂μ = μ.real (Set.Ioc (-a) (0:ℝ)) * a := by
      rw [setIntegral_const, smul_eq_mul]
    have h3 : μ.real (Set.Ioc (-a) (0:ℝ)) ≤ 1 := by
      simp
    have h5 : (0:ℝ) ≤ μ.real (Set.Ioc (-a) (0:ℝ)) := measureReal_nonneg
    nlinarith [h1, h2, h3, h5, ha.le]
  have hmass := setIntegral_Iic_neg hid hmean
  linarith

/-- The right tail of a nonnegative convex function vanishing at the origin. -/
theorem setIntegral_Ici_convex_ge {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) {h : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ h)
    (h0 : h 0 = 0) (hnn : ∀ x, 0 ≤ h x) (hhi : Integrable h μ)
    {a : ℝ} (ha : 0 < a) (hP : a / 2 ≤ ∫ z in Set.Ici a, z ∂μ) :
    h a / 2 ≤ ∫ z in Set.Ici a, h z ∂μ := by
  have hha : 0 ≤ h a := hnn a
  have hle : ∀ z ∈ Set.Ici a, (h a / a) * z ≤ h z := by
    intro z hz
    have hray := convex_ray_right hc h0 ha (Set.mem_Ici.mp hz)
    have heq : (z / a) * h a = (h a / a) * z := by field_simp
    linarith
  have hA : IntegrableOn (fun z : ℝ => (h a / a) * z) (Set.Ici a) μ :=
    (hid.integrableOn).const_mul _
  have hB : IntegrableOn h (Set.Ici a) μ := hhi.integrableOn
  have hstep : ∫ z in Set.Ici a, (h a / a) * z ∂μ ≤ ∫ z in Set.Ici a, h z ∂μ :=
    setIntegral_mono_on hA hB measurableSet_Ici hle
  have hpull : ∫ z in Set.Ici a, (h a / a) * z ∂μ = (h a / a) * ∫ z in Set.Ici a, z ∂μ :=
    integral_const_mul _ _
  have hcoef : 0 ≤ h a / a := by positivity
  have hmul : (h a / a) * (a / 2) ≤ (h a / a) * ∫ z in Set.Ici a, z ∂μ :=
    mul_le_mul_of_nonneg_left hP hcoef
  have hval : (h a / a) * (a / 2) = h a / 2 := by field_simp
  linarith

/-- The left tail of a nonnegative convex function vanishing at the origin. -/
theorem setIntegral_Iic_convex_ge {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) {h : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ h)
    (h0 : h 0 = 0) (hnn : ∀ x, 0 ≤ h x) (hhi : Integrable h μ)
    {a : ℝ} (ha : 0 < a) (hN : a / 2 ≤ ∫ z in Set.Iic (-a), (-z) ∂μ) :
    h (-a) / 2 ≤ ∫ z in Set.Iic (-a), h z ∂μ := by
  have hha : 0 ≤ h (-a) := hnn (-a)
  have hle : ∀ z ∈ Set.Iic (-a), (h (-a) / a) * (-z) ≤ h z := by
    intro z hz
    have hray := convex_ray_left hc h0 ha (Set.mem_Iic.mp hz)
    have heq : ((-z) / a) * h (-a) = (h (-a) / a) * (-z) := by field_simp
    linarith
  have hA : IntegrableOn (fun z : ℝ => (h (-a) / a) * (-z)) (Set.Iic (-a)) μ :=
    (hid.neg.integrableOn).const_mul _
  have hB : IntegrableOn h (Set.Iic (-a)) μ := hhi.integrableOn
  have hstep : ∫ z in Set.Iic (-a), (h (-a) / a) * (-z) ∂μ ≤ ∫ z in Set.Iic (-a), h z ∂μ :=
    setIntegral_mono_on hA hB measurableSet_Iic hle
  have hpull : ∫ z in Set.Iic (-a), (h (-a) / a) * (-z) ∂μ
      = (h (-a) / a) * ∫ z in Set.Iic (-a), (-z) ∂μ := integral_const_mul _ _
  have hcoef : 0 ≤ h (-a) / a := by positivity
  have hmul : (h (-a) / a) * (a / 2) ≤ (h (-a) / a) * ∫ z in Set.Iic (-a), (-z) ∂μ :=
    mul_le_mul_of_nonneg_left hN hcoef
  have hval : (h (-a) / a) * (a / 2) = h (-a) / 2 := by field_simp
  linarith

/-- The two tails of a nonnegative convex function vanishing at the origin. -/
theorem twoPoint_le_integral_of_nonneg_convex {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) {h : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ h)
    (h0 : h 0 = 0) (hnn : ∀ x, 0 ≤ h x) (hhi : Integrable h μ)
    {a : ℝ} (ha : 0 < a)
    (hP : a / 2 ≤ ∫ z in Set.Ici a, z ∂μ) (hN : a / 2 ≤ ∫ z in Set.Iic (-a), (-z) ∂μ) :
    (h a + h (-a)) / 2 ≤ ∫ z, h z ∂μ := by
  have hdisj : Disjoint (Set.Ici a) (Set.Iic (-a)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 := Set.mem_Ici.mp hz
    have h2 := Set.mem_Iic.mp hz'
    linarith
  have hA : IntegrableOn h (Set.Ici a) μ := hhi.integrableOn
  have hB : IntegrableOn h (Set.Iic (-a)) μ := hhi.integrableOn
  have hunion : ∫ z in Set.Ici a ∪ Set.Iic (-a), h z ∂μ
      = (∫ z in Set.Ici a, h z ∂μ) + ∫ z in Set.Iic (-a), h z ∂μ :=
    setIntegral_union hdisj measurableSet_Iic hA hB
  have hle : ∫ z in Set.Ici a ∪ Set.Iic (-a), h z ∂μ ≤ ∫ z, h z ∂μ :=
    setIntegral_le_integral hhi (Filter.Eventually.of_forall hnn)
  have h1 := setIntegral_Ici_convex_ge hid hc h0 hnn hhi ha hP
  have h2 := setIntegral_Iic_convex_ge hid hc h0 hnn hhi ha hN
  linarith

/-- **A mean-zero law whose positive part carries mass at least `p` dominates, in convex
order, the symmetric two-point law at `±a` for every `0 < a ≤ p/2`.** -/
theorem twoPointLaw_convex_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) (hmean : ∫ z, z ∂μ = 0)
    {a p : ℝ} (ha : 0 < a) (hp : p ≤ ∫ z in Set.Ioi (0:ℝ), z ∂μ) (hap : a ≤ p / 2)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : ConvexOn ℝ Set.univ f) (hfL : LipschitzWith K f) :
    ∫ z, f z ∂(twoPointLaw a) ≤ ∫ z, f z ∂μ := by
  obtain ⟨β, hβ⟩ := exists_supporting_line hf
  have hc : ConvexOn ℝ Set.univ (fun x : ℝ => f x - f 0 - β * x) := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    have hkey := hf.2 (Set.mem_univ x) (Set.mem_univ y) hs ht hst
    simp only [smul_eq_mul] at hkey ⊢
    have hf0 : s * f 0 + t * f 0 = f 0 := by rw [← add_mul, hst, one_mul]
    have hexp : s * (f x - f 0 - β * x) + t * (f y - f 0 - β * y)
        = (s * f x + t * f y) - (s * f 0 + t * f 0) - β * (s * x + t * y) := by ring
    rw [hexp, hf0]
    linarith [hkey]
  have h0 : (fun x : ℝ => f x - f 0 - β * x) 0 = 0 := by simp
  have hnn : ∀ x : ℝ, 0 ≤ (fun x : ℝ => f x - f 0 - β * x) x := by
    intro x
    have := hβ x
    simp only
    linarith
  have hfi : Integrable f μ := integrable_real_lipschitz hfL hid
  have i1 : Integrable (fun z : ℝ => f z - f 0) μ := hfi.sub (integrable_const (f 0))
  have i2 : Integrable (fun z : ℝ => β * z) μ := hid.const_mul β
  have hhi : Integrable (fun x : ℝ => f x - f 0 - β * x) μ := i1.sub i2
  have hint : ∫ z, (f z - f 0 - β * z) ∂μ = (∫ z, f z ∂μ) - f 0 := by
    rw [integral_sub i1 i2, integral_sub hfi (integrable_const (f 0)), integral_const_mul, hmean]
    simp
  have hP := half_le_setIntegral_Ici hid ha hp hap
  have hN := half_le_setIntegral_Iic hid hmean ha hp hap
  have hkey := twoPoint_le_integral_of_nonneg_convex hid hc h0 hnn hhi ha hP hN
  rw [hint] at hkey
  rw [integral_twoPointLaw a f]
  linarith

/-- The positive part integral is the integral over the positive half line. -/
theorem integral_posPart_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hid : Integrable (id : ℝ → ℝ) μ) :
    ∫ z, max z 0 ∂μ = ∫ z in Set.Ioi (0:ℝ), z ∂μ := by
  have hpos : Integrable (fun z : ℝ => max z 0) μ :=
    integrable_real_lipschitz (LipschitzWith.id.max (LipschitzWith.const (0:ℝ))) hid
  have hdisj : Disjoint (Set.Iic (0:ℝ)) (Set.Ioi (0:ℝ)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd (Set.mem_Ioi.mp hz') (not_lt.mpr (Set.mem_Iic.mp hz))
  have hA : IntegrableOn (fun z : ℝ => max z 0) (Set.Iic (0:ℝ)) μ := hpos.integrableOn
  have hB : IntegrableOn (fun z : ℝ => max z 0) (Set.Ioi (0:ℝ)) μ := hpos.integrableOn
  have hsplit : ∫ z, max z 0 ∂μ
      = (∫ z in Set.Iic (0:ℝ), max z 0 ∂μ) + ∫ z in Set.Ioi (0:ℝ), max z 0 ∂μ := by
    have hu := setIntegral_union (f := fun z : ℝ => max z 0) (μ := μ) hdisj measurableSet_Ioi hA hB
    rw [Set.Iic_union_Ioi, setIntegral_univ] at hu
    exact hu
  have hleft : ∫ z in Set.Iic (0:ℝ), max z 0 ∂μ = 0 := by
    have hz0 : ∫ z in Set.Iic (0:ℝ), max z 0 ∂μ = ∫ _z in Set.Iic (0:ℝ), (0:ℝ) ∂μ :=
      setIntegral_congr_fun (f := fun z : ℝ => max z 0) (g := fun _ : ℝ => (0:ℝ))
        measurableSet_Iic (fun z hz => max_eq_right (Set.mem_Iic.mp hz))
    rw [hz0, integral_zero]
  have hright : ∫ z in Set.Ioi (0:ℝ), max z 0 ∂μ = ∫ z in Set.Ioi (0:ℝ), z ∂μ :=
    setIntegral_congr_fun (f := fun z : ℝ => max z 0) (g := fun z : ℝ => z)
      measurableSet_Ioi (fun z hz => max_eq_left (le_of_lt (Set.mem_Ioi.mp hz)))
  rw [hsplit, hleft, hright, zero_add]

/-- A nonconstant integer law of mean zero has a positive part of positive mass. -/
theorem posMass_pos {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => ((k : ℝ))) ν) (hmean : ∫ k, ((k : ℝ)) ∂ν = 0)
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) :
    0 < ∫ k, max ((k : ℝ)) 0 ∂ν := by
  have hmaxeq : ∀ k : ℤ, max ((k : ℝ)) 0 = (((k : ℝ)) + |(k : ℝ)|) / 2 := by
    intro k
    by_cases h : (0:ℝ) ≤ ((k : ℝ))
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right (not_le.mp h).le, abs_of_neg (not_le.mp h)]; ring
  have habsnn : ∀ k : ℤ, 0 ≤ |(k : ℝ)| := fun k => abs_nonneg _
  have habspos : 0 < ∫ k, |(k : ℝ)| ∂ν := by
    rcases lt_or_eq_of_le (integral_nonneg (f := fun k : ℤ => |(k : ℝ)|) (μ := ν) habsnn)
      with h | h
    · exact h
    · exfalso
      have hae := (integral_eq_zero_iff_of_nonneg (f := fun k : ℤ => |(k : ℝ)|) (μ := ν)
        habsnn hint.abs).mp h.symm
      have hae0 : ∀ᵐ k ∂ν, k = 0 := by
        filter_upwards [hae] with k hk
        have hk0 : |(k : ℝ)| = 0 := hk
        have : ((k : ℝ)) = 0 := abs_eq_zero.mp hk0
        exact_mod_cast this
      have hcompl : ν {k : ℤ | k ≠ 0} = 0 := ae_iff.mp hae0
      have hone : ν {(0 : ℤ)} = 1 := by
        have hmc := measure_add_measure_compl (μ := ν) (measurableSet_singleton (0 : ℤ))
        have hset : ({(0:ℤ)}ᶜ : Set ℤ) = {k : ℤ | k ≠ 0} := by ext k; simp
        rw [hset, hcompl, add_zero, measure_univ] at hmc
        exact hmc
      exact hnc 0 hone
  have hcongr : ∫ k, max ((k : ℝ)) 0 ∂ν = ∫ k, (((k : ℝ)) + |(k : ℝ)|) / 2 ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall hmaxeq)
  rw [hcongr, integral_div, integral_add hint hint.abs, hmean, zero_add]
  positivity

/-- The positive mass of the recentred one-site law moves by at most `(K+1)δ`. -/
theorem posMass_shift_ge {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) {δ : ℝ} (hδ : δ ∈ Set.Ioc (0:ℝ) δ₀) :
    (∫ k, max ((k : ℝ)) 0 ∂(ν 0)) - (max K 0 + 1) * δ
      ≤ ∫ z, max z 0 ∂(shiftLaw δ (ν δ)) := by
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, hcoup⟩ := hfam
  have hδmem : δ ∈ Set.Icc (0:ℝ) δ₀ := ⟨hδ.1.le, hδ.2⟩
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) δ₀ := ⟨le_rfl, hδ₀.le⟩
  haveI hpδ : IsProbabilityMeasure (ν δ) := hprob δ hδmem
  haveI hp0 : IsProbabilityMeasure (ν 0) := hprob 0 h0mem
  have hiδ : Integrable (fun k : ℤ => ((k : ℝ))) (ν δ) :=
    integrable_intCast_of_exp hθ (ν δ) (hexp δ hδmem).1
  have hi0 : Integrable (fun k : ℤ => ((k : ℝ))) (ν 0) :=
    integrable_intCast_of_exp hθ (ν 0) (hexp 0 h0mem).1
  obtain ⟨π, hπ, hfst, hsnd, hW⟩ := hcoup δ hδ
  have hmf : AEMeasurable (Prod.fst : ℤ × ℤ → ℤ) π := measurable_fst.aemeasurable
  have hms : AEMeasurable (Prod.snd : ℤ × ℤ → ℤ) π := measurable_snd.aemeasurable
  have hasm : AEStronglyMeasurable (fun k : ℤ => ((k : ℝ))) (ν δ) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hasm0 : AEStronglyMeasurable (fun k : ℤ => ((k : ℝ))) (ν 0) :=
    (measurable_of_countable _).aestronglyMeasurable
  have h1 : Integrable (fun p : ℤ × ℤ => ((p.1 : ℝ))) π :=
    (integrable_map_measure (g := fun k : ℤ => ((k : ℝ))) (f := Prod.fst)
      (by rw [hfst]; exact hasm) hmf).mp (by rw [hfst]; exact hiδ)
  have h2 : Integrable (fun p : ℤ × ℤ => ((p.2 : ℝ))) π :=
    (integrable_map_measure (g := fun k : ℤ => ((k : ℝ))) (f := Prod.snd)
      (by rw [hsnd]; exact hasm0) hms).mp (by rw [hsnd]; exact hi0)
  have hgcont : Continuous (fun z : ℝ => max z 0) := continuous_id.max continuous_const
  have hA : ∫ z, max z 0 ∂(shiftLaw δ (ν δ)) = ∫ p : ℤ × ℤ, max ((p.1 : ℝ) + δ) 0 ∂π := by
    rw [shiftLaw, integral_map (measurable_intShift δ).aemeasurable hgcont.aestronglyMeasurable,
      ← hfst, integral_map hmf (measurable_of_countable _).aestronglyMeasurable]
  have hB : ∫ k, max ((k : ℝ)) 0 ∂(ν 0) = ∫ p : ℤ × ℤ, max ((p.2 : ℝ)) 0 ∂π := by
    rw [← hsnd, integral_map hms (measurable_of_countable _).aestronglyMeasurable]
  have hint1 : Integrable (fun p : ℤ × ℤ => max ((p.1 : ℝ) + δ) 0) π := by
    refine Integrable.mono' ((h1.abs).add (integrable_const |δ|))
      (measurable_of_countable _).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    simp only [Pi.add_apply]
    refine max_le ?_ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have e1 := le_abs_self ((p.1 : ℝ))
    have e2 := le_abs_self δ
    linarith
  have hint2 : Integrable (fun p : ℤ × ℤ => max ((p.2 : ℝ)) 0) π := by
    refine Integrable.mono' (h2.abs)
      (measurable_of_countable _).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have habs : Integrable (fun p : ℤ × ℤ => |(p.1 : ℝ) - (p.2 : ℝ)|) π := by
    simpa [Pi.sub_apply] using (h1.sub h2).abs
  have hint3 : Integrable (fun p : ℤ × ℤ => |(p.1 : ℝ) - (p.2 : ℝ)| + δ) π :=
    habs.add (integrable_const δ)
  have hptw : ∀ p : ℤ × ℤ,
      max ((p.2 : ℝ)) 0 ≤ max ((p.1 : ℝ) + δ) 0 + (|(p.1 : ℝ) - (p.2 : ℝ)| + δ) := by
    intro p
    have e1 : |max ((p.2 : ℝ)) 0 - max ((p.1 : ℝ) + δ) 0| ≤ |(p.2 : ℝ) - ((p.1 : ℝ) + δ)| :=
      abs_max_sub_max_le_abs _ _ _
    have e2 : |(p.2 : ℝ) - ((p.1 : ℝ) + δ)| ≤ |(p.1 : ℝ) - (p.2 : ℝ)| + δ := by
      have e : (p.2 : ℝ) - ((p.1 : ℝ) + δ) = -(((p.1 : ℝ) - (p.2 : ℝ)) + δ) := by ring
      rw [e, abs_neg]
      calc |((p.1 : ℝ) - (p.2 : ℝ)) + δ| ≤ |(p.1 : ℝ) - (p.2 : ℝ)| + |δ| := abs_add_le _ _
        _ = |(p.1 : ℝ) - (p.2 : ℝ)| + δ := by rw [abs_of_pos hδ.1]
    have e3 := le_abs_self (max ((p.2 : ℝ)) 0 - max ((p.1 : ℝ) + δ) 0)
    linarith
  have hmono : ∫ p : ℤ × ℤ, max ((p.2 : ℝ)) 0 ∂π
      ≤ ∫ p : ℤ × ℤ, (max ((p.1 : ℝ) + δ) 0 + (|(p.1 : ℝ) - (p.2 : ℝ)| + δ)) ∂π := by
    simpa [Pi.add_apply] using integral_mono hint2 (hint1.add hint3) hptw
  have hsum : ∫ p : ℤ × ℤ, (|(p.1 : ℝ) - (p.2 : ℝ)| + δ) ∂π
      = (∫ p : ℤ × ℤ, |(p.1 : ℝ) - (p.2 : ℝ)| ∂π) + δ := by
    rw [integral_add habs (integrable_const δ), integral_const]
    simp
  rw [integral_add hint1 hint3, hsum] at hmono
  rw [hA, hB]
  have hK : K * δ ≤ max K 0 * δ := mul_le_mul_of_nonneg_right (le_max_left K 0) hδ.1.le
  have hring : (max K 0 + 1) * δ = max K 0 * δ + δ := by ring
  linarith [hW, hmono, hK, hring]

/-- **The lower bound of the near-family, uniformly in `δ`.** There are `a₀ > 0` and
`δ₁ > 0` such that the symmetric two-point law at `±a₀` is below the shifted law at
parameter `δ` in convex order for every `δ ∈ (0, δ₁]`. -/
theorem exists_twoPoint_comparison {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) :
    ∃ a₀ δ₁ : ℝ, 0 < a₀ ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧ ∀ δ ∈ Set.Ioc (0:ℝ) δ₁,
      ∀ (f : ℝ → ℝ) (Kf : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith Kf f →
        ∫ z, f z ∂(twoPointLaw a₀) ≤ ∫ z, f z ∂(shiftLaw δ (ν δ)) := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, hnc, hexp, -⟩ := hfam
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) δ₀ := ⟨le_rfl, hδ₀.le⟩
  haveI hp0 : IsProbabilityMeasure (ν 0) := hprob 0 h0mem
  have hi0 : Integrable (fun k : ℤ => ((k : ℝ))) (ν 0) :=
    integrable_intCast_of_exp hθ (ν 0) (hexp 0 h0mem).1
  have hmean0 : ∫ k, ((k : ℝ)) ∂(ν 0) = 0 := by
    rw [hmeanν 0 h0mem, neg_zero]
  have hp0pos : 0 < ∫ k, max ((k : ℝ)) 0 ∂(ν 0) := posMass_pos hi0 hmean0 hnc
  set p₀ : ℝ := ∫ k, max ((k : ℝ)) 0 ∂(ν 0) with hp₀
  have hKpos : (0:ℝ) < max K 0 + 1 := by
    have := le_max_right K 0
    linarith
  refine ⟨p₀ / 4, min δ₀ (p₀ / (2 * (max K 0 + 1))), by positivity, ?_, min_le_left _ _, ?_⟩
  · exact lt_min hδ₀ (by positivity)
  intro δ hδ f Kf hf hfL
  have hδ1 : δ ≤ δ₀ := le_trans hδ.2 (min_le_left _ _)
  have hδ2 : δ ≤ p₀ / (2 * (max K 0 + 1)) := le_trans hδ.2 (min_le_right _ _)
  have hδmem : δ ∈ Set.Ioc (0:ℝ) δ₀ := ⟨hδ.1, hδ1⟩
  have hδicc : δ ∈ Set.Icc (0:ℝ) δ₀ := ⟨hδ.1.le, hδ1⟩
  haveI hpδ : IsProbabilityMeasure (ν δ) := hprob δ hδicc
  have hiδ : Integrable (fun k : ℤ => ((k : ℝ))) (ν δ) :=
    integrable_intCast_of_exp hθ (ν δ) (hexp δ hδicc).1
  have hid : Integrable (id : ℝ → ℝ) (shiftLaw δ (ν δ)) := integrable_id_shiftLaw δ (ν δ) hiδ
  have hmean : ∫ z, z ∂(shiftLaw δ (ν δ)) = 0 := by
    rw [integral_shiftLaw_id δ (ν δ) hiδ, hmeanν δ hδicc]
    ring
  have hsmall : (max K 0 + 1) * δ ≤ p₀ / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (max K 0 + 1))] at hδ2
    nlinarith [hδ2, hKpos]
  have hshift := posMass_shift_ge hfam' hδmem
  have hmass : p₀ / 2 ≤ ∫ z in Set.Ioi (0:ℝ), z ∂(shiftLaw δ (ν δ)) := by
    rw [← integral_posPart_eq hid]
    linarith [hshift, hsmall]
  exact twoPointLaw_convex_le hid hmean (by positivity) hmass (by linarith) hf hfL

end LatticeProb.ConvexOrder
