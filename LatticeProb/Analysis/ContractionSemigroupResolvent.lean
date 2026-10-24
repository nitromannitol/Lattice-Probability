import LatticeProb.Analysis.ContractionSemigroup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Laplace integrals for contraction semigroups

The exponentially discounted orbit is Bochner integrable for every positive discount.
Its integral defines a bounded linear operator with the sharp contraction bound.
The two inverse identities identify its range with the generator domain and show that
the generator graph is closed.
-/

namespace LatticeProb.ContractionSemigroup

open MeasureTheory Set Filter Topology
open scoped NNReal

noncomputable section

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]

/-- Contraction controls each discounted orbit by an integrable scalar exponential. -/
theorem norm_discounted_orbit_le (T : StronglyContinuousContractionSemigroup L)
    (μ t : ℝ) (f : L) :
    ‖Real.exp (-μ * t) • T.operator t.toNNReal f‖ ≤ Real.exp (-μ * t) * ‖f‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_mul] using
      (T.operator t.toNNReal).le_of_opNorm_le (T.norm_le_one _) f)
    (Real.exp_pos _).le

/-- The discounted orbit is continuous, including at time zero. -/
theorem continuous_discounted_orbit (T : StronglyContinuousContractionSemigroup L)
    (μ : ℝ) (f : L) :
    Continuous (fun t : ℝ => Real.exp (-μ * t) • T.operator t.toNNReal f) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((T.continuous_orbit f).comp continuous_real_toNNReal)

/-- Positive discount makes every orbit Bochner integrable on the positive half-line. -/
theorem integrable_discounted_orbit (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (f : L) :
    IntegrableOn (fun t : ℝ => Real.exp (-μ * t) • T.operator t.toNNReal f) (Ioi 0) := by
  exact ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hμ) 0).mul_const ‖f‖).mono'
    (continuous_discounted_orbit T μ f).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_discounted_orbit_le T μ t f)

/-- The Laplace integral has norm at most the inverse discount times the initial norm. -/
theorem norm_integral_discounted_orbit_le (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (f : L) :
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) • T.operator t.toNNReal f‖ ≤ μ⁻¹ * ‖f‖ := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) * ‖f‖ :=
      norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hμ) 0).mul_const ‖f‖)
        (Eventually.of_forall fun t => norm_discounted_orbit_le T μ t f)
    _ = μ⁻¹ * ‖f‖ := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos hμ)]
      simp only [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg, one_div]

/-- The Laplace resolvent, defined by the genuine Bochner integral at positive discount. -/
def resolvent (T : StronglyContinuousContractionSemigroup L) (μ : ℝ) (hμ : 0 < μ) :
    L →L[ℝ] L :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) • T.operator t.toNNReal f
      map_add' := fun f g => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_discounted_orbit T hμ f)
          (integrable_discounted_orbit T hμ g)
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, map_smul, smul_comm (Real.exp _) c]
        exact integral_smul c _ }
    μ⁻¹ (norm_integral_discounted_orbit_le T hμ)

/-- Evaluation of the resolvent is its defining half-line integral. -/
theorem resolvent_apply (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (f : L) :
    resolvent T μ hμ f =
      ∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) • T.operator t.toNNReal f := rfl

/-- The resolvent operator norm is bounded by the inverse positive discount. -/
theorem norm_resolvent_le (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) : ‖resolvent T μ hμ‖ ≤ μ⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr hμ.le) _

omit [CompleteSpace L] in
/-- Translation of a half-line integral translates its lower endpoint. -/
theorem integral_Ioi_translate (F : ℝ → L) (s : ℝ) :
    (∫ t in Ioi (0 : ℝ), F (t + s)) = ∫ t in Ioi s, F t := by
  calc
    _ = ∫ t : ℝ, (Ioi s).indicator F (t + s) := by
      rw [← integral_indicator measurableSet_Ioi]
      congr 1
      ext t
      simp only [indicator_apply, mem_Ioi, lt_add_iff_pos_left]
    _ = _ := by
      rw [integral_add_right_eq_self, integral_indicator measurableSet_Ioi]

/-- The semigroup shifts the Laplace integral to a discounted tail integral. -/
theorem operator_resolvent (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (s : ℝ≥0) (f : L) :
    T.operator s (resolvent T μ hμ f) = Real.exp (μ * s) •
      ∫ t in Ioi (s : ℝ), Real.exp (-μ * t) • T.operator t.toNNReal f := by
  rw [resolvent_apply, ← (T.operator s).integral_comp_comm
    (integrable_discounted_orbit T hμ f)]
  rw [← integral_Ioi_translate _ (s : ℝ), ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change T.operator s (Real.exp (-μ * t) • T.operator t.toNNReal f) =
    Real.exp (μ * s) • (Real.exp (-μ * (t + s)) • T.operator (t + s).toNNReal f)
  rw [map_smul, smul_smul]
  have he : Real.exp (μ * s) * Real.exp (-μ * (t + s)) = Real.exp (-μ * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Real.toNNReal_add ht.le s.coe_nonneg, Real.toNNReal_coe,
    add_comm t.toNNReal s, T.map_add]
  rfl

/-- The orbit of a resolvent is an exponential times its initial value minus a short integral. -/
theorem operator_resolvent_eq (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (s : ℝ≥0) (f : L) :
    T.operator s (resolvent T μ hμ f) = Real.exp (μ * s) •
      (resolvent T μ hμ f -
        ∫ t in (0 : ℝ)..(s : ℝ), Real.exp (-μ * t) • T.operator t.toNNReal f) := by
  rw [operator_resolvent T hμ s f, resolvent_apply]
  congr 1
  apply eq_sub_iff_add_eq.mpr
  exact (add_comm _ _).trans (intervalIntegral.integral_interval_add_Ioi
    (integrable_discounted_orbit T hμ f)
    ((integrable_discounted_orbit T hμ f).mono_set (Ioi_subset_Ioi s.coe_nonneg)))

/-- The Laplace resolvent takes every vector into the generator graph with the expected value. -/
theorem resolvent_mem_generatorGraph (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (f : L) :
    (resolvent T μ hμ f, μ • resolvent T μ hμ f - f) ∈ generatorGraph T := by
  let F : ℝ → L := fun t => Real.exp (-μ * t) • T.operator t.toNNReal f
  have hc : Continuous F := continuous_discounted_orbit T μ f
  have hF : F 0 = f := by
    simp only [F, mul_zero, Real.exp_zero, Real.toNNReal_zero, T.map_zero,
      ContinuousLinearMap.id_apply, one_smul]
  have hi : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..s, F t) f 0 := by
    rw [← hF]
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : HasDerivAt (fun s : ℝ => Real.exp (μ * s)) μ 0 := by
    simpa only [id_eq, mul_zero, Real.exp_zero, mul_one, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).const_mul μ).exp
  have hd := he.smul ((hasDerivAt_const (0 : ℝ) (resolvent T μ hμ f)).sub hi)
  simp only [Pi.sub_apply, mul_zero, Real.exp_zero, intervalIntegral.integral_same,
    sub_zero, zero_sub, one_smul] at hd
  rw [add_comm (-f), ← sub_eq_add_neg] at hd
  change HasDerivAt (fun s : ℝ => Real.exp (μ * s) •
    (resolvent T μ hμ f - ∫ t in (0 : ℝ)..s, F t))
      (μ • resolvent T μ hμ f - f) 0 at hd
  have hlim := hd.tendsto_slope_zero_right
  simp only [zero_add, mul_zero, Real.exp_zero, intervalIntegral.integral_same,
    sub_zero, one_smul] at hlim
  change Tendsto (fun t : ℝ => t⁻¹ •
    (T.operator t.toNNReal (resolvent T μ hμ f) - resolvent T μ hμ f))
      (𝓝[>] (0 : ℝ)) (𝓝 (μ • resolvent T μ hμ f - f))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hs : T.operator t.toNNReal (resolvent T μ hμ f) = Real.exp (μ * t) •
      (resolvent T μ hμ f - ∫ r in (0 : ℝ)..t, F r) := by
    simpa only [Real.coe_toNNReal t ht.le] using
      operator_resolvent_eq T hμ t.toNNReal f
  exact congrArg (fun z : L => t⁻¹ • (z - resolvent T μ hμ f)) hs.symm

/-- A generator graph pair differentiates every orbit on the right at nonnegative times. -/
theorem hasDerivWithinAt_orbit (T : StronglyContinuousContractionSemigroup L)
    {v w : L} (h : (v, w) ∈ generatorGraph T) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r : ℝ => T.operator r.toNNReal v)
      (T.operator t.toNNReal w) (Ioi t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp only [mem_Ioi, lt_self_iff_false,
    not_false_eq_true])]
  have hs : Tendsto (fun r : ℝ => r - t) (𝓝[>] t) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun r : ℝ => r - t) := continuous_id.sub continuous_const
      simpa only [sub_self] using (hc.tendsto t).mono_left
        (nhdsWithin_le_nhds (s := Ioi t))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r - t
      exact sub_pos.mpr hr
  have hh := ((T.operator t.toNNReal).continuous.tendsto w).comp (h.comp hs)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have htime : r.toNNReal = t.toNNReal + (r - t).toNNReal := by
    rw [← Real.toNNReal_add ht (sub_pos.mpr hr).le]
    congr 1
    ring
  simp only [Function.comp_apply, slope_def_module, map_smul, map_sub]
  rw [htime, T.map_add]
  rfl

/-- Discounted orbits vanish at infinity by contraction and exponential decay. -/
theorem tendsto_discounted_orbit_zero (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (v : L) :
    Tendsto (fun t : ℝ => Real.exp (-μ * t) • T.operator t.toNNReal v) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun t => norm_discounted_orbit_le T μ t v)
  have he : Tendsto (fun t : ℝ => Real.exp (-μ * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hμ))
  simpa only [zero_mul] using he.mul_const ‖v‖

/-- Differentiation of a discounted orbit uses the actual generator graph value. -/
theorem hasDerivWithinAt_discounted_orbit (T : StronglyContinuousContractionSemigroup L)
    {v w : L} (h : (v, w) ∈ generatorGraph T) (μ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r : ℝ => Real.exp (-μ * r) • T.operator r.toNNReal v)
      (Real.exp (-μ * t) • T.operator t.toNNReal (w - μ • v)) (Ioi t) t := by
  have he := (((hasDerivAt_id t).const_mul (-μ)).exp).hasDerivWithinAt (s := Ioi t)
  convert he.smul (hasDerivWithinAt_orbit T h ht) using 1
  · rfl
  · rw [map_sub, map_smul, smul_sub, smul_smul]
    simp only [id_eq, mul_one, mul_neg, neg_smul, sub_eq_add_neg]

/-- The Laplace resolvent is a left inverse for the positive shifted generator. -/
theorem resolvent_of_mem_generatorGraph (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) {v w : L} (h : (v, w) ∈ generatorGraph T) :
    resolvent T μ hμ (μ • v - w) = v := by
  have hi (b : ℝ) (hb : 0 ≤ b) :
      (∫ t in (0 : ℝ)..b, Real.exp (-μ * t) • T.operator t.toNNReal (w - μ • v)) =
        Real.exp (-μ * b) • T.operator b.toNNReal v - v := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb
      (continuous_discounted_orbit T μ v).continuousOn
      (fun t ht => hasDerivWithinAt_discounted_orbit T h μ ht.1.le)
      ((continuous_discounted_orbit T μ (w - μ • v)).intervalIntegrable 0 b)
    simpa only [mul_zero, Real.exp_zero, Real.toNNReal_zero, T.map_zero,
      ContinuousLinearMap.id_apply, one_smul] using hh
  have hl := intervalIntegral_tendsto_integral_Ioi 0
    (integrable_discounted_orbit T hμ (w - μ • v)) tendsto_id
  have hr : Tendsto (fun t : ℝ =>
      Real.exp (-μ * t) • T.operator t.toNNReal v - v) atTop (𝓝 (-v)) := by
    simpa only [zero_sub] using (tendsto_discounted_orbit_zero T hμ v).sub_const v
  have he : resolvent T μ hμ (w - μ • v) = -v := by
    rw [resolvent_apply]
    apply tendsto_nhds_unique hl
    apply hr.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    exact (hi b hb).symm
  have hn : μ • v - w = -(w - μ • v) := neg_sub _ _ |>.symm
  rw [hn, map_neg, he, neg_neg]

/-- The generator graph contains the zero pair. -/
theorem zero_mem_generatorGraph (T : StronglyContinuousContractionSemigroup L) :
    ((0 : L), (0 : L)) ∈ generatorGraph T := by
  change Tendsto _ _ _
  simpa only [map_zero, sub_zero, smul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : L)) (𝓝[>] (0 : ℝ)) (𝓝 0))

/-- Addition of right derivatives gives addition in the generator graph. -/
theorem add_mem_generatorGraph (T : StronglyContinuousContractionSemigroup L)
    {v w v' w' : L} (h : (v, w) ∈ generatorGraph T)
    (h' : (v', w') ∈ generatorGraph T) :
    (v + v', w + w') ∈ generatorGraph T := by
  change Tendsto _ _ _ at h h' ⊢
  convert h.add h' using 1
  ext t
  simp only [map_add, add_sub_add_comm, smul_add]

/-- Scalar multiplication of right derivatives preserves the generator graph. -/
theorem smul_mem_generatorGraph (T : StronglyContinuousContractionSemigroup L)
    (c : ℝ) {v w : L} (h : (v, w) ∈ generatorGraph T) :
    (c • v, c • w) ∈ generatorGraph T := by
  change Tendsto _ _ _ at h ⊢
  convert h.const_smul c using 1
  ext t
  simp only [map_smul, ← smul_sub, smul_comm (t⁻¹) c]

/-- The domain of the generator is a real vector subspace. -/
def generatorSubmodule (T : StronglyContinuousContractionSemigroup L) : Submodule ℝ L where
  carrier := generatorDomain T
  zero_mem' := ⟨0, zero_mem_generatorGraph T⟩
  add_mem' := by
    rintro v v' ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨w + w', add_mem_generatorGraph T hw hw'⟩
  smul_mem' := by
    rintro c v ⟨w, hw⟩
    exact ⟨c • w, smul_mem_generatorGraph T c hw⟩

/-- Membership in the generator submodule is exactly membership in its domain. -/
theorem mem_generatorSubmodule (T : StronglyContinuousContractionSemigroup L) (v : L) :
    v ∈ generatorSubmodule T ↔ v ∈ generatorDomain T := Iff.rfl

/-- The two resolvent identities characterize generator graph membership. -/
theorem mem_generatorGraph_iff_resolvent (T : StronglyContinuousContractionSemigroup L)
    {μ : ℝ} (hμ : 0 < μ) (v w : L) :
    (v, w) ∈ generatorGraph T ↔ resolvent T μ hμ (μ • v - w) = v := by
  constructor
  · exact resolvent_of_mem_generatorGraph T hμ
  · intro hv
    have hg := resolvent_mem_generatorGraph T hμ (μ • v - w)
    rw [hv, sub_sub_cancel] at hg
    exact hg

/-- The generator graph is closed because it is the equalizer of continuous maps. -/
theorem isClosed_generatorGraph (T : StronglyContinuousContractionSemigroup L) :
    IsClosed (generatorGraph T) := by
  have he : generatorGraph T =
      {p : L × L | resolvent T 1 (by norm_num) (p.1 - p.2) = p.1} := by
    ext p
    simpa only [one_smul, mem_setOf_eq] using
      mem_generatorGraph_iff_resolvent T (by norm_num : (0 : ℝ) < 1) p.1 p.2
  rw [he]
  exact isClosed_eq ((resolvent T 1 (by norm_num)).continuous.comp
    (continuous_fst.sub continuous_snd)) continuous_fst

/-- The full generator domain is a core for its closed generator graph. -/
theorem isCore_generatorSubmodule (T : StronglyContinuousContractionSemigroup L) :
    IsCore T (generatorSubmodule T) := by
  constructor
  · intro v hv
    exact hv
  · have he : {p : L × L | p.1 ∈ generatorSubmodule T ∧ p ∈ generatorGraph T} =
        generatorGraph T := by
      ext p
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨⟨p.2, h⟩, h⟩
    rw [he]
    exact (isClosed_generatorGraph T).closure_eq

/-- On the identity semigroup the resolvent is exactly inverse-discount scalar multiplication. -/
theorem identity_resolvent_apply {μ : ℝ} (hμ : 0 < μ) (f : L) :
    resolvent identitySemigroup μ hμ f = μ⁻¹ • f := by
  have hg : (μ⁻¹ • f, (0 : L)) ∈ generatorGraph identitySemigroup := by
    rw [identity_generatorGraph]
    rfl
  simpa only [smul_smul, mul_inv_cancel₀ hμ.ne', one_smul, sub_zero] using
    resolvent_of_mem_generatorGraph identitySemigroup hμ hg

end

end LatticeProb.ContractionSemigroup
