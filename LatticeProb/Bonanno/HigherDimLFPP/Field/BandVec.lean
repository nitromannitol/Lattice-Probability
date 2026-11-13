/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.BandVec at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.Kernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The band vectors `k_{a,b,z}` and their Gram kernel (packet P-F1, targets T1 and T4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1), (3.1) and "Var `H_{ε,1}(z) = log ε⁻¹`";
planning audit HA2, Details D1 (Lemmas D1.2, D1.4 (F1), (F2)).

For `t > 0`, `∫ K_t(z - y) K_t(w - y) dy = t⁻¹ C((z - w)/t)` (`integral_scaleKernel_mul`, change of
variables `y = w - t u`).  With Tonelli/Fubini on `ℝ × ℝ^d`:

* `memLp_bandKernel`: `k_{a,b,z} ∈ L²(ℝ × ℝ^d)` for `0 < a` (any `b`);
* `inner_bandVec`: `⟪k_{a,b,z}, k_{a',b',w}⟫ = ∫_{(max a a', min b b')} C(t⁻¹(z - w)) dt/t`
  (target T4; an empty band gives `0`, `inner_bandVec_eq_zero_of_le`);
* `bandVec_norm_sq_impl`: `‖k_{a,b,z}‖² = log(b/a)` (target T1, the frozen `bandVec_norm_sq`);
* `norm_bandVec_sub_sq`: `‖k_z - k_w‖² = 2 ∫_{(a,b)} (1 - C(t⁻¹(z - w))) dt/t`;
* `norm_bandVec_sub_sq_le`: `‖k_z - k_w‖² ≤ L ‖z - w‖² / a²` whenever `1 - C(x) ≤ L ‖x‖²`
  (target T4, increment bound; (F2) of HA2).

Template: `LQGMetric/Field/WhiteNoiseKernel.lean` (`memLp_phiKernel`, `inner_phiKernelL2`), with the
heat kernel replaced by the compact kernel `K_t` and `ℂ` by `ℝ^d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ### The scaled kernel `K_t` -/

theorem scaleKernel_mul_scaleKernel {t : ℝ} (ht : 0 < t) (u v : Rd d) :
    scaleKernel κ t u * scaleKernel κ t v =
      t ^ (-((d : ℝ) + 1)) * (κ (t⁻¹ • u) * κ (t⁻¹ • v)) := by
  unfold scaleKernel
  have h : t ^ (-((d : ℝ) + 1) / 2) * t ^ (-((d : ℝ) + 1) / 2) = t ^ (-((d : ℝ) + 1)) := by
    rw [← Real.rpow_add ht]
    ring_nf
  calc t ^ (-((d : ℝ) + 1) / 2) * κ (t⁻¹ • u) * (t ^ (-((d : ℝ) + 1) / 2) * κ (t⁻¹ • v))
      = (t ^ (-((d : ℝ) + 1) / 2) * t ^ (-((d : ℝ) + 1) / 2)) * (κ (t⁻¹ • u) * κ (t⁻¹ • v)) := by
        ring
    _ = t ^ (-((d : ℝ) + 1)) * (κ (t⁻¹ • u) * κ (t⁻¹ • v)) := by rw [h]

/-- Change of variables `y = w - t u`: `∫ κ(t⁻¹(z - y)) κ(t⁻¹(w - y)) dy = t^d C(t⁻¹(z - w))`. -/
theorem integral_kappa_smul_mul {t : ℝ} (ht : 0 < t) (z w : Rd d) :
    ∫ y, κ (t⁻¹ • (z - y)) * κ (t⁻¹ • (w - y)) = t ^ d * autoCorr κ (t⁻¹ • (z - w)) := by
  rw [← integral_sub_left_eq_self (fun y => κ (t⁻¹ • (z - y)) * κ (t⁻¹ • (w - y))) volume w]
  have e : ∀ y : Rd d, κ (t⁻¹ • (z - (w - y))) * κ (t⁻¹ • (w - (w - y))) =
      (fun u => κ u * κ (u + t⁻¹ • (z - w))) (t⁻¹ • y) := by
    intro y
    simp only [sub_sub_cancel]
    rw [mul_comm]
    congr 2
    rw [← smul_add]
    congr 1
    abel
  simp_rw [e]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun u => κ u * κ (u + t⁻¹ • (z - w)))
    ht.le, finrank_euclideanSpace_fin, smul_eq_mul]
  rfl

/-- **(3.1) at the level of kernels** (HA2 D1.2):
`∫ K_t(z - y) K_t(w - y) dy = C(t⁻¹(z - w)) / t` for `t > 0`. -/
theorem integral_scaleKernel_mul {t : ℝ} (ht : 0 < t) (z w : Rd d) :
    ∫ y, scaleKernel κ t (z - y) * scaleKernel κ t (w - y) = autoCorr κ (t⁻¹ • (z - w)) / t := by
  simp_rw [scaleKernel_mul_scaleKernel ht]
  rw [integral_const_mul, integral_kappa_smul_mul ht]
  have h : t ^ (-((d : ℝ) + 1)) * t ^ d = t⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    ring_nf
    exact Real.rpow_neg_one t
  calc t ^ (-((d : ℝ) + 1)) * (t ^ d * autoCorr κ (t⁻¹ • (z - w)))
      = (t ^ (-((d : ℝ) + 1)) * t ^ d) * autoCorr κ (t⁻¹ • (z - w)) := by ring
    _ = autoCorr κ (t⁻¹ • (z - w)) / t := by rw [h, inv_mul_eq_div]

theorem integrable_scaleKernel_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (z w : Rd d) :
    Integrable fun y => scaleKernel κ t (z - y) * scaleKernel κ t (w - y) := by
  simp_rw [scaleKernel_mul_scaleKernel ht]
  refine Integrable.const_mul ?_ _
  obtain ⟨A, hA⟩ := hκ.exists_bound
  have hg : Integrable fun y => κ (t⁻¹ • (w - y)) :=
    (hκ.integrable.comp_smul (inv_ne_zero ht.ne')).comp_sub_left w
  refine hg.bdd_mul (c := A) ?_ (Eventually.of_forall fun y => ?_)
  · exact (hκ.continuous.comp ((continuous_const.sub continuous_id).const_smul t⁻¹))
      |>.aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using hA _

/-! ### The band kernels `k_{a,b,z}` -/

theorem measurable_scaleKernel_uncurry (hκ : IsLFPPKernel κ) (z : Rd d) :
    Measurable fun p : ℝ × Rd d => scaleKernel κ p.1 (z - p.2) := by
  unfold scaleKernel
  refine (measurable_fst.pow_const _).mul (hκ.continuous.measurable.comp ?_)
  exact measurable_fst.inv.smul (measurable_const.sub measurable_snd)

theorem bandKernel_eq_indicator (a b : ℝ) (z : Rd d) :
    bandKernel κ a b z = (Ioo a b ×ˢ univ).indicator fun p => scaleKernel κ p.1 (z - p.2) := by
  funext p
  by_cases h : p.1 ∈ Ioo a b
  · rw [bandKernel, indicator_of_mem h, indicator_of_mem (mk_mem_prod h (mem_univ p.2))]
  · rw [bandKernel, indicator_of_notMem h,
      indicator_of_notMem fun hp => h (mem_prod.1 hp).1]

theorem measurable_bandKernel (hκ : IsLFPPKernel κ) (a b : ℝ) (z : Rd d) :
    Measurable (bandKernel κ a b z) := by
  rw [bandKernel_eq_indicator]
  exact (measurable_scaleKernel_uncurry hκ z).indicator (measurableSet_Ioo.prod MeasurableSet.univ)

/-- The product of two band kernels is the kernel product on the common band. -/
theorem bandKernel_mul_apply (a b a' b' : ℝ) (z w : Rd d) (p : ℝ × Rd d) :
    bandKernel κ a b z p * bandKernel κ a' b' w p =
      (Ioo (max a a') (min b b')).indicator
        (fun t => scaleKernel κ t (z - p.2) * scaleKernel κ t (w - p.2)) p.1 := by
  rw [← Ioo_inter_Ioo]
  simp only [bandKernel]
  by_cases h1 : p.1 ∈ Ioo a b
  · by_cases h2 : p.1 ∈ Ioo a' b'
    · rw [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem (mem_inter h1 h2)]
    · have h3 : p.1 ∉ Ioo a b ∩ Ioo a' b' := fun h => h2 h.2
      rw [indicator_of_notMem h2, indicator_of_notMem h3, mul_zero]
  · have h3 : p.1 ∉ Ioo a b ∩ Ioo a' b' := fun h => h1 h.1
    rw [indicator_of_notMem h1, indicator_of_notMem h3, zero_mul]

/-- `t ↦ 1/t` is integrable on `(a, b)` for `0 < a`. -/
theorem integrableOn_inv_Ioo {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun t : ℝ => t⁻¹) (Ioo a b) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
  exact continuousOn_inv₀.mono fun t ht => (lt_of_lt_of_le ha ht.1).ne'

/-- `k_{a,b,z}` is square integrable for `0 < a`, with `∫ k_{a,b,z}² = ∫_{(a,b)} dt/t`. -/
theorem integrable_bandKernel_sq (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    Integrable fun p => bandKernel κ a b z p ^ 2 := by
  have e : ∀ p : ℝ × Rd d, bandKernel κ a b z p ^ 2 =
      (Ioo a b).indicator (fun t => scaleKernel κ t (z - p.2) * scaleKernel κ t (z - p.2)) p.1 := by
    intro p
    rw [sq, bandKernel_mul_apply, max_self, min_self]
  simp_rw [e]
  set F : ℝ × Rd d → ℝ := fun p =>
    (Ioo a b).indicator (fun t => scaleKernel κ t (z - p.2) * scaleKernel κ t (z - p.2)) p.1
    with hF
  have hFm : Measurable F := by
    have : F = fun p => bandKernel κ a b z p ^ 2 := by funext p; rw [e]
    rw [this]
    exact (measurable_bandKernel hκ a b z).pow_const 2
  rw [show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl,
    integrable_prod_iff hFm.aestronglyMeasurable]
  constructor
  · refine Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ Ioo a b
    · simp only [hF, indicator_of_mem ht]
      exact integrable_scaleKernel_mul hκ (lt_trans ha ht.1) z z
    · simp only [hF, indicator_of_notMem ht]
      exact integrable_zero _ _ _
  · have hval : (fun t => ∫ y, ‖F (t, y)‖) = (Ioo a b).indicator fun t => t⁻¹ := by
      funext t
      by_cases ht : t ∈ Ioo a b
      · simp only [hF, indicator_of_mem ht]
        have hnn : ∀ y : Rd d, 0 ≤ scaleKernel κ t (z - y) * scaleKernel κ t (z - y) :=
          fun y => mul_self_nonneg _
        simp_rw [Real.norm_of_nonneg (hnn _)]
        rw [integral_scaleKernel_mul (lt_trans ha ht.1), sub_self, smul_zero, autoCorr_zero hκ,
          one_div]
      · simp only [hF, indicator_of_notMem ht, norm_zero, integral_zero]
    rw [hval, integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_inv_Ioo ha b

/-- **`k_{a,b,z} ∈ L²(ℝ × ℝ^d)`** for `0 < a` (and every `b`). -/
theorem memLp_bandKernel (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    MemLp (bandKernel κ a b z) 2 volume :=
  (memLp_two_iff_integrable_sq (measurable_bandKernel hκ a b z).aestronglyMeasurable).2
    (integrable_bandKernel_sq hκ ha b z)

/-! ### The band vectors and their Gram kernel -/

theorem bandVec_eq_toLp (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    bandVec κ a b z = (memLp_bandKernel hκ ha b z).toLp _ := by
  rw [bandVec, dite_eq_left (memLp_bandKernel hκ ha b z)]

theorem coeFn_bandVec (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    (bandVec κ a b z : ℝ × Rd d → ℝ) =ᵐ[volume] bandKernel κ a b z := by
  rw [bandVec_eq_toLp hκ ha]
  exact MemLp.coeFn_toLp _

theorem integrable_bandKernel_mul (hκ : IsLFPPKernel κ) {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (b b' : ℝ) (z w : Rd d) :
    Integrable fun p => bandKernel κ a b z p * bandKernel κ a' b' w p :=
  (memLp_bandKernel hκ ha b z).integrable_mul (memLp_bandKernel hκ ha' b' w)

theorem inner_bandVec_eq_integral (hκ : IsLFPPKernel κ) {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (b b' : ℝ) (z w : Rd d) :
    ⟪bandVec κ a b z, bandVec κ a' b' w⟫ = ∫ p, bandKernel κ a b z p * bandKernel κ a' b' w p := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bandVec hκ ha b z, coeFn_bandVec hκ ha' b' w] with p h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
  simp only [conj_trivial, mul_comm, RCLike.mul_re, RCLike.re_to_real, RCLike.im_to_real, mul_zero,
    sub_zero]

/-- Fubini: `∫∫ k_{a,b,z} k_{a',b',w} = ∫_{(max a a', min b b')} C(t⁻¹(z - w)) dt/t`. -/
theorem integral_bandKernel_mul (hκ : IsLFPPKernel κ) {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (b b' : ℝ) (z w : Rd d) :
    ∫ p, bandKernel κ a b z p * bandKernel κ a' b' w p =
      ∫ t in Ioo (max a a') (min b b'), autoCorr κ (t⁻¹ • (z - w)) / t := by
  rw [show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl,
    integral_prod _ (integrable_bandKernel_mul hκ ha ha' b b' z w)]
  have hin : ∀ t : ℝ, ∫ y : Rd d, bandKernel κ a b z (t, y) * bandKernel κ a' b' w (t, y) =
      (Ioo (max a a') (min b b')).indicator (fun t => autoCorr κ (t⁻¹ • (z - w)) / t) t := by
    intro t
    simp_rw [bandKernel_mul_apply]
    by_cases ht : t ∈ Ioo (max a a') (min b b')
    · simp only [indicator_of_mem ht]
      exact integral_scaleKernel_mul (lt_of_le_of_lt (le_max_of_le_left ha.le) ht.1) z w
    · simp only [indicator_of_notMem ht, integral_zero]
  simp_rw [hin]
  rw [integral_indicator measurableSet_Ioo]

/-- **Gram formula** (target T4, (3.1)/(F1) of HA2):
`⟪k_{a,b,z}, k_{a',b',w}⟫ = ∫_{(max a a', min b b')} C(t⁻¹(z - w)) dt/t` for `0 < a`, `0 < a'`. -/
theorem inner_bandVec (hκ : IsLFPPKernel κ) {a a' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (b b' : ℝ) (z w : Rd d) :
    ⟪bandVec κ a b z, bandVec κ a' b' w⟫ =
      ∫ t in Ioo (max a a') (min b b'), autoCorr κ (t⁻¹ • (z - w)) / t := by
  rw [inner_bandVec_eq_integral hκ ha ha', integral_bandKernel_mul hκ ha ha']

/-- The variance normalization `‖k_{a,b,z}‖² = log(b/a)` for `0 < a ≤ b`. -/
theorem norm_bandVec_sq (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : Rd d) :
    ‖bandVec κ a b z‖ ^ 2 = Real.log (b / a) := by
  rw [← real_inner_self_eq_norm_sq, inner_bandVec hκ ha ha, max_self, min_self]
  simp_rw [sub_self, smul_zero, autoCorr_zero hκ, one_div]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  exact integral_inv_of_pos ha (lt_of_lt_of_le ha hab)

/-- **Target T1** (the frozen `bandVec_norm_sq`): for an admissible kernel and `0 < a < b`,
`k_{a,b,z}` is square integrable and `‖k_{a,b,z}‖² = log(b/a)`. -/
theorem bandVec_norm_sq_impl : ∀ d : ℕ, 1 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ a b : ℝ, 0 < a → a < b → ∀ z : Rd d,
      MemLp (bandKernel κ a b z) 2 volume ∧ ‖bandVec κ a b z‖ ^ 2 = Real.log (b / a) := by
  intro d _ κ hκ a b ha hab z
  exact ⟨memLp_bandKernel hκ ha b z, norm_bandVec_sq hκ ha hab.le z⟩

/-! ### Increments -/

theorem continuousOn_autoCorr_div (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (v : Rd d) : ContinuousOn (fun t : ℝ => autoCorr κ (t⁻¹ • v) / t) (Icc a b) := by
  have hne : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => (lt_of_lt_of_le ha ht.1).ne'
  refine ContinuousOn.div ?_ continuousOn_id hne
  refine (continuous_autoCorr hκ).comp_continuousOn ?_
  exact (continuousOn_inv₀.mono fun t ht => hne t ht).smul continuousOn_const

theorem integrableOn_autoCorr_div (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (v : Rd d) : IntegrableOn (fun t : ℝ => autoCorr κ (t⁻¹ • v) / t) (Ioo a b) :=
  ((continuousOn_autoCorr_div hκ ha b v).integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem integrableOn_one_sub_autoCorr_div (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (v : Rd d) : IntegrableOn (fun t : ℝ => (1 - autoCorr κ (t⁻¹ • v)) / t) (Ioo a b) := by
  simp_rw [sub_div, one_div]
  exact (integrableOn_inv_Ioo ha b).sub (integrableOn_autoCorr_div hκ ha b v)

/-- `‖k_{a,b,z} - k_{a,b,w}‖² = 2 ∫_{(a,b)} (1 - C(t⁻¹(z - w))) dt/t` ((F2) of HA2). -/
theorem norm_bandVec_sub_sq (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z w : Rd d) :
    ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 =
      2 * ∫ t in Ioo a b, (1 - autoCorr κ (t⁻¹ • (z - w))) / t := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_bandVec hκ ha ha, inner_bandVec hκ ha ha, inner_bandVec hκ ha ha, max_self, min_self]
  simp_rw [sub_self, smul_zero, autoCorr_zero hκ]
  have h1 : IntegrableOn (fun t : ℝ => 1 / t) (Ioo a b) := by
    simp_rw [one_div]; exact integrableOn_inv_Ioo ha b
  have h2 := integrableOn_autoCorr_div hκ ha b (z - w)
  simp_rw [sub_div]
  rw [integral_sub h1 h2]
  ring

/-- **Increment bound** (target T4, (F2) of HA2): if `1 - C(x) ≤ L ‖x‖²` with `L ≥ 0`, then
`‖k_{a,b,z} - k_{a,b,w}‖² ≤ L ‖z - w‖² / a²` for `0 < a` (every `b`). -/
theorem norm_bandVec_sub_sq_le (hκ : IsLFPPKernel κ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x, 1 - autoCorr κ x ≤ L * ‖x‖ ^ 2) {a : ℝ} (ha : 0 < a) (b : ℝ) (z w : Rd d) :
    ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2 := by
  rw [norm_bandVec_sub_sq hκ ha]
  set v := z - w with hv
  set f : ℝ → ℝ := fun t => L * ‖v‖ ^ 2 * t ^ (-3 : ℝ) with hf
  have hf_int : IntegrableOn f (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha).const_mul _
  have hpt : ∀ t ∈ Ioo a b, (1 - autoCorr κ (t⁻¹ • v)) / t ≤ f t := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have h1 := hL (t⁻¹ • v)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)] at h1
    have h3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    calc (1 - autoCorr κ (t⁻¹ • v)) / t ≤ L * (t⁻¹ * ‖v‖) ^ 2 / t :=
          div_le_div_of_nonneg_right h1 ht0.le
      _ = f t := by
          show L * (t⁻¹ * ‖v‖) ^ 2 / t = L * ‖v‖ ^ 2 * t ^ (-3 : ℝ)
          rw [h3]
          field_simp
  have hle1 : ∫ t in Ioo a b, (1 - autoCorr κ (t⁻¹ • v)) / t ≤ ∫ t in Ioo a b, f t :=
    setIntegral_mono_on (integrableOn_one_sub_autoCorr_div hκ ha b v)
      (hf_int.mono_set Ioo_subset_Ioi_self) measurableSet_Ioo hpt
  have hle2 : ∫ t in Ioo a b, f t ≤ ∫ t in Ioi a, f t := by
    refine setIntegral_mono_set hf_int ?_ (Eventually.of_forall Ioo_subset_Ioi_self)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans ha ht
    exact mul_nonneg (by positivity) (Real.rpow_nonneg ht0.le _)
  have hval : ∫ t in Ioi a, f t = L * ‖v‖ ^ 2 / a ^ 2 / 2 := by
    rw [hf, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
    have h2 : a ^ ((-3 : ℝ) + 1) = (a ^ 2)⁻¹ := by
      rw [show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    rw [h2]
    field_simp
    ring
  calc 2 * ∫ t in Ioo a b, (1 - autoCorr κ (t⁻¹ • v)) / t ≤ 2 * ∫ t in Ioi a, f t := by
        linarith
    _ = L * ‖v‖ ^ 2 / a ^ 2 := by rw [hval]; ring

/-- Increment bound with an explicit constant from `exists_one_sub_autoCorr_le`. -/
theorem exists_norm_bandVec_sub_sq_le (hκ : IsLFPPKernel κ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (a : ℝ), 0 < a → ∀ (b : ℝ) (z w : Rd d),
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := exists_one_sub_autoCorr_le hκ
  exact ⟨L, hL0, fun a ha b z w =>
    norm_bandVec_sub_sq_le hκ hL0 (fun x => (hL x).2) ha b z w⟩

end HigherDimLFPP
