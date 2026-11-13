/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.Measures at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandVec
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian

/-!
# Measure-level band vectors and their covariance (packet P-F2, target T1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1), (3.1) and §3.1; planning audit HA2
(`planning/audits/HA2-section-3.md`), notation paragraph, Details D1 ("Band integrands"), D2.1, D4
and the Lean block (c) (`bandFun`, `IsPairable`, `bandVec`, `scaleCov`).

For a finite measure `μ` on `ℝ^d` and a Borel scale set `S ⊆ (0, ∞)`, the band integrand is
`F^S_μ(t, y) = 1_S(t) (μ * K_t)(y)` with `(μ * K_t)(y) = ∫ K_t(z - y) dμ(z)` (`scaleConv`).
The white-noise vector of `⟨H_S, μ - ν⟩` is `bandVecM κ S μ ν ∈ L²(ℝ × ℝ^d)` (junk `0` unless
`IsPairable κ S μ ν`, i.e. `F^S_μ - F^S_ν ∈ L²`), and
`scaleCov κ S μ ν μ' ν' = ⟪bandVecM κ S μ ν, bandVecM κ S μ' ν'⟫` (Itô isometry: this is the
covariance of the pairings).  The point vectors of P-F1 are the case of Dirac masses
(`bandVecM_dirac_zero`).

Main results:

* fixed scale (HA2 D3, Step 1): for `t > 0` and finite measures,
  `∫ (μ * K_t)(y) (μ' * K_t)(y) dy = ∫∫ C(t⁻¹(z - w))/t dμ(z) dμ'(w)` (`integral_scaleConv_mul`),
  hence `∫ ((μ - ν) * K_t)((μ' - ν') * K_t) = scalePair κ t μ ν μ' ν'`
  (`integral_scaleConv_sub_mul`), where `scalePair` is the four-term expansion `mixInt` of
  `∫∫ C(t⁻¹(z - w))/t (μ - ν)(dz) (μ' - ν')(dw)`;
* `isPairable_iff_lintegral`: `IsPairable κ S μ ν ↔ ∫⁻_S scalePair κ t μ ν μ ν dt < ∞`;
* `scaleCov_eq_integral`: `scaleCov κ S μ ν μ' ν' = ∫_S scalePair κ t μ ν μ' ν' dt` for pairable
  pairs (the formula of target T1);
* `bandVecM_dirac_zero`: compatibility with the point vectors `bandVec κ a b z` of P-F1;
* bilinearity (`bandVecM_add`, `bandVecM_swap`, `bandVecM_smul`, `bandVecM_sub`, ...);
* the Gram property: `sum_mul_scaleCov_nonneg`, `psdOn_scaleCov`;
* scale sets: `IsPairable.mono_set`, `scaleCov_self_le_of_subset` (HA2 D4, (3.3) for nested scale
  sets), `bandVecM_union` (band additivity (F3)), `inner_bandVecM_eq_zero_of_disjoint`
  (orthogonality of disjoint bands, HA2 D2.1);
* pairability: `isPairable_of_subset_Icc` (bounded bands, any finite measures) and
  `isPairable_of_subset_Ici` (unbounded bands, equal masses and bounded supports).

Templates: `LQGMetric/Field/WhiteNoiseKernel.lean` (`memLp_phiKernel`, `inner_phiKernelL2`) and
P-F1's `HigherDimLFPP/Field/BandVec.lean` (point vectors); there is no 2D measure-level analogue
(the 2D library works with finite segment combinations, `LQGDimension.Blueprint.Draft.SegComb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

variable {d : ℕ}

/-! ### Definitions -/

/-- `(μ * K_t)(y) = ∫ K_t(z - y) dμ(z)`. -/
def scaleConv (κ : Rd d → ℝ) (t : ℝ) (μ : Measure (Rd d)) (y : Rd d) : ℝ :=
  ∫ z, scaleKernel κ t (z - y) ∂μ

/-- Scale-band integrand of a finite measure: `(t, y) ↦ 1_S(t) ∫ K_t(z - y) dμ(z)`
(HA2's `bandFun`). -/
def bandFun (κ : Rd d → ℝ) (S : Set ℝ) (μ : Measure (Rd d)) : ℝ × Rd d → ℝ :=
  fun p => S.indicator (fun t => ∫ z, scaleKernel κ t (z - p.2) ∂μ) p.1

/-- Square-integrability of the band integrand of `μ - ν` (the domain of the pairing
`⟨H_S, μ - ν⟩`; HA2's `IsPairable`). -/
def IsPairable (κ : Rd d → ℝ) (S : Set ℝ) (μ ν : Measure (Rd d)) : Prop :=
  MemLp (bandFun κ S μ - bandFun κ S ν) 2 volume

/-- The white-noise kernel vector of `⟨H_S, μ - ν⟩` in `L²(ℝ × ℝ^d)` (junk `0` if not pairable;
HA2's `bandVec`, renamed because `bandVec` is the frozen point vector `k_{a,b,z}`). -/
def bandVecM (κ : Rd d → ℝ) (S : Set ℝ) (μ ν : Measure (Rd d)) : WN d := by
  classical
  exact if h : IsPairable κ S μ ν then h.toLp _ else 0

/-- `Cov(⟨H_S, μ - ν⟩, ⟨H_S, μ' - ν'⟩)`, defined as the `L²` inner product of the kernel vectors
(Itô isometry); a Gram kernel, hence positive semidefinite (HA2's `scaleCov`). -/
def scaleCov (κ : Rd d → ℝ) (S : Set ℝ) (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  ⟪bandVecM κ S μ ν, bandVecM κ S μ' ν'⟫

/-- `∫∫ g(z, w) (μ - ν)(dz) (μ' - ν')(dw)`, expanded into its four product-measure integrals. -/
def mixInt (g : Rd d → Rd d → ℝ) (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  (∫ p, g p.1 p.2 ∂(μ.prod μ')) - (∫ p, g p.1 p.2 ∂(μ.prod ν'))
    - (∫ p, g p.1 p.2 ∂(ν.prod μ')) + (∫ p, g p.1 p.2 ∂(ν.prod ν'))

/-- The scale-`t` covariance density
`∫∫ t⁻¹ C(t⁻¹(z - w)) (μ - ν)(dz) (μ' - ν')(dw)`, with `C = autoCorr κ`. -/
def scalePair (κ : Rd d → ℝ) (t : ℝ) (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  mixInt (fun z w => autoCorr κ (t⁻¹ • (z - w)) / t) μ ν μ' ν'

/-! ### The kernel `K_t` -/

section Kernel

variable {κ : Rd d → ℝ}

theorem continuous_scaleKernel (hκ : IsLFPPKernel κ) (t : ℝ) : Continuous (scaleKernel κ t) := by
  unfold scaleKernel
  exact continuous_const.mul (hκ.continuous.comp (continuous_const_smul _))

/-- Joint measurability of `((t, y), z) ↦ K_t(z - y)`. -/
theorem measurable_scaleKernel_prod (hκ : IsLFPPKernel κ) :
    Measurable fun q : (ℝ × Rd d) × Rd d => scaleKernel κ q.1.1 (q.2 - q.1.2) := by
  unfold scaleKernel
  refine (measurable_fst.fst.pow_const _).mul (hκ.continuous.measurable.comp ?_)
  exact measurable_fst.fst.inv.smul (measurable_snd.sub measurable_fst.snd)
/-- `|K_t(v)| ≤ |t^{-(d+1)/2}| A` for every `t` (no sign condition on `t`). -/
theorem abs_scaleKernel_le' {A : ℝ} (hA : ∀ x, |κ x| ≤ A) (t : ℝ) (v : Rd d) :
    |scaleKernel κ t v| ≤ |t ^ (-((d : ℝ) + 1) / 2)| * A := by
  unfold scaleKernel
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hA _) (abs_nonneg _)

/-- `z ↦ K_t(z - y)` is integrable for every finite measure (and every `t`). -/
theorem integrable_scaleKernel_sub (hκ : IsLFPPKernel κ) (t : ℝ) (y : Rd d)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] : Integrable (fun z => scaleKernel κ t (z - y)) μ := by
  obtain ⟨A, hA⟩ := hκ.exists_bound
  refine Integrable.of_bound ((continuous_scaleKernel hκ t).comp
    (continuous_id.sub continuous_const)).aestronglyMeasurable (|t ^ (-((d : ℝ) + 1) / 2)| * A)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_scaleKernel_le' hA t _

/-- `∫ |K_t(z - y) K_t(w - y)| dy ≤ 1/t` (from `2|ab| ≤ a² + b²` and `‖K_t‖₂² = 1/t`). -/
theorem integral_abs_scaleKernel_mul_le (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (z w : Rd d) :
    ∫ y, |scaleKernel κ t (z - y) * scaleKernel κ t (w - y)| ≤ t⁻¹ := by
  have hz := integrable_scaleKernel_mul hκ ht z z
  have hw := integrable_scaleKernel_mul hκ ht w w
  have hzw := integrable_scaleKernel_mul hκ ht z w
  calc ∫ y, |scaleKernel κ t (z - y) * scaleKernel κ t (w - y)|
      ≤ ∫ y, (scaleKernel κ t (z - y) * scaleKernel κ t (z - y) +
          scaleKernel κ t (w - y) * scaleKernel κ t (w - y)) / 2 := by
        refine integral_mono hzw.abs ((hz.add hw).div_const 2) fun y => ?_
        set a := scaleKernel κ t (z - y)
        set b := scaleKernel κ t (w - y)
        rw [abs_mul]
        nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
    _ = t⁻¹ := by
        rw [integral_div, integral_add hz hw, integral_scaleKernel_mul ht,
          integral_scaleKernel_mul ht]
        simp only [sub_self, smul_zero, autoCorr_zero hκ]
        ring

end Kernel

/-! ### Fixed scale: the Fubini identity -/

section FixedScale

variable {κ : Rd d → ℝ}

/-- `(μ * K_t)(y) (μ' * K_t)(y) = ∫ K_t(z - y) K_t(w - y) d(μ ⊗ μ')(z, w)`. -/
theorem scaleConv_mul_scaleConv (t : ℝ) (μ μ' : Measure (Rd d)) [SFinite μ] [SFinite μ']
    (y : Rd d) :
    scaleConv κ t μ y * scaleConv κ t μ' y =
      ∫ x, scaleKernel κ t (x.1 - y) * scaleKernel κ t (x.2 - y) ∂(μ.prod μ') :=
  (integral_prod_mul (fun z => scaleKernel κ t (z - y)) (fun w => scaleKernel κ t (w - y))).symm

theorem measurable_scaleKernel_mul_prod (hκ : IsLFPPKernel κ) (t : ℝ) :
    Measurable fun q : (Rd d × Rd d) × Rd d =>
      scaleKernel κ t (q.1.1 - q.2) * scaleKernel κ t (q.1.2 - q.2) := by
  have h := (continuous_scaleKernel hκ t).measurable
  exact (h.comp (measurable_fst.fst.sub measurable_snd)).mul
    (h.comp (measurable_fst.snd.sub measurable_snd))

/-- For `t > 0`, `((z, w), y) ↦ K_t(z - y) K_t(w - y)` is integrable for `(μ ⊗ μ') ⊗ dy`. -/
theorem integrable_scaleKernel_mul_prod (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ μ' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    Integrable (fun q : (Rd d × Rd d) × Rd d =>
      scaleKernel κ t (q.1.1 - q.2) * scaleKernel κ t (q.1.2 - q.2)) ((μ.prod μ').prod volume) := by
  have hm := measurable_scaleKernel_mul_prod hκ t
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun x => integrable_scaleKernel_mul hκ ht x.1 x.2, ?_⟩
  refine Integrable.of_bound hm.norm.aestronglyMeasurable.integral_prod_right' t⁻¹
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  simp only [Real.norm_eq_abs]
  exact integral_abs_scaleKernel_mul_le hκ ht x.1 x.2

/-- For `t > 0`, `y ↦ (μ * K_t)(y) (μ' * K_t)(y)` is integrable. -/
theorem integrable_scaleConv_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ μ' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    Integrable fun y => scaleConv κ t μ y * scaleConv κ t μ' y := by
  refine (integrable_scaleKernel_mul_prod hκ ht μ μ').integral_prod_right.congr
    (Eventually.of_forall fun y => ?_)
  exact (scaleConv_mul_scaleConv t μ μ' y).symm

/-- **(3.1) for measures at a fixed scale** (HA2 D3, Step 1): for `t > 0`,
`∫ (μ * K_t)(μ' * K_t) = ∫∫ C(t⁻¹(z - w))/t dμ(z) dμ'(w)`. -/
theorem integral_scaleConv_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ μ' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    ∫ y, scaleConv κ t μ y * scaleConv κ t μ' y =
      ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod μ') := by
  simp_rw [scaleConv_mul_scaleConv t μ μ']
  rw [← integral_integral_swap (f := fun (x : Rd d × Rd d) (y : Rd d) =>
    scaleKernel κ t (x.1 - y) * scaleKernel κ t (x.2 - y)) (integrable_scaleKernel_mul_prod hκ ht μ μ')]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact integral_scaleKernel_mul ht x.1 x.2

/-- The four-term expansion at a fixed scale: for `t > 0`,
`((μ - ν) * K_t) ((μ' - ν') * K_t)` is integrable with integral `scalePair κ t μ ν μ' ν'`. -/
theorem integrable_scaleConv_sub_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] :
    Integrable fun y => (scaleConv κ t μ y - scaleConv κ t ν y) *
      (scaleConv κ t μ' y - scaleConv κ t ν' y) := by
  have e : (fun y => (scaleConv κ t μ y - scaleConv κ t ν y) *
      (scaleConv κ t μ' y - scaleConv κ t ν' y)) = fun y =>
      scaleConv κ t μ y * scaleConv κ t μ' y - scaleConv κ t μ y * scaleConv κ t ν' y -
        scaleConv κ t ν y * scaleConv κ t μ' y + scaleConv κ t ν y * scaleConv κ t ν' y := by
    funext y; ring
  rw [e]
  exact (((integrable_scaleConv_mul hκ ht μ μ').sub (integrable_scaleConv_mul hκ ht μ ν')).sub
    (integrable_scaleConv_mul hκ ht ν μ')).add (integrable_scaleConv_mul hκ ht ν ν')

theorem integral_scaleConv_sub_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] :
    ∫ y, (scaleConv κ t μ y - scaleConv κ t ν y) * (scaleConv κ t μ' y - scaleConv κ t ν' y) =
      scalePair κ t μ ν μ' ν' := by
  have e : (fun y => (scaleConv κ t μ y - scaleConv κ t ν y) *
      (scaleConv κ t μ' y - scaleConv κ t ν' y)) = fun y =>
      scaleConv κ t μ y * scaleConv κ t μ' y - scaleConv κ t μ y * scaleConv κ t ν' y -
        scaleConv κ t ν y * scaleConv κ t μ' y + scaleConv κ t ν y * scaleConv κ t ν' y := by
    funext y; ring
  rw [e, integral_add _ (integrable_scaleConv_mul hκ ht ν ν'),
    integral_sub _ (integrable_scaleConv_mul hκ ht ν μ'),
    integral_sub (integrable_scaleConv_mul hκ ht μ μ') (integrable_scaleConv_mul hκ ht μ ν'),
    integral_scaleConv_mul hκ ht, integral_scaleConv_mul hκ ht, integral_scaleConv_mul hκ ht,
    integral_scaleConv_mul hκ ht]
  · rfl
  · exact (integrable_scaleConv_mul hκ ht μ μ').sub (integrable_scaleConv_mul hκ ht μ ν')
  · exact ((integrable_scaleConv_mul hκ ht μ μ').sub (integrable_scaleConv_mul hκ ht μ ν')).sub
      (integrable_scaleConv_mul hκ ht ν μ')

end FixedScale

/-! ### Band functions, pairability and the covariance formula -/

section Band

variable {κ : Rd d → ℝ}

theorem bandFun_apply (S : Set ℝ) (μ : Measure (Rd d)) (p : ℝ × Rd d) :
    bandFun κ S μ p = S.indicator (fun t => scaleConv κ t μ p.2) p.1 := rfl

theorem bandFun_eq_indicator (S : Set ℝ) (μ : Measure (Rd d)) :
    bandFun κ S μ = (S ×ˢ univ).indicator fun p => scaleConv κ p.1 μ p.2 := by
  funext p
  by_cases h : p.1 ∈ S
  · rw [bandFun_apply, indicator_of_mem h, indicator_of_mem (mk_mem_prod h (mem_univ p.2))]
  · rw [bandFun_apply, indicator_of_notMem h,
      indicator_of_notMem fun hp => h (mem_prod.1 hp).1]

theorem measurable_scaleConv_uncurry (hκ : IsLFPPKernel κ) (μ : Measure (Rd d)) [SFinite μ] :
    Measurable fun p : ℝ × Rd d => scaleConv κ p.1 μ p.2 :=
  ((measurable_scaleKernel_prod hκ).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem measurable_bandFun (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (μ : Measure (Rd d)) [SFinite μ] : Measurable (bandFun κ S μ) := by
  rw [bandFun_eq_indicator]
  exact (measurable_scaleConv_uncurry hκ μ).indicator (hS.prod MeasurableSet.univ)

/-- The difference of two band functions on a slice `t ∈ S`. -/
theorem bandFun_sub_apply_of_mem {S : Set ℝ} (μ ν : Measure (Rd d)) {t : ℝ} (ht : t ∈ S)
    (y : Rd d) :
    bandFun κ S μ (t, y) - bandFun κ S ν (t, y) = scaleConv κ t μ y - scaleConv κ t ν y := by
  rw [bandFun_apply, bandFun_apply, indicator_of_mem ht, indicator_of_mem ht]

theorem bandFun_apply_of_notMem {S : Set ℝ} (μ : Measure (Rd d)) {p : ℝ × Rd d}
    (hp : p.1 ∉ S) : bandFun κ S μ p = 0 := by
  rw [bandFun_apply, indicator_of_notMem hp]

/-- **Tonelli for band functions**: `∫ |F^S_μ - F^S_ν|² = ∫_S scalePair κ t μ ν μ ν dt` (in
`ℝ≥0∞`). -/
theorem lintegral_bandFun_sub_sq (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫⁻ p, ENNReal.ofReal ((bandFun κ S μ p - bandFun κ S ν p) ^ 2) =
      ∫⁻ t in S, ENNReal.ofReal (scalePair κ t μ ν μ ν) := by
  have hm : Measurable fun p => ENNReal.ofReal ((bandFun κ S μ p - bandFun κ S ν p) ^ 2) :=
    (((measurable_bandFun hκ hS μ).sub (measurable_bandFun hκ hS ν)).pow_const 2).ennreal_ofReal
  rw [show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl,
    lintegral_prod _ hm.aemeasurable, ← lintegral_indicator hS]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ S
  · rw [indicator_of_mem ht]
    have ht0 : 0 < t := hS0 ht
    simp_rw [bandFun_sub_apply_of_mem μ ν ht]
    rw [← ofReal_integral_eq_lintegral_ofReal, ← integral_scaleConv_sub_mul hκ ht0]
    · simp_rw [sq]
    · simp_rw [sq]
      exact integrable_scaleConv_sub_mul hκ ht0 μ ν μ ν
    · exact Eventually.of_forall fun y => sq_nonneg _
  · rw [indicator_of_notMem ht]
    simp only [bandFun_apply_of_notMem μ (p := (t, _)) ht, bandFun_apply_of_notMem ν (p := (t, _)) ht,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero,
      lintegral_zero]

/-- **Pairability criterion**: for `S ⊆ (0, ∞)` and finite measures,
`IsPairable κ S μ ν ↔ ∫_S scalePair κ t μ ν μ ν dt < ∞`. -/
theorem isPairable_iff_lintegral (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsPairable κ S μ ν ↔ ∫⁻ t in S, ENNReal.ofReal (scalePair κ t μ ν μ ν) < ⊤ := by
  have hm : Measurable (bandFun κ S μ - bandFun κ S ν) :=
    (measurable_bandFun hκ hS μ).sub (measurable_bandFun hκ hS ν)
  rw [IsPairable, memLp_two_iff_integrable_sq hm.aestronglyMeasurable,
    ← lintegral_bandFun_sub_sq hκ hS hS0 μ ν]
  have h0 : 0 ≤ᵐ[volume] fun p => (bandFun κ S μ - bandFun κ S ν) p ^ 2 :=
    Eventually.of_forall fun p => sq_nonneg _
  constructor
  · intro h
    exact (hasFiniteIntegral_iff_ofReal h0).1 h.2
  · intro h
    exact ⟨(hm.pow_const 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).2 h⟩

/-- Pairability from an integrable majorant of the scale density. -/
theorem isPairable_of_le (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : ℝ → ℝ} (hg : IntegrableOn g S) (hle : ∀ t ∈ S, scalePair κ t μ ν μ ν ≤ g t) :
    IsPairable κ S μ ν := by
  rw [isPairable_iff_lintegral hκ hS hS0]
  calc ∫⁻ t in S, ENNReal.ofReal (scalePair κ t μ ν μ ν)
      ≤ ∫⁻ t in S, ENNReal.ofReal (g t) :=
        setLIntegral_mono' hS fun t ht => ENNReal.ofReal_le_ofReal (hle t ht)
    _ < ⊤ := Integrable.lintegral_lt_top hg

theorem bandVecM_eq_toLp {S : Set ℝ} {μ ν : Measure (Rd d)} (h : IsPairable κ S μ ν) :
    bandVecM κ S μ ν = h.toLp _ := by
  rw [bandVecM, dite_eq_left h]

theorem bandVecM_of_not {S : Set ℝ} {μ ν : Measure (Rd d)} (h : ¬IsPairable κ S μ ν) :
    bandVecM κ S μ ν = 0 := by
  rw [bandVecM, dite_eq_right h]

theorem coeFn_bandVecM {S : Set ℝ} {μ ν : Measure (Rd d)} (h : IsPairable κ S μ ν) :
    (bandVecM κ S μ ν : ℝ × Rd d → ℝ) =ᵐ[volume] bandFun κ S μ - bandFun κ S ν := by
  rw [bandVecM_eq_toLp h]
  exact MemLp.coeFn_toLp _

/-- `⟪bandVecM κ S μ ν, bandVecM κ S' μ' ν'⟫ = ∫ (F^S_μ - F^S_ν)(F^{S'}_{μ'} - F^{S'}_{ν'})`. -/
theorem inner_bandVecM_eq_integral {S S' : Set ℝ} {μ ν μ' ν' : Measure (Rd d)}
    (h : IsPairable κ S μ ν) (h' : IsPairable κ S' μ' ν') :
    ⟪bandVecM κ S μ ν, bandVecM κ S' μ' ν'⟫ =
      ∫ p, (bandFun κ S μ p - bandFun κ S ν p) * (bandFun κ S' μ' p - bandFun κ S' ν' p) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bandVecM h, coeFn_bandVecM h'] with p h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
  simp only [Pi.sub_apply, conj_trivial, mul_comm, RCLike.mul_re, RCLike.re_to_real,
    RCLike.im_to_real, mul_zero, sub_zero]

/-- **The covariance formula** (target T1):
`scaleCov κ S μ ν μ' ν' = ∫_S ∫∫ t⁻¹ C(t⁻¹(z - w)) (μ - ν)(dz) (μ' - ν')(dw) dt`
for pairable pairs and `S ⊆ (0, ∞)`. -/
theorem scaleCov_eq_integral (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (h : IsPairable κ S μ ν)
    (h' : IsPairable κ S μ' ν') :
    scaleCov κ S μ ν μ' ν' = ∫ t in S, scalePair κ t μ ν μ' ν' := by
  have hint : Integrable fun p => (bandFun κ S μ p - bandFun κ S ν p) *
      (bandFun κ S μ' p - bandFun κ S ν' p) := h.integrable_mul h'
  rw [scaleCov, inner_bandVecM_eq_integral h h',
    show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl, integral_prod _ hint,
    ← integral_indicator hS]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ S
  · simp only [indicator_of_mem ht, bandFun_sub_apply_of_mem _ _ ht]
    exact integral_scaleConv_sub_mul hκ (hS0 ht) μ ν μ' ν'
  · simp only [indicator_of_notMem ht, bandFun_apply_of_notMem _ (p := (t, _)) ht, sub_self,
      mul_zero, integral_zero]

end Band

/-! ### Point vectors, bilinearity and the Gram property -/

section Algebra

variable {κ : Rd d → ℝ}

theorem bandFun_zero_measure (S : Set ℝ) : bandFun κ S (0 : Measure (Rd d)) = 0 := by
  funext p
  simp only [bandFun, integral_zero_measure, indicator_zero, Pi.zero_apply]

/-- The band function of a Dirac mass is P-F1's point kernel `k_{a,b,z}`. -/
theorem bandFun_dirac (a b : ℝ) (z : Rd d) :
    bandFun κ (Ioo a b) (Measure.dirac z) = bandKernel κ a b z := by
  funext p
  simp only [bandFun, bandKernel, integral_dirac]

/-- **Compatibility with the point vectors** (target T1): `bandVecM κ (a, b) δ_z 0 = k_{a,b,z}`
(the frozen `bandVec`), for all `a, b, z`. -/
theorem bandVecM_dirac_zero (a b : ℝ) (z : Rd d) :
    bandVecM κ (Ioo a b) (Measure.dirac z) 0 = bandVec κ a b z := by
  have e : bandFun κ (Ioo a b) (Measure.dirac z) - bandFun κ (Ioo a b) 0 = bandKernel κ a b z := by
    rw [bandFun_dirac, bandFun_zero_measure, sub_zero]
  by_cases h : MemLp (bandKernel κ a b z) 2 volume
  · have h' : IsPairable κ (Ioo a b) (Measure.dirac z) 0 := by rw [IsPairable, e]; exact h
    rw [bandVecM_eq_toLp h', bandVec, dite_eq_left h]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun e))
  · have h' : ¬IsPairable κ (Ioo a b) (Measure.dirac z) 0 := by rw [IsPairable, e]; exact h
    rw [bandVecM_of_not h', bandVec, dite_eq_right h]

theorem scaleConv_add (hκ : IsLFPPKernel κ) (t : ℝ) (μ₁ μ₂ : Measure (Rd d)) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (y : Rd d) :
    scaleConv κ t (μ₁ + μ₂) y = scaleConv κ t μ₁ y + scaleConv κ t μ₂ y :=
  integral_add_measure (integrable_scaleKernel_sub hκ t y μ₁) (integrable_scaleKernel_sub hκ t y μ₂)

theorem bandFun_add (hκ : IsLFPPKernel κ) (S : Set ℝ) (μ₁ μ₂ : Measure (Rd d))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    bandFun κ S (μ₁ + μ₂) = bandFun κ S μ₁ + bandFun κ S μ₂ := by
  funext p
  simp only [Pi.add_apply, bandFun_apply]
  have e : (fun t => scaleConv κ t (μ₁ + μ₂) p.2) =
      fun t => scaleConv κ t μ₁ p.2 + scaleConv κ t μ₂ p.2 :=
    funext fun t => scaleConv_add hκ t μ₁ μ₂ p.2
  rw [e, indicator_add]

theorem IsPairable.add (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ₁ ν₁ μ₂ ν₂ : Measure (Rd d)}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h₁ : IsPairable κ S μ₁ ν₁) (h₂ : IsPairable κ S μ₂ ν₂) :
    IsPairable κ S (μ₁ + μ₂) (ν₁ + ν₂) := by
  have e : bandFun κ S (μ₁ + μ₂) - bandFun κ S (ν₁ + ν₂) =
      (bandFun κ S μ₁ - bandFun κ S ν₁) + (bandFun κ S μ₂ - bandFun κ S ν₂) := by
    rw [bandFun_add hκ, bandFun_add hκ]; abel
  rw [IsPairable, e]
  exact MemLp.add h₁ h₂

theorem isPairable_comm {S : Set ℝ} {μ ν : Measure (Rd d)} :
    IsPairable κ S μ ν ↔ IsPairable κ S ν μ := by
  rw [IsPairable, IsPairable, ← neg_sub, memLp_neg_iff]

theorem bandVecM_self (S : Set ℝ) (μ : Measure (Rd d)) : bandVecM κ S μ μ = 0 := by
  have h : IsPairable κ S μ μ := by rw [IsPairable, sub_self]; exact MemLp.zero
  refine Lp.ext ?_
  filter_upwards [coeFn_bandVecM h, Lp.coeFn_zero (E := ℝ) (p := 2)
    (μ := (volume : Measure (ℝ × Rd d)))] with p hp1 hp2
  rw [hp1, hp2]
  simp only [Pi.sub_apply, sub_self, Pi.zero_apply]
theorem IsPairable.sub (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ ν μ' ν' : Measure (Rd d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (h : IsPairable κ S μ ν) (h' : IsPairable κ S μ' ν') :
    IsPairable κ S (μ + ν') (ν + μ') :=
  IsPairable.add hκ h (isPairable_comm.1 h')


end Algebra

/-! ### Scale sets -/

section ScaleSets

variable {κ : Rd d → ℝ}

end ScaleSets

/-! ### Bounds on `mixInt` and pairability -/

section Pairability

variable {κ : Rd d → ℝ}

/-- `mixInt` of a constant: `c (μ(ℝ^d) - ν(ℝ^d)) (μ'(ℝ^d) - ν'(ℝ^d))`. -/
theorem mixInt_const (c : ℝ) (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] :
    mixInt (fun _ _ => c) μ ν μ' ν' =
      c * ((μ.real univ - ν.real univ) * (μ'.real univ - ν'.real univ)) := by
  simp only [mixInt, integral_const, smul_eq_mul, ← univ_prod_univ, measureReal_prod_prod]
  ring

/-- `mixInt` is additive in the integrand (given integrability on the four products). -/
theorem mixInt_sub {g₁ g₂ : Rd d → Rd d → ℝ} {μ ν μ' ν' : Measure (Rd d)}
    (h1 : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => g₁ p.1 p.2) (α.prod β))
    (h2 : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => g₂ p.1 p.2) (α.prod β)) :
    mixInt (fun z w => g₁ z w - g₂ z w) μ ν μ' ν' = mixInt g₁ μ ν μ' ν' - mixInt g₂ μ ν μ' ν' := by
  simp only [mixInt]
  rw [integral_sub (h1 μ μ' (Or.inl rfl) (Or.inl rfl)) (h2 μ μ' (Or.inl rfl) (Or.inl rfl)),
    integral_sub (h1 μ ν' (Or.inl rfl) (Or.inr rfl)) (h2 μ ν' (Or.inl rfl) (Or.inr rfl)),
    integral_sub (h1 ν μ' (Or.inr rfl) (Or.inl rfl)) (h2 ν μ' (Or.inr rfl) (Or.inl rfl)),
    integral_sub (h1 ν ν' (Or.inr rfl) (Or.inr rfl)) (h2 ν ν' (Or.inr rfl) (Or.inr rfl))]
  ring

/-- Integrability of a continuous bounded kernel of `z - w` against finite product measures. -/
theorem integrable_autoCorr_div (hκ : IsLFPPKernel κ) (t : ℝ) (α β : Measure (Rd d))
    [IsFiniteMeasure α] [IsFiniteMeasure β] :
    Integrable (fun p : Rd d × Rd d => autoCorr κ (t⁻¹ • (p.1 - p.2)) / t) (α.prod β) := by
  refine Integrable.of_bound (((continuous_autoCorr hκ).comp
    ((continuous_fst.sub continuous_snd).const_smul t⁻¹)).div_const t).aestronglyMeasurable
    (|t⁻¹|) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_div, div_eq_mul_inv, abs_inv]
  calc |autoCorr κ (t⁻¹ • (p.1 - p.2))| * |t|⁻¹ ≤ 1 * |t|⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 (abs_nonneg t))
    _ = |t|⁻¹ := one_mul _

/-- With equal masses of the first pair, any constant can be subtracted from the integrand:
`scalePair κ t μ ν μ' ν' = ∫∫ (C(t⁻¹(z - w))/t - c₀) (μ - ν)(dz) (μ' - ν')(dw)`. -/
theorem scalePair_eq_mixInt_sub_const (hκ : IsLFPPKernel κ) (t c₀ : ℝ)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] (hmass : μ.real univ = ν.real univ) :
    scalePair κ t μ ν μ' ν' =
      mixInt (fun z w => autoCorr κ (t⁻¹ • (z - w)) / t - c₀) μ ν μ' ν' := by
  rw [mixInt_sub (g₁ := fun z w => autoCorr κ (t⁻¹ • (z - w)) / t) (g₂ := fun _ _ => c₀)]
  · rw [mixInt_const, hmass, sub_self, zero_mul, mul_zero, sub_zero]
    rfl
  · rintro α β (rfl | rfl) (rfl | rfl) <;> exact integrable_autoCorr_div hκ t _ _
  · rintro α β (rfl | rfl) (rfl | rfl) <;> exact integrable_const _

end Pairability

end HigherDimLFPP
