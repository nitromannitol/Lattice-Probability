/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.HypothesisTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingDef
import LatticeProb.Bonanno.ReflectedGMS.GMS.HypothesisTransferSplit
import Mathlib.Util.AssertNoSorry

/-!
# Transfer of GMS's hypotheses to the general-cell environment law

GMS Theorem 1.16 (`Theorem116Statement.Theorem1_16`) is proved as a corollary of the general-cell
main theorems, applied to the raw-code law `P := μ.map codeMap`.  This file transfers GMS's four
hypotheses on `μ` to the hypotheses of those theorems on `generalLaw P hP`, and pulls almost-sure
statements under `validLaw P hV` back to `μ`.

Inputs proved in other packets are explicit hypotheses:

* `hmeas : Measurable codeMap`;
* `hgood : MeasurableSet {H | H.1.LineConnected}`;
* `hvalid : ∀ H, H.1.LineConnected → ValidGeneral H.1.code`;
* `hinv`, `hsim` — similar configurations are line connected together, and between line-connected
  configurations GMS similarity is a general similarity of the codes;
* for (FE), `hdensPi` / `hdensPiStar` — at a line-connected configuration, each half of the rooted
  (FE) integrand of its code is bounded by GMS's corresponding integrand at any cell containing `0`;
* for `SupportedOnValidGeneral`, a **measurable core**: a Borel set `C` of codes, contained in
  `ValidGeneral`, containing the code of every line-connected configuration.

**Why a measurable core is needed.**  `ValidGeneral` is not known to be a Borel set of codes, and
the pushforward of `μ` is carried by a non-measurable set `S` only if some measurable subset of `S`
has full measure: an almost-sure statement under `μ.map codeMap` is about the outer measure of the
exceptional set, and `codeMap '' {LineConnected}` need not be Borel.  (With a Bernstein set `S`,
the trace law on `S` pushed into `[0,1]` is Lebesgue measure, which does not charge `S` in the
almost-sure sense.)  `hmeas`, `hgood`, `hvalid` alone therefore do not give
`SupportedOnValidGeneral (μ.map codeMap)`; `supportedOnValidGeneral_map_of_measurableSet_image`
states the special case `C = codeMap '' {LineConnected}`.

Main results (namespace `ReflectedGMS.GMS`):

* `supportedOnValidGeneral_map` — `SupportedOnValidGeneral (μ.map codeMap)`;
* `map_goodEnv` — `generalLaw (μ.map codeMap) hP` is the pushforward of `μ` under the measurable
  lift `goodEnv` to general environments;
* `massTransport_ennreal` — GMS's mass transport, stated for `ℝ≥0`-valued kernels, extends to
  `ℝ≥0∞`-valued ones (covariant truncation `min(F, n |w₀ − w₁|⁻²)` and monotone convergence);
* `massTransport_generalLaw`, `finiteEnergyMoment_generalLaw`, `environmentErgodic_generalLaw`;
* `ae_of_ae_validLaw` — pull-back of `validLaw`-almost-sure statements, with no measurability of
  the predicate.

The theorems about `generalLaw` take an arbitrary proof `hP` of `SupportedOnValidGeneral`.

Searched before writing: `supportedLaw_unique` (reused, for the lift), `lintegral_map_le` (reused:
an upper bound for lower integrals against a pushforward, with no measurability of the integrand),
`Measure.map_congr`, `lintegral_iSup`, `inf_iSup_eq`, `ENNReal.iSup_natCast`,
`ae_iff_exists_measurable_null_set` (project), and `GeneralLawTransfer` (the analogous transfer of
kernels, ergodicity and (FE) between `generalLaw` and `validLaw`, whose structure is followed).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.GMS

open Code GeneralLaws

/-! ### The raw-code law is carried by general environments -/

/-- A measurable set of general codes of full `μ`-measure under `codeMap` carries the raw law. -/
theorem supportedOnValidGeneral_map_of_ae_mem {μ : Measure GMSSpace} (hmeas : Measurable codeMap)
    {C : Set RawCode} (hC : MeasurableSet C) (hCval : ∀ r ∈ C, ValidGeneral r)
    (hCae : ∀ᵐ H ∂μ, codeMap H ∈ C) : SupportedOnValidGeneral (μ.map codeMap) :=
  ((ae_map_iff hmeas.aemeasurable hC).2 hCae).mono hCval

/-- **GMS configurations give a raw law carried by general environments**, given a measurable core
`C ⊆ ValidGeneral` containing the codes of the line-connected configurations. -/
theorem supportedOnValidGeneral_map {μ : Measure GMSSpace} (hmeas : Measurable codeMap)
    (hL : ConnectedAlongLines μ) {C : Set RawCode} (hC : MeasurableSet C)
    (hCval : ∀ r ∈ C, ValidGeneral r) (hCgood : ∀ H : GMSSpace, H.1.LineConnected → codeMap H ∈ C) :
    SupportedOnValidGeneral (μ.map codeMap) :=
  supportedOnValidGeneral_map_of_ae_mem hmeas hC hCval
    (((connectedAlongLines_iff μ).1 hL).mono hCgood)

/-- The special case where the image of the line-connected configurations is itself Borel. -/
theorem supportedOnValidGeneral_map_of_measurableSet_image {μ : Measure GMSSpace}
    (hmeas : Measurable codeMap)
    (hvalid : ∀ H : GMSSpace, H.1.LineConnected → ValidGeneral H.1.code)
    (hL : ConnectedAlongLines μ)
    (himg : MeasurableSet (codeMap '' {H : GMSSpace | H.1.LineConnected})) :
    SupportedOnValidGeneral (μ.map codeMap) :=
  supportedOnValidGeneral_map hmeas hL himg
    (by
      rintro r ⟨H, hH, rfl⟩
      exact hvalid H hH)
    (fun H hH => ⟨H, hH, rfl⟩)

/-! ### The lift to general environments -/

section Lift

variable (hvalid : ∀ H : GMSSpace, H.1.LineConnected → ValidGeneral H.1.code)

open Classical in
/-- The code of a line-connected configuration as a general environment; a fixed environment `d`
otherwise. -/
noncomputable def goodEnv (d : EnvGeneral) (H : GMSSpace) : EnvGeneral :=
  if h : H.1.LineConnected then ⟨H.1.code, hvalid H h⟩ else d

theorem goodEnv_of_lineConnected (d : EnvGeneral) (H : GMSSpace) (h : H.1.LineConnected) :
    goodEnv hvalid d H = ⟨H.1.code, hvalid H h⟩ := by
  classical
  exact dif_pos h

theorem goodEnv_of_not_lineConnected (d : EnvGeneral) (H : GMSSpace) (h : ¬ H.1.LineConnected) :
    goodEnv hvalid d H = d := by
  classical
  exact dif_neg h

theorem measurable_goodEnv (hmeas : Measurable codeMap)
    (hgood : MeasurableSet {H : GMSSpace | H.1.LineConnected}) (d : EnvGeneral) :
    Measurable (goodEnv hvalid d) := by
  classical
  have hval : (fun H => (goodEnv hvalid d H).val) =
      fun H => if H.1.LineConnected then codeMap H else d.val := by
    funext H
    by_cases h : H.1.LineConnected
    · rw [goodEnv_of_lineConnected hvalid d H h, if_pos h]
      rfl
    · rw [goodEnv_of_not_lineConnected hvalid d H h, if_neg h]
  have hm : Measurable fun H => (goodEnv hvalid d H).val := by
    rw [hval]
    exact Measurable.ite hgood hmeas measurable_const
  exact hm.subtype_mk

/-- **The general-environment law is the pushforward of `μ` under the lift.** -/
theorem map_goodEnv {μ : Measure GMSSpace} [IsProbabilityMeasure μ] (hmeas : Measurable codeMap)
    (hgood : MeasurableSet {H : GMSSpace | H.1.LineConnected}) (hL : ConnectedAlongLines μ)
    (hP : SupportedOnValidGeneral (μ.map codeMap)) (d : EnvGeneral) :
    μ.map (goodEnv hvalid d) = generalLaw (μ.map codeMap) hP := by
  have h : (μ.map (goodEnv hvalid d)).map (Subtype.val : EnvGeneral → RawCode) =
      μ.map codeMap := by
    rw [Measure.map_map measurable_subtype_coe (measurable_goodEnv hvalid hmeas hgood d)]
    refine Measure.map_congr ?_
    filter_upwards [(connectedAlongLines_iff μ).1 hL] with H hH
    show (goodEnv hvalid d H).val = codeMap H
    rw [goodEnv_of_lineConnected hvalid d H hH]
    rfl
  exact supportedLaw_unique (μ.map codeMap) {r | ValidGeneral r} hP _ h

end Lift

/-- A general environment, from the almost-sure line connectivity of a probability law. -/
theorem exists_envGeneral (hvalid : ∀ H : GMSSpace, H.1.LineConnected → ValidGeneral H.1.code)
    {μ : Measure GMSSpace} [IsProbabilityMeasure μ] (hL : ConnectedAlongLines μ) :
    Nonempty EnvGeneral := by
  obtain ⟨H, hH⟩ := ((connectedAlongLines_iff μ).1 hL).exists
  exact ⟨⟨H.1.code, hvalid H hH⟩⟩

/-! ### Mass transport for `ℝ≥0∞`-valued kernels -/

/-- `|w₀ − w₁|⁻²` as an extended real (`0` on the diagonal). -/
noncomputable def invDistSq (p : Plane × Plane) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist p.1 p.2 ^ 2)⁻¹)

theorem measurable_invDistSq : Measurable invDistSq :=
  ((continuous_dist.measurable.pow_const 2).inv).ennreal_ofReal

theorem invDistSq_ne_zero {p : Plane × Plane} (hp : p.1 ≠ p.2) : invDistSq p ≠ 0 :=
  (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (dist_pos.2 hp) 2))).ne'

theorem invDistSq_similarity {s : ℝ} (hs : 0 < s) (u w₀ w₁ : Plane) :
    invDistSq (positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * invDistSq (w₀, w₁) := by
  show ENNReal.ofReal ((dist (positiveSimilarity s u w₀) (positiveSimilarity s u w₁) ^ 2)⁻¹) =
    ENNReal.ofReal ((s ^ 2)⁻¹) * ENNReal.ofReal ((dist w₀ w₁ ^ 2)⁻¹)
  rw [positiveSimilarity_apply, positiveSimilarity_apply, dist_smul₀, dist_sub_right,
    Real.norm_of_nonneg hs.le, mul_pow, mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg s))]

section Truncation

variable (F : GMSSpace × Plane × Plane → ℝ≥0∞)

/-- The covariant truncation `min(F, n |w₀ − w₁|⁻²)`. -/
noncomputable def truncateKernel (n : ℕ) (x : GMSSpace × Plane × Plane) : ℝ≥0∞ :=
  min (F x) ((n : ℝ≥0∞) * invDistSq x.2)

theorem truncateKernel_ne_top (n : ℕ) (x : GMSSpace × Plane × Plane) :
    truncateKernel F n x ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top)
    (min_le_right _ _)

theorem measurable_truncateKernel (hF : Measurable F) (n : ℕ) :
    Measurable (truncateKernel F n) :=
  hF.min (measurable_const.mul (measurable_invDistSq.comp measurable_snd))

theorem truncateKernel_mono (x : GMSSpace × Plane × Plane) :
    Monotone fun n : ℕ => truncateKernel F n x := fun _ _ hmn =>
  min_le_min le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hmn) zero_le)

theorem iSup_truncateKernel (x : GMSSpace × Plane × Plane) (hx : x.2.1 ≠ x.2.2) :
    ⨆ n : ℕ, truncateKernel F n x = F x := by
  have htop : ⨆ n : ℕ, (n : ℝ≥0∞) * invDistSq x.2 = ∞ := by
    rw [← ENNReal.iSup_mul, ENNReal.iSup_natCast, ENNReal.top_mul (invDistSq_ne_zero hx)]
  calc ⨆ n : ℕ, truncateKernel F n x = ⨆ n : ℕ, F x ⊓ ((n : ℝ≥0∞) * invDistSq x.2) := rfl
    _ = F x ⊓ ⨆ n : ℕ, (n : ℝ≥0∞) * invDistSq x.2 := (inf_iSup_eq _ _).symm
    _ = F x := by rw [htop, inf_top_eq]

theorem truncateKernel_similarity {s : ℝ} (hs : 0 < s) (u : Plane) {H H' : GMSSpace}
    (hF : ∀ w₀ w₁ : Plane, F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * F (H, w₀, w₁)) (n : ℕ) (w₀ w₁ : Plane) :
    truncateKernel F n (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * truncateKernel F n (H, w₀, w₁) := by
  show min (F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁))
      ((n : ℝ≥0∞) * invDistSq (positiveSimilarity s u w₀, positiveSimilarity s u w₁)) =
    ENNReal.ofReal ((s ^ 2)⁻¹) * min (F (H, w₀, w₁)) ((n : ℝ≥0∞) * invDistSq (w₀, w₁))
  rw [hF, invDistSq_similarity hs, mul_left_comm]
  exact (Monotone.map_min (f := fun a => ENNReal.ofReal ((s ^ 2)⁻¹) * a)
    fun _ _ hab => mul_le_mul_of_nonneg_left hab zero_le).symm

/-- The `ℝ≥0`-valued truncation, the form GMS's mass transport accepts. -/
noncomputable def truncateKernelNN (n : ℕ) (x : GMSSpace × Plane × Plane) : ℝ≥0 :=
  (truncateKernel F n x).toNNReal

theorem coe_truncateKernelNN (n : ℕ) (x : GMSSpace × Plane × Plane) :
    (truncateKernelNN F n x : ℝ≥0∞) = truncateKernel F n x :=
  ENNReal.coe_toNNReal (truncateKernel_ne_top F n x)

theorem truncateKernelNN_similarity {s : ℝ} (hs : 0 < s) (u : Plane) {H H' : GMSSpace}
    (hF : ∀ w₀ w₁ : Plane, F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * F (H, w₀, w₁)) (n : ℕ) (w₀ w₁ : Plane) :
    (truncateKernelNN F n (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) : ℝ) =
      (s ^ 2)⁻¹ * (truncateKernelNN F n (H, w₀, w₁) : ℝ) := by
  simp only [truncateKernelNN, ENNReal.coe_toNNReal_eq_toReal]
  rw [truncateKernel_similarity F hs u hF n w₀ w₁, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg s))]

/-- The double integral of `F` along `w ↦ σ w` is the supremum of those of its truncations,
provided `σ w` is off the diagonal for `w ≠ 0`. -/
theorem lintegral_lintegral_eq_iSup_truncateKernel (μ : Measure GMSSpace) (hF : Measurable F)
    (σ : Plane → Plane × Plane) (hσ : Measurable σ) (hdiag : ∀ w : Plane, w ≠ 0 → (σ w).1 ≠ (σ w).2) :
    ∫⁻ H, ∫⁻ w, F (H, σ w) ∂volume ∂μ =
      ⨆ n : ℕ, ∫⁻ H, ∫⁻ w, truncateKernel F n (H, σ w) ∂volume ∂μ := by
  have hne : ∀ᵐ w ∂(volume : Measure Plane), w ∉ ({0} : Set Plane) :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : Plane))
  have hinner : ∀ H : GMSSpace, ∫⁻ w, F (H, σ w) ∂volume =
      ⨆ n : ℕ, ∫⁻ w, truncateKernel F n (H, σ w) ∂volume := by
    intro H
    rw [← lintegral_iSup (f := fun n w => truncateKernel F n (H, σ w))
      (fun n => (measurable_truncateKernel F hF n).comp (measurable_const.prodMk hσ))
      (fun m n hmn w => truncateKernel_mono F (H, σ w) hmn)]
    refine lintegral_congr_ae ?_
    filter_upwards [hne] with w hw
    exact (iSup_truncateKernel F (H, σ w) (hdiag w hw)).symm
  have hmeasH : ∀ n : ℕ, Measurable fun H : GMSSpace =>
      ∫⁻ w, truncateKernel F n (H, σ w) ∂volume := fun n =>
    ((measurable_truncateKernel F hF n).comp
      (measurable_fst.prodMk (hσ.comp measurable_snd))).lintegral_prod_right'
  calc ∫⁻ H, ∫⁻ w, F (H, σ w) ∂volume ∂μ
      = ∫⁻ H, ⨆ n : ℕ, ∫⁻ w, truncateKernel F n (H, σ w) ∂volume ∂μ :=
        lintegral_congr fun H => hinner H
    _ = ⨆ n : ℕ, ∫⁻ H, ∫⁻ w, truncateKernel F n (H, σ w) ∂volume ∂μ :=
        lintegral_iSup hmeasH fun m n hmn H =>
          lintegral_mono fun w => truncateKernel_mono F (H, σ w) hmn

/-- **GMS's mass transport extends to `ℝ≥0∞`-valued kernels.**  GMS state Definition 1.2(4) for
`[0,∞)`-valued kernels; a measurable `[0,∞]`-valued kernel of degree `−2` is the increasing limit of
the covariant finite truncations `min(F, n |w₀ − w₁|⁻²)`, which agree with `F` off the diagonal. -/
theorem massTransport_ennreal {μ : Measure GMSSpace} (hMT : MassTransport μ) (hF : Measurable F)
    (hcov : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ w₀ w₁ : Plane, F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * F (H, w₀, w₁)) :
    ∫⁻ H, ∫⁻ w, F (H, 0, w) ∂volume ∂μ = ∫⁻ H, ∫⁻ w, F (H, w, 0) ∂volume ∂μ := by
  have hn : ∀ n : ℕ, ∫⁻ H, ∫⁻ w, truncateKernel F n (H, 0, w) ∂volume ∂μ =
      ∫⁻ H, ∫⁻ w, truncateKernel F n (H, w, 0) ∂volume ∂μ := by
    intro n
    have h := hMT (truncateKernelNN F n)
      ((measurable_truncateKernel F hF n).ennreal_toNNReal)
      (fun s u hs H H' hHH' w₀ w₁ =>
        truncateKernelNN_similarity F hs u (hcov s u hs H H' hHH') n w₀ w₁)
    simpa only [coe_truncateKernelNN] using h
  rw [lintegral_lintegral_eq_iSup_truncateKernel F μ hF (fun w => ((0 : Plane), w))
      (measurable_const.prodMk measurable_id) (fun w hw => (Ne.symm hw)),
    lintegral_lintegral_eq_iSup_truncateKernel F μ hF (fun w => (w, (0 : Plane)))
      (measurable_id.prodMk measurable_const) (fun w hw => hw)]
  exact iSup_congr hn

end Truncation

/-! ### Mass transport -/

section Transfer

variable (hvalid : ∀ H : GMSSpace, H.1.LineConnected → ValidGeneral H.1.code)

open Classical in
/-- A general transport kernel read on GMS configurations through the lift, extended by zero off
the line-connected configurations. -/
noncomputable def liftKernel (d : EnvGeneral) (T : MassTransportKernel)
    (x : GMSSpace × Plane × Plane) : ℝ≥0∞ :=
  if x.1.1.LineConnected then T.toFun (goodEnv hvalid d x.1, x.2) else 0

open Classical in
theorem liftKernel_apply (d : EnvGeneral) (T : MassTransportKernel) (H : GMSSpace)
    (w : Plane × Plane) :
    liftKernel hvalid d T (H, w) =
      if H.1.LineConnected then T.toFun (goodEnv hvalid d H, w) else 0 := by
  classical
  rfl

theorem measurable_liftKernel (hmeas : Measurable codeMap)
    (hgood : MeasurableSet {H : GMSSpace | H.1.LineConnected}) (d : EnvGeneral)
    (T : MassTransportKernel) : Measurable (liftKernel hvalid d T) := by
  classical
  exact Measurable.ite (measurable_fst hgood)
    (T.measurable_toFun.comp
      (((measurable_goodEnv hvalid hmeas hgood d).comp measurable_fst).prodMk measurable_snd))
    measurable_const

/-- The lifted kernel is covariant for GMS similarities. -/
theorem liftKernel_similarity
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      (H.1.LineConnected ↔ H'.1.LineConnected))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace) (hL : H.1.LineConnected)
      (hL' : H'.1.LineConnected), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨H.1.code, hvalid H hL⟩ ⟨H'.1.code, hvalid H' hL'⟩)
    (d : EnvGeneral) (T : MassTransportKernel) (s : ℝ) (u : Plane) (hs : 0 < s)
    (H H' : GMSSpace) (hHH' : IsSimilar s u hs H H') (w₀ w₁ : Plane) :
    liftKernel hvalid d T (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * liftKernel hvalid d T (H, w₀, w₁) := by
  classical
  rw [liftKernel_apply, liftKernel_apply]
  by_cases hH : H.1.LineConnected
  · have hH' : H'.1.LineConnected := (hinv s u hs H H' hHH').1 hH
    rw [if_pos hH, if_pos hH', goodEnv_of_lineConnected hvalid d H hH,
      goodEnv_of_lineConnected hvalid d H' hH']
    exact T.covariant s u hs _ _ (hsim s u hs H H' hH hH' hHH') w₀ w₁
  · have hH' : ¬ H'.1.LineConnected := fun h => hH ((hinv s u hs H H' hHH').2 h)
    rw [if_neg hH, if_neg hH', mul_zero]

/-- Double integrals of a general kernel under `generalLaw` are double integrals of the lifted
kernel under `μ`. -/
theorem lintegral_generalLaw_eq_liftKernel {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable codeMap) (hgood : MeasurableSet {H : GMSSpace | H.1.LineConnected})
    (hL : ConnectedAlongLines μ) (hP : SupportedOnValidGeneral (μ.map codeMap)) (d : EnvGeneral)
    (T : MassTransportKernel) (σ : Plane → Plane × Plane) (hσ : Measurable σ) :
    ∫⁻ e, ∫⁻ w, T.toFun (e, σ w) ∂volume ∂generalLaw (μ.map codeMap) hP =
      ∫⁻ H, ∫⁻ w, liftKernel hvalid d T (H, σ w) ∂volume ∂μ := by
  classical
  have hTσ : Measurable fun e : EnvGeneral => ∫⁻ w, T.toFun (e, σ w) ∂volume :=
    (T.measurable_toFun.comp (measurable_fst.prodMk (hσ.comp measurable_snd))).lintegral_prod_right'
  rw [← map_goodEnv hvalid hmeas hgood hL hP d,
    lintegral_map hTσ (measurable_goodEnv hvalid hmeas hgood d)]
  refine lintegral_congr_ae ?_
  filter_upwards [(connectedAlongLines_iff μ).1 hL] with H hH
  refine lintegral_congr fun w => ?_
  rw [liftKernel_apply, if_pos hH]

/-- **Mass transport transfers** from GMS's configuration law to the general-environment law. -/
theorem massTransport_generalLaw {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable codeMap) (hgood : MeasurableSet {H : GMSSpace | H.1.LineConnected})
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      (H.1.LineConnected ↔ H'.1.LineConnected))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace) (hL : H.1.LineConnected)
      (hL' : H'.1.LineConnected), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨H.1.code, hvalid H hL⟩ ⟨H'.1.code, hvalid H' hL'⟩)
    (hL : ConnectedAlongLines μ) (hP : SupportedOnValidGeneral (μ.map codeMap))
    (hMT : MassTransport μ) :
    GeneralLaws.MassTransport (generalLaw (μ.map codeMap) hP) := by
  intro T
  obtain ⟨d⟩ := exists_envGeneral hvalid hL
  have h := massTransport_ennreal (liftKernel hvalid d T) hMT
    (measurable_liftKernel hvalid hmeas hgood d T)
    (liftKernel_similarity hvalid hinv hsim d T)
  rw [lintegral_generalLaw_eq_liftKernel hvalid hmeas hgood hL hP d T (fun w => ((0 : Plane), w))
      (measurable_const.prodMk measurable_id),
    lintegral_generalLaw_eq_liftKernel hvalid hmeas hgood hL hP d T (fun w => (w, (0 : Plane)))
      (measurable_id.prodMk measurable_const)]
  exact h

/-! ### Ergodicity -/

/-- **Ergodicity modulo scaling transfers** from GMS's configuration law to the
general-environment law. -/
theorem environmentErgodic_generalLaw {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable codeMap) (hgood : MeasurableSet {H : GMSSpace | H.1.LineConnected})
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      (H.1.LineConnected ↔ H'.1.LineConnected))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace) (hL : H.1.LineConnected)
      (hL' : H'.1.LineConnected), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨H.1.code, hvalid H hL⟩ ⟨H'.1.code, hvalid H' hL'⟩)
    (hL : ConnectedAlongLines μ) (hP : SupportedOnValidGeneral (μ.map codeMap))
    (hErg : ErgodicModuloScaling μ) :
    GeneralLaws.EnvironmentErgodic (generalLaw (μ.map codeMap) hP) := by
  intro A hA hAinv
  obtain ⟨d⟩ := exists_envGeneral hvalid hL
  have hg := measurable_goodEnv hvalid hmeas hgood d
  rw [← map_goodEnv hvalid hmeas hgood hL hP d, Measure.map_apply hg hA]
  let A' : Set GMSSpace := {H | H.1.LineConnected} ∩ goodEnv hvalid d ⁻¹' A
  have hA'm : MeasurableSet A' := hgood.inter (hg hA)
  have hA'inv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      (H ∈ A' ↔ H' ∈ A') := by
    intro s u hs H H' hHH'
    show (H.1.LineConnected ∧ goodEnv hvalid d H ∈ A) ↔
      (H'.1.LineConnected ∧ goodEnv hvalid d H' ∈ A)
    by_cases hH : H.1.LineConnected
    · have hH' : H'.1.LineConnected := (hinv s u hs H H' hHH').1 hH
      rw [goodEnv_of_lineConnected hvalid d H hH, goodEnv_of_lineConnected hvalid d H' hH']
      have hiff := hAinv s u hs _ _ (hsim s u hs H H' hH hH' hHH')
      exact ⟨fun h => ⟨hH', hiff.1 h.2⟩, fun h => ⟨hH, hiff.2 h.2⟩⟩
    · have hH' : ¬ H'.1.LineConnected := fun h => hH ((hinv s u hs H H' hHH').2 h)
      exact ⟨fun h => absurd h.1 hH, fun h => absurd h.1 hH'⟩
  have heq : μ (goodEnv hvalid d ⁻¹' A) = μ A' := by
    refine measure_congr ?_
    filter_upwards [(connectedAlongLines_iff μ).1 hL] with H hH
    show (goodEnv hvalid d H ∈ A) = (H.1.LineConnected ∧ goodEnv hvalid d H ∈ A)
    exact propext ⟨fun h => ⟨hH, h⟩, fun h => h.2⟩
  rw [heq]
  exact hErg A' hA'm hA'inv

/-! ### The (FE) moment -/

/-- **The (FE) moment transfers** from GMS's finite-expectation hypothesis (1.5).  The two halves
of the general integrand are measurable (`measurable_rootedRowEnergyDensity_config`), which is what
lets the two separate GMS bounds, at an arbitrary and possibly non-measurable root choice `H₀`, be
added. -/
theorem finiteEnergyMoment_generalLaw {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable codeMap) (hgood : MeasurableSet {H : GMSSpace | H.1.LineConnected})
    (hdensPi : ∀ (H : GMSSpace) (hH : H.1.LineConnected), ∀ K ∈ H.1.cells,
      (0 : Plane) ∈ (K : Set Plane) →
        rootedRowEnergyDensity id (config ⟨H.1.code, hvalid H hH⟩) 0 ≤
          ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.1.pi K))
    (hdensPiStar : ∀ (H : GMSSpace) (hH : H.1.LineConnected), ∀ K ∈ H.1.cells,
      (0 : Plane) ∈ (K : Set Plane) →
        rootedRowEnergyDensity (fun x : ℝ => x⁻¹) (config ⟨H.1.code, hvalid H hH⟩) 0 ≤
          ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.1.piStar K))
    (hL : ConnectedAlongLines μ) (hP : SupportedOnValidGeneral (μ.map codeMap))
    (hFE : FiniteExpectation μ) :
    GeneralLaws.FiniteEnergyMoment (generalLaw (μ.map codeMap) hP) := by
  obtain ⟨H₀, hH₀, hπ, hπs⟩ := hFE
  obtain ⟨d⟩ := exists_envGeneral hvalid hL
  have hg := measurable_goodEnv hvalid hmeas hgood d
  have hmPi : Measurable fun H : GMSSpace =>
      rootedRowEnergyDensity id (config (goodEnv hvalid d H)) 0 :=
    (measurable_rootedRowEnergyDensity_config measurable_id rfl).comp hg
  have hL' := (connectedAlongLines_iff μ).1 hL
  unfold GeneralLaws.FiniteEnergyMoment
  rw [← map_goodEnv hvalid hmeas hgood hL hP d]
  calc ∫⁻ e, rootedFiniteEnergyDensity (config e) 0 ∂μ.map (goodEnv hvalid d)
      ≤ ∫⁻ H, rootedFiniteEnergyDensity (config (goodEnv hvalid d H)) 0 ∂μ :=
        lintegral_map_le _ hg.aemeasurable
    _ = ∫⁻ H, rootedRowEnergyDensity id (config (goodEnv hvalid d H)) 0 +
          rootedRowEnergyDensity (fun x : ℝ => x⁻¹) (config (goodEnv hvalid d H)) 0 ∂μ :=
        lintegral_congr fun H => rootedFiniteEnergyDensity_eq_add _ 0
    _ = (∫⁻ H, rootedRowEnergyDensity id (config (goodEnv hvalid d H)) 0 ∂μ) +
          ∫⁻ H, rootedRowEnergyDensity (fun x : ℝ => x⁻¹) (config (goodEnv hvalid d H)) 0 ∂μ :=
        lintegral_add_left hmPi _
    _ ≤ (∫⁻ H, ENNReal.ofReal (Metric.diam (H₀ H : Set Plane) ^ 2 / CellConfig.area (H₀ H) *
            H.1.pi (H₀ H)) ∂μ) +
          ∫⁻ H, ENNReal.ofReal (Metric.diam (H₀ H : Set Plane) ^ 2 / CellConfig.area (H₀ H) *
            H.1.piStar (H₀ H)) ∂μ := by
        refine add_le_add (lintegral_mono_ae ?_) (lintegral_mono_ae ?_)
        · filter_upwards [hL'] with H hH
          rw [goodEnv_of_lineConnected hvalid d H hH]
          exact hdensPi H hH (H₀ H) (hH₀ H).1 (hH₀ H).2
        · filter_upwards [hL'] with H hH
          rw [goodEnv_of_lineConnected hvalid d H hH]
          exact hdensPiStar H hH (H₀ H) (hH₀ H).1 (hH₀ H).2
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hπ, hπs⟩

end Transfer

/-! ### Pulling almost-sure conclusions back to `μ` -/

/-- **Pull-back of `validLaw`-almost-sure statements.**  If `p` holds for `validLaw`-almost every
environment, then for `μ`-almost every configuration the code is valid and satisfies `p`.  No
measurability of `p` is needed. -/
theorem ae_of_ae_validLaw {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable codeMap) (hV : EnvironmentLaws.SupportedOnValid (μ.map codeMap))
    {p : Env → Prop} (h : ∀ᵐ e ∂EnvironmentLaws.validLaw (μ.map codeMap) hV, p e) :
    ∀ᵐ H ∂μ, ∃ hv : Valid H.1.code, p ⟨H.1.code, hv⟩ := by
  obtain ⟨N, hNm, hN0, hN⟩ := (ae_iff_exists_measurable_null_set _ p).1 h
  obtain ⟨B, hB, hNB⟩ := hNm
  obtain ⟨M, hMm, hM0, hM⟩ :=
    (ae_iff_exists_measurable_null_set (μ.map codeMap) (fun r => Valid r)).1 hV
  have hB0 : μ (codeMap ⁻¹' B) = 0 :=
    calc μ (codeMap ⁻¹' B) = (μ.map codeMap) B := (Measure.map_apply hmeas hB).symm
      _ = ((EnvironmentLaws.validLaw (μ.map codeMap) hV).map Subtype.val) B := by
          rw [EnvironmentLaws.map_validLaw]
      _ = EnvironmentLaws.validLaw (μ.map codeMap) hV (Subtype.val ⁻¹' B) :=
          Measure.map_apply measurable_subtype_coe hB
      _ = 0 := by rw [hNB]; exact hN0
  have hM0' : μ (codeMap ⁻¹' M) = 0 := by
    rw [← Measure.map_apply hmeas hMm]
    exact hM0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_union_null hB0 hM0')] with H hH
  have hv : Valid H.1.code := hM _ fun h => hH (Or.inr h)
  refine ⟨hv, hN _ ?_⟩
  rw [← hNB]
  exact fun h => hH (Or.inl h)

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.supportedOnValidGeneral_map_of_ae_mem
assert_no_sorry ReflectedGMS.GMS.supportedOnValidGeneral_map
assert_no_sorry ReflectedGMS.GMS.supportedOnValidGeneral_map_of_measurableSet_image
assert_no_sorry ReflectedGMS.GMS.measurable_goodEnv
assert_no_sorry ReflectedGMS.GMS.map_goodEnv
assert_no_sorry ReflectedGMS.GMS.massTransport_ennreal
assert_no_sorry ReflectedGMS.GMS.massTransport_generalLaw
assert_no_sorry ReflectedGMS.GMS.environmentErgodic_generalLaw
assert_no_sorry ReflectedGMS.GMS.finiteEnergyMoment_generalLaw
assert_no_sorry ReflectedGMS.GMS.ae_of_ae_validLaw

#print axioms ReflectedGMS.GMS.supportedOnValidGeneral_map
#print axioms ReflectedGMS.GMS.supportedOnValidGeneral_map_of_measurableSet_image
#print axioms ReflectedGMS.GMS.map_goodEnv
#print axioms ReflectedGMS.GMS.massTransport_ennreal
#print axioms ReflectedGMS.GMS.massTransport_generalLaw
#print axioms ReflectedGMS.GMS.environmentErgodic_generalLaw
#print axioms ReflectedGMS.GMS.finiteEnergyMoment_generalLaw
#print axioms ReflectedGMS.GMS.ae_of_ae_validLaw
