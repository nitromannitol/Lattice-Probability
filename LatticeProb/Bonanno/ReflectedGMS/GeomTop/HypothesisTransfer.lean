/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.HypothesisTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.Statement
import LatticeProb.Bonanno.ReflectedGMS.GMS.HypothesisTransfer
import Mathlib.Util.AssertNoSorry

/-!
# Transfer of the geometric-topology hypotheses to the general-cell environment law

Theorems 1.2 and 1.3 of the geometric-topology revision (`GeomTop/Statement.lean`) are derived from
the general-cell main theorems (`GeneralMainTheorems`) applied to the law `P := μ.map coords` of the
auxiliary rational-label coordinates.  This file transfers the hypotheses on `μ` (a law on
`(C_sing, B_sing)`) to the hypotheses of those theorems on `generalLaw P hP`.

The structure is that of the GMS transfer (`GMS/HypothesisTransfer.lean`), with one simplification:
the gate is the set `coords⁻¹' {ValidGeneral}` itself, which is **Borel** here
(`hmeas`, `hvalidB`) and similarity invariant (`hinv`).  So no line-connectivity predicate on `C_sing`
needs to be measurable, and every transfer except `SupportedOnValidGeneral` needs only
`SupportedOnValidGeneral (μ.map coords)` itself (`ae_validGeneral_coords`), not (LCS).

Inputs proved in other packets are explicit hypotheses:

* `hmeas : Measurable coords`;
* `hvalidB : MeasurableSet {r | ValidGeneral r}`;
* `hvalid` — an environment satisfying (LCS) with one of its witnesses has general coordinates;
* `hinv` — similar environments have general coordinates together;
* `hsim` — between environments with general coordinates, similarity of environments is general
  similarity of their coordinates;
* `hFEle` — the rooted (FE) integrand of the coordinates is at most the (FE) integrand of `C_sing`.

Main results (namespace `ReflectedGMS.GeomTop`):

* `supportedOnValidGeneral_coords` — `SupportedOnValidGeneral (μ.map coords)` from (LCS) on a
  measurable probability-one set;
* `map_coordsEnv` — `generalLaw (μ.map coords) hP` is the pushforward of `μ` under the measurable
  lift `coordsEnv`;
* `massTransport_ennreal_geom` — the mass transport (1.4) on `C_sing`, stated for `ℝ≥0`-valued
  kernels, extends to `ℝ≥0∞`-valued ones (covariant truncation `min(F, n |w₀ − w₁|⁻²)`);
* `massTransport_generalLaw_geom`, `finiteEnergyMoment_generalLaw_geom`,
  `environmentErgodic_generalLaw_geom`.

Reused: `supportedLaw_unique`, `GMS.invDistSq` with its measurability, positivity and similarity
lemmas, `lintegral_map_le`, `ae_map_iff`, `prob_compl_eq_zero_iff`.  The truncation lemmas of
`GMS/HypothesisTransfer.lean` are stated for GMS's space only; they are restated here for an
arbitrary environment space (same proofs).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.GeomTop

open Code GeneralLaws

/-! ### Mass transport for `ℝ≥0∞`-valued kernels, on any environment space -/

section Truncation

variable {X : Type*} [MeasurableSpace X] (F : X × Plane × Plane → ℝ≥0∞)

/-- The covariant truncation `min(F, n |w₀ − w₁|⁻²)` (`GMS.truncateKernel` on an arbitrary
environment space). -/
noncomputable def geomTruncate (n : ℕ) (x : X × Plane × Plane) : ℝ≥0∞ :=
  min (F x) ((n : ℝ≥0∞) * GMS.invDistSq x.2)

theorem geomTruncate_ne_top (n : ℕ) (x : X × Plane × Plane) : geomTruncate F n x ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top)
    (min_le_right _ _)

theorem measurable_geomTruncate (hF : Measurable F) (n : ℕ) : Measurable (geomTruncate F n) :=
  hF.min (measurable_const.mul (GMS.measurable_invDistSq.comp measurable_snd))

theorem geomTruncate_mono (x : X × Plane × Plane) :
    Monotone fun n : ℕ => geomTruncate F n x := fun _ _ hmn =>
  min_le_min le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hmn) zero_le)

theorem iSup_geomTruncate (x : X × Plane × Plane) (hx : x.2.1 ≠ x.2.2) :
    ⨆ n : ℕ, geomTruncate F n x = F x := by
  have htop : ⨆ n : ℕ, (n : ℝ≥0∞) * GMS.invDistSq x.2 = ∞ := by
    rw [← ENNReal.iSup_mul, ENNReal.iSup_natCast, ENNReal.top_mul (GMS.invDistSq_ne_zero hx)]
  calc ⨆ n : ℕ, geomTruncate F n x = ⨆ n : ℕ, F x ⊓ ((n : ℝ≥0∞) * GMS.invDistSq x.2) := rfl
    _ = F x ⊓ ⨆ n : ℕ, (n : ℝ≥0∞) * GMS.invDistSq x.2 := (inf_iSup_eq _ _).symm
    _ = F x := by rw [htop, inf_top_eq]

theorem geomTruncate_similarity {s : ℝ} (hs : 0 < s) (u : Plane) {H H' : X}
    (hF : ∀ w₀ w₁ : Plane, F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * F (H, w₀, w₁)) (n : ℕ) (w₀ w₁ : Plane) :
    geomTruncate F n (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * geomTruncate F n (H, w₀, w₁) := by
  show min (F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁))
      ((n : ℝ≥0∞) * GMS.invDistSq (positiveSimilarity s u w₀, positiveSimilarity s u w₁)) =
    ENNReal.ofReal ((s ^ 2)⁻¹) * min (F (H, w₀, w₁)) ((n : ℝ≥0∞) * GMS.invDistSq (w₀, w₁))
  rw [hF, GMS.invDistSq_similarity hs, mul_left_comm]
  exact (Monotone.map_min (f := fun a => ENNReal.ofReal ((s ^ 2)⁻¹) * a)
    fun _ _ hab => mul_le_mul_of_nonneg_left hab zero_le).symm

/-- The `ℝ≥0`-valued truncation, the form the mass transport (1.4) on `C_sing` accepts. -/
noncomputable def geomTruncateNN (n : ℕ) (x : X × Plane × Plane) : ℝ≥0 :=
  (geomTruncate F n x).toNNReal

theorem coe_geomTruncateNN (n : ℕ) (x : X × Plane × Plane) :
    (geomTruncateNN F n x : ℝ≥0∞) = geomTruncate F n x :=
  ENNReal.coe_toNNReal (geomTruncate_ne_top F n x)

theorem geomTruncateNN_similarity {s : ℝ} (hs : 0 < s) (u : Plane) {H H' : X}
    (hF : ∀ w₀ w₁ : Plane, F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * F (H, w₀, w₁)) (n : ℕ) (w₀ w₁ : Plane) :
    (geomTruncateNN F n (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) : ℝ) =
      (s ^ 2)⁻¹ * (geomTruncateNN F n (H, w₀, w₁) : ℝ) := by
  simp only [geomTruncateNN, ENNReal.coe_toNNReal_eq_toReal]
  rw [geomTruncate_similarity F hs u hF n w₀ w₁, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg s))]

/-- The double integral of `F` along `w ↦ σ w` is the supremum of those of its truncations,
provided `σ w` is off the diagonal for `w ≠ 0`. -/
theorem lintegral_lintegral_eq_iSup_geomTruncate (μ : Measure X) (hF : Measurable F)
    (σ : Plane → Plane × Plane) (hσ : Measurable σ) (hdiag : ∀ w : Plane, w ≠ 0 → (σ w).1 ≠ (σ w).2) :
    ∫⁻ H, ∫⁻ w, F (H, σ w) ∂volume ∂μ =
      ⨆ n : ℕ, ∫⁻ H, ∫⁻ w, geomTruncate F n (H, σ w) ∂volume ∂μ := by
  have hne : ∀ᵐ w ∂(volume : Measure Plane), w ∉ ({0} : Set Plane) :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : Plane))
  have hinner : ∀ H : X, ∫⁻ w, F (H, σ w) ∂volume =
      ⨆ n : ℕ, ∫⁻ w, geomTruncate F n (H, σ w) ∂volume := by
    intro H
    rw [← lintegral_iSup (f := fun n w => geomTruncate F n (H, σ w))
      (fun n => (measurable_geomTruncate F hF n).comp (measurable_const.prodMk hσ))
      (fun m n hmn w => geomTruncate_mono F (H, σ w) hmn)]
    refine lintegral_congr_ae ?_
    filter_upwards [hne] with w hw
    exact (iSup_geomTruncate F (H, σ w) (hdiag w hw)).symm
  have hmeasH : ∀ n : ℕ, Measurable fun H : X =>
      ∫⁻ w, geomTruncate F n (H, σ w) ∂volume := fun n =>
    ((measurable_geomTruncate F hF n).comp
      (measurable_fst.prodMk (hσ.comp measurable_snd))).lintegral_prod_right'
  calc ∫⁻ H, ∫⁻ w, F (H, σ w) ∂volume ∂μ
      = ∫⁻ H, ⨆ n : ℕ, ∫⁻ w, geomTruncate F n (H, σ w) ∂volume ∂μ :=
        lintegral_congr fun H => hinner H
    _ = ⨆ n : ℕ, ∫⁻ H, ∫⁻ w, geomTruncate F n (H, σ w) ∂volume ∂μ :=
        lintegral_iSup hmeasH fun m n hmn H =>
          lintegral_mono fun w => geomTruncate_mono F (H, σ w) hmn

end Truncation

/-- **The mass transport (1.4) on `C_sing` extends to `ℝ≥0∞`-valued kernels.**  The manuscript's
kernels are nonnegative; `MassTransport` tests `[0,∞)`-valued ones (the weakest reading).  A
measurable `[0,∞]`-valued kernel of degree `−2` is the increasing limit of the covariant finite
truncations `min(F, n |w₀ − w₁|⁻²)`, which agree with `F` off the diagonal. -/
theorem massTransport_ennreal_geom {μ : Measure SingSpace} (hMT : MassTransport μ)
    (F : SingSpace × Plane × Plane → ℝ≥0∞) (hF : Measurable F)
    (hcov : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      ∀ w₀ w₁ : Plane, F (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * F (H, w₀, w₁)) :
    ∫⁻ H, ∫⁻ w, F (H, 0, w) ∂volume ∂μ = ∫⁻ H, ∫⁻ w, F (H, w, 0) ∂volume ∂μ := by
  have hn : ∀ n : ℕ, ∫⁻ H, ∫⁻ w, geomTruncate F n (H, 0, w) ∂volume ∂μ =
      ∫⁻ H, ∫⁻ w, geomTruncate F n (H, w, 0) ∂volume ∂μ := by
    intro n
    have h := hMT (geomTruncateNN F n)
      ((measurable_geomTruncate F hF n).ennreal_toNNReal)
      (fun s u hs H H' hHH' w₀ w₁ =>
        geomTruncateNN_similarity F hs u (hcov s u hs H H' hHH') n w₀ w₁)
    simpa only [coe_geomTruncateNN] using h
  rw [lintegral_lintegral_eq_iSup_geomTruncate F μ hF (fun w => ((0 : Plane), w))
      (measurable_const.prodMk measurable_id) (fun w hw => (Ne.symm hw)),
    lintegral_lintegral_eq_iSup_geomTruncate F μ hF (fun w => (w, (0 : Plane)))
      (measurable_id.prodMk measurable_const) (fun w hw => hw)]
  exact iSup_congr hn

/-! ### The coordinate law is carried by general environments -/

/-- The environments whose auxiliary coordinates are a general environment. -/
def validCoordSet : Set SingSpace := {H | ValidGeneral (coords H)}

theorem measurableSet_validCoordSet (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r}) : MeasurableSet validCoordSet :=
  hmeas hvalidB

/-- **(LCS) on a measurable probability-one set gives a coordinate law carried by general
environments.** -/
theorem supportedOnValidGeneral_coords {μ : Measure SingSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable coords) (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hvalid : ∀ H : SingSpace, (∃ w : GeomTop.SingularWitness H.1, LineConnectedOff H.1 w.sing) →
      ValidGeneral (coords H))
    (hLCS : LCSOnMeasurableSet μ) : SupportedOnValidGeneral (μ.map coords) := by
  obtain ⟨A, hA, hμA, hAgood⟩ := hLCS
  have hae : ∀ᵐ H ∂μ, H ∈ A := ae_iff.2 ((prob_compl_eq_zero_iff hA).2 hμA)
  exact (ae_map_iff hmeas.aemeasurable hvalidB).2
    (hae.mono fun H hH => hvalid H (hAgood H hH))

/-- Almost every environment has general coordinates, whenever the coordinate law is carried by
general environments. -/
theorem ae_validGeneral_coords {μ : Measure SingSpace} (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hP : SupportedOnValidGeneral (μ.map coords)) : ∀ᵐ H ∂μ, ValidGeneral (coords H) :=
  (ae_map_iff hmeas.aemeasurable hvalidB).1 hP

/-! ### The lift to general environments -/

open Classical in
/-- The coordinates of an environment as a general environment, when they are one; a fixed
environment `d` otherwise. -/
noncomputable def coordsEnv (d : EnvGeneral) (H : SingSpace) : EnvGeneral :=
  if h : ValidGeneral (coords H) then ⟨coords H, h⟩ else d

theorem coordsEnv_of_valid (d : EnvGeneral) (H : SingSpace) (h : ValidGeneral (coords H)) :
    coordsEnv d H = ⟨coords H, h⟩ := by
  classical
  exact dif_pos h

theorem coordsEnv_of_not_valid (d : EnvGeneral) (H : SingSpace) (h : ¬ ValidGeneral (coords H)) :
    coordsEnv d H = d := by
  classical
  exact dif_neg h

theorem measurable_coordsEnv (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r}) (d : EnvGeneral) :
    Measurable (coordsEnv d) := by
  classical
  have hval : (fun H => (coordsEnv d H).val) =
      fun H => if ValidGeneral (coords H) then coords H else d.val := by
    funext H
    by_cases h : ValidGeneral (coords H)
    · rw [coordsEnv_of_valid d H h, if_pos h]
    · rw [coordsEnv_of_not_valid d H h, if_neg h]
  have hm : Measurable fun H => (coordsEnv d H).val := by
    rw [hval]
    exact Measurable.ite (measurableSet_validCoordSet hmeas hvalidB) hmeas measurable_const
  exact hm.subtype_mk

/-- **The general-environment law is the pushforward of `μ` under the lift.** -/
theorem map_coordsEnv {μ : Measure SingSpace} [IsProbabilityMeasure μ] (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hP : SupportedOnValidGeneral (μ.map coords)) (d : EnvGeneral) :
    μ.map (coordsEnv d) = generalLaw (μ.map coords) hP := by
  have h : (μ.map (coordsEnv d)).map (Subtype.val : EnvGeneral → RawCode) = μ.map coords := by
    rw [Measure.map_map measurable_subtype_coe (measurable_coordsEnv hmeas hvalidB d)]
    refine Measure.map_congr ?_
    filter_upwards [ae_validGeneral_coords hmeas hvalidB hP] with H hH
    show (coordsEnv d H).val = coords H
    rw [coordsEnv_of_valid d H hH]
  exact supportedLaw_unique (μ.map coords) {r | ValidGeneral r} hP _ h

/-- A general environment, from a probability law whose coordinate law is carried by general
environments. -/
theorem exists_envGeneral_geom {μ : Measure SingSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable coords) (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hP : SupportedOnValidGeneral (μ.map coords)) : Nonempty EnvGeneral := by
  obtain ⟨H, hH⟩ := (ae_validGeneral_coords hmeas hvalidB hP).exists
  exact ⟨⟨coords H, hH⟩⟩

/-! ### Mass transport -/

section Transfer

open Classical in
/-- A general transport kernel read on `C_sing` through the lift, extended by zero off the
environments with general coordinates. -/
noncomputable def coordsKernel (d : EnvGeneral) (T : MassTransportKernel)
    (x : SingSpace × Plane × Plane) : ℝ≥0∞ :=
  if ValidGeneral (coords x.1) then T.toFun (coordsEnv d x.1, x.2) else 0

open Classical in
theorem coordsKernel_apply (d : EnvGeneral) (T : MassTransportKernel) (H : SingSpace)
    (w : Plane × Plane) :
    coordsKernel d T (H, w) = if ValidGeneral (coords H) then T.toFun (coordsEnv d H, w) else 0 := by
  classical
  rfl

theorem measurable_coordsKernel (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r}) (d : EnvGeneral) (T : MassTransportKernel) :
    Measurable (coordsKernel d T) := by
  classical
  exact Measurable.ite (measurable_fst (measurableSet_validCoordSet hmeas hvalidB))
    (T.measurable_toFun.comp
      (((measurable_coordsEnv hmeas hvalidB d).comp measurable_fst).prodMk measurable_snd))
    measurable_const

/-- The lifted kernel is covariant for similarities of `C_sing`. -/
theorem coordsKernel_similarity
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      (ValidGeneral (coords H) ↔ ValidGeneral (coords H')))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace) (h : ValidGeneral (coords H))
      (h' : ValidGeneral (coords H')), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨coords H, h⟩ ⟨coords H', h'⟩)
    (d : EnvGeneral) (T : MassTransportKernel) (s : ℝ) (u : Plane) (hs : 0 < s)
    (H H' : SingSpace) (hHH' : IsSimilar s u hs H H') (w₀ w₁ : Plane) :
    coordsKernel d T (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * coordsKernel d T (H, w₀, w₁) := by
  classical
  rw [coordsKernel_apply, coordsKernel_apply]
  by_cases hH : ValidGeneral (coords H)
  · have hH' : ValidGeneral (coords H') := (hinv s u hs H H' hHH').1 hH
    rw [if_pos hH, if_pos hH', coordsEnv_of_valid d H hH, coordsEnv_of_valid d H' hH']
    exact T.covariant s u hs _ _ (hsim s u hs H H' hH hH' hHH') w₀ w₁
  · have hH' : ¬ ValidGeneral (coords H') := fun h => hH ((hinv s u hs H H' hHH').2 h)
    rw [if_neg hH, if_neg hH', mul_zero]

/-- Double integrals of a general kernel under `generalLaw` are double integrals of the lifted
kernel under `μ`. -/
theorem lintegral_generalLaw_eq_coordsKernel {μ : Measure SingSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hP : SupportedOnValidGeneral (μ.map coords)) (d : EnvGeneral)
    (T : MassTransportKernel) (σ : Plane → Plane × Plane) (hσ : Measurable σ) :
    ∫⁻ e, ∫⁻ w, T.toFun (e, σ w) ∂volume ∂generalLaw (μ.map coords) hP =
      ∫⁻ H, ∫⁻ w, coordsKernel d T (H, σ w) ∂volume ∂μ := by
  classical
  have hTσ : Measurable fun e : EnvGeneral => ∫⁻ w, T.toFun (e, σ w) ∂volume :=
    (T.measurable_toFun.comp (measurable_fst.prodMk (hσ.comp measurable_snd))).lintegral_prod_right'
  rw [← map_coordsEnv hmeas hvalidB hP d,
    lintegral_map hTσ (measurable_coordsEnv hmeas hvalidB d)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_validGeneral_coords hmeas hvalidB hP] with H hH
  refine lintegral_congr fun w => ?_
  rw [coordsKernel_apply, if_pos hH]

/-- **Mass transport transfers** from the law on `C_sing` to the general-environment law of its
coordinates. -/
theorem massTransport_generalLaw_geom {μ : Measure SingSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      (ValidGeneral (coords H) ↔ ValidGeneral (coords H')))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace) (h : ValidGeneral (coords H))
      (h' : ValidGeneral (coords H')), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨coords H, h⟩ ⟨coords H', h'⟩)
    (hP : SupportedOnValidGeneral (μ.map coords)) (hMT : MassTransport μ) :
    GeneralLaws.MassTransport (generalLaw (μ.map coords) hP) := by
  intro T
  obtain ⟨d⟩ := exists_envGeneral_geom hmeas hvalidB hP
  have h := massTransport_ennreal_geom hMT (coordsKernel d T)
    (measurable_coordsKernel hmeas hvalidB d T)
    (coordsKernel_similarity hinv hsim d T)
  rw [lintegral_generalLaw_eq_coordsKernel hmeas hvalidB hP d T (fun w => ((0 : Plane), w))
      (measurable_const.prodMk measurable_id),
    lintegral_generalLaw_eq_coordsKernel hmeas hvalidB hP d T (fun w => (w, (0 : Plane)))
      (measurable_id.prodMk measurable_const)]
  exact h

/-! ### Ergodicity -/

/-- **Ergodicity modulo scaling transfers** from the law on `C_sing` to the general-environment law
of its coordinates. -/
theorem environmentErgodic_generalLaw_geom {μ : Measure SingSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      (ValidGeneral (coords H) ↔ ValidGeneral (coords H')))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace) (h : ValidGeneral (coords H))
      (h' : ValidGeneral (coords H')), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨coords H, h⟩ ⟨coords H', h'⟩)
    (hP : SupportedOnValidGeneral (μ.map coords)) (hErg : EnvironmentErgodic μ) :
    GeneralLaws.EnvironmentErgodic (generalLaw (μ.map coords) hP) := by
  intro A hA hAinv
  obtain ⟨d⟩ := exists_envGeneral_geom hmeas hvalidB hP
  have hg := measurable_coordsEnv hmeas hvalidB d
  rw [← map_coordsEnv hmeas hvalidB hP d, Measure.map_apply hg hA]
  let A' : Set SingSpace := validCoordSet ∩ coordsEnv d ⁻¹' A
  have hA'm : MeasurableSet A' := (measurableSet_validCoordSet hmeas hvalidB).inter (hg hA)
  have hA'inv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      (H ∈ A' ↔ H' ∈ A') := by
    intro s u hs H H' hHH'
    show (ValidGeneral (coords H) ∧ coordsEnv d H ∈ A) ↔
      (ValidGeneral (coords H') ∧ coordsEnv d H' ∈ A)
    by_cases hH : ValidGeneral (coords H)
    · have hH' : ValidGeneral (coords H') := (hinv s u hs H H' hHH').1 hH
      rw [coordsEnv_of_valid d H hH, coordsEnv_of_valid d H' hH']
      have hiff := hAinv s u hs _ _ (hsim s u hs H H' hH hH' hHH')
      exact ⟨fun h => ⟨hH', hiff.1 h.2⟩, fun h => ⟨hH, hiff.2 h.2⟩⟩
    · have hH' : ¬ ValidGeneral (coords H') := fun h => hH ((hinv s u hs H H' hHH').2 h)
      exact ⟨fun h => absurd h.1 hH, fun h => absurd h.1 hH'⟩
  have heq : μ (coordsEnv d ⁻¹' A) = μ A' := by
    refine measure_congr ?_
    filter_upwards [ae_validGeneral_coords hmeas hvalidB hP] with H hH
    show (coordsEnv d H ∈ A) = (ValidGeneral (coords H) ∧ coordsEnv d H ∈ A)
    exact propext ⟨fun h => ⟨hH, h⟩, fun h => h.2⟩
  rw [heq]
  exact hErg A' hA'm hA'inv

/-! ### The (FE) moment -/

/-- **The (FE) moment transfers** from the law on `C_sing` to the general-environment law of its
coordinates, given the pointwise comparison `hFEle` of the rooted integrands.  The integrand on
`C_sing` need not be measurable: only an upper bound of a lower integral is needed. -/
theorem finiteEnergyMoment_generalLaw_geom {μ : Measure SingSpace} [IsProbabilityMeasure μ]
    (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hFEle : ∀ (H : SingSpace) (h : ValidGeneral (coords H)),
      GeneralLaws.rootedFiniteEnergyDensity (config ⟨coords H, h⟩) 0 ≤ rootedFEDensity H.1)
    (hP : SupportedOnValidGeneral (μ.map coords)) (hFE : FiniteEnergyMoment μ) :
    GeneralLaws.FiniteEnergyMoment (generalLaw (μ.map coords) hP) := by
  obtain ⟨d⟩ := exists_envGeneral_geom hmeas hvalidB hP
  have hg := measurable_coordsEnv hmeas hvalidB d
  unfold GeneralLaws.FiniteEnergyMoment
  rw [← map_coordsEnv hmeas hvalidB hP d]
  calc ∫⁻ e, GeneralLaws.rootedFiniteEnergyDensity (config e) 0 ∂μ.map (coordsEnv d)
      ≤ ∫⁻ H, GeneralLaws.rootedFiniteEnergyDensity (config (coordsEnv d H)) 0 ∂μ :=
        lintegral_map_le _ hg.aemeasurable
    _ ≤ ∫⁻ H, rootedFEDensity H.1 ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_validGeneral_coords hmeas hvalidB hP] with H hH
        rw [coordsEnv_of_valid d H hH]
        exact hFEle H hH
    _ < ∞ := hFE

end Transfer

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.massTransport_ennreal_geom
assert_no_sorry ReflectedGMS.GeomTop.supportedOnValidGeneral_coords
assert_no_sorry ReflectedGMS.GeomTop.ae_validGeneral_coords
assert_no_sorry ReflectedGMS.GeomTop.measurable_coordsEnv
assert_no_sorry ReflectedGMS.GeomTop.map_coordsEnv
assert_no_sorry ReflectedGMS.GeomTop.massTransport_generalLaw_geom
assert_no_sorry ReflectedGMS.GeomTop.environmentErgodic_generalLaw_geom
assert_no_sorry ReflectedGMS.GeomTop.finiteEnergyMoment_generalLaw_geom

#print axioms ReflectedGMS.GeomTop.massTransport_ennreal_geom
#print axioms ReflectedGMS.GeomTop.supportedOnValidGeneral_coords
#print axioms ReflectedGMS.GeomTop.map_coordsEnv
#print axioms ReflectedGMS.GeomTop.massTransport_generalLaw_geom
#print axioms ReflectedGMS.GeomTop.environmentErgodic_generalLaw_geom
#print axioms ReflectedGMS.GeomTop.finiteEnergyMoment_generalLaw_geom
