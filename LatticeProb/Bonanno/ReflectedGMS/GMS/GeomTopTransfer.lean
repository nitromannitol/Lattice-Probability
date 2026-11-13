/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.GeomTopTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.Theorems
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.GMSTopology
import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet
import Mathlib.Util.AssertNoSorry

/-!
# GMS's hypotheses transfer to the geometric-topology revision (Corollary 2.8)

Manuscript `work/geomtop/manuscript-text.txt`: Proposition 2.5 (lines ~433–456) makes the class
`C_GMS` of GMS cell configurations a subspace of `C_sing` whose Borel σ-algebra is the trace of
`B_sing`; Corollary 2.8 (line ~532) transfers GMS's hypotheses on a law `μ` of `C_GMS` to the
hypotheses of Theorems 1.2 and 1.3 on its image law in `C_sing`; Corollary 22.1 (line ~2746) then
derives GMS Theorem 1.16.

This file proves the direction of Corollary 2.8 that Theorem 1.16 needs.  For a probability law `μ`
on GMS's space `GMSSpace` (Borel for `d^CC`), with `toSing : GMSSpace → SingSpace` the inclusion:

* `measurable_toSing` — the inclusion is Borel (it is continuous, `GeomTop.continuous_toSing`,
  Proposition 2.5);
* `coords_comp_toSing`, `map_coords_map_toSing` — the auxiliary coordinates of the included
  configuration are GMS's code, so `(μ.map toSing).map coords = μ.map codeMap`;
* `massTransport_map_toSing` — GMS's mass transport (Definition 1.2(4)) gives (1.4) on `C_sing`: a
  `B_sing ⊗ B(ℂ²)`-measurable covariant kernel `T` pulls back to the measurable covariant kernel
  `T ∘ (toSing × id)` (GMS similarity and singular similarity are the same relation on the
  underlying configurations);
* `environmentErgodic_map_toSing` — the preimage of an invariant `B_sing` event is an invariant GMS
  Borel event;
* `finiteEnergyMoment_map_toSing` — GMS's finite expectation (and connectedness along lines) gives
  (FE): at a line-connected configuration the (FE) integrand of `C_sing` is the rooted (FE)
  integrand of the code (`GeomTop.rootedFiniteEnergyDensity_config_sing`), whose integral is finite
  by the GMS transfer `finiteEnergyMoment_generalLaw_gms`;
* `lcsOnMeasurableSet_map_toSing` — Definition 1.1 and (LCS) hold on the Borel probability-one set
  `coords⁻¹' {ValidGeneral}`: the code of a line-connected configuration is a general code
  (`validGeneral_codeMap`), and every general code gives a singular witness with (LCS) off it
  (`GeomTop.exists_witness_of_validGeneral_code`);
* `ae_of_ae_of_map_val_eq` — almost-sure statements under any law `ν` of labelled environments
  with `ν.map Subtype.val = μ.map codeMap` pull back to `μ`, with no measurability of the predicate.

Searched before writing: `GMS/HypothesisTransfer*.lean` (the transfer to the general-cell law, whose
lift `goodEnv`, `map_goodEnv`, `measurable_rootedRowEnergyDensity_config` and
`finiteEnergyMoment_generalLaw_gms` are reused), `GeomTop/HypothesisTransfer.lean`
(`validCoordSet`, `measurableSet_validCoordSet`), `ae_of_ae_validLaw` (whose proof is followed),
mathlib's `lintegral_map`, `lintegral_map_le`, `Measure.map_map`, `ae_of_ae_map`,
`prob_compl_eq_zero_iff`, `Measurable.lintegral_prod_right'`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.GMS

open Code

/-! ### The inclusion and the coordinates -/

/-- **The inclusion `C_GMS → C_sing` is Borel** (it is continuous, Proposition 2.5). -/
theorem measurable_toSing : Measurable GeomTop.toSing :=
  GeomTop.continuous_toSing.measurable

/-- The auxiliary coordinates of an included GMS configuration are its GMS code. -/
theorem coords_comp_toSing : GeomTop.coords ∘ GeomTop.toSing = codeMap := rfl

/-- **The coordinate law of the image law is GMS's coded law.** -/
theorem map_coords_map_toSing (μ : Measure GMSSpace) :
    (μ.map GeomTop.toSing).map GeomTop.coords = μ.map codeMap := by
  rw [Measure.map_map GeomTop.measurable_coords measurable_toSing, coords_comp_toSing]

/-- GMS similarity of configurations is singular similarity of their inclusions. -/
theorem isSimilar_toSing {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (h : IsSimilar s u hs H H') : GeomTop.IsSimilar s u hs (GeomTop.toSing H) (GeomTop.toSing H') :=
  h

/-! ### The hypotheses of Theorem 1.3 for the image law (Corollary 2.8) -/

/-- **Mass transport (1.4)** of the image law from GMS's mass transport (Definition 1.2(4)). -/
theorem massTransport_map_toSing {μ : Measure GMSSpace} (hMT : MassTransport μ) :
    GeomTop.MassTransport (μ.map GeomTop.toSing) := by
  intro T hT hcov
  have hF : Measurable fun x : GMSSpace × Plane × Plane => T (GeomTop.toSing x.1, x.2) :=
    hT.comp ((measurable_toSing.comp measurable_fst).prodMk measurable_snd)
  have h := hMT (fun x => T (GeomTop.toSing x.1, x.2)) hF fun s u hs H H' hHH' w₀ w₁ =>
    hcov s u hs (GeomTop.toSing H) (GeomTop.toSing H') (isSimilar_toSing hHH') w₀ w₁
  have hm0 : Measurable fun H : GeomTop.SingSpace => ∫⁻ z : Plane, (T (H, 0, z) : ℝ≥0∞) ∂volume :=
    (measurable_coe_nnreal_ennreal.comp
      (hT.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))).lintegral_prod_right'
  have hm1 : Measurable fun H : GeomTop.SingSpace => ∫⁻ z : Plane, (T (H, z, 0) : ℝ≥0∞) ∂volume :=
    (measurable_coe_nnreal_ennreal.comp
      (hT.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))).lintegral_prod_right'
  rw [lintegral_map hm0 measurable_toSing, lintegral_map hm1 measurable_toSing]
  exact h

/-- **Ergodicity modulo scaling** of the image law from GMS's ergodicity (Definition 1.3). -/
theorem environmentErgodic_map_toSing {μ : Measure GMSSpace} (hErg : ErgodicModuloScaling μ) :
    GeomTop.EnvironmentErgodic (μ.map GeomTop.toSing) := by
  intro A hA hAinv
  rw [Measure.map_apply measurable_toSing hA]
  exact hErg (GeomTop.toSing ⁻¹' A) (measurable_toSing hA) fun s u hs H H' hHH' =>
    hAinv s u hs (GeomTop.toSing H) (GeomTop.toSing H') (isSimilar_toSing hHH')

/-- The rooted (FE) integrand of a general environment is a measurable function of it. -/
theorem measurable_rootedFiniteEnergyDensity_config :
    Measurable fun e : EnvGeneral => GeneralLaws.rootedFiniteEnergyDensity (config e) 0 := by
  have hEq : (fun e : EnvGeneral => GeneralLaws.rootedFiniteEnergyDensity (config e) 0) =
      fun e => rootedRowEnergyDensity id (config e) 0 +
        rootedRowEnergyDensity (fun x : ℝ => x⁻¹) (config e) 0 :=
    funext fun e => rootedFiniteEnergyDensity_eq_add _ 0
  rw [hEq]
  exact (measurable_rootedRowEnergyDensity_config measurable_id rfl).add
    (measurable_rootedRowEnergyDensity_config measurable_inv inv_zero)

/-- **(FE)** for the image law from GMS's finite-expectation hypothesis (1.5), given
connectedness along lines. -/
theorem finiteEnergyMoment_map_toSing {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) (hFE : FiniteExpectation μ) :
    GeomTop.FiniteEnergyMoment (μ.map GeomTop.toSing) := by
  have hP := supportedOnValidGeneral_codeMap hL
  obtain ⟨d⟩ := exists_envGeneral validGeneral_codeMap hL
  have hg := measurable_goodEnv validGeneral_codeMap measurable_codeMap measurableSet_lineConnected d
  unfold GeomTop.FiniteEnergyMoment
  calc ∫⁻ H, GeomTop.rootedFEDensity H.1 ∂μ.map GeomTop.toSing
      ≤ ∫⁻ H, GeomTop.rootedFEDensity (GeomTop.toSing H).1 ∂μ :=
        lintegral_map_le _ measurable_toSing.aemeasurable
    _ = ∫⁻ H, GeneralLaws.rootedFiniteEnergyDensity
          (config (goodEnv validGeneral_codeMap d H)) 0 ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [(connectedAlongLines_iff μ).1 hL] with H hH
        rw [goodEnv_of_lineConnected validGeneral_codeMap d H hH]
        exact (GeomTop.rootedFiniteEnergyDensity_config_sing (GeomTop.toSing H).2
          (e := ⟨H.1.code, validGeneral_codeMap H hH⟩) rfl).symm
    _ = ∫⁻ e, GeneralLaws.rootedFiniteEnergyDensity (config e) 0
          ∂μ.map (goodEnv validGeneral_codeMap d) :=
        (lintegral_map measurable_rootedFiniteEnergyDensity_config hg).symm
    _ = ∫⁻ e, GeneralLaws.rootedFiniteEnergyDensity (config e) 0
          ∂GeneralLaws.generalLaw (μ.map codeMap) hP := by
        rw [map_goodEnv validGeneral_codeMap measurable_codeMap measurableSet_lineConnected hL hP d]
    _ < ∞ := finiteEnergyMoment_generalLaw_gms hL hP hFE

/-- **Definition 1.1 and (LCS) on a Borel probability-one set** for the image law, from
connectedness along lines. -/
theorem lcsOnMeasurableSet_map_toSing {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) : GeomTop.LCSOnMeasurableSet (μ.map GeomTop.toSing) := by
  have hA : MeasurableSet GeomTop.validCoordSet :=
    GeomTop.measurableSet_validCoordSet GeomTop.measurable_coords GeomTop.measurableSet_validGeneral
  refine ⟨GeomTop.validCoordSet, hA, ?_,
    fun H hH => GeomTop.exists_witness_of_validGeneral_code H.2 hH⟩
  have hae : ∀ᵐ H ∂μ, H ∈ GeomTop.toSing ⁻¹' GeomTop.validCoordSet :=
    ((connectedAlongLines_iff μ).1 hL).mono fun H hH => validGeneral_codeMap H hH
  rw [Measure.map_apply measurable_toSing hA]
  exact (prob_compl_eq_zero_iff (measurable_toSing hA)).1 (ae_iff.1 hae)

/-! ### Pulling almost-sure conclusions back to `μ` -/

/-- **Pull-back of almost-sure statements** under any law `ν` of labelled environments whose
underlying raw law is GMS's coded law.  No measurability of the predicate is needed. -/
theorem ae_of_ae_of_map_val_eq {μ : Measure GMSSpace} {ν : Measure Env}
    (hν : ν.map Subtype.val = μ.map codeMap) (hvalid : ∀ᵐ H ∂μ, Valid H.1.code)
    {p : Env → Prop} (h : ∀ᵐ e ∂ν, p e) : ∀ᵐ H ∂μ, ∃ hv : Valid H.1.code, p ⟨H.1.code, hv⟩ := by
  obtain ⟨N, hNm, hN0, hN⟩ := (ae_iff_exists_measurable_null_set _ p).1 h
  obtain ⟨B, hB, hNB⟩ := hNm
  have hB0 : μ (codeMap ⁻¹' B) = 0 :=
    calc μ (codeMap ⁻¹' B) = (μ.map codeMap) B := (Measure.map_apply measurable_codeMap hB).symm
      _ = (ν.map Subtype.val) B := by rw [hν]
      _ = ν (Subtype.val ⁻¹' B) := Measure.map_apply measurable_subtype_coe hB
      _ = 0 := by rw [hNB]; exact hN0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hB0, hvalid] with H hH hv
  refine ⟨hv, hN _ ?_⟩
  rw [← hNB]
  exact hH

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.measurable_toSing
assert_no_sorry ReflectedGMS.GMS.coords_comp_toSing
assert_no_sorry ReflectedGMS.GMS.map_coords_map_toSing
assert_no_sorry ReflectedGMS.GMS.isSimilar_toSing
assert_no_sorry ReflectedGMS.GMS.massTransport_map_toSing
assert_no_sorry ReflectedGMS.GMS.environmentErgodic_map_toSing
assert_no_sorry ReflectedGMS.GMS.measurable_rootedFiniteEnergyDensity_config
assert_no_sorry ReflectedGMS.GMS.finiteEnergyMoment_map_toSing
assert_no_sorry ReflectedGMS.GMS.lcsOnMeasurableSet_map_toSing
assert_no_sorry ReflectedGMS.GMS.ae_of_ae_of_map_val_eq

#print axioms ReflectedGMS.GMS.measurable_toSing
#print axioms ReflectedGMS.GMS.map_coords_map_toSing
#print axioms ReflectedGMS.GMS.massTransport_map_toSing
#print axioms ReflectedGMS.GMS.environmentErgodic_map_toSing
#print axioms ReflectedGMS.GMS.measurable_rootedFiniteEnergyDensity_config
#print axioms ReflectedGMS.GMS.finiteEnergyMoment_map_toSing
#print axioms ReflectedGMS.GMS.lcsOnMeasurableSet_map_toSing
#print axioms ReflectedGMS.GMS.ae_of_ae_of_map_val_eq
