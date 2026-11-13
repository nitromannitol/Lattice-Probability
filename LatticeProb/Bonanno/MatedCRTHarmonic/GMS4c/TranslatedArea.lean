/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.TranslatedArea at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaCertBorel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaReader
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Events
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift

/-! Local dyadic GMC reconstruction for a translated cone field. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.CellScaling
  MatedCRTHarmonic.GMS4FO

/-- Spatial continuity of translated circle averages follows from the exact translation identity. -/
theorem continuousAt_circleAvg_translate {h : DistC} {r : ℝ} {b z : ℂ}
    (hc : ContinuousAt (fun x => circleAvg h r x) (z + b)) :
    ContinuousAt (fun x => circleAvg (affineComp 1 b h) r x) z := by
  simp only [LQGMetric.GM.circleAvg_affineComp_one_at]
  exact ContinuousAt.comp (f := fun x : ℂ => x + b) (x := z)
    (g := fun x => circleAvg h r x) hc
    (continuousAt_id.add continuousAt_const)

/-- Dyadic GMC approximations and their vague limit commute with a translation. -/
theorem lqgArea_affineComp_one_of_vague (γ : ℝ) (h : DistC) (b : ℂ)
    (hv : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) :
    CellScaling.lqgArea γ (affineComp 1 b h) =
      (CellScaling.lqgArea γ h).map (subHomeo b) := by
  have hraw : CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h)
      (CellScaling.lqgArea γ h) := by
    unfold CellScaling.lqgArea
    rw [dif_pos hv]
    exact Classical.choose_spec hv
  have hmap : QuantumZipper.IsVagueLimitOn (univ : Set ℂ)
      (fun k => CellScaling.lqgAreaApprox γ (affineComp 1 b h) k)
      ((CellScaling.lqgArea γ h).map (subHomeo b)) := by
    have ht := LQGCone.isVagueLimitOn_map_homeomorph isOpen_univ
      (LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hraw) (subHomeo b)
    have hrange : (subHomeo b) '' (univ : Set ℂ) = univ := by
      rw [image_univ]
      exact (subHomeo b).surjective.range_eq
    rw [hrange] at ht
    convert ht using 1
    funext k
    rw [lqgAreaApprox_affineComp_one, LQGCone.lqgAreaApprox_eq_areaApproxC]
  have hv' : ∃ μ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (affineComp 1 b h)) μ := by
    exact ⟨_, LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr (by
      simpa only [LQGCone.lqgAreaApprox_eq_areaApproxC] using hmap)⟩
  have hchosen : CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (affineComp 1 b h))
      (CellScaling.lqgArea γ (affineComp 1 b h)) := by
    unfold CellScaling.lqgArea
    rw [dif_pos hv']
    exact Classical.choose_spec hv'
  exact QuantumZipper.isVagueLimitOn_unique isOpen_univ
    (LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hchosen) (by
      simpa only [LQGCone.lqgAreaApprox_eq_areaApproxC] using hmap)

/-- Translation preserves existence of the dyadic GMC vague limit. -/
theorem exists_isVagueLimitC_affineComp_one (γ : ℝ) (h : DistC) (b : ℂ)
    (hv : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) :
    ∃ μ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (affineComp 1 b h)) μ := by
  obtain ⟨μ, hμ⟩ := hv
  refine ⟨μ.map (subHomeo b), ?_⟩
  apply LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr
  have ht := LQGCone.isVagueLimitOn_map_homeomorph isOpen_univ
    (LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hμ) (subHomeo b)
  have hrange : (subHomeo b) '' (univ : Set ℂ) = univ := by
    rw [image_univ]
    exact (subHomeo b).surjective.range_eq
  rw [hrange] at ht
  convert ht using 1
  funext k
  rw [← LQGCone.lqgAreaApprox_eq_areaApproxC,
    ← LQGCone.lqgAreaApprox_eq_areaApproxC]
  exact lqgAreaApprox_affineComp_one γ h b k

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Circle averages of the translated γ-cone are spatially continuous almost
 everywhere at every sufficiently fine local GMC scale. -/
theorem ae_gamma_translated_localCircle_continuous_eventually
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) (z₀ : ℂ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ)
          (affineComp 1 (-z₀) (CellScaling.coneField (X ω) (CellScaling.coneRadial γ γ
            (fun t => B t ω) (fun t => B' t ω)))))
        (CellScaling.dyadicScale k) w) z := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨K, hK⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt hδ
  filter_upwards [LQGCoord.ae_radialGood D.gff D.bm_B D.bm_B'
      (MesoModel.FrozenIdentities.lt_lqgQ hγ),
    LQGCoord.ae_tendsto_mollAvgS_circleAvg D.gff] with ω hr hs
  filter_upwards [eventually_ge_atTop K] with k hk
  have hρ : 0 < CellScaling.dyadicScale k := by
    unfold CellScaling.dyadicScale
    positivity
  have hsmall : CellScaling.dyadicScale k < δ := by
    rw [LQGCone.dyadicScale_eq_radius]
    exact hK k hk
  have hne : ∀ᵐ z : ℂ, ‖z - z₀‖ ≠ CellScaling.dyadicScale k := by
    rw [ae_iff]
    have hsphere : volume (sphere z₀ (CellScaling.dyadicScale k)) = 0 :=
      Measure.addHaar_sphere volume z₀ (CellScaling.dyadicScale k)
    apply le_antisymm _ bot_le
    calc
      volume {a | ¬‖a - z₀‖ ≠ CellScaling.dyadicScale k} ≤
          volume (sphere z₀ (CellScaling.dyadicScale k)) := by
        apply measure_mono
        intro z hz
        rw [mem_sphere, dist_eq_norm]
        exact not_not.mp hz
      _ = 0 := hsphere
  filter_upwards [ae_restrict_of_ae hne,
    ae_restrict_mem V.isOpen.measurableSet] with z hzne hz
  apply continuousAt_localCircleProcess_restrictTo V hρ hsmall _ hz
  apply continuousAt_circleAvg_translate
  simpa [sub_eq_add_neg] using
    (continuousAt_circleAvg_coneField_off_resonance hr hs.2 hρ hzne)

/-- Eventual compact finiteness also transports through translation. -/
theorem ae_gamma_translated_areaApprox_finite_eventually
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (z₀ : ℂ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      CellScaling.lqgAreaApprox γ
        (affineComp 1 (-z₀) (CellScaling.coneField (X ω) (CellScaling.coneRadial γ γ
          (fun t => B t ω) (fun t => B' t ω)))) k (closure V) < ⊤ := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hK : IsCompact ((subHomeo (-z₀)) ⁻¹' closure (V : Set ℂ)) :=
    (subHomeo (-z₀)).isCompact_preimage.mpr hVb.isCompact_closure
  filter_upwards [ae_cone_areaApprox_finite_eventually hγ.1 hγ.2
      (MesoModel.FrozenIdentities.lt_lqgQ hγ) D.gff D.bm_B D.bm_B' hK] with ω hf
  filter_upwards [hf] with k hk
  rw [lqgAreaApprox_affineComp_one,
    Measure.map_apply (subHomeo (-z₀)).measurable isClosed_closure.measurableSet]
  exact hk

/-- The translated γ-cone satisfies the same local dyadic good-sample predicate. -/
theorem ae_gamma_translated_localDyadicGood
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (z₀ : ℂ) :
    ∀ᵐ ω ∂P, LocalDyadicGood γ V δ
      (restrictTo (thickOpen V δ)
        (affineComp 1 (-z₀) (CellScaling.coneField (X ω) (CellScaling.coneRadial γ γ
          (fun t => B t ω) (fun t => B' t ω))))) := by
  filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ,
    ae_gamma_translated_localCircle_continuous_eventually D hγ V hδ z₀,
    ae_gamma_translated_areaApprox_finite_eventually D hγ V hVb z₀]
      with ω hv hc hf
  exact localDyadicGood_of_vague_continuity_finiteness γ V hVb hδ _
    (exists_isVagueLimitC_affineComp_one γ _ (-z₀) hv) hc hf

/-- The selected local dyadic GMC is the translated cone's actual area. -/
theorem ae_gamma_translated_localAreaVagueSelection_correct
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (z₀ : ℂ) :
    ∀ᵐ ω ∂P,
      localAreaVagueSelection γ V δ
        (restrictTo (thickOpen V δ)
          (affineComp 1 (-z₀) (CellScaling.coneField (X ω) (CellScaling.coneRadial γ γ
            (fun t => B t ω) (fun t => B' t ω))))) =
      ((CellScaling.lqgArea γ (CellScaling.coneField (X ω) (CellScaling.coneRadial γ γ
        (fun t => B t ω) (fun t => B' t ω)))).map
          (fun x => x + z₀)).restrict V := by
  filter_upwards [ae_gamma_translated_localDyadicGood D hγ V hVb hδ z₀,
    ae_gamma_translated_localCircle_continuous_eventually D hγ V hδ z₀,
    MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ]
      with ω hg hc hv
  have hv' := exists_isVagueLimitC_affineComp_one γ _ (-z₀) hv
  rw [localAreaVagueSelection_eq_lqgArea_of_ae_continuous γ V hδ _ hg hc hv']
  have hvP : ∃ μ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (CellScaling.coneField (X ω)
        (CellScaling.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) μ := hv
  rw [lqgArea_affineComp_one_of_vague γ _ (-z₀) hvP]
  congr 1
  congr 1
  funext x
  simp [subHomeo]

/-- A Borel shifted certificate for the translated cone's dyadic approximation. -/
theorem ae_gamma_translated_shiftedLocalAreaCert
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (z₀ : ℂ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ))) :
    ∀ᵐ ω ∂P, shiftedLocalAreaCert γ V δ J
      (restrictTo (thickOpen V δ)
        (affineComp 1 (-z₀) (CellScaling.coneField (X ω) (CellScaling.coneRadial γ γ
          (fun t => B t ω) (fun t => B' t ω))))) := by
  filter_upwards [ae_gamma_translated_localDyadicGood D hγ V hVb hδ z₀,
    ae_gamma_translated_localCircle_continuous_eventually D hγ V hδ z₀,
    ae_gamma_translated_areaApprox_finite_eventually D hγ V hVb z₀]
      with ω hg hc hf
  exact shiftedLocalAreaCert_of_vague_finite γ V δ J hJb _ _
    (localAreaVagueSelection_spec hg).1
    (eventually_finite_localAreaApproxDy_of_ae_continuous γ V hδ _ hc hf)

end MatedCRTHarmonic.GMS4c

