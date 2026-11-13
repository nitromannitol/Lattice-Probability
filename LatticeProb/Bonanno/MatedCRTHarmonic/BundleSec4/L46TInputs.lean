/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.L46TInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.ZeroConeIG
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.JointLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Transfer
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OBase
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFWP

/-!
# bundle inputs for the local comparison → the transfer adapter (phase version, phase independence, version transport)

The local comparison adds the IG phase `U` to the local observation of [18] (4.16)/Lemma 4.3:
`(restrictTo V h, restrictTo V hIG₀, U)`. The bundle's `U` and its raw cone fields are only a.e.-measurable, so the
consumers take measurable versions (the measurable-version argument). This file provides the bundle facts the adapter needs:

* `phaseVersion D` — a measurable version of `U` (`measurable_phaseVersion`, `phaseVersion_ae_eq`), with the same law;
* `indepFun_coneField_IG_phaseVersion`, `indepFun_zeroConeField_IG_phaseVersion` — the pair (raw γ-cone field, `hIG₀`)
  and the pair (raw 0-cone field, `hIG₀`) are independent of the phase (from the bundle's `indep_curve` and
  `igField`, through the continuous Brownian versions; the three-variable lemma
  `GMSCase.indepFun_prodMk_of_indepFun`);
* `coneFieldVersion`, `zeroConeFieldVersion` — one global measurable version of each raw cone field;
* `localFieldLawComparison_congr` — the `GMS4c.LocalFieldLawComparison` transported along a.e.-equal measurable
  versions of its four fields (used to move the per-disk versions to the global ones).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LQGMetric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-! ### Transport of a local field-law comparison along a.e.-equal versions -/

/-- **`GMS4c.LocalFieldLawComparison` along a.e.-equal measurable versions.** The density, its moment and the law
identity only see pushforward laws, which a.e.-equal observation maps share. -/
def localFieldLawComparison_congr {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ} {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {h₀ hIG₀ : Ω₀ → DistC} {p q : ℝ}
    (c : GMS4c.LocalFieldLawComparison V Pγ P₀ hγ hIGγ h₀ hIG₀ p q)
    {hγ' hIGγ' : Ωγ → DistC} {h₀' hIG₀' : Ω₀ → DistC}
    (mγ : Measurable (GMS4c.localFieldPair V hγ' hIGγ'))
    (m₀ : Measurable (GMS4c.localFieldPair V h₀' hIG₀'))
    (eγ : GMS4c.localFieldPair V hγ hIGγ =ᵐ[Pγ] GMS4c.localFieldPair V hγ' hIGγ')
    (e₀ : GMS4c.localFieldPair V h₀ hIG₀ =ᵐ[P₀] GMS4c.localFieldPair V h₀' hIG₀') :
    GMS4c.LocalFieldLawComparison V Pγ P₀ hγ' hIGγ' h₀' hIG₀' p q where
  gamma_measurable := mγ
  target_measurable := m₀
  density := c.density
  density_measurable := c.density_measurable
  law_eq := by
    rw [← Measure.map_congr eγ, ← Measure.map_congr e₀]
    exact c.law_eq
  moment_finite := by
    rw [← Measure.map_congr eγ]
    exact c.moment_finite
  conjugate := c.conjugate

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-! ### The phase version -/

theorem aemeasurable_phase
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable U P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif (IGLaw.period_pos_of_uniform D.igField.2.1)
    D.igField.2.1

/-- A measurable version of the bundle's IG phase `U`. -/
def phaseVersion
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Ω → ℝ :=
  (aemeasurable_phase D).mk U

theorem measurable_phaseVersion
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable (phaseVersion D) :=
  (aemeasurable_phase D).measurable_mk

theorem phaseVersion_ae_eq
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    phaseVersion D =ᵐ[P] U :=
  (aemeasurable_phase D).ae_eq_mk.symm

/-! ### Independence of the cone data and IG field from the phase -/

/-- `(hIG₀, Ũ) ⟂ (X, B, B', X₀, B₀, B₀')` for the measurable phase version `Ũ`. -/
theorem indepFun_IGphase_coneData
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (fun ω => (hIG₀ ω, phaseVersion D ω))
      (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
        (fun t => B₀ t ω), (fun t => B₀' t ω))) P := by
  refine D.indep_curve.congr ?_ (ae_eq_refl _)
  filter_upwards [phaseVersion_ae_eq D] with ω hω
  rw [hω]

/-- If `X ⟂ Y`, `(X, Y) ⟂ Z` (all measurable) then `(Z, Y) ⟂ X`. -/
theorem bundle_indepFun_pair_of_triple {Ω' α β δ : Type*} [MeasurableSpace Ω'] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace δ] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {X' : Ω' → α} {Y : Ω' → β} {Z : Ω' → δ}
    (hX : Measurable X') (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X' Y Q) (hXYZ : IndepFun (fun ω => (X' ω, Y ω)) Z Q) :
    IndepFun (fun ω => (Z ω, Y ω)) X' Q := by
  have h := GMSCase.indepFun_prodMk_of_indepFun hX hY hZ hXY hXYZ
  have hswap : Measurable fun p : β × δ => (p.2, p.1) := measurable_snd.prodMk measurable_fst
  exact (h.comp measurable_id hswap).symm

/-- **The pair (raw γ-cone field, `hIG₀`) is independent of the phase version.** -/
theorem indepFun_coneField_IG_phaseVersion
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => (MatedCRT.coneField (X ω)
      (MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)), hIG₀ ω)) (phaseVersion D) P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B'
  let coneXBB : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) →
      MatedCRT.Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) := fun q => (q.1, (q.2.1, q.2.2.1))
  have hconeXBB : Measurable coneXBB :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hXBB : IndepFun (fun ω => (hIG₀ ω, phaseVersion D ω))
      (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) P :=
    (indepFun_IGphase_coneData D).comp measurable_id hconeXBB
  have hpath : (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) =ᵐ[P]
      fun ω => (X ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hXBc : IndepFun (fun ω => (hIG₀ ω, phaseVersion D ω)) (fun ω => (X ω, (Bc ω, Bc' ω))) P :=
    IGLaw.indepFun_triple_continuousMap_of_coe (hXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω)
  have hWm : Measurable W := (ConeScaling.measurable_radMap γ γ).comp (hBcm.prodMk hBc'm)
  have hF : Measurable fun p : MatedCRT.Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  let F : Ω → MatedCRT.Field := fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω)
  have hFm : Measurable F := hF.comp (D.gff.measurable.prodMk hWm)
  have hIGF : IndepFun (fun ω => (hIG₀ ω, phaseVersion D ω)) F P :=
    hXBc.comp measurable_id (hF.comp (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ γ).comp measurable_snd)))
  -- the version `F` agrees a.s. with the raw cone field
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B.eval_zero_ae_eq_zero,
      D.bm_B'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B' (CellScaling.lqgQ_sub_pos hγ.1 hγ.2)]
        with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ γ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ γ (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ γ (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hFeq : F =ᵐ[P] fun ω => MatedCRT.coneField (X ω)
      (MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) := by
    filter_upwards [hW] with ω hω
    show ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω) = _
    rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
    exact (ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hω).symm
  -- the three-variable step
  have hIGm : Measurable hIG₀ := D.igField.1.1.measurable
  have hUH : IndepFun (phaseVersion D) hIG₀ P := by
    refine (D.igField.2.2.symm).congr ?_ (ae_eq_refl _)
    exact (phaseVersion_ae_eq D).symm
  have hswap : Measurable fun p : MatedCRT.Field × ℝ => (p.2, p.1) :=
    measurable_snd.prodMk measurable_fst
  have hUHF : IndepFun (fun ω => (phaseVersion D ω, hIG₀ ω)) F P :=
    hIGF.comp hswap measurable_id
  have htriple := bundle_indepFun_pair_of_triple (measurable_phaseVersion D) hIGm hFm hUH hUHF
  refine htriple.congr ?_ (ae_eq_refl _)
  filter_upwards [hFeq] with ω hω
  rw [hω]

/-- **The pair (raw 0-cone field, `hIG₀`) is independent of the phase version.** -/
theorem indepFun_zeroConeField_IG_phaseVersion
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => (MatedCRT.coneField (X₀ ω)
      (MatedCRT.coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)), hIG₀ ω)) (phaseVersion D) P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B₀
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B₀'
  let zeroData : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × MatedCRT.Field ×
      (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → MatedCRT.Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :=
    fun q => (q.2.2.2.1, (q.2.2.2.2.1, q.2.2.2.2.2))
  have hzeroData : Measurable zeroData := by fun_prop
  have hXBB : IndepFun (fun ω => (hIG₀ ω, phaseVersion D ω))
      (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) P :=
    (indepFun_IGphase_coneData D).comp measurable_id hzeroData
  have hpath : (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) =ᵐ[P]
      fun ω => (X₀ ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hXBc : IndepFun (fun ω => (hIG₀ ω, phaseVersion D ω)) (fun ω => (X₀ ω, (Bc ω, Bc' ω))) P :=
    IGLaw.indepFun_triple_continuousMap_of_coe (hXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ 0 (Bc ω, Bc' ω)
  have hWm : Measurable W := (ConeScaling.measurable_radMap γ 0).comp (hBcm.prodMk hBc'm)
  have hF : Measurable fun p : MatedCRT.Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  let F : Ω → MatedCRT.Field := fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω)
  have hFm : Measurable F := hF.comp (D.gff₀.measurable.prodMk hWm)
  have hIGF : IndepFun (fun ω => (hIG₀ ω, phaseVersion D ω)) F P :=
    hXBc.comp measurable_id (hF.comp (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ 0).comp measurable_snd)))
  have hQ0 : 0 < CellScaling.lqgQ γ - 0 := by
    have hq := CellScaling.lqgQ_sub_pos hγ.1 hγ.2
    linarith [hγ.1]
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B₀.eval_zero_ae_eq_zero,
      D.bm_B₀'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B₀' hQ0]
        with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B₀ s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B₀' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ 0 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ 0 (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ 0 (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hFeq : F =ᵐ[P] fun ω => MatedCRT.coneField (X₀ ω)
      (MatedCRT.coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)) := by
    filter_upwards [hW] with ω hω
    show ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω) = _
    rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
    simp only [CellScaling.coneField, ConeScaling.fieldOf]
    have he : ConeScaling.radialOf (W ω) =
        (fun z : ℂ => CellScaling.coneRadial γ 0
          (fun t => B₀ t ω) (fun t => B₀' t ω) (-Real.log ‖z‖)) := by
      funext z
      exact hω (-Real.log ‖z‖)
    rw [he]
  have hIGm : Measurable hIG₀ := D.igField.1.1.measurable
  have hUH : IndepFun (phaseVersion D) hIG₀ P := by
    refine (D.igField.2.2.symm).congr ?_ (ae_eq_refl _)
    exact (phaseVersion_ae_eq D).symm
  have hswap : Measurable fun p : MatedCRT.Field × ℝ => (p.2, p.1) :=
    measurable_snd.prodMk measurable_fst
  have hUHF : IndepFun (fun ω => (phaseVersion D ω, hIG₀ ω)) F P :=
    hIGF.comp hswap measurable_id
  have htriple := bundle_indepFun_pair_of_triple (measurable_phaseVersion D) hIGm hFm hUH hUHF
  refine htriple.congr ?_ (ae_eq_refl _)
  filter_upwards [hFeq] with ω hω
  rw [hω]

end Bundle

end MatedCRTHarmonic.BundleSec4
