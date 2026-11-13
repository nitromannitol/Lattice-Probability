/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.Bundle at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.ConeLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.IGData

/-!
# The Case 3 and Case 4 laws on the frozen mating-of-trees coupling

Source: (`[18]:N`), Proposition 4.10, Cases 2–4 and the final
paragraph, `[18]`; (inverse coordinate `2(w − z₀)`); the
IG observation is `(hIG₀, U)`, field plus phase).

On the frozen coupling `D`, the **full IG observation** is `igObs ω = ((hIG₀ ω, U ω), ηL ω)`, the
Case 0–4 whole-plane field is the normalized `X₀` (`normalizedWP (X₀ ω)`, definitionally CANON's
`Canon.normalizeWholePlane (X₀ ω)`), and the γ-cone field is
`coneField (X ω) (coneRadial γ γ B B')` (the field of `MoTInput.cellModelOfCoupling`).

* `map_igTransform_igObs`: the Case 4 transformation `igTransform r z₀` (IG field `hIG₀(·/2 + z₀)`
  renormalized, phase shifted by `(hIG₀)_{1/2}(z₀)` modulo `r = 2πχ`, curve `case4Curve z₀ ηL`)
  preserves the law of `igObs` (from IGData's `map_igTransform_of_ccPos` and the v4 `igMap`).
* `indepFun_coneTuple_igObs`, `indepFun_normalizedWP_igObs`, `indepFun_coneField_igObs`: the IG
  observation is independent of the cone data, of the normalized `X₀` and of the γ-cone field.
* **`map_case4Local_eq_cone`** (Case 4 ↔ cone, fixed root): the law of
  `(case4Field γ (normalizedWP X₀) z₀ |_𝔻, igTransform r z₀ igObs)` equals the law of
  `(γ-cone field |_𝔻, igObs)`.
* **`map_case3_marked_cone`** (Cases 2–4 with an independent root `z₀ ∼ λ`, `B̄_{1/2}(z₀) ⊆ B̄_1(0)`
  λ-a.s.): under `P ⊗ λ`, the law of `((z₀, (normalizedWP X₀)_{1/2}(z₀)),
  (case4Field|_𝔻, igTransform r z₀ igObs))` is `law(z₀, h_{1/2}(z₀)) ⊗ law(cone|_𝔻, igObs)`.
  The Case 2 index of [18] is `(normalizedWP X₀)_{1/2}(z₀) + γ log 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw

/-- The full imaginary-geometry observation `((hIG₀, U), ηL)`. -/
def igObs {Ω : Type*} (hIG₀ : Ω → Field) (U : Ω → ℝ) (ηL : Ω → C(ℝ, ℂ)) (ω : Ω) :
    (DistC × ℝ) × C(ℝ, ℂ) :=
  ((hIG₀ ω, U ω), ηL ω)

/-- The cone tuple `(X, B, B', X₀, B₀, B₀')` of the frozen bundle. -/
def coneTuple {Ω : Type*} (X X₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω, (fun t => B₀ t ω), (fun t => B₀' t ω))

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The IG period `2πχ` is positive. -/
theorem igPeriod_pos (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    0 < 2 * Real.pi * igChi γ := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact period_pos_of_uniform D.igField.2.1

/-- The phase `U` is almost everywhere measurable. -/
theorem aemeasurable_phase (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable U P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif (igPeriod_pos D) D.igField.2.1

theorem aemeasurable_igObs (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (igObs hIG₀ U ηL) P :=
  (D.igField.1.1.measurable.aemeasurable.prodMk (aemeasurable_phase D)).prodMk
    D.measurable_curves.1.aemeasurable

/-- The IG observation is a.s. a measurable function of the IG field and phase. -/
theorem exists_igObs_factor (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ G : DistC × ℝ → (DistC × ℝ) × C(ℝ, ℂ), Measurable G ∧
      igObs hIG₀ U ηL =ᵐ[P] fun ω => G (hIG₀ ω, U ω) := by
  obtain ⟨Φ, hΦ, hroot, -⟩ := igMapPos_of_igMapPositiveRadii (IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D)
  refine ⟨fun p => (p, Φ (posIn (igCircleAvgInput p))),
    measurable_id.prodMk (hΦ.comp (measurable_posIn.comp measurable_igCircleAvgInput)), ?_⟩
  filter_upwards [hroot] with ω hω
  show ((hIG₀ ω, U ω), ηL ω) = ((hIG₀ ω, U ω), Φ (posIn (igCircleAvgInput (hIG₀ ω, U ω))))
  rw [hω]
  rfl

/-- The IG observation is independent of the cone tuple `(X, B, B', X₀, B₀, B₀')`. -/
theorem indepFun_coneTuple_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (coneTuple X X₀ B B' B₀ B₀') (igObs hIG₀ U ηL) P := by
  obtain ⟨G, hG, hfac⟩ := exists_igObs_factor D
  have h1 : IndepFun (coneTuple X X₀ B B' B₀ B₀') (fun ω => (hIG₀ ω, U ω)) P :=
    D.indep_curve.symm
  exact (h1.comp measurable_id hG).congr (ae_eq_refl _) hfac.symm

/-- **The γ-cone field is independent of the IG observation** (IGCO's
`indepFun_coneField_ηL`, with the IG field and phase retained). -/
theorem indepFun_coneField_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))
      (igObs hIG₀ U ηL) P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B'
  let coneXBB : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) →
      Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) := fun q => (q.1, (q.2.1, q.2.2.1))
  have hconeXBB : Measurable coneXBB :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hηXBB : IndepFun (igObs hIG₀ U ηL)
      (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) P :=
    ((indepFun_coneTuple_igObs D).comp hconeXBB measurable_id).symm
  have hpath : (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) =ᵐ[P]
      fun ω => (X ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hηXBc : IndepFun (igObs hIG₀ U ηL) (fun ω => (X ω, (Bc ω, Bc' ω))) P :=
    indepFun_triple_continuousMap_of_coe (hηXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω)
  have hηXW : IndepFun (igObs hIG₀ U ηL) (fun ω => (X ω, W ω)) P :=
    hηXBc.comp measurable_id (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ γ).comp measurable_snd))
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B.eval_zero_ae_eq_zero, D.bm_B'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B' (CellScaling.lqgQ_sub_pos hγ.1 hγ.2)] with ω h1 h2 h3 h4 hdrift t
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
  have hF : Measurable fun p : Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  have hind : IndepFun (fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω))
      (igObs hIG₀ U ηL) P :=
    (hηXW.comp measurable_id hF).symm
  refine hind.congr ?_ (ae_eq_refl _)
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact (ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hω).symm

/-- The γ-cone field is almost everywhere measurable (through IGCO's measurable radial path). -/
theorem aemeasurable_coneField
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (fun ω => coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) P := by
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B'
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω)
  have hWm : Measurable W := (ConeScaling.measurable_radMap γ γ).comp (hBcm.prodMk hBc'm)
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B.eval_zero_ae_eq_zero, D.bm_B'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B' (CellScaling.lqgQ_sub_pos hγ.1 hγ.2)] with ω h1 h2 h3 h4 hdrift t
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
  have hF : Measurable fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω) :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp D.gff.measurable).prodMk hWm)
  refine hF.aemeasurable.congr ?_
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact (ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hω).symm

end Bundle

end MatedCRTHarmonic.GMSCase
