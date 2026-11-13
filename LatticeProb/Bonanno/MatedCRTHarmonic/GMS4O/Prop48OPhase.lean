/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OPhase at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhaseHaar
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhaseIG
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhaseCone

/-!
# Phase independence of the zero-cone curve

**Missing step in [18].** In the proof of Lemma 4.9
The observed IG average `a₂ = h^IG_r(z)` is subtracted from the IG field and Theorem 4.4 is applied
to the recentred pair. Adding a constant `c` to an imaginary-geometry field rotates every flow line
by `c/χ`, so the recentred curve is not the curve of the recentred field: one needs that the law of a
*rotation-invariant* functional of the curve does not depend on the IG additive constant. In the
frozen coupling the IG field driving `ηL` is `hIG₀ + U`, with a uniform phase `U` shared by every
point. Conditioning on the full IG average `h^IG_r(z) + U` (the corrected (4.22)
observation) makes Lemma 4.9 require a moment bound uniform in the phase, and conditioning on
`hIG₀` alone makes the far-pair step of Proposition 4.8 require that the conditional mean not depend
on the phase. Both follow from:

* `p48o_indepFun_rotInvariant_zeroConeCurve_phase`: for every measurable rotation-invariant
  functional `Ψ` of a curve, `Ψ(η₀)` is independent of the IG phase `U`.

Proof: rotating the 0-cone field and the IG field by `θ` and shifting the phase by `-χθ` (mod `2πχ`)
preserves the law of the data (`p48o_map_rotateField_zeroCone`, `p48o_map_rotate_phase_eq`, and
`p48o_zeroCone_indepFun_IGdata`), rotates the Lebesgue curve (`p48o_ig_rotation_package`), rotates
The GMC and hence the area-parametrized curve (`p48o_ae_isVagueLimitC_rotateField_zeroCone`,
`p48o_parEval_rot`). So the law of `(Ψ(η₀), U)` is invariant under every phase shift, and Haar
uniqueness on the circle gives independence (`p48o_indepFun_real_of_shift`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4O

open LQGMetric MatedCRTHarmonic.IGLaw

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-! ### Curves and their underlying functions -/

/-- The σ-algebra of (curve, real) pairs is the trace of that of (function, real) pairs. -/
theorem p48o_prod_measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace (C(ℝ, ℂ) × ℝ)) =
      MeasurableSpace.comap (fun p : C(ℝ, ℂ) × ℝ => ((⇑p.1 : ℝ → ℂ), p.2)) inferInstance := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [CellScaling.JointScalingO.measurableSpace_continuousMap_complex_eq_comap,
        MeasurableSpace.comap_comp, MeasurableSpace.comap_le_iff_le_map]
      intro s hs
      exact ⟨Prod.fst ⁻¹' s, measurable_fst hs, rfl⟩
    · rw [MeasurableSpace.comap_le_iff_le_map]
      intro s hs
      exact ⟨Prod.snd ⁻¹' s, measurable_snd hs, rfl⟩
  · exact (Measurable.prodMk
      (CellScaling.JointScalingO.measurable_coe_continuousMap_complex.comp measurable_fst)
      measurable_snd).comap_le

/-- Equality of the laws of (function, real) pairs gives equality of the laws of the (curve, real)
pairs. -/
theorem p48o_map_prod_eq_of_map_coe_eq {f g : Ω → C(ℝ, ℂ)} {u v : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hu : AEMeasurable u P) (hv : AEMeasurable v P)
    (h : P.map (fun ω => ((⇑(f ω) : ℝ → ℂ), u ω)) = P.map (fun ω => ((⇑(g ω) : ℝ → ℂ), v ω))) :
    P.map (fun ω => (f ω, u ω)) = P.map (fun ω => (g ω, v ω)) := by
  have hfu : AEMeasurable (fun ω => (f ω, u ω)) P := hf.aemeasurable.prodMk hu
  have hgv : AEMeasurable (fun ω => (g ω, v ω)) P := hg.aemeasurable.prodMk hv
  have hcm : Measurable fun p : C(ℝ, ℂ) × ℝ => ((⇑p.1 : ℝ → ℂ), p.2) :=
    (CellScaling.JointScalingO.measurable_coe_continuousMap_complex.comp measurable_fst).prodMk
      measurable_snd
  ext S hS
  have hS' : MeasurableSet[MeasurableSpace.comap
      (fun p : C(ℝ, ℂ) × ℝ => ((⇑p.1 : ℝ → ℂ), p.2)) inferInstance] S := by
    rw [← p48o_prod_measurableSpace_eq_comap]
    exact hS
  obtain ⟨T, hT, rfl⟩ := hS'
  rw [Measure.map_apply_of_aemeasurable hfu (hcm hT),
    Measure.map_apply_of_aemeasurable hgv (hcm hT)]
  have h1 := congrArg (fun μ : Measure ((ℝ → ℂ) × ℝ) => μ T) h
  have hfu' : AEMeasurable (fun ω => ((⇑(f ω) : ℝ → ℂ), u ω)) P := hcm.comp_aemeasurable hfu
  have hgv' : AEMeasurable (fun ω => ((⇑(g ω) : ℝ → ℂ), v ω)) P := hcm.comp_aemeasurable hgv
  simp only [Measure.map_apply_of_aemeasurable hfu' hT,
    Measure.map_apply_of_aemeasurable hgv' hT] at h1
  exact h1

/-! ### The zero-cone curve -/

/-- **The zero-cone curve is the area parametrization of `ηL`** (the area-scaling construction's `parEval`), almost surely. -/
theorem p48o_ae_coe_eta0_eq_parEval
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, (⇑(η₀ ω) : ℝ → ℂ) =
      fun t => CellScaling.JointScalingO.parEval γ (p48oZeroConeField γ X₀ B₀ B₀' ω) (ηL ω) t := by
  filter_upwards [D.areaParam₀, p48o_ae_isVagueLimitC_rotateField_zeroCone D hγ 0] with ω hpar hv
  obtain ⟨⟨φ, hφ0, hφ⟩, hareaμ⟩ := hpar
  have harea : ∀ s t : ℝ, s ≤ t →
      CellScaling.lqgArea γ (p48oZeroConeField γ X₀ B₀ B₀' ω) (η₀ ω '' Icc s t) =
        ENNReal.ofReal (t - s) :=
    hareaμ _ hv.1
  exact CellScaling.JointScalingO.coe_eq_parEval_of_areaParam ⟨_, hv.1⟩ hφ0 hφ harea

/-- **The law of (zero-cone curve, phase) is invariant under rotation with phase shift.** For
every angle `θ`, `(e^{-iθ} η₀, (U − χθ) mod 2πχ)` has the law of `(η₀, U)`. -/
theorem p48o_map_zeroConeCurve_phase_shift
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * MatedCRT.igChi γ)] (θ : ℝ) :
    P.map (fun ω => (rotCurve (-θ) (η₀ ω),
        modRep (2 * Real.pi * MatedCRT.igChi γ) (-(MatedCRT.igChi γ * θ) + U ω))) =
      P.map (fun ω => (η₀ ω, U ω)) := by
  have := D.isProbabilityMeasure
  obtain ⟨Φ, hΦ, hroot, hrot⟩ := p48o_ig_rotation_package D
  have hh₀ : AEMeasurable (p48oZeroConeField γ X₀ B₀ B₀') P :=
    p48o_aemeasurable_zeroConeField D hγ
  have hUlaw : P.map U = volume[|Ico (0 : ℝ) (2 * Real.pi * MatedCRT.igChi γ)] := D.igField.2.1
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif (period_pos_of_uniform hUlaw) hUlaw
  have hIGU : AEMeasurable (fun ω => (hIG₀ ω, U ω)) P :=
    D.igField.1.1.measurable.aemeasurable.prodMk hUm
  -- the law of the data is invariant
  let Gθ : MatedCRT.Field × ℝ → MatedCRT.Field × ℝ := fun p =>
    (MoTPort.rotateField θ p.1,
      modRep (2 * Real.pi * MatedCRT.igChi γ) (-(MatedCRT.igChi γ * θ) + p.2))
  have hGθ : Measurable Gθ :=
    ((MoTPort.measurable_rotateField θ).comp measurable_fst).prodMk
      ((measurable_modRep _).comp (measurable_const.add measurable_snd))
  have hind : IndepFun (p48oZeroConeField γ X₀ B₀ B₀') (fun ω => (hIG₀ ω, U ω)) P :=
    p48o_zeroCone_indepFun_IGdata D hγ
  have hindθ : IndepFun (fun ω => MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω))
      (fun ω => Gθ (hIG₀ ω, U ω)) P := hind.comp (MoTPort.measurable_rotateField θ) hGθ
  have hRh₀ : AEMeasurable (fun ω => MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω)) P :=
    (MoTPort.measurable_rotateField θ).comp_aemeasurable hh₀
  have hGIG : AEMeasurable (fun ω => Gθ (hIG₀ ω, U ω)) P := hGθ.comp_aemeasurable hIGU
  have hdata : P.map (fun ω => (MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω),
        Gθ (hIG₀ ω, U ω))) =
      P.map (fun ω => (p48oZeroConeField γ X₀ B₀ B₀' ω, (hIG₀ ω, U ω))) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hRh₀ hGIG).1 hindθ,
      (indepFun_iff_map_prod_eq_prod_map_map hh₀ hIGU).1 hind,
      p48o_map_rotateField_zeroCone D hγ θ]
    congr 1
    exact p48o_map_rotate_phase_eq D θ
  -- the measurable reconstruction of (curve, phase) from the data
  let G : DistC × (MatedCRT.Field × ℝ) → (ℝ → ℂ) × ℝ := fun p =>
    ((fun t => CellScaling.JointScalingO.parEval γ p.1 (Φ (igCircleAvgInput p.2)) t), p.2.2)
  have hG : Measurable G := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun t => ?_) (measurable_snd.comp measurable_snd)
    exact (CellScaling.JointScalingO.measurable_parEval γ t).comp
      (measurable_fst.prodMk (hΦ.comp (measurable_igCircleAvgInput.comp measurable_snd)))
  have hΞ : AEMeasurable (fun ω => (p48oZeroConeField γ X₀ B₀ B₀' ω, (hIG₀ ω, U ω))) P :=
    hh₀.prodMk hIGU
  have hΞθ : AEMeasurable (fun ω => (MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω),
      Gθ (hIG₀ ω, U ω))) P :=
    hRh₀.prodMk hGIG
  have e0 : (fun ω => ((⇑(η₀ ω) : ℝ → ℂ), U ω)) =ᵐ[P]
      G ∘ fun ω => (p48oZeroConeField γ X₀ B₀ B₀' ω, (hIG₀ ω, U ω)) := by
    filter_upwards [p48o_ae_coe_eta0_eq_parEval D hγ, hroot] with ω h1 h2
    simp only [Function.comp_apply, G]
    rw [h1, ← h2]
  have eθ : (fun ω => ((⇑(rotCurve (-θ) (η₀ ω)) : ℝ → ℂ),
        modRep (2 * Real.pi * MatedCRT.igChi γ) (-(MatedCRT.igChi γ * θ) + U ω))) =ᵐ[P]
      G ∘ fun ω => (MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω),
        Gθ (hIG₀ ω, U ω)) := by
    filter_upwards [p48o_ae_coe_eta0_eq_parEval D hγ, hrot θ,
      p48o_ae_isVagueLimitC_rotateField_zeroCone D hγ θ] with ω h1 h2 hv
    refine Prod.ext ?_ rfl
    funext t
    have h3 := p48o_parEval_rot θ hv.1 hv.2 (ηL ω) t
    rw [p48oRotCurve_eq_rotCurve] at h3
    change (rotCurve (-θ) (η₀ ω)) t = CellScaling.JointScalingO.parEval γ
      (MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω))
      (Φ (igCircleAvgInput (MoTPort.rotateField θ (hIG₀ ω),
        modRep (2 * Real.pi * MatedCRT.igChi γ) (-(MatedCRT.igChi γ * θ) + U ω)))) t
    rw [h2, h3, ← congrFun h1 t, ← p48oRotCurve_eq_rotCurve, p48oRotCurve_apply, p48oRot_apply]
  have hfun : P.map (fun ω => ((⇑(rotCurve (-θ) (η₀ ω)) : ℝ → ℂ),
        modRep (2 * Real.pi * MatedCRT.igChi γ) (-(MatedCRT.igChi γ * θ) + U ω))) =
      P.map (fun ω => ((⇑(η₀ ω) : ℝ → ℂ), U ω)) := by
    rw [Measure.map_congr eθ, Measure.map_congr e0,
      ← AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hΞθ,
      ← AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hΞ, hdata]
  have hη : Measurable η₀ := D.measurable_curves.2.2.1
  exact p48o_map_prod_eq_of_map_coe_eq ((measurable_rotCurve (-θ)).comp hη) hη
    ((measurable_modRep _).comp_aemeasurable (aemeasurable_const.add hUm)) hUm hfun

/-- **Phase independence of the zero-cone curve.** Every measurable functional of the curve that is
invariant under rotations about the origin is independent of the IG phase `U`. -/
theorem p48o_indepFun_rotInvariant_zeroConeCurve_phase
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {β : Type*} [MeasurableSpace β]
    {Ψ : C(ℝ, ℂ) → β} (hΨ : Measurable Ψ) (hrotΨ : ∀ (θ : ℝ) (c : C(ℝ, ℂ)), Ψ (rotCurve θ c) = Ψ c) :
    IndepFun (fun ω => Ψ (η₀ ω)) U P := by
  have := D.isProbabilityMeasure
  have hr : 0 < 2 * Real.pi * MatedCRT.igChi γ := p48o_period_pos D
  have : Fact (0 < 2 * Real.pi * MatedCRT.igChi γ) := ⟨hr⟩
  have hχ : MatedCRT.igChi γ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hr
    exact lt_irrefl 0 hr
  have hη : Measurable η₀ := D.measurable_curves.2.2.1
  have hUlaw : P.map U = volume[|Ico (0 : ℝ) (2 * Real.pi * MatedCRT.igChi γ)] := D.igField.2.1
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hr hUlaw
  refine p48o_indepFun_real_of_shift (hΨ.comp hη) hUlaw fun c => ?_
  set θ : ℝ := -(c / MatedCRT.igChi γ) with hθ
  have hc : -(MatedCRT.igChi γ * θ) = c := by
    rw [hθ]
    field_simp
  have hlaw := p48o_map_zeroConeCurve_phase_shift D hγ θ
  rw [hc] at hlaw
  have hm : Measurable fun p : C(ℝ, ℂ) × ℝ => (Ψ p.1, p.2) :=
    (hΨ.comp measurable_fst).prodMk measurable_snd
  have h1 : AEMeasurable (fun ω => (rotCurve (-θ) (η₀ ω),
      modRep (2 * Real.pi * MatedCRT.igChi γ) (c + U ω))) P :=
    ((measurable_rotCurve (-θ)).comp hη).aemeasurable.prodMk
      ((measurable_modRep _).comp_aemeasurable (aemeasurable_const.add hUm))
  have h2 : AEMeasurable (fun ω => (η₀ ω, U ω)) P := hη.aemeasurable.prodMk hUm
  have hpush := congrArg (Measure.map fun p : C(ℝ, ℂ) × ℝ => (Ψ p.1, p.2)) hlaw
  rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable h1,
    AEMeasurable.map_map_of_aemeasurable hm.aemeasurable h2] at hpush
  simpa only [Function.comp_def, hrotΨ] using hpush

end MatedCRTHarmonic.GMS4O
