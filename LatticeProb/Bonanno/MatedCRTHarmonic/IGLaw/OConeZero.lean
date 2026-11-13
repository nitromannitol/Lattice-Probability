/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OConeZero at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OBase
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.OpenSupport

/-!
# The α-quantum cone at its mass scale, for every `α < Q` (used at `α = 0`)

[18] Theorem 4.4 works with the `0`-quantum cone. DMS Proposition 4.13(i) and the auxiliary
facts for the γ-cone (`α = γ`) extend to `α < Q`. This file supplies the
α-general wrappers in the `CellScaling` namespace:

* `indepFun_triple_continuousMap_of_coe`: independence from `(Y, U, V)` for continuous paths `U, V` is independence
  from `(Y, ⇑U, ⇑V)`;
* `exists_radialPath_alpha`: a measurable continuous version `W` of the radial path `coneRadial γ α B B'` with
  `X ⊥ W` and `(X, W) ⊥ ηL` whenever `X ⊥ (B, B')` and `ηL ⊥ (X, B, B')`;
* `map_radShift_coneRadial_alpha`: the radial law at the last level (DMS Prop 4.13(i), radial part), copied from
  `map_radShift_coneRadial` with `γ` replaced by `α`;
* `indepFun_motConeRadial_alpha`: the hypothesis `hXA` for the α-cone;
* `ae_lqgArea_coneRescaleField_alpha`: the area covariance at the cone scale, `μ_{h_b}(A) = b⁻¹ μ_h(R A)`, for the
  α-cone field, simultaneously in `R`, `b`, `A`;
* `coneScale_eq_exp_lastLevel_alpha`, `coneField_eq_fieldOf_alpha`: the cone scale and field in the lateral/radial coordinates.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.IGLaw

open LQGMetric

/-- Independence from `(Y, (U, V))` for continuous paths `U, V` is independence from their underlying functions
(the triple form of `indepFun_pair_continuousMap_of_coe`). -/
theorem indepFun_triple_continuousMap_of_coe {Ω β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSpace δ] {P : Measure Ω} {f : Ω → β} {Y : Ω → δ} {U V : Ω → C(ℝ≥0, ℝ)}
    (h : IndepFun f (fun ω => (Y ω, ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)))) P) :
    IndepFun f (fun ω => (Y ω, (U ω, V ω))) P := by
  have hc : Measurable fun f : C(ℝ≥0, ℝ) => (⇑f : ℝ≥0 → ℝ) :=
    measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t
  have hσ : MeasurableSpace.comap (fun ω => (Y ω, (U ω, V ω)))
        (inferInstance : MeasurableSpace (δ × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)))) =
      MeasurableSpace.comap (fun ω => (Y ω, ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ))))
        (inferInstance : MeasurableSpace (δ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)))) := by
    apply le_antisymm
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap
        (fun ω => (Y ω, ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)))) inferInstance
      have hm : Measurable fun ω => (Y ω, ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ))) :=
        comap_measurable _
      exact (measurable_fst.comp hm).prodMk
        ((ContinuousMap.measurable_iff_eval.2 fun t =>
          (measurable_pi_apply t).comp (measurable_fst.comp (measurable_snd.comp hm))).prodMk
        (ContinuousMap.measurable_iff_eval.2 fun t =>
          (measurable_pi_apply t).comp (measurable_snd.comp (measurable_snd.comp hm))))
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (Y ω, (U ω, V ω))) inferInstance
      have hm : Measurable fun ω => (Y ω, (U ω, V ω)) := comap_measurable _
      exact ((measurable_fst.comp hm).prodMk
        ((hc.comp (measurable_fst.comp (measurable_snd.comp hm))).prodMk
          (hc.comp (measurable_snd.comp (measurable_snd.comp hm)))))
  unfold IndepFun Kernel.IndepFun at h ⊢
  rw [hσ]
  exact h

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The α-cone's radial path as a measurable continuous version**, independent of the GFF `X`, and jointly with
`X` independent of a curve `ηL` independent of `(X, B, B')`. -/
theorem exists_radialPath_alpha {β : Type*} [MeasurableSpace β] {γ α : ℝ}
    (hαQ : 0 < CellScaling.lqgQ γ - α) {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {ηL : Ω → β}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hXBB : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P)
    (hηXBB : IndepFun ηL (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) P) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧ IndepFun X W P ∧ IndepFun (fun ω => (X ω, W ω)) ηL P ∧
      ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω) t := by
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version hB
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version hB'
  have hpath : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P]
      fun ω => ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ)) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hXC : IndepFun X (fun ω => (Bc ω, Bc' ω)) P :=
    ConeScaling.indepFun_pair_continuousMap_of_coe (hXBB.congr (ae_eq_refl _) hpath)
  have hpath3 : (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) =ᵐ[P]
      fun ω => (X ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hpath] with ω hω
    exact congrArg (fun p => (X ω, p)) hω
  have hηC : IndepFun ηL (fun ω => (X ω, (Bc ω, Bc' ω))) P :=
    indepFun_triple_continuousMap_of_coe (hηXBB.congr (ae_eq_refl _) hpath3)
  have hrm := ConeScaling.measurable_radMap γ α
  refine ⟨fun ω => ConeScaling.radMap γ α (Bc ω, Bc' ω), hrm.comp (hBcm.prodMk hBc'm),
    hXC.comp measurable_id hrm, ?_, ?_⟩
  · have hG : Measurable fun p : DistC × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) =>
        (p.1, ConeScaling.radMap γ α p.2) := measurable_fst.prodMk (hrm.comp measurable_snd)
    exact (hηC.comp measurable_id hG).symm
  · filter_upwards [hBc, hBc', hB.eval_zero_ae_eq_zero, hB'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift hB' hαQ] with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ α := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ α (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ α (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]

/-- **The radial law of the α-quantum cone** (DMS Prop 4.13(i), radial part, `α < Q`): for a measurable continuous
version `W` of `coneRadial γ α B B'`, every last-level recentring `radShift Q y W` has the law of `W`. -/
theorem map_radShift_coneRadial_alpha [IsProbabilityMeasure P] {γ α : ℝ}
    (hαQ : α < CellScaling.lqgQ γ) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P) {W : Ω → C(ℝ, ℝ)}
    (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω) t)
    (y : ℝ) :
    P.map (fun ω => ConeScaling.radShift (CellScaling.lqgQ γ) y (W ω)) = P.map W := by
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by
    dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  let A : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t
  have hA : MoTPort.IsConeProcess α (CellScaling.lqgQ γ) A P := by
    rw [hQ]; exact LQGCone.isConeProcess_motConeRadial hB hB' hBB'
  have hWA : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.lqgQ γ * t + A t ω := by
    filter_upwards [hW] with ω hω t
    rw [hω, LQGCone.coneRadial_eq_Q_add_motConeRadial]
  have hdpos : 0 < CellScaling.lqgQ γ - α := by linarith
  have hgood : ∀ᵐ ω ∂P, ConeScaling.IsGoodRadial (CellScaling.lqgQ γ) (W ω) := by
    filter_upwards [hW, hB.eval_zero_ae_eq_zero, CellScaling.ae_goodDrift hB' hdpos] with ω hω h0 hdrift
    refine ⟨?_, fun s hs => ?_⟩
    · rw [hω, CellScaling.coneRadial, ite_eq_left (le_refl (0 : ℝ))]
      simp [h0]
    · have e : W ω (-s) + CellScaling.lqgQ γ * s =
          CellScaling.coneLogRadial γ α (fun t => B t ω) (fun t => B' t ω) s := by
        rw [hω]; rfl
      rw [e, CellScaling.coneLogRadial_of_pos _ _ _ _ hs]
      exact hdrift.pos_of_lastZeroR_lt (by linarith [hdrift.lastZeroR_nonneg])
  exact ConeScaling.map_radShift_of_good hWm
    (fun y hy => ConeScaling.map_radShift_of_neg hA hαQ hWm hWA hy) hgood y

/-- **The GFF is independent of the α-cone process** (the hypothesis `hXA`). -/
theorem indepFun_motConeRadial_alpha {γ α : ℝ} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    {W : Ω → C(ℝ, ℝ)} (hXW : IndepFun X W P)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω) t) :
    IndepFun X (fun ω t => LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P := by
  let G : C(ℝ, ℝ) → (ℝ → ℝ) := fun w t => w t - CellScaling.lqgQ γ * t
  have hG : Measurable G :=
    measurable_pi_iff.2 fun t => (ContinuousMap.measurable_eval t).sub_const _
  refine (hXW.comp measurable_id hG).congr (ae_eq_refl _) ?_
  filter_upwards [hW] with ω hω
  funext t
  simp only [Function.comp_apply, G, hω, LQGCone.motConeRadial]

/-- **The area at the random scale for the α-cone** (the covariance): a.s., for every `R > 0`, `b > 0` and set `A`,
`μ_{h_b}(A) = b⁻¹ μ_h(R A)` with `h = coneField X (coneRadial γ α B B')`. -/
theorem ae_lqgArea_coneRescaleField_alpha {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < CellScaling.lqgQ γ) (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ b₀ : ℝ, 0 < b₀ → ∀ A : Set ℂ,
      CellScaling.lqgArea γ (CellScaling.coneRescaleField γ R b₀
          (CellScaling.coneField (X ω) (CellScaling.coneRadial γ α (fun t => B t ω) (fun t => B' t ω)))) A =
        ENNReal.ofReal b₀⁻¹ *
          CellScaling.lqgArea γ
            (CellScaling.coneField (X ω) (CellScaling.coneRadial γ α (fun t => B t ω) (fun t => B' t ω)))
            ((fun w => (R : ℂ) * w) '' A) := by
  filter_upwards [LQGCoord.ae_lqgArea_affine_coneField_holds hγ hγ2 hαQ hX hB hB'] with
    ω h R hR b₀ hb₀ A
  have e1 : CellScaling.coneRescaleField γ R b₀
      (CellScaling.coneField (X ω) (CellScaling.coneRadial γ α (fun t => B t ω) (fun t => B' t ω))) =
      addConst (affineComp R 0
        (CellScaling.coneField (X ω) (CellScaling.coneRadial γ α (fun t => B t ω) (fun t => B' t ω))))
        (CellScaling.lqgQ γ * Real.log R + -(γ⁻¹ * Real.log b₀)) := by
    rw [CellScaling.coneRescaleField, sub_eq_add_neg]
  have e2 : Real.exp (γ * -(γ⁻¹ * Real.log b₀)) = b₀⁻¹ := by
    rw [show γ * -(γ⁻¹ * Real.log b₀) = -Real.log b₀ by field_simp, Real.exp_neg,
      Real.exp_log hb₀]
  rw [e1, h R hR _ 0 A, e2]
  congr 2
  ext w
  simp

/-- The α-cone field in the lateral/radial coordinates. -/
theorem coneField_eq_fieldOf_alpha (γ α : ℝ) (X : DistC) {b b' : NNReal → ℝ} {w : C(ℝ, ℝ)}
    (hw : ∀ t, w t = CellScaling.coneRadial γ α b b' t) :
    CellScaling.coneField X (CellScaling.coneRadial γ α b b') =
      ConeScaling.fieldOf (CellScaling.lateralPart X) w := by
  unfold CellScaling.coneField ConeScaling.fieldOf
  congr 2
  funext z
  simp only [ConeScaling.radialOf, hw]

end MatedCRTHarmonic.IGLaw
