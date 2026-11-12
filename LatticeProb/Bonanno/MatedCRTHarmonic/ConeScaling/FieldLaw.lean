/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.FieldLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialPath
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.Lateral
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldDecomp
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4G
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeAddConstLat

/-!
# DMS Proposition 4.13(i): the re-centred quantum cone has the law of the quantum cone

Source: DMS (Prop 4.13(i): for the circle-average
embedding `h` of an α-quantum cone and `C ∈ ℝ`, the field `h(R_C ·) + Q log R_C + C/γ`, re-centred at
the radius `R_C` where the circle average of `h + C/γ` plus `Q log r` last hits `0`, has the law of
`h`); in the notation `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b`, this is `C = −log b` ([18], Eq. (2.8)). The proof uses:

* `h = h^{lat} + A_{−log|·|}` with `h^{lat} = lateralPart X ⊥ A` (DMS Def 4.10);
* `h_b = h^{lat}(R_b ·) + (Θ_y A)_{−log|·|}`, `Θ_y = radShift Q y`, `R_b = exp L_y(A)`
  (`FieldDecomp.coneRescaleField_fieldOf`);
* `Θ_y A =d A` (`RadialLaw.map_radShift_coneRadial`), and for each fixed `r > 0`,
  `h^{lat}(r ·) =d h^{lat}` (`Lateral.map_affineComp_lateralPart`); since `R_b` is a function of `A`
  and `A ⊥ h^{lat}`, conditioning on `A` (QuantumZipper's `F1.map_prod_mk_dep`) gives
  `(A, h^{lat}(R_b ·)) =d (A, h^{lat})`, hence `(Θ_y A, h^{lat}(R_b ·)) =d (A, h^{lat})`.

Main results: `map_fieldOf_shift_eq` (abstract form), `map_coneRescaleField_coneFieldOf` (for
whole-plane GFF and Brownian data, with the a.e.-measurability of both fields), and
`ConeRealization.map_rescaledField_eq` (for the cell-model realization). SLE-free.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

open LQGMetric MatedCRTHarmonic.CellScaling

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The field law, abstract form**: if `X` is a whole-plane GFF, `W` a measurable `C(ℝ, ℝ)`-valued
path independent of `X`, and re-centring at level `y` preserves the law of `W`, then
`fieldOf (lateralPart X (e^{L_y(W)} ·)) (radShift Q y W)` has the law of `fieldOf (lateralPart X) W`. -/
theorem map_fieldOf_shift_eq {X : Ω → DistC} (hX : IsWholePlaneGFF X P) {W : Ω → C(ℝ, ℝ)}
    (hWm : Measurable W) (hWX : IndepFun W X P) {Q y : ℝ}
    (hrad : P.map (fun ω => radShift Q y (W ω)) = P.map W) :
    P.map (fun ω => fieldOf (affineComp (Real.exp (lastLevel Q y (W ω))) 0
        (lateralPart (X ω))) (radShift Q y (W ω))) =
      P.map (fun ω => fieldOf (lateralPart (X ω)) (W ω)) := by
  have hXm := hX.measurable
  set μW := P.map W with hμW
  set μX := P.map X with hμX
  set μL := μX.map lateralPart with hμL
  have : IsProbabilityMeasure μW := (Measure.isProbabilityMeasure_map_iff hWm.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure μX := (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure μL :=
    (Measure.isProbabilityMeasure_map_iff measurable_lateralPart.aemeasurable).2 inferInstance
  have hWXm : Measurable fun ω => (W ω, X ω) := hWm.prodMk hXm
  have hjoint : P.map (fun ω => (W ω, X ω)) = μW.prod μX :=
    (indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable hXm.aemeasurable).1 hWX
  set Rh : C(ℝ, ℝ) → ℝ := fun w => Real.exp (lastLevel Q y w) with hRh_def
  have hRh : Measurable Rh := Real.measurable_exp.comp (measurable_lastLevel Q y)
  set g1 : C(ℝ, ℝ) × DistC → DistC := fun p => affineComp (Rh p.1) 0 (lateralPart p.2) with hg1_def
  have hg1 : Measurable g1 := MoTPort.ConeMeas.measurable_affineComp_joint.comp
    ((hRh.comp measurable_fst).prodMk (measurable_lateralPart.comp measurable_snd))
  have hdep : (μW.prod μX).map (fun p => (p.1, g1 p)) = μW.prod μL := by
    refine QuantumZipper.F1.map_prod_mk_dep μW μX hg1 μL fun u => ?_
    have hu : Measurable fun x : DistC => g1 (u, x) := hg1.comp measurable_prodMk_left
    rw [hμX, Measure.map_map hu hXm, hμL, hμX, Measure.map_map measurable_lateralPart hXm]
    show P.map (fun ω => affineComp (Real.exp (lastLevel Q y u)) 0 (lateralPart (X ω))) =
      P.map (fun ω => lateralPart (X ω))
    exact map_affineComp_lateralPart hX (Real.exp_pos (lastLevel Q y u))
  set Φ : C(ℝ, ℝ) × DistC → DistC := fun q => fieldOf q.2 (radShift Q y q.1) with hΦ_def
  set Ψ : C(ℝ, ℝ) × DistC → DistC := fun q => fieldOf q.2 q.1 with hΨ_def
  have hΨ : Measurable Ψ := measurable_fieldOf.comp (measurable_snd.prodMk measurable_fst)
  have hΦ : Φ = Ψ ∘ Prod.map (radShift Q y) id := rfl
  have hΦm : Measurable Φ := by
    rw [hΦ]; exact hΨ.comp ((measurable_radShift Q y).prodMap measurable_id)
  have hrad' : μW.map (radShift Q y) = μW := by
    rw [hμW, Measure.map_map (measurable_radShift Q y) hWm]; exact hrad
  have hcommon : (μW.prod μL).map Φ = (μW.prod μL).map Ψ := by
    rw [hΦ, ← Measure.map_map hΨ ((measurable_radShift Q y).prodMap measurable_id),
      ← Measure.map_prod_map μW μL (measurable_radShift Q y) measurable_id, hrad', Measure.map_id]
  have hL : P.map (fun ω => fieldOf (affineComp (Real.exp (lastLevel Q y (W ω))) 0
        (lateralPart (X ω))) (radShift Q y (W ω))) = (μW.prod μL).map Φ := by
    rw [← hdep, Measure.map_map hΦm (measurable_fst.prodMk hg1), ← hjoint,
      Measure.map_map (hΦm.comp (measurable_fst.prodMk hg1)) hWXm]
    rfl
  have hR : P.map (fun ω => fieldOf (lateralPart (X ω)) (W ω)) = (μW.prod μL).map Ψ := by
    have hpm : Measurable (Prod.map (id : C(ℝ, ℝ) → C(ℝ, ℝ)) lateralPart) :=
      measurable_id.prodMap measurable_lateralPart
    have hprod : (μW.prod μX).map (Prod.map id lateralPart) = μW.prod μL := by
      rw [← Measure.map_prod_map μW μX measurable_id measurable_lateralPart, Measure.map_id]
    rw [← hprod, Measure.map_map hΨ hpm, ← hjoint, Measure.map_map (hΨ.comp hpm) hWXm]
    rfl
  rw [hL, hR, hcommon]

/-- **DMS Proposition 4.13(i)** for the γ-quantum cone built from a whole-plane GFF `X` and Brownian
motions `B, B'` (`X ⊥ (B, B')`, `B ⊥ B'`): for every `b₀ > 0`... in fact every `b₀ ∈ ℝ` (the junk
values of `log` are harmless), both `h` and `h_b = coneRescaleField γ R_b b₀ h` are a.e.-measurable
and `h_b` has the law of `h`. -/
theorem map_coneRescaleField_coneFieldOf {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {X : Ω → DistC}
    {B B' : ℝ≥0 → Ω → ℝ} (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) (b₀ : ℝ) :
    AEMeasurable (fun ω => coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) P ∧
      AEMeasurable (fun ω => coneRescaleField γ
        (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) b₀
        (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) P ∧
      P.map (fun ω => coneRescaleField γ
          (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) b₀
          (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) =
        P.map (fun ω => coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) := by
  obtain ⟨W, hWm, hXW, hW⟩ := exists_radialPath hγ hγ2 hB hB' hind.1
  have hXm := hX.measurable
  set y : ℝ := γ⁻¹ * Real.log b₀ with hy
  have hrad := map_radShift_coneRadial hγ hγ2 hB hB' hind.2 hWm hW y
  -- local integrability of the radial function
  have hQ : lqgQ γ = QuantumZipper.Qc γ := by dsimp [lqgQ, QuantumZipper.Qc]
  have hA : MoTPort.IsConeProcess γ (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial hB hB' hind.2
  have hli : ∀ᵐ ω ∂P, LocallyIntegrable (radialOf (W ω)) volume := by
    filter_upwards [hW, MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω hl
    refine hl.congr (Eventually.of_forall fun z => ?_)
    simp only [radialOf, hω, LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
  -- measurable versions
  set hh : Ω → DistC := fun ω => fieldOf (lateralPart (X ω)) (W ω) with hhh
  set hb : Ω → DistC := fun ω => fieldOf (affineComp (Real.exp (lastLevel (lqgQ γ) y (W ω))) 0
    (lateralPart (X ω))) (radShift (lqgQ γ) y (W ω)) with hhb
  have hhm : Measurable hh :=
    measurable_fieldOf.comp ((measurable_lateralPart.comp hXm).prodMk hWm)
  have hbm : Measurable hb := by
    refine measurable_fieldOf.comp (Measurable.prodMk ?_ ((measurable_radShift _ _).comp hWm))
    exact MoTPort.ConeMeas.measurable_affineComp_joint.comp
      ((Real.measurable_exp.comp ((measurable_lastLevel _ _).comp hWm)).prodMk
        (measurable_lateralPart.comp hXm))
  have ehh : (fun ω => coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) =ᵐ[P] hh := by
    filter_upwards [hW] with ω hω
    exact coneFieldOf_eq_fieldOf γ (X ω) hω
  have ehb : (fun ω => coneRescaleField γ
      (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) b₀
      (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) =ᵐ[P] hb := by
    filter_upwards [hW, hli] with ω hω hl
    rw [coneScale_eq_exp_lastLevel γ b₀ hω, coneFieldOf_eq_fieldOf γ (X ω) hω,
      coneRescaleField_fieldOf γ b₀ _ hl]
  refine ⟨hhm.aemeasurable.congr ehh.symm, hbm.aemeasurable.congr ehb.symm, ?_⟩
  rw [Measure.map_congr ehb, Measure.map_congr ehh]
  exact map_fieldOf_shift_eq hX hWm hXW.symm hrad

namespace ConeRealization

variable {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M)

/-- **DMS Proposition 4.13(i) for the cell model** (the cone scaling identity, field part): for
every `b > 0`, `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b` has the law of the cone field `h`, and both
are a.e.-measurable. -/
theorem map_rescaledField_eq (b : ℝ) :
    AEMeasurable D.field M.coupled.family.P ∧
      AEMeasurable (fun ω => coneRescaleField γ (D.scale b ω) b (D.field ω))
        M.coupled.family.P ∧
      M.coupled.family.P.map (fun ω => coneRescaleField γ (D.scale b ω) b (D.field ω)) =
        M.coupled.family.P.map D.field := by
  have := D.gff.gaussian.isProbabilityMeasure
  exact map_coneRescaleField_coneFieldOf M.hγ.1 M.hγ.2 D.gff D.brownian D.brownian' D.indep b

end ConeRealization

end MatedCRTHarmonic.ConeScaling
