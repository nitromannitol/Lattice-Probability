/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OPhaseCone at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhaseRot
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.CircleAvgCovariance
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeOfFun
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.Lateral
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOPath

/-!
# Rotation of the zero-quantum cone

For the frozen coupling's 0-cone field `h₀ = coneField X₀ (coneRadial γ 0 B₀ B₀')`:

* `p48o_map_rotateField_lateralPart`: the lateral part of a whole-plane GFF has a rotation-invariant
  law (the rotation analogue of ASL's `ConeScaling.map_affineComp_lateralPart`);
* `p48o_map_rotateField_zeroCone`: the law of `h₀(e^{iθ}·)` is the law of `h₀`;
* `p48o_ae_circleAvg_rotateField_zeroCone`: almost surely, simultaneously for all positive radii
  and all centres off the circle through `0`, `(h₀(e^{iθ}·))_ρ(w) = (h₀)_ρ(e^{iθ} w)`;
* `p48o_ae_isVagueLimitC_rotateField_zeroCone`: hence the dyadic GMC of `h₀(e^{iθ}·)` is almost
  surely the image of that of `h₀` under `z ↦ e^{-iθ} z`.

These are the cone-field halves of the phase-independence lemma (`Prop48OPhase.lean`). Sources:
DMS Def 4.10 / Lemmas 4.2–4.4 for the lateral part,
[18] for the 0-cone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4O

open LQGMetric MatedCRTHarmonic.CellScaling

/-! ### Deterministic rotation identities for distributions -/

/-- The test-function pullback used by `rotateField θ`. -/
abbrev p48oRotTest (θ : ℝ) : TestC →L[ℝ] TestC :=
  MoTPort.FieldOps.testPullCLE (rotation (Circle.exp (-θ))).toContinuousLinearEquiv

lemma p48oRotTest_apply (θ : ℝ) (φ : TestC) (x : ℂ) :
    p48oRotTest θ φ x = φ (Complex.exp ((-θ : ℝ) * Complex.I) * x) := by
  change φ (Circle.exp (-θ) * x) = _
  rw [Circle.coe_exp]

lemma p48o_rotateField_add (θ : ℝ) (a b : DistC) :
    MoTPort.rotateField θ (a + b) = MoTPort.rotateField θ a + MoTPort.rotateField θ b := by
  ext φ
  rfl

lemma p48o_rotateField_sub (θ : ℝ) (a b : DistC) :
    MoTPort.rotateField θ (a - b) = MoTPort.rotateField θ a - MoTPort.rotateField θ b := by
  ext φ
  rfl

/-- `ofFunC g` of a radial locally integrable `g` is invariant under `rotateField`. -/
lemma p48o_rotateField_ofFunC_of_radial {g : ℂ → ℝ} (hg : LocallyIntegrable g volume)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → g z = g w) (θ : ℝ) :
    MoTPort.rotateField θ (CellScaling.ofFunC g) = CellScaling.ofFunC g := by
  ext φ
  rw [MoTPort.rotateField_apply, LQGCoord.ofFunC_apply_li hg, LQGCoord.ofFunC_apply_li hg]
  have h := (measurePreserving_p48oRot (-θ)).integral_comp (measurableEmbedding_p48oRot (-θ))
    (fun x : ℂ => φ x * g x)
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : g x = g (p48oRot (-θ) x) := hrad _ _ (by simp)
  change (MoTPort.FieldOps.testPullCLE (rotation (Circle.exp (-θ))).toContinuousLinearEquiv φ) x *
      g x = φ (p48oRot (-θ) x) * g (p48oRot (-θ) x)
  rw [← hx]
  rfl

/-- The classical circle average of a radial function is invariant under rotating the centre. -/
lemma p48o_circleAverage_rot_of_radial {g : ℂ → ℝ}
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → g z = g w) (θ ρ : ℝ) (w : ℂ) :
    Real.circleAverage g (p48oRot θ w) ρ = Real.circleAverage g w ρ := by
  unfold Real.circleAverage
  congr 1
  set f : ℝ → ℝ := fun t => g (circleMap w ρ t)
  have hper : Function.Periodic f (2 * Real.pi) := by
    intro t
    simp only [f, circleMap]
    rw [show ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I = t * Complex.I + 2 * Real.pi * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have e : (fun t : ℝ => g (circleMap (p48oRot θ w) ρ t)) = fun t => f (t - θ) := by
    funext t
    simp only [f]
    apply hrad
    rw [p48oRot_apply, circleMap, circleMap]
    have : Complex.exp (θ * Complex.I) * w + (ρ : ℂ) * Complex.exp (t * Complex.I) =
        Complex.exp (θ * Complex.I) * (w + (ρ : ℂ) * Complex.exp (((t - θ : ℝ) : ℂ) * Complex.I)) := by
      rw [mul_add, ← mul_assoc, mul_comm (Complex.exp (θ * Complex.I)) (ρ : ℂ), mul_assoc,
        ← Complex.exp_add]
      push_cast
      ring_nf
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [e, intervalIntegral.integral_comp_sub_right f θ, zero_sub,
    show 2 * Real.pi - θ = -θ + 2 * Real.pi by ring, hper.intervalIntegral_add_eq (-θ) 0, zero_add]

/-! ### The law of the rotated lateral part -/

lemma p48o_symmTest_rotTest (θ : ℝ) (φ : TestC) :
    GMCFacts.symmTest (p48oRotTest θ φ) = GMCFacts.symmTest φ := by
  ext w
  simp only [GMCFacts.symmTest_apply]
  have e : (⇑(p48oRotTest θ φ) : ℂ → ℝ) =
      fun x => φ (Complex.exp ((-θ : ℝ) * Complex.I) * x) := by
    funext x; exact p48oRotTest_apply θ φ x
  rw [e]
  unfold GMCFacts.rotSymm
  have h := GMCFacts.rotSymm_exp_mul φ (-θ) w
  unfold GMCFacts.rotSymm at h
  rw [← h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  ring_nf

lemma p48o_rotTest_symmTest (θ : ℝ) (φ : TestC) :
    p48oRotTest θ (GMCFacts.symmTest φ) = GMCFacts.symmTest φ := by
  ext x
  rw [p48oRotTest_apply]
  exact GMCFacts.isRotInv_rotSymm φ (-θ) x

lemma p48o_latTest_rotTest (θ : ℝ) (φ : TestC) :
    p48oRotTest θ φ - GMCFacts.symmTest (p48oRotTest θ φ) =
      p48oRotTest θ (φ - GMCFacts.symmTest φ) := by
  rw [p48o_symmTest_rotTest, map_sub, p48o_rotTest_symmTest]

/-- **Rotation invariance of the lateral law.** -/
theorem p48o_map_rotateField_lateralPart {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistC} (hX : IsWholePlaneGFF X P) (θ : ℝ) :
    P.map (fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X ω))) =
      P.map (fun ω => CellScaling.lateralPart (X ω)) := by
  have := hX.gaussian.isProbabilityMeasure
  have hXm := hX.measurable
  have hL : Measurable fun ω => CellScaling.lateralPart (X ω) :=
    ConeScaling.measurable_lateralPart.comp hXm
  have hRL : Measurable fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X ω)) :=
    (MoTPort.measurable_rotateField θ).comp hL
  apply ConeScaling.distC_measure_ext
  rw [Measure.map_map ConeScaling.measurable_evDist hRL,
    Measure.map_map ConeScaling.measurable_evDist hL]
  have hfin : ∀ I : Finset TestC,
      (P.map (ConeScaling.evDist ∘ fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X ω)))).map
          I.restrict =
        (P.map (ConeScaling.evDist ∘ fun ω => CellScaling.lateralPart (X ω))).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (ConeScaling.measurable_evDist.comp hRL),
      Measure.map_map (Finset.measurable_restrict I) (ConeScaling.measurable_evDist.comp hL)]
    have hleft : (I.restrict ∘ ConeScaling.evDist ∘
        fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X ω))) =ᵐ[P]
        fun ω (i : I) => MoTPort.rotateField θ (X ω) (ConeScaling.latTest i.1).1 := by
      filter_upwards [ae_all_iff.2 fun i : I =>
        GMCFacts.ae_lateralPart_apply hX (p48oRotTest θ i.1)] with ω hω
      funext i
      have h1 := hω i
      simp only [Function.comp_apply, Finset.restrict, ConeScaling.evDist]
      rw [MoTPort.rotateField_apply, MoTPort.rotateField_apply]
      change CellScaling.lateralPart (X ω) (p48oRotTest θ i.1) =
        X ω (p48oRotTest θ (ConeScaling.latTest i.1).1)
      rw [h1, p48o_latTest_rotTest]
      rfl
    have hright : (I.restrict ∘ ConeScaling.evDist ∘ fun ω => CellScaling.lateralPart (X ω)) =ᵐ[P]
        fun ω (i : I) => X ω (ConeScaling.latTest i.1).1 := by
      filter_upwards [ae_all_iff.2 fun i : I => GMCFacts.ae_lateralPart_apply hX i.1] with ω hω
      funext i
      exact hω i
    rw [Measure.map_congr hleft, Measure.map_congr hright]
    let F : (TestC0 → ℝ) → (I → ℝ) := fun q i => q (ConeScaling.latTest i.1)
    have hF : Measurable F := measurable_pi_iff.2 fun i => measurable_pi_apply _
    have hRX : IsWholePlaneGFF (fun ω => MoTPort.rotateField θ (X ω)) P :=
      IGLaw.IsWholePlaneGFF.rotateField hX θ
    have hlaw := congrArg (Measure.map F) (IGLaw.map_pairProc_rotateField_eq hX θ)
    rw [Measure.map_map hF (GFFLaw.measurable_pairProc hRX.measurable),
      Measure.map_map hF (GFFLaw.measurable_pairProc hXm)] at hlaw
    exact hlaw
  exact IsProjectiveLimit.unique
    (P := fun I => (P.map (ConeScaling.evDist ∘ fun ω => CellScaling.lateralPart (X ω))).map
      I.restrict)
    hfin (fun _ => rfl)

/-! ### The zero-quantum cone of the frozen coupling -/

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The zero-cone field of the coupling, written with the `CellScaling` copies of the frozen
definitions (`MesoModel.FrozenIdentities.coneField_eq_cellScaling`). -/
def p48oZeroConeField (γ : ℝ) (X₀ : Ω → MatedCRT.Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    DistC :=
  CellScaling.coneField (X₀ ω) (CellScaling.coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))

lemma p48o_lqgQ_pos {γ : ℝ} (hγ : 0 < γ) : (0 : ℝ) < CellScaling.lqgQ γ := by
  unfold CellScaling.lqgQ; positivity

/-- The zero cone's radial process as a measurable continuous path `W`, with `X₀ ⟂ W` and
`(X₀, W) ⟂ (hIG₀, U)` (IGCO's `exists_radialPath_alpha` at `α = 0`, fed with the IG data). -/
theorem p48o_zeroCone_radialPath
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧ IndepFun X₀ W P ∧
      IndepFun (fun ω => (X₀ ω, W ω)) (fun ω => (hIG₀ ω, U ω)) P ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t) ∧
      (∀ᵐ ω ∂P, LocallyIntegrable (ConeScaling.radialOf (W ω)) volume) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hQ0 : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ.1
  have hQ0' : 0 < CellScaling.lqgQ γ - 0 := by rw [sub_zero]; exact hQ0
  have hproj : Measurable fun q : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × MatedCRT.Field ×
      (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => (q.2.2.2.1, (q.2.2.2.2.1, q.2.2.2.2.2)) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        measurable_snd)))).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
          measurable_snd)))))
  have hIGX₀BB : IndepFun (fun ω => (hIG₀ ω, U ω))
      (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) P :=
    D.indep_curve.comp measurable_id hproj
  obtain ⟨W, hWm, hXW, hXWIG, hW⟩ := IGLaw.exists_radialPath_alpha (γ := γ) (α := 0) hQ0' D.bm_B₀
    D.bm_B₀' D.indep_cone₀.1 hIGX₀BB
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  have hA : MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hli : ∀ᵐ ω ∂P, LocallyIntegrable (ConeScaling.radialOf (W ω)) volume := by
    filter_upwards [hW, MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω hl
    refine hl.congr (Eventually.of_forall fun z => ?_)
    simp only [ConeScaling.radialOf, hω, LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
  exact ⟨W, hWm, hXW, hXWIG, hW, hli⟩

/-- The zero-cone field is almost surely `fieldOf (lateralPart X₀) W`. -/
theorem p48o_zeroCone_ae_eq_fieldOf {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t) :
    (p48oZeroConeField γ X₀ B₀ B₀') =ᵐ[P]
      fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω) := by
  filter_upwards [hW] with ω hω
  exact IGLaw.coneField_eq_fieldOf_alpha γ 0 (X₀ ω) hω

/-- The zero-cone field is almost everywhere measurable. -/
theorem p48o_aemeasurable_zeroConeField
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : AEMeasurable (p48oZeroConeField γ X₀ B₀ B₀') P := by
  obtain ⟨W, hWm, -, -, hW, -⟩ := p48o_zeroCone_radialPath D hγ
  refine AEMeasurable.congr ?_ (p48o_zeroCone_ae_eq_fieldOf hW).symm
  exact (ConeScaling.measurable_fieldOf.comp
    ((ConeScaling.measurable_lateralPart.comp D.gff₀.measurable).prodMk hWm)).aemeasurable

/-- The zero-cone field is independent of the IG data `(hIG₀, U)`. -/
theorem p48o_zeroCone_indepFun_IGdata
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (p48oZeroConeField γ X₀ B₀ B₀') (fun ω => (hIG₀ ω, U ω)) P := by
  obtain ⟨W, -, -, hXWIG, hW, -⟩ := p48o_zeroCone_radialPath D hγ
  have hF : Measurable fun p : MatedCRT.Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  exact (hXWIG.comp hF measurable_id).congr (p48o_zeroCone_ae_eq_fieldOf hW).symm
    (ae_eq_refl _)

/-- **The law of the zero-cone field is rotation invariant.** -/
theorem p48o_map_rotateField_zeroCone
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (θ : ℝ) :
    P.map (fun ω => MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω)) =
      P.map (p48oZeroConeField γ X₀ B₀ B₀') := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨W, hWm, hXW, -, hW, hli⟩ := p48o_zeroCone_radialPath D hγ
  have hX₀m := D.gff₀.measurable
  have hL : Measurable fun ω => CellScaling.lateralPart (X₀ ω) :=
    ConeScaling.measurable_lateralPart.comp hX₀m
  have hRL : Measurable fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)) :=
    (MoTPort.measurable_rotateField θ).comp hL
  have hindL : IndepFun (fun ω => CellScaling.lateralPart (X₀ ω)) W P :=
    hXW.comp ConeScaling.measurable_lateralPart measurable_id
  have hindRL : IndepFun (fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω))) W P :=
    hXW.comp ((MoTPort.measurable_rotateField θ).comp ConeScaling.measurable_lateralPart)
      measurable_id
  have hpair : P.map (fun ω => (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)), W ω)) =
      P.map (fun ω => (CellScaling.lateralPart (X₀ ω), W ω)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hRL.aemeasurable hWm.aemeasurable).1 hindRL,
      (indepFun_iff_map_prod_eq_prod_map_map hL.aemeasurable hWm.aemeasurable).1 hindL,
      p48o_map_rotateField_lateralPart D.gff₀ θ]
  have hfield : (fun ω => MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω)) =ᵐ[P]
      fun ω => ConeScaling.fieldOf (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω))) (W ω) := by
    filter_upwards [hW, hli] with ω hω hl
    rw [p48oZeroConeField, IGLaw.coneField_eq_fieldOf_alpha γ 0 (X₀ ω) hω, ConeScaling.fieldOf,
      ConeScaling.fieldOf, p48o_rotateField_add,
      p48o_rotateField_ofFunC_of_radial hl (fun z w hzw => by simp [ConeScaling.radialOf, hzw])]
  have hpRL : AEMeasurable (fun ω => (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)), W ω)) P :=
    (hRL.prodMk hWm).aemeasurable
  have hpL : AEMeasurable (fun ω => (CellScaling.lateralPart (X₀ ω), W ω)) P :=
    (hL.prodMk hWm).aemeasurable
  rw [Measure.map_congr hfield, Measure.map_congr (p48o_zeroCone_ae_eq_fieldOf hW)]
  change P.map ((fun p : DistC × C(ℝ, ℝ) => ConeScaling.fieldOf p.1 p.2) ∘
      fun ω => (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)), W ω)) =
    P.map ((fun p : DistC × C(ℝ, ℝ) => ConeScaling.fieldOf p.1 p.2) ∘
      fun ω => (CellScaling.lateralPart (X₀ ω), W ω))
  rw [← AEMeasurable.map_map_of_aemeasurable ConeScaling.measurable_fieldOf.aemeasurable hpRL,
    ← AEMeasurable.map_map_of_aemeasurable ConeScaling.measurable_fieldOf.aemeasurable hpL, hpair]

/-- **Circle-average covariance of the rotated zero cone**, on one almost-sure event for all
positive radii and all centres off the circle through the cone point. -/
theorem p48o_ae_circleAvg_rotateField_zeroCone
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (θ : ℝ) :
    ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ, ‖w‖ ≠ ρ →
      circleAvg (MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω)) ρ w =
        circleAvg (p48oZeroConeField γ X₀ B₀ B₀' ω) ρ (p48oRot θ w) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hαQ : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ.1
  have hRX : IsWholePlaneGFF (fun ω => MoTPort.rotateField θ (X₀ ω)) P :=
    IGLaw.IsWholePlaneGFF.rotateField D.gff₀ θ
  filter_upwards [LQGCoord.ae_radialGood D.gff₀ D.bm_B₀ D.bm_B₀' hαQ,
    LQGCoord.ae_tendsto_mollAvgS_circleAvg D.gff₀,
    LQGCoord.ae_tendsto_mollAvgS_circleAvg hRX,
    IGLaw.rotCircleAvgCovarianceAll_holds P X₀ D.gff₀ θ] with ω hr hX hRXω hcov
  intro ρ hρ w hw
  set b : ℝ≥0 → ℝ := fun t => B₀ t ω
  set b' : ℝ≥0 → ℝ := fun t => B₀' t ω
  set g₁ : ℂ → ℝ := CellScaling.radialAvg (X₀ ω)
  set g₂ : ℂ → ℝ := LQGCoord.coneProfile γ 0 b b'
  have hc₁ : ContinuousOn g₁ {0}ᶜ := LQGCoord.continuousOn_radialAvg hr.good
  have hc₂ : ContinuousOn g₂ {0}ᶜ := LQGCoord.continuousOn_coneProfile hr
  obtain ⟨C₁, hC₁⟩ := LQGCoord.abs_radialAvg_le hr one_pos
  obtain ⟨C₂, hC₂⟩ := LQGCoord.abs_coneProfile_le hr one_pos
  have hl₁ : LocallyIntegrable g₁ volume :=
    LQGCoord.locallyIntegrable_of_logBound (LQGCoord.measurable_radialAvg _) hc₁ hC₁
  have hl₂ : LocallyIntegrable g₂ volume :=
    LQGCoord.locallyIntegrable_of_logBound (LQGCoord.measurable_coneProfile hr) hc₂
      fun w h0 h1 => (hC₂ w h0 h1).1
  have hrad₁ : ∀ z w : ℂ, ‖z‖ = ‖w‖ → g₁ z = g₁ w := by
    intro z w hzw
    simp only [g₁, CellScaling.radialAvg, hzw]
  have hrad₂ : ∀ z w : ℂ, ‖z‖ = ‖w‖ → g₂ z = g₂ w := by
    intro z w hzw
    simp only [g₂, LQGCoord.coneProfile, hzw]
  have hdec : p48oZeroConeField γ X₀ B₀ B₀' ω = X₀ ω - CellScaling.ofFunC g₁ + CellScaling.ofFunC g₂ :=
    LQGCoord.coneField_eq_cone γ 0 (X₀ ω) b b'
  have hdecR : MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω) =
      MoTPort.rotateField θ (X₀ ω) - CellScaling.ofFunC g₁ + CellScaling.ofFunC g₂ := by
    rw [hdec, p48o_rotateField_add, p48o_rotateField_sub,
      p48o_rotateField_ofFunC_of_radial hl₁ hrad₁, p48o_rotateField_ofFunC_of_radial hl₂ hrad₂]
  have hwR : ‖p48oRot θ w‖ ≠ ρ := by
    rwa [LinearIsometryEquiv.norm_map]
  rw [hdecR, LQGCoord.circleAvg_cone hl₁ hl₂ hc₁ hc₂ hρ hw (hRXω.2 ρ hρ w), hdec,
    LQGCoord.circleAvg_cone hl₁ hl₂ hc₁ hc₂ hρ hwR (hX.2 ρ hρ (p48oRot θ w)),
    hcov ρ hρ w, p48oRot_apply, ← p48oRot_apply,
    p48o_circleAverage_rot_of_radial hrad₁, p48o_circleAverage_rot_of_radial hrad₂]

/-- **The dyadic GMC of the rotated zero cone** is almost surely the rotated GMC of the zero
cone, which is itself the vague limit of its approximations. -/
theorem p48o_ae_isVagueLimitC_rotateField_zeroCone
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (θ : ℝ) :
    ∀ᵐ ω ∂P,
      IsVagueLimitC (lqgAreaApprox γ (p48oZeroConeField γ X₀ B₀ B₀' ω))
          (lqgArea γ (p48oZeroConeField γ X₀ B₀ B₀' ω)) ∧
        IsVagueLimitC (lqgAreaApprox γ (MoTPort.rotateField θ (p48oZeroConeField γ X₀ B₀ B₀' ω)))
          ((lqgArea γ (p48oZeroConeField γ X₀ B₀ B₀' ω)).map (p48oRot (-θ))) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hγ0, hγ2⟩ := hγ
  have hQ0 : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ0
  have hQ0' : 0 < CellScaling.lqgQ γ - 0 := by rw [sub_zero]; exact hQ0
  have hQc : (0 : ℝ) < QuantumZipper.Qc γ := by
    have : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
    rw [← this]; exact hQ0
  obtain ⟨W, -, hXW, -, hW, -⟩ := p48o_zeroCone_radialPath D ⟨hγ0, hγ2⟩
  have hXA := IGLaw.indepFun_motConeRadial_alpha (γ := γ) (α := 0) hXW hW
  have hvague := LQGCone.ae_isVagueLimitC_coneField hγ0 hγ2 hQc D.gff₀ D.bm_B₀ D.bm_B₀'
    D.indep_cone₀.2 hXA
  filter_upwards [hvague, p48o_ae_circleAvg_rotateField_zeroCone D ⟨hγ0, hγ2⟩ θ] with ω hv hcov
  have hv' : IsVagueLimitC (lqgAreaApprox γ (p48oZeroConeField γ X₀ B₀ B₀' ω))
      (lqgArea γ (p48oZeroConeField γ X₀ B₀ B₀' ω)) :=
    CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hv
  refine ⟨hv', p48o_isVagueLimitC_rot θ (fun k => ?_) hv'⟩
  filter_upwards [LQGCoord.ae_norm_ne (dyadicScale k)] with z hz
  exact hcov _ (LQGCoord.dyadicScale_pos k) z hz

end ZeroCone

end MatedCRTHarmonic.GMS4O
