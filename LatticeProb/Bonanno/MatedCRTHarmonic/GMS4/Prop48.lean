/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.SLEInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.BundleAdapter
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.UStarMoments
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Packing
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Lemma49Observable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleExcursions
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ZeroConeScalingCells
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-!
# The second-moment conclusion in [18] Proposition 4.8

Source: Gwynne--Miller--Sheffield, *Harmonic functions on mated-CRT maps*,
 (equation (4.38) and the Chebyshev step in
Step 3 of Proposition 4.8). The source obtains an uncentered second-moment estimate for the
localized-density integral and applies Chebyshev with a positive threshold. The theorem below
records exactly that generic implication, including its failure probability.

The closest library result is Mathlib's `mul_meas_ge_le_lintegral₀` (Markov's inequality). We
specialize it to the square of a real random variable. This is only the concentration core; it
does not assume any of the field, cell, or localized-density estimates that produce the
second-moment premise in Proposition 4.8.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4

/-- **Second moment / Chebyshev implication used after [18, (4.38)].**

If the uncentered second moment of `X` is at most
`bound^2 * (C * ε^α)`, then the probability that `X` exceeds the positive threshold `bound`
is at most `C * ε^α`. The use of a one-sided event matches Proposition 4.8's required upper-tail
estimate; no centering hypothesis is needed once the second-moment bound has been established. -/
theorem measure_gt_le_of_lintegral_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ}
    (hX : AEMeasurable X P) {bound C ε α : ℝ} (hbound : 0 < bound)
    (hsecond : (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) ≤
      ENNReal.ofReal (bound ^ 2 * (C * ε ^ α))) :
    P {ω | bound < X ω} ≤ ENNReal.ofReal (C * ε ^ α) := by
  let t : ℝ≥0∞ := ENNReal.ofReal (bound ^ 2)
  let f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (X ω ^ 2)
  have ht0 : t ≠ 0 := by
    change ENNReal.ofReal (bound ^ 2) ≠ 0
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have htt : t ≠ ⊤ := by simp [t]
  have hXsq : AEMeasurable (fun ω => X ω ^ 2) P := by
    have heq : (fun ω => X ω ^ 2) = X * X := by
      funext ω
      simp [pow_two]
    rw [heq]
    exact hX.mul hX
  have hf : AEMeasurable f P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hXsq
  have hsubset : {ω | bound < X ω} ⊆ {ω | t ≤ f ω} := by
    intro ω hω
    change bound < X ω at hω
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hmul : t * P {ω | bound < X ω} ≤
      t * ENNReal.ofReal (C * ε ^ α) := by
    calc
      t * P {ω | bound < X ω} ≤ t * P {ω | t ≤ f ω} :=
        mul_le_mul' le_rfl (measure_mono hsubset)
      _ ≤ ∫⁻ ω, f ω ∂P := mul_meas_ge_le_lintegral₀ hf t
      _ ≤ ENNReal.ofReal (bound ^ 2 * (C * ε ^ α)) := hsecond
      _ = t * ENNReal.ofReal (C * ε ^ α) := by
        rw [ENNReal.ofReal_mul (sq_nonneg bound)]
  exact (ENNReal.mul_le_mul_iff_left ht0 htt).mp (by simpa [mul_comm] using hmul)

/-! ## The source-level completion boundary

The following three predicates keep the still-missing producers separate. In particular, none of
them assumes (4.38) or the conclusion of Proposition 4.8.
-/

/-! ## Source-facing localized observable -/

/-- Minimal L27 data for the localized observable in [18, (4.27)--(4.29)]. The random variable
used below is the integral of
`1_{F^ε(z)} u_*^ε(z) - E[1_{F^ε(z)}u_*^ε(z) | local circle averages]`.

The last three fields are the exact regularity outputs needed to pass from this definition to the
good-event inequality: local truncation agrees with `u_*` on `E^ε`, the conditional mean integrates
to at most `A ∫ f`, and integration commutes with the subtraction. Source: [18, Proposition 4.8];
producer classification: **L27** (local observable/measurability) together with the conditional
moment output (4.27). -/
structure Prop48LocalizedObservable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The integration domain `D`. -/
  domain : Set ℂ
  measurableSet_domain : MeasurableSet domain
  /-- The nonnegative test function `f`. -/
  test : ℂ → ℝ
  /-- The localized density `u_*^ε`. -/
  uStar : Ω → ℂ → ℝ
  /-- The pointwise local event `F^ε(z)`. -/
  localEvent : ℂ → Set Ω
  /-- The conditional expectation in (4.27)--(4.28). -/
  conditionalMean : Ω → ℂ → ℝ
  /-- The global good event `E^ε`. -/
  goodEvent : Set Ω
  /-- The deterministic conditional-mean constant `A`. -/
  meanConstant : ℝ
  aeMeasurable_fluctuation : AEMeasurable (fun ω =>
    ∫ z in domain, test z *
      ((localEvent z).indicator (fun _ => uStar ω z) ω - conditionalMean ω z)) P
  localEvent_of_good : ∀ ω ∈ goodEvent, ∀ z ∈ domain, ω ∈ localEvent z
  conditionalIntegral_le : ∀ ω ∈ goodEvent,
    (∫ z in domain, test z * conditionalMean ω z) ≤
      meanConstant * ∫ z in domain, test z
  integral_subtraction : ∀ ω ∈ goodEvent,
    (∫ z in domain, test z *
      ((localEvent z).indicator (fun _ => uStar ω z) ω - conditionalMean ω z)) =
      (∫ z in domain, test z *
        (localEvent z).indicator (fun _ => uStar ω z) ω) -
      ∫ z in domain, test z * conditionalMean ω z

/-! ## L27 cell-model specialization -/
/-- The exact localized-observable output still required from L27 for a concrete
`GMSLemma27.CellModel γ`. This is a data interface indexed by the model, so its probability measure
is definitionally `M.P`; it adds no probabilistic conclusion to `Prop48LocalizedObservable`.
Producer classification: **local**, using the cell/field/curve data of `CellModel` and the
localized definitions in [18] . -/
abbrev L27CellModelLocalizedObservable {γ : ℝ}
    (M : MatedCRTHarmonic.GMSLemma27.CellModel γ) :=
  Prop48LocalizedObservable M.P

/-- **Missing L27 producer data for the actual source observable.** The current `CellModel` has the
field, area measure, and curve, but does not yet define the local structure graph, `τ_z`, the area
ratio `DA^ε`, the in/out degrees, or the IG circle average. This interface names those lower-level
outputs explicitly and enforces both source formulas:

* `u_*^ε(z) = DA^ε(z) (deg_in^ε(z) + deg_out^ε(z))`, [18, (4.19), ];
* `F^ε(z)` is exactly the conjunction of the three local conditions at [18] .

The source's SLE input `SegmentsContainBalls` ([GHM15, Proposition 3.4 and Remark 3.9],
`GMSLemma27/SLEInterfaces.lean`) is included explicitly. The final two fields identify these
source objects with the localized integral data. No probability or Proposition 4.8 conclusion is
included. Producer classification: **local**. -/
structure L27CellModelProp48Data {γ : ℝ}
    (M : MatedCRTHarmonic.GMSLemma27.CellModel γ) (ε q ζ : ℝ) where
  /-- The SLE-only segment-ball input used to control outer degree; see
  `GMSLemma27.SLEInterfaces.SegmentsContainBalls` and [18] . -/
  segmentsContainBalls : MatedCRTHarmonic.GMSLemma27.SegmentsContainBalls M
  /-- `DA^ε(z)`, the area ratio from [18, §4.2]. -/
  areaRatio : M.Ω → ℂ → ℝ
  /-- `deg_in^ε(z)` in the local structure graph. -/
  degreeIn : M.Ω → ℂ → ℕ
  /-- `deg_out^ε(z)` in the local structure graph. -/
  degreeOut : M.Ω → ℂ → ℕ
  /-- `diam(η([τ_z-ε,τ_z+ε]))`. -/
  localSegmentDiameter : M.Ω → ℂ → ℝ
  /-- The circle average `h_{ε^{q-4ζ}}(z)`. -/
  fieldCircleAverage : M.Ω → ℂ → ℝ
  /-- The IG-field circle average `h^{IG}_{ε^{q-4ζ}}(z)`. -/
  igCircleAverage : M.Ω → ℂ → ℝ
  /-- The source localized density `u_*^ε`. -/
  uStar : M.Ω → ℂ → ℝ
  /-- The local event `F^ε(z)`. -/
  localEvent : ℂ → Set M.Ω
  uStar_formula : ∀ ω z, uStar ω z =
    areaRatio ω z * ((degreeIn ω z + degreeOut ω z : ℕ) : ℝ)
  localEvent_formula : ∀ ω z, ω ∈ localEvent z ↔
    localSegmentDiameter ω z ≤ ε ^ q ∧
    ((degreeIn ω z + degreeOut ω z : ℕ) : ℝ) ≤ ε ^ (-ζ) ∧
    max |fieldCircleAverage ω z| |igCircleAverage ω z| ≤ 2 * q * Real.log ε⁻¹
  localizedObservable : L27CellModelLocalizedObservable M
  localized_uStar : ∀ ω z, localizedObservable.uStar ω z = uStar ω z
  localized_event : ∀ z, localizedObservable.localEvent z = localEvent z


/-! ### The concrete zero-cone realization used in Proposition 4.8 -/

open MatedCRTHarmonic.MatedCRT

/-- The bundle's 0-cone field and area-parametrized curve, packaged as an L27 cell model.
The area-parametrization proof uses the v3 `areaParam₀` field only after the SLE-free
existence of the dyadic vague limit has been supplied by `FrozenIdentities`. -/
def prop48ZeroConeCellModel
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    MatedCRTHarmonic.GMSLemma27.CellModel γ where
  Ω := Ω
  measurableSpace := inferInstance
  P := P
  isProbabilityMeasure := D.isProbabilityMeasure
  field := fun ω => coneField (X₀ ω)
    (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
  area := fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ
    (coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))
  curve := fun ω => η₀ ω
  ae_continuous_curve := Filter.Eventually.of_forall fun ω => (η₀ ω).continuous
  ae_curve_zero := by
    filter_upwards [D.areaParam₀, D.spaceFilling] with ω harea hspace
    rcases harea.1 with ⟨φ, hφ0, hηeq⟩
    rw [hηeq, hφ0, hspace.2.2.1]
  ae_area_curve := by
    filter_upwards [D.areaParam₀,
      MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ]
      with ω harea hex
    have hex' : ∃ μ : Measure ℂ, MatedCRTHarmonic.CellScaling.IsVagueLimitC
        (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ
          (coneField (X₀ ω)
            (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))) μ := hex
    rw [MatedCRTHarmonic.CellScaling.lqgArea, dif_pos hex']
    exact harea.2 _ hex'.choose_spec

/-- The 0-cone field is almost surely measurable, using the Brownian cone-process
realization of the frozen bundle. -/
theorem aemeasurable_prop48ZeroConeField
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) P := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  let A : ℝ → Ω → ℝ := fun t ω =>
    MatedCRTHarmonic.LQGCone.motConeRadial γ 0
      (fun s => B₀ s ω) (fun s => B₀' s ω) t
  have hA : MatedCRTHarmonic.MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ) A P :=
    MatedCRTHarmonic.LQGCone.isConeProcess_motConeRadial
      D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hm := MatedCRTHarmonic.MoTPort.ConeMeas2.aemeasurable_coneField D.gff₀ hA
  refine hm.congr (ae_of_all _ fun ω => ?_)
  exact (MatedCRTHarmonic.LQGCone.coneField_eq_motConeField γ 0 (X₀ ω)
    (fun t => B₀ t ω) (fun t => B₀' t ω)).symm

end MatedCRTHarmonic.GMS4

