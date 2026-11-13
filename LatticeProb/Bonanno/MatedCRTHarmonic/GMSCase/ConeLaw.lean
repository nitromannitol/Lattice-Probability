/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.ConeLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.JointLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OG4Adapter
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeCirc

/-!
# Case 4 versus the γ-quantum cone on the unit disk

Source: (`[18]:N`), proof of Proposition 4.10, Case 4 and the
final paragraph, `[18]`: "`h⁴` has the law of a whole-plane GFF plus
`−γ log|·|`, normalized so that its circle average over `∂𝔻` is 0 (even if we condition on `z`)
… If `h` is the circle-average embedding of a γ-quantum cone in `(ℂ, 0, ∞)`, then
`h⁴|_𝔻 =d h|_𝔻`."

We make this precise **jointly with the curve**, on the frozen mating-of-trees coupling `D`:

* `case4Field γ h z₀ = h(·/2 + z₀) − h_{1/2}(z₀) − γ log|·|` is the Case 4 field;
* `map_restrict_coneField`: the γ-cone field restricted to `𝔻` has the law of `(h − γ log|·|)|_𝔻`
  for any normalized whole-plane GFF `h` (on any probability space).

The bundle assembly with the full IG data is `GMSCase/Bundle.lean`.

The cone's restriction to the closed unit disk is a normalized whole-plane GFF minus `γ log|·|`
pathwise (`GMCFacts.exists_cone_decomposition`), and the cone field is independent of `ηL`
(IGCO's `IGLaw.IsMatingOfTreesCoupling.indepFun_coneField_ηL`). The normalized field
`normalizedWP (X₀ ω)` is definitionally CANON's `Canon.normalizeWholePlane (X₀ ω)`; the generic
statements (`…_of`) hold for any normalized whole-plane GFF independent of `ηL`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT

/-! ## The Case 4 field -/

/-- The logarithmic singularity `u ↦ γ (−log|u|)` of the Case 4 field and of the γ-cone on `𝔻`. -/
def logSing (γ : ℝ) (u : ℂ) : ℝ := γ * (-Real.log ‖u‖)

/-- Adding the fixed singularity `γ(−log|·|)`. -/
def addLogSing (γ : ℝ) (g : DistC) : DistC := g + MoTPort.ofFunC (logSing γ)

theorem measurable_addLogSing (γ : ℝ) : Measurable (addLogSing γ) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  show Measurable fun g : DistC => g φ + MoTPort.ofFunC (logSing γ) φ
  exact (measurable_distOn_apply φ).add measurable_const

theorem locallyIntegrable_logSing (γ : ℝ) : LocallyIntegrable (logSing γ) volume := by
  have h := (QuantumZipper.K3.locallyIntegrable_log_norm.neg).smul γ
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp [logSing, smul_eq_mul]

/-- Two locally integrable functions agreeing on an open set give the same restricted shift. -/
theorem restrictTo_add_ofFunC_congr {g₁ g₂ : ℂ → ℝ} (h₁ : LocallyIntegrable g₁ volume)
    (h₂ : LocallyIntegrable g₂ volume) (V : Opens ℂ) (heq : ∀ z ∈ (V : Set ℂ), g₁ z = g₂ z)
    (T : DistC) :
    restrictTo V (T + MoTPort.ofFunC g₁) = restrictTo V (T + MoTPort.ofFunC g₂) := by
  refine DFunLike.ext _ _ fun φ => ?_
  show (T + MoTPort.ofFunC g₁) (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ) =
    (T + MoTPort.ofFunC g₂) (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    MoTPort.ConeCirc.ofFunC_apply' h₁, MoTPort.ConeCirc.ofFunC_apply' h₂]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hval : ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ : TestC) :
      ℂ → ℝ) x = φ x := by
    rw [TestFunction.monoCLM_apply]
    simp only [le_refl, le_top, and_self, ite_true]
  simp only
  rw [hval]
  by_cases hx : x ∈ (V : Set ℂ)
  · rw [heq x hx]
  · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hs => hx (φ.tsupport_subset hs)
    rw [h0, zero_mul, zero_mul]

/-! ## The γ-cone on the unit disk -/

section Cone

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The γ-cone field restricted to `𝔻` has the law of `(h − γ log|·|)|_𝔻`** for any normalized
whole-plane GFF `h` on any probability space, given the cone data `(X, B, B')` with the laws and
independence of the frozen bundle. -/
theorem map_restrict_coneField {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) {X : Ω → DistC}
    {B B' : ℝ≥0 → Ω → ℝ} (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {h : Ω' → DistC}
    (hh : IsNormalizedWPGFF h P') :
    P.map (fun ω => restrictTo (ballO (0 : ℂ) 1)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) =
      P'.map (fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (h ω))) := by
  obtain ⟨Xt, hXt, hdec⟩ := GMCFacts.exists_cone_decomposition hγ.1 hX hB hB' hind hγ.2
  have hcongr : (fun ω => restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) =ᵐ[P]
      fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (Xt ω)) := by
    filter_upwards [hdec] with ω ⟨g, hg, _, hgli, _, hgD⟩
    have e : coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) =
        Xt ω + MoTPort.ofFunC g := hg
    rw [e, addLogSing]
    refine restrictTo_add_ofFunC_congr hgli (locallyIntegrable_logSing γ) _ (fun z hz => ?_) _
    have hz' : ‖z‖ ≤ 1 := by
      have : z ∈ ball (0 : ℂ) 1 := hz
      rw [mem_ball, dist_zero_right] at this
      exact this.le
    rw [hgD z hz', logSing]
  have hF : Measurable fun g : DistC => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ g) :=
    (measurable_restrictTo _).comp (measurable_addLogSing γ)
  rw [Measure.map_congr hcongr]
  have hlaw : P.map Xt = P'.map h := CircleAvg.map_eq_of_isNormalizedWPGFF hXt hh
  have e1 : P.map (fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (Xt ω))) =
      (P.map Xt).map fun g => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ g) := by
    rw [Measure.map_map hF hXt.1.measurable]
    rfl
  have e2 : P'.map (fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (h ω))) =
      (P'.map h).map fun g => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ g) := by
    rw [Measure.map_map hF hh.1.measurable]
    rfl
  rw [e1, e2, hlaw]

end Cone

end MatedCRTHarmonic.GMSCase
