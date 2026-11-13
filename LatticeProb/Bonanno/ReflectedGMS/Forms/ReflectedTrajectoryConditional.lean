/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ReflectedTrajectoryConditional at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.StrongMarkov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! The existing bounded-observable Markov proof, generalized to measurable
functionals of the entire future trajectory. Vertex tests specialize this API. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.ReflectedMarkovConditional

open ReflectedWalk ReflectedWalk.Theorem16

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]
variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

private lemma integrable_trajectoryTest (Φ : Trajectory V → ℝ) (C : ℝ)
    (hΦ : Measurable Φ) (hf : ∀ γ, ‖Φ γ‖ ≤ C) (z : V) (s : ℝ≥0) :
    Integrable (fun ω => Φ (shiftedPath PF.X s ω)) (PF.P z) := by
  apply Integrable.of_bound
    (hΦ.comp (measurable_shiftedPath PF.measurable_X s)).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun ω => hf _

/-- On one vertex fibre at time `s`, property (iv) gives the exact restricted
integral identity for every event in the natural filtration at `s`. -/
theorem setIntegral_trajectoryFiber (h : IsReflectedWalk G w hmin PF) (z x : V)
    (s : ℝ≥0) (Φ : Trajectory V → ℝ) (C : ℝ)
    (hΦ : Measurable Φ) (hf : ∀ γ, ‖Φ γ‖ ≤ C) {F : Set PF.Ω}
    (hF : MeasurableSet[PF.naturalFiltration s] F) :
    ∫ ω in F, {ω | PF.X s ω = some x}.indicator
        (fun ω => Φ (shiftedPath PF.X s ω)) ω ∂PF.P z =
      ∫ ω in F, {ω | PF.X s ω = some x}.indicator
        (fun _ => ∫ γ, Φ γ ∂PF.law x) ω ∂PF.P z := by
  let E : Set PF.Ω := {ω | PF.X s ω = some x}
  have hE : MeasurableSet E :=
    (PF.measurable_X s) (measurableSet_singleton (some x))
  rw [ProcessFamily.naturalFiltration, naturalFiltration_apply] at hF
  obtain ⟨S, hS, rfl⟩ := measurableSet_pastSigma_iff.1 hF
  let pair : PF.Ω → (Set.Iic s → Option V) × Trajectory V :=
    fun ω => (pastPath PF.X s ω, shiftedPath PF.X s ω)
  let obs : Trajectory V → ℝ := Φ
  let q : ((Set.Iic s → Option V) × Trajectory V) → ℝ :=
    fun p => (S ×ˢ (univ : Set (Trajectory V))).indicator (fun p => obs p.2) p
  have hpair : Measurable pair :=
    (measurable_pastPath PF.measurable_X s).prodMk
      (measurable_shiftedPath PF.measurable_X s)
  have hobs : Measurable obs := hΦ
  have hq : Measurable q :=
    (hobs.comp measurable_snd).indicator (hS.prod MeasurableSet.univ)
  let nu : Measure (Set.Iic s → Option V) :=
    ((PF.P z).restrict E).map (pastPath PF.X s)
  let rho : Measure (Trajectory V) := PF.law x
  have hqint : Integrable q (nu.prod rho) := by
    have hC : 0 ≤ C := (norm_nonneg (Φ (fun _ => none))).trans (hf _)
    apply Integrable.of_bound hq.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun p => by
      by_cases hp : p ∈ S ×ˢ (univ : Set (Trajectory V))
      · simp only [q, Set.indicator_of_mem hp]
        exact hf _
      · simp only [q, Set.indicator_of_notMem hp, norm_zero]
        exact hC
  have hM := (h z).2.2.2.2.2.1 s x
  have heq :
      ∫ p, q p ∂((PF.P z).restrict E).map pair = ∫ p, q p ∂nu.prod rho := by
    rw [hM]
  have hleft :
      ∫ p, q p ∂((PF.P z).restrict E).map pair =
        ∫ ω in pastPath PF.X s ⁻¹' S,
          E.indicator (fun ω => Φ (shiftedPath PF.X s ω)) ω ∂PF.P z := by
    rw [integral_map hpair.aemeasurable hq.aestronglyMeasurable]
    rw [← integral_indicator hE,
      ← integral_indicator ((measurable_pastPath PF.measurable_X s) hS)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hSω : pastPath PF.X s ω ∈ S <;>
        by_cases hxω : PF.X s ω = some x
      · simp [q, pair, obs, E, hSω, hxω]
      · simp [q, pair, obs, E, hSω, hxω]
      · simp [q, pair, obs, E, hSω, hxω]
      · simp [q, pair, obs, E, hSω, hxω]
  have hright :
      ∫ p, q p ∂nu.prod rho =
        ∫ ω in pastPath PF.X s ⁻¹' S,
          E.indicator
            (fun _ => ∫ γ, Φ γ ∂PF.law x) ω ∂PF.P z := by
    rw [integral_prod q hqint]
    have hinner : ∀ a : Set.Iic s → Option V,
        (∫ b, q (a, b) ∂rho) =
          S.indicator (fun _ => ∫ b, obs b ∂rho) a := by
      intro a
      by_cases ha : a ∈ S
      · simp [q, ha]
      · simp [q, ha]
    simp_rw [hinner]
    rw [integral_indicator hS, setIntegral_const, smul_eq_mul]
    let A : Set PF.Ω := pastPath PF.X s ⁻¹' S
    have hA : MeasurableSet A := (measurable_pastPath PF.measurable_X s) hS
    rw [← integral_indicator hA]
    have hind : A.indicator
          (E.indicator
            (fun _ => ∫ γ, Φ γ ∂PF.law x)) =
        (A ∩ E).indicator
          (fun _ => ∫ γ, Φ γ ∂PF.law x) := by
      funext ω
      by_cases hAω : ω ∈ A <;> by_cases hEω : ω ∈ E <;>
        simp [hAω, hEω]
    rw [hind, integral_indicator (hA.inter hE), setIntegral_const, smul_eq_mul]
    congr 1
    simp only [nu, measureReal_def, Measure.map_apply
      (measurable_pastPath PF.measurable_X s) hS]
    change (((PF.P z).restrict E) A).toReal = ((PF.P z) (A ∩ E)).toReal
    rw [Measure.restrict_apply hA]
  rw [← hleft, heq, hright]

lemma measurableSet_vertexFiber_naturalFiltration (s : ℝ≥0) (x : V) :
    MeasurableSet[PF.naturalFiltration s] {ω | PF.X s ω = some x} := by
  rw [ProcessFamily.naturalFiltration, naturalFiltration_apply]
  apply measurableSet_pastSigma_iff.2
  let i : Set.Iic s := ⟨s, show s ≤ s from le_rfl⟩
  refine ⟨(fun p : Set.Iic s → Option V => p i) ⁻¹' {some x},
    measurable_pi_apply i (measurableSet_option {some x}), ?_⟩
  ext ω
  simp [pastPath, i]

/-- The conditional expectation identity localized to the fibre where the
process is at a specified vertex at time `s`. -/
theorem condExp_trajectoryFiber (h : IsReflectedWalk G w hmin PF) (z x : V)
    (s : ℝ≥0) (Φ : Trajectory V → ℝ) (C : ℝ)
    (hΦ : Measurable Φ) (hf : ∀ γ, ‖Φ γ‖ ≤ C) :
    (PF.P z)[{ω | PF.X s ω = some x}.indicator
        (fun ω => Φ (shiftedPath PF.X s ω)) | PF.naturalFiltration s] =ᵐ[PF.P z]
      {ω | PF.X s ω = some x}.indicator
        (fun _ => ∫ γ, Φ γ ∂PF.law x) := by
  let E : Set PF.Ω := {ω | PF.X s ω = some x}
  let Y : PF.Ω → ℝ := fun ω => Φ (shiftedPath PF.X s ω)
  let c : ℝ := ∫ γ, Φ γ ∂PF.law x
  have hE : MeasurableSet[PF.naturalFiltration s] E :=
    measurableSet_vertexFiber_naturalFiltration s x
  have hYint : Integrable Y (PF.P z) := integrable_trajectoryTest Φ C hΦ hf z s
  have hgint : Integrable (E.indicator fun _ => c) (PF.P z) :=
    (integrable_const c).indicator ((PF.naturalFiltration.le s) E hE)
  have hchar :
      E.indicator (fun _ => c) =ᵐ[PF.P z]
        (PF.P z)[E.indicator Y | PF.naturalFiltration s] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (PF.naturalFiltration.le s)
      (hYint.indicator ((PF.naturalFiltration.le s) E hE))
      (fun _ _ _ => hgint.integrableOn)
    · intro F hF _
      exact (setIntegral_trajectoryFiber h z x s Φ C hΦ hf hF).symm
    · exact (measurable_const.indicator hE).aestronglyMeasurable
  exact hchar.symm

/-- For a bounded measurable trajectory test, the reflected walk satisfies the usual
deterministic-time Markov conditional-expectation formula. -/
theorem condExp_trajectory_test (h : IsReflectedWalk G w hmin PF) (z : V)
    (s : ℝ≥0) (Φ : Trajectory V → ℝ) (C : ℝ)
    (hΦ : Measurable Φ) (hf : ∀ γ, ‖Φ γ‖ ≤ C) :
    (PF.P z)[(fun ω => Φ (shiftedPath PF.X s ω)) | PF.naturalFiltration s] =ᵐ[PF.P z]
      fun ω => (PF.X s ω).elim 0
        (fun x => ∫ γ, Φ γ ∂PF.law x) := by
  let Y : PF.Ω → ℝ := fun ω => Φ (shiftedPath PF.X s ω)
  have hYint : Integrable Y (PF.P z) := integrable_trajectoryTest Φ C hΦ hf z s
  have hall : ∀ᵐ ω ∂PF.P z, ∀ x : V,
      {ω | PF.X s ω = some x}.indicator
          ((PF.P z)[Y | PF.naturalFiltration s]) ω =
        {ω | PF.X s ω = some x}.indicator
          (fun _ => ∫ γ, Φ γ ∂PF.law x) ω := by
    apply ae_all_iff.2
    intro x
    let E : Set PF.Ω := {ω | PF.X s ω = some x}
    have hE : MeasurableSet[PF.naturalFiltration s] E :=
      measurableSet_vertexFiber_naturalFiltration s x
    have hind := condExp_indicator hYint hE
    have hfib := condExp_trajectoryFiber h z x s Φ C hΦ hf
    exact hind.symm.trans hfib
  filter_upwards [hall, (h z).2.1 s] with ω hω hdefined
  obtain ⟨x, hx⟩ := hdefined.1
  have hxid := hω x
  simpa [Y, hx] using hxid

end ReflectedGMS.ReflectedMarkovConditional
