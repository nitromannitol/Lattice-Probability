/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ReflectedIntegrableTrajectoryConditional at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedTrajectoryConditional

/-! The deterministic-time trajectory Markov formula for integrable observables. -/

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

/-- The restricted trajectory-law identity on one vertex fibre extends from
bounded tests to tests integrable under that vertex's trajectory law. -/
theorem setIntegral_trajectoryFiber_integrable
    (h : IsReflectedWalk G w hmin PF) (z x : V) (s : ℝ≥0)
    (Φ : Trajectory V → ℝ) (hΦ : Measurable Φ)
    (hΦlaw : Integrable Φ (PF.law x)) {F : Set PF.Ω}
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
    have hcomp : Integrable (fun p : (Set.Iic s → Option V) × Trajectory V => Φ p.2)
        (nu.prod rho) := hΦlaw.comp_snd nu
    exact hcomp.indicator (hS.prod MeasurableSet.univ)
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
        by_cases hxω : PF.X s ω = some x <;>
          simp [q, pair, obs, E, hSω, hxω]
  have hright :
      ∫ p, q p ∂nu.prod rho =
        ∫ ω in pastPath PF.X s ⁻¹' S,
          E.indicator (fun _ => ∫ γ, Φ γ ∂PF.law x) ω ∂PF.P z := by
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
          (E.indicator (fun _ => ∫ γ, Φ γ ∂PF.law x)) =
        (A ∩ E).indicator (fun _ => ∫ γ, Φ γ ∂PF.law x) := by
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

/-- Conditional expectation on one vertex fibre for an integrable trajectory test. -/
theorem condExp_trajectoryFiber_integrable
    (h : IsReflectedWalk G w hmin PF) (z x : V) (s : ℝ≥0)
    (Φ : Trajectory V → ℝ) (hΦ : Measurable Φ)
    (hshift : Integrable (fun ω => Φ (shiftedPath PF.X s ω)) (PF.P z))
    (hΦlaw : Integrable Φ (PF.law x)) :
    (PF.P z)[{ω | PF.X s ω = some x}.indicator
        (fun ω => Φ (shiftedPath PF.X s ω)) | PF.naturalFiltration s] =ᵐ[PF.P z]
      {ω | PF.X s ω = some x}.indicator
        (fun _ => ∫ γ, Φ γ ∂PF.law x) := by
  let E : Set PF.Ω := {ω | PF.X s ω = some x}
  let Y : PF.Ω → ℝ := fun ω => Φ (shiftedPath PF.X s ω)
  let c : ℝ := ∫ γ, Φ γ ∂PF.law x
  have hE : MeasurableSet[PF.naturalFiltration s] E :=
    measurableSet_vertexFiber_naturalFiltration s x
  have hgint : Integrable (E.indicator fun _ => c) (PF.P z) :=
    (integrable_const c).indicator ((PF.naturalFiltration.le s) E hE)
  have hchar :
      E.indicator (fun _ => c) =ᵐ[PF.P z]
        (PF.P z)[E.indicator Y | PF.naturalFiltration s] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (PF.naturalFiltration.le s)
      (hshift.indicator ((PF.naturalFiltration.le s) E hE))
      (fun _ _ _ => hgint.integrableOn)
    · intro F hF _
      exact (setIntegral_trajectoryFiber_integrable h z x s Φ hΦ hΦlaw hF).symm
    · exact (measurable_const.indicator hE).aestronglyMeasurable
  exact hchar.symm

/-- The deterministic-time trajectory Markov formula for a measurable test
that is integrable under the shifted starting law and every vertex law. -/
theorem condExp_trajectory_test_integrable
    (h : IsReflectedWalk G w hmin PF) (z : V) (s : ℝ≥0)
    (Φ : Trajectory V → ℝ) (hΦ : Measurable Φ)
    (hshift : Integrable (fun ω => Φ (shiftedPath PF.X s ω)) (PF.P z))
    (hΦlaw : ∀ x, Integrable Φ (PF.law x)) :
    (PF.P z)[(fun ω => Φ (shiftedPath PF.X s ω)) | PF.naturalFiltration s] =ᵐ[PF.P z]
      fun ω => (PF.X s ω).elim 0 (fun x => ∫ γ, Φ γ ∂PF.law x) := by
  let Y : PF.Ω → ℝ := fun ω => Φ (shiftedPath PF.X s ω)
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
    have hind := condExp_indicator hshift hE
    have hfib := condExp_trajectoryFiber_integrable h z x s Φ hΦ hshift (hΦlaw x)
    exact hind.symm.trans hfib
  filter_upwards [hall, (h z).2.1 s] with ω hω hdefined
  obtain ⟨x, hx⟩ := hdefined.1
  have hxid := hω x
  simpa [Y, hx] using hxid

end ReflectedGMS.ReflectedMarkovConditional
