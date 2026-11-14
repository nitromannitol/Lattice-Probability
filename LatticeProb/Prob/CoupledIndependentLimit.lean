import LatticeProb.Prob.ApproximateIndependentLaw
import LatticeProb.Prob.CoupledLawConvergence

/-! # Independence of coupled weak limits

Independent pairs remain independent in a joint weak limit when they are close in
probability to pairs whose laws converge to that limit.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LatticeProb

/-- Independence passes to a joint weak limit of pairs that are close in probability to
independent pairs on the same probability space. -/
theorem indepFun_of_tendsto_law_of_coupled {S T Ω Ω' : Type*}
    [PseudoMetricSpace S] [PseudoMetricSpace T] [MeasurableSpace S] [MeasurableSpace T]
    [BorelSpace S] [BorelSpace T] [SecondCountableTopology S] [SecondCountableTopology T]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Xn Un : ℕ → Ω → S} {Yn Vn : ℕ → Ω → T} {X : Ω' → S} {Y : Ω' → T}
    (hXn : ∀ n, AEMeasurable (Xn n) P) (hYn : ∀ n, AEMeasurable (Yn n) P)
    (hUn : ∀ n, AEMeasurable (Un n) P) (hVn : ∀ n, AEMeasurable (Vn n) P)
    (hX : AEMeasurable X P') (hY : AEMeasurable Y P')
    (hind : ∀ n, IndepFun (Xn n) (Yn n) P)
    {ρ : ℕ → ProbabilityMeasure (S × T)} {ρ₀ : ProbabilityMeasure (S × T)}
    (hρn : ∀ n, (ρ n : Measure (S × T)) = P.map fun ω => (Un n ω, Vn n ω))
    (hρ₀ : (ρ₀ : Measure (S × T)) = P'.map fun ω => (X ω, Y ω))
    (hρ : Tendsto ρ atTop (𝓝 ρ₀))
    (hclose : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun n => P {ω | ε ≤ edist (Xn n ω, Yn n ω) (Un n ω, Vn n ω)})
        atTop (𝓝 0)) : IndepFun X Y P' := by
  let σ : ℕ → ProbabilityMeasure (S × T) := fun n =>
    ⟨P.map (fun ω => (Xn n ω, Yn n ω)), (Measure.isProbabilityMeasure_map_iff ((hXn n).prodMk (hYn n))).2 inferInstance⟩
  have hσ : ∀ n, (σ n : Measure (S × T)) = P.map fun ω => (Xn n ω, Yn n ω) :=
    fun _ => rfl
  have hc := tendsto_levyProkhorovDist_map_of_coupled P
    (fun n => (hXn n).prodMk (hYn n)) (fun n => (hUn n).prodMk (hVn n)) hclose
  apply indepFun_of_tendsto_law_of_levyProkhorovDist hXn hYn hX hY hind hσ hρ₀ hρ
  simpa only [hσ, hρn] using hc

end LatticeProb
