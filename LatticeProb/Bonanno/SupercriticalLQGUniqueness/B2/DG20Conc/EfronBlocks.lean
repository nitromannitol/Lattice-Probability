/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.EfronBlocks at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Prob.EfronSteinCopy

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace SupercriticalLQGUniqueness.B2.DG20Conc

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure[m₀] Ω}
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ι → Type*} [mE : ∀ i, MeasurableSpace (E i)]

 

theorem variance_decomposition [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {F : Ω → ℝ} (hF : MemLp F 2 P) :
    Var[F; P] = (∫ ω, Var[F; P | m] ω ∂P) + Var[P[F | m]; P] := by
  exact (integral_condVar_add_variance_condExp hm hF).symm

 
theorem efron_stein_independent_blocks [IsProbabilityMeasure P]
    (X X' : ∀ i, Ω → E i)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i))
    (hind : iIndep (LQGMetric.esCopySigma X X') P)
    (hlaw : ∀ i, P.map (X' i) = P.map (X i))
    {f : (∀ j, E j) → ℝ} (hf : Measurable f)
    (hF : MemLp (fun ω => f (fun j => X j ω)) 2 P) :
    Var[fun ω => f (fun j => X j ω); P] ≤
      ∑ i, ∫ ω, max
        (f (Function.update (fun j => X j ω) i (X' i ω)) - f (fun j => X j ω)) 0 ^ 2 ∂P := by
  exact LQGMetric.efronStein_copy_posPart hX hX' hind hlaw hf hF

 

end SupercriticalLQGUniqueness.B2.DG20Conc
