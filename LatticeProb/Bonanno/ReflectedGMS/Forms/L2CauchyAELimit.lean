/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.L2CauchyAELimit at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Identifying an L2 Cauchy limit from almost-everywhere convergence

On a finite measure space, an L2-Cauchy sequence that converges almost everywhere
to a measurable function converges to that function in L2.  This is a small adapter
around completeness of `Lp` and uniqueness of limits in measure.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ReflectedGMS

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- An almost-everywhere limit of an L2-Cauchy sequence is in L2, and the whole
sequence converges to it in L2. -/
theorem memLp_two_and_tendsto_eLpNorm_of_cauchySeq_of_tendsto_ae
    {P : Measure Ω} [IsFiniteMeasure P] {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 P)
    (hcauchy : CauchySeq fun n => (hfn n).toLp (fn n))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => fn n ω) atTop (𝓝 (f ω))) :
    MemLp f 2 P ∧ Tendsto (fun n => eLpNorm (fn n - f) 2 P) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hg_measure : TendstoInMeasure P (fun n => (hfn n).toLp (fn n)) atTop g :=
    tendstoInMeasure_of_tendsto_Lp hg
  have hf_measure : TendstoInMeasure P fn atTop f :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hfn n).aestronglyMeasurable) hae
  have hfn_coe (n : ℕ) : (fun ω => (hfn n).toLp (fn n) ω) =ᵐ[P] fn n :=
    (hfn n).coeFn_toLp
  have hgf : (fun ω => g ω) =ᵐ[P] f :=
    tendstoInMeasure_ae_unique
      (hg_measure.congr_left hfn_coe) hf_measure
  have hfLp : MemLp f 2 P := (Lp.memLp g).ae_eq hgf
  have hgfLp : g = hfLp.toLp f := by
    apply Lp.ext
    exact hgf.trans hfLp.coeFn_toLp.symm
  refine ⟨hfLp, ?_⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fn hfn f hfLp).mp (hgfLp ▸ hg)

end ReflectedGMS
