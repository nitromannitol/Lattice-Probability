/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.WedgeAddConstLat at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (WedgeTK). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Independence.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible

/-!
# WEDGE-ADDCONST (3): scale invariance of the lateral part under an independent random factor

Input of the translation step of B4(c) (Sheffield, arXiv:1012.4797, §1.6 and §5.4: the lateral
part `h†` of a free-boundary GFF is scale invariant and independent of the radial part;
Duplantier–Miller–Sheffield, arXiv:1409.7055, §4.1 and the proof of Prop. 4.6, where the field is
re-centred at the first hitting radius of the radial part and the lateral part, being independent
of that radius, keeps its law).

`WedgeTK.fieldLawFull_lateralPart_rescale` gives, for each **fixed** `a > 0`, that the lateral
part of `rescale X Q a` has the law of the lateral part of `X`. Here the factor is random,
`a = f (U)`, with `U` independent of `X`: then `(U, lateral coordinates of rescale X Q (f U))` has
the joint law of `(U, lateral coordinates of X)` (`map_prod_latCoords_rescale_indep`,
`map_prod_lateralData_rescale_indep`). Proof: disintegration of the product law along `U`
(`map_prod_mk_dep`: if every section `x ↦ g (u, x)` pushes `ν` to the same `ν₀`, then
`(u, x) ↦ (u, g (u, x))` pushes `μ ⊗ ν` to `μ ⊗ ν₀`), joint measurability of
`(x, a) ↦ rescale x Q a` (`Prop16Area.measurable_rescale_apply_joint`).

Own elementary argument (conditioning on an independent variable, rectangle computation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace F1



/-- **Disintegration along the first factor.** If every section `x ↦ g (u, x)` pushes `ν`
forward to the same law `ν₀`, then `(u, x) ↦ (u, g (u, x))` pushes `μ ⊗ ν` to `μ ⊗ ν₀`. -/
theorem map_prod_mk_dep {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μ : Measure β) (ν : Measure γ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : β × γ → δ} (hg : Measurable g) (ν₀ : Measure δ)
    [IsProbabilityMeasure ν₀] (h : ∀ u, ν.map (fun x => g (u, x)) = ν₀) :
    (μ.prod ν).map (fun q => (q.1, g q)) = μ.prod ν₀ := by
  have hm : Measurable fun q : β × γ => (q.1, g q) := measurable_fst.prodMk hg
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hm (hs.prod ht), Measure.prod_apply (hm (hs.prod ht))]
  have e : ∀ u, ν (Prod.mk u ⁻¹' ((fun q : β × γ => (q.1, g q)) ⁻¹' s ×ˢ t)) =
      s.indicator (fun _ => ν₀ t) u := by
    intro u
    by_cases hu : u ∈ s
    · rw [indicator_of_mem hu, ← h u, Measure.map_apply
        (show Measurable fun x => g (u, x) from hg.comp measurable_prodMk_left) ht]
      congr 1
      ext x
      simp [hu]
    · rw [indicator_of_notMem hu]
      have : Prod.mk u ⁻¹' ((fun q : β × γ => (q.1, g q)) ⁻¹' s ×ˢ t) = ∅ := by
        ext x
        simp [hu]
      rw [this, measure_empty]
  simp_rw [e]
  rw [lintegral_indicator_const hs, mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

end F1
end QuantumZipper
