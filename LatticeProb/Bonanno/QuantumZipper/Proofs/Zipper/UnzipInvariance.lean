/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.UnzipInvariance at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Basic.ENNReal.Basic
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `Γ⁰` is invariant under unzipping (blueprint node B1)

Task S5-B1. Conditionally on Theorem 1.2 (`theorem1_2`), for `κ > 0`, `γ = √κ`, `t > 0`, a
Brownian motion `B` and a free field `X ⊥ B`, the configuration
`c ω = (𝔥₀ + X ω, √κ B(·, ω))` satisfies

* `configLawMod0 (zipCapDown γ t ∘ c) P = configLawMod0 c P` (Corollary 1.5(a) at time `-t`),
* the unzipped field is independent of the future driver `s ↦ W(t+s) - W t`.

Route (blueprint B1):
1. `fwdMapInv W t = revMap V t` on `ℍ` for the time-reversed driver `V s = W(t-s) - W t`
   (`fwdMapInv_eq_revMap_timeRev`).
2. `B'_s = B_{t-s} + B_{max s t} - 2 B_t` is a Brownian motion (`isBrownianReal_revBM`), a
   function of `B`, hence independent of `X`, and `√κ B' = V` on `[0,t]`.
3. For a deterministic good measure `ν`, a.s. `evalReg (𝔥₀ + X) ν = ∫ 𝔥₀ dν + X ν`
   (`ae_evalReg_h0rev_add`, mean-value property of `log` plus the GFF regularization lemma);
   with independence this gives, for every test function, a.s. equality of the raw pairings of
   the unzipped field and of the Theorem 1.2 field `𝔥_t(V) + X ∘ revMap V t`.
4. Theorem 1.2 for `(B', X)` identifies the field law; the weak Markov property gives the
   driver law and the independence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace UnzipInvariance

open CharFun

/-! ## 1. Unzipping is the reverse flow of the time-reversed driver -/

/-! ## 2. Regularized evaluation of `𝔥₀ + X` -/

/-! ## 3. The unzipped field versus the Theorem 1.2 field, for a fixed driver path -/

/-! ## 4. Laws on product spaces -/

/-- Independent join: if `m₁, m₂ ≤ m_B` are independent and `m_X` is independent of `m_B`, then
`m₁ ⊔ m_X` is independent of `m₂`. -/
theorem indep_sup_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m₁ m₂ mX mB : MeasurableSpace Ω} (h₁ : m₁ ≤ mB) (h₂ : m₂ ≤ mB)
    (hmB : mB ≤ mΩ) (hmX : mX ≤ mΩ) (h12 : Indep m₁ m₂ P) (hXB : Indep mX mB P) :
    Indep (m₁ ⊔ mX) m₂ P := by
  refine IndepSets.indep (sup_le (h₁.trans hmB) hmX) (h₂.trans hmB)
    (GermZeroOne.isPiSystem_rectSets m₁ mX) (@MeasurableSpace.isPiSystem_measurableSet Ω m₂)
    (GermZeroOne.sup_eq_generateFrom_rectSets m₁ mX)
    (@MeasurableSpace.generateFrom_measurableSet Ω m₂).symm ?_
  rw [IndepSets_iff]
  rintro _ D ⟨A, C, hA, hC, rfl⟩ hD
  have e1 : P (C ∩ (A ∩ D)) = P C * P (A ∩ D) :=
    (Indep_iff _ _ _).1 hXB C (A ∩ D) hC ((h₁ A hA).inter (h₂ D hD))
  have e2 : P (A ∩ D) = P A * P D := (Indep_iff _ _ _).1 h12 A D hA hD
  have e3 : P (C ∩ A) = P C * P A := (Indep_iff _ _ _).1 hXB C A hC (h₁ A hA)
  calc P (A ∩ C ∩ D) = P (C ∩ (A ∩ D)) := by
        congr 1; ext ω; simp only [mem_inter_iff]; tauto
    _ = P C * (P A * P D) := by rw [e1, e2]
    _ = P (A ∩ C) * P D := by rw [inter_comm A C, e3, mul_assoc]

/-! ## 5. The time-reversed Brownian motion -/

/-- Time reversal of `B` at time `τ`, continued after `τ`: `B'_s = B_{τ-s} + B_{max s τ} - 2B_τ`,
i.e. `B_{τ-s} - B_τ` for `s ≤ τ` and `B_s - 2 B_τ` for `s ≥ τ` (when `B_0 = 0`). -/
def revBM {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (s : ℝ≥0) : Ω → ℝ :=
  B (τ - s) + B (max s τ) - (2 : ℝ) • B τ

@[simp] theorem revBM_apply {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ s : ℝ≥0) (ω : Ω) :
    revBM B τ s ω = B (τ - s) ω + B (max s τ) ω - 2 * B τ ω := by
  simp [revBM]

section Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end Brownian

/-! ## 6. Assembly -/

/-! ## 7. Unconditional versions (Theorem 1.2 is proved in `Proofs/Thm12/Main.lean`) -/

end UnzipInvariance
end QuantumZipper
