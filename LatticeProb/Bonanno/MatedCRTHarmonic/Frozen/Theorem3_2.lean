/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.Theorem3_2 at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.EnergyOn
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsHarmonicExtension
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsTutteEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.ExitGreen
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.DirichletEnergy
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HasBoundedConvexity
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTCell
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.MainResultsFinal

/-!
# [18] Theorem 3.2 (quantitative Dirichlet energy bound), conditional on the mating-of-trees input bundle

Main theorem of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here called [18]. It is conditional on the
mating-of-trees input bundle: it holds for every mating-of-trees coupling (every witness of
`MatedCRT.MatingOfTreesInput γ`); the bundle itself is not proved here. The statement is the frozen
statement text, with the library namespace renamed and the theorem named after [18]; the proof is
`matedCRT_energy_le_add_of_matingOfTrees_holds` in `MatedCRTHarmonic.GMSMain.MainResultsFinal`, which proves the same statement.

Every theorem is stated for every mating-of-trees coupling `MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B'
B₀ B₀' U ηL η η₀ bm` with `γ ∈ (0, 2)` on a standard Borel probability space, that is, for every witness of the
bundle `MatedCRT.MatingOfTreesInput γ`: `η` is the whole-plane space-filling SLE_{16/γ²} parametrized by the γ-LQG
area of the γ-quantum cone, with `η(0) = 0`, and `bm` is its normalized boundary-length pair. For a mesh `ε > 0` the
vertex `x : ℤ` stands for `εx ∈ εℤ`, its cell is `MatedCRT.cell ε η x = η([εx − ε, εx])` ([18] (1.3)), its embedded
position is `η(εx)`, and the map `G^ε` is `MatedCRT.graph ε (bm ω) h`, the mated-CRT map of [18] (1.1) with its
double edges. "With probability at least `1 − O_ε(ε^α)`" is `∃ C, ∀ ε ∈ (0, 1), P(bad event) ≤ C ε^α`, with `P` the
outer measure of the bad event; the bad event contains the null set where `G^ε` is not locally finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

/-- **[18] Theorem 3.2 (quantitative Dirichlet energy bound)**, for every mating-of-trees coupling. There are
`α = α(γ) > 0` and `β = β(γ) > 0` (chosen before `ρ`) such that for every `ρ ∈ (0, 1)` and `C ≥ 1` there are
`A = A(C, ρ, γ) > 0` and a rate constant depending only on `(C, ρ, γ)` with: for every `ε ∈ (0, 1)` and every
`(D, f) ∈ 𝒞_C(ε^β)` (`D ⊂ B_ρ(0)` open, `area(B_r(∂D)) ≤ C r` for `r ∈ (0, 1)`, `C`-bounded convexity; `f`
differentiable on `D` with `∇f` `ε^{-β}`-Lipschitz and `‖f‖_∞, ‖∇f‖_∞ ≤ ε^{-β}`; `f` continuous on `D̄`), with
probability at least `1 − O_ε(ε^α)` the harmonic function `f_ε` of (1.6) exists and
`Energy(f_ε; G^ε(D)) ≤ A Energy(f; D) + ε^α` ((3.10)). -/
theorem theorem3_2 :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
          ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            ∀ D : Set ℂ, ∀ hD : IsOpen D, D ⊆ ball (0 : ℂ) ρ →
            (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
            HasBoundedConvexity C D →
            ∀ f : ℂ → ℝ, ∀ hf : DifferentiableOn ℝ f D,
              (∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
              (∀ z ∈ D, |f z| ≤ ε ^ (-β)) → (∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
              ContinuousOn f (closure D) →
                P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
                  (∃ g : ℤ → ℝ,
                    (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g) ∧
                  ∀ g : ℤ → ℝ,
                    (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g →
                    (MatedCRT.graph ε (bm ω) h).energyOn (verticesMeeting (MatedCRT.cell ε (η ω)) D) g ≤
                      ENNReal.ofReal A * dirichletEnergy f D hD hf + ENNReal.ofReal (ε ^ α)} ≤
                  ENNReal.ofReal (Cr * ε ^ α) := by
  exact GMSMain.MainResults.matedCRT_energy_le_add_of_matingOfTrees_holds

end MatedCRTHarmonic
