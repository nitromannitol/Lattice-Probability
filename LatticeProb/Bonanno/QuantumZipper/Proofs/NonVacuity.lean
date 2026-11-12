/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.NonVacuity at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess

/-!
# Non-vacuity of the main hypotheses

The hypotheses of the main statements (a Brownian motion independent of a free / zero-boundary
GFF; a quantum wedge independent of a Brownian motion) are jointly satisfiable.

Mathlib (at this pin) defines `IsBrownianReal` but contains **no existence theorem** for
Brownian motion (no Kolmogorov extension over `ℝ≥0`, no continuity theorem / Lévy
construction). We therefore isolate this single missing fact as the proposition
`BrownianMotionExists` and prove everything else from it.

Independence of the coordinates of a product measure is proved *without any measurability
assumption* on the random variables (via `Measure.prod_prod` for arbitrary sets), which
avoids having to prove measurability of the wedge field (which involves `lastZero`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper

namespace NonVacuity

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {Q : Measure Ω'} {f : Ω' → Ω}

theorem nv_map_comp (hf : MeasurePreserving f Q P) {E : Type*} [MeasurableSpace E]
    {X : Ω → E} (hX : AEMeasurable X P) : Q.map (fun ω => X (f ω)) = P.map X := by
  rw [← hf.map_eq] at hX ⊢
  exact (AEMeasurable.map_map_of_aemeasurable hX hf.measurable.aemeasurable).symm

theorem nv_aemeas_comp (hf : MeasurePreserving f Q P) {E : Type*} [MeasurableSpace E]
    {X : Ω → E} (hX : AEMeasurable X P) : AEMeasurable (fun ω => X (f ω)) Q := by
  rw [← hf.map_eq] at hX
  exact hX.comp_aemeasurable hf.measurable.aemeasurable

theorem nv_hasGaussianLaw (hf : MeasurePreserving f Q P) {E : Type*} [TopologicalSpace E]
    [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E]
    {X : Ω → E} (h : HasGaussianLaw X P) : HasGaussianLaw (fun ω => X (f ω)) Q where
  aemeasurable := nv_aemeas_comp hf h.aemeasurable
  isGaussian_map := by rw [nv_map_comp hf h.aemeasurable]; exact h.isGaussian_map

end Transfer

section Indep

variable {α β 𝓧 𝓨 : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- Coordinates of a product probability measure are independent, with no measurability
assumptions on the random variables. -/
theorem nv_indepFun_prod (X : α → 𝓧) (Y : β → 𝓨) :
    IndepFun (fun p : α × β => X p.1) (fun p => Y p.2) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have e1 : (fun p : α × β => X p.1) ⁻¹' s = (X ⁻¹' s) ×ˢ (Set.univ : Set β) := by ext; simp
  have e2 : (fun p : α × β => Y p.2) ⁻¹' t = (Set.univ : Set α) ×ˢ (Y ⁻¹' t) := by ext; simp
  have e3 : (X ⁻¹' s) ×ˢ (Set.univ : Set β) ∩ (Set.univ : Set α) ×ˢ (Y ⁻¹' t)
      = (X ⁻¹' s) ×ˢ (Y ⁻¹' t) := by ext; simp
  rw [e1, e2, e3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp

end Indep
