/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CutFreeComponentStabilization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceTransition
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedEnergyAlgebra
import LatticeProb.Bonanno.ReflectedGMS.Forms.HilbertEnergySpace
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs

/-!
# Finite-trace transitions respect finite separators

Erasing an energy minimizer on a complement component with zero boundary data
cannot increase its full network energy. Uniqueness therefore forces it to
vanish there. In particular, the actual induced transition kernel cannot cross
a finite separator that is retained in its target set. This is the finite-trace
input for ruling out component switches during cut-free reflected excursions;
the all-times pathwise application is a separate step.
-/

set_option autoImplicit false

namespace ReflectedGMS.CutFreeComponentStabilization

open ReflectedWalk Classical

variable {V : Type*} (G : ConductanceGraph V)

/-- Erasing a component does not increase energy when the function vanishes on
the separating cut. This uses the full energy, with no support assumption. -/
theorem gradSq_erase_component_le (K : Finset V)
    (C : G.toSimpleGraph.ComponentCompl (K : Set V)) (f : V → ℝ)
    (hK : ∀ v ∈ K, f v = 0) (p : V × V) :
    G.gradSq (fun v => if v ∈ C then 0 else f v) p ≤ G.gradSq f p := by
  classical
  rcases p with ⟨x, y⟩
  by_cases hc : G.c x y = 0
  · simp [ConductanceGraph.gradSq, hc]
  have hadj : G.toSimpleGraph.Adj x y :=
    G.toSimpleGraph_adj.mpr (lt_of_le_of_ne (G.c_nonneg x y) (Ne.symm hc))
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · simpa [ConductanceGraph.gradSq, hx, hy] using G.gradSq_nonneg f (x, y)
  · have hyK : y ∈ K := by
      by_contra hyK
      exact hy (SimpleGraph.ComponentCompl.mem_of_adj x y hx hyK hadj)
    simpa [ConductanceGraph.gradSq, hx, hy, hK y hyK] using
      G.gradSq_nonneg f (x, y)
  · have hxK : x ∈ K := by
      by_contra hxK
      exact hx (SimpleGraph.ComponentCompl.mem_of_adj y x hy hxK hadj.symm)
    simpa [ConductanceGraph.gradSq, hx, hy, hK x hxK] using
      G.gradSq_nonneg f (x, y)
  · simp [ConductanceGraph.gradSq, hx, hy]

/-- The full-energy minimizer vanishes on a complementary component if its
prescribed boundary values vanish both on that component and on the cut. -/
theorem energyMin_eq_zero_on_component
    (hG : G.toSimpleGraph.Connected) {A K : Finset V} (hA : A.Nonempty)
    (hKA : K ⊆ A) (C : G.toSimpleGraph.ComponentCompl (K : Set V))
    (φ : V → ℝ) (hφK : ∀ v ∈ K, φ v = 0)
    (hφC : ∀ v ∈ A, v ∈ C → φ v = 0) {x : V} (hx : x ∈ C) :
    G.energyMin hG A φ x = 0 := by
  classical
  let f := G.energyMin hG A φ
  have hfK : ∀ v ∈ K, f v = 0 := by
    intro v hv
    exact (G.energyMin_eqOn hG hA φ (hKA hv)).trans (hφK v hv)
  obtain ⟨hfin, hE⟩ := G.Energy_le_of_gradSq_le
    (G.energyMin_hasFiniteEnergy hG hA φ) (gradSq_erase_component_le G K C f hfK)
  have heq : Set.EqOn (fun v => if v ∈ C then 0 else f v) φ (A : Set V) := by
    intro v hv
    by_cases hvC : v ∈ C
    · simp [hvC, hφC v hv hvC]
    · simpa [hvC, f] using G.energyMin_eqOn hG hA φ hv
  have huniq := G.energyMin_unique hG hA φ hfin heq
    (fun g hg hgA => hE.trans (G.energyMin_le_energy hG hA φ hg hgA))
  simpa only [if_pos hx] using (congrFun huniq x).symm

/-- Harmonic measure cannot cross a retained finite cut to a different
complementary component. -/
theorem harmonicMeasure_eq_zero_of_separated
    (hG : G.toSimpleGraph.Connected) {A K : Finset V} (hA : A.Nonempty)
    (hKA : K ⊆ A) (C : G.toSimpleGraph.ComponentCompl (K : Set V))
    {x y : V} (hx : x ∈ C) (hyK : y ∉ K) (hyC : y ∉ C) :
    G.harmonicMeasure hG A x y = 0 := by
  classical
  apply energyMin_eq_zero_on_component G hG hA hKA C (G.indic y) _ _ hx
  · intro v hv
    have hvy : v ≠ y := fun he => hyK (he ▸ hv)
    simp [ConductanceGraph.indic, hvy]
  · intro v _ hvC
    have hvy : v ≠ y := fun he => hyC (he ▸ hvC)
    simp [ConductanceGraph.indic, hvy]

/-- The actual finite-target transition probability between distinct
complementary components is zero when the target retains the cut. -/
theorem inducedTransProb_eq_zero_of_separated
    (hG : G.toSimpleGraph.Connected) {A K : Finset V} (hA : A.Nonempty)
    (hKA : K ⊆ A) (C : G.toSimpleGraph.ComponentCompl (K : Set V))
    {x y : V} (hxA : x ∈ A) (hyA : y ∈ A)
    (hxC : x ∈ C) (hyK : y ∉ K) (hyC : y ∉ C) :
    G.inducedTransProb hG A x y = 0 := by
  classical
  rw [FullNetworkForm.inducedTransProb_eq_harmonic_trace_div G hG hA hxA hyA]
  suffices hsum : (∑' v, G.c x v * G.harmonicMeasure hG A v y) = 0 by
    rw [hsum, zero_div]
  suffices hall : ∀ v, G.c x v * G.harmonicMeasure hG A v y = 0 by
    simp only [hall, tsum_zero]
  intro v
  by_cases hc : G.c x v = 0
  · simp [hc]
  have hadj : G.toSimpleGraph.Adj x v :=
    G.toSimpleGraph_adj.mpr (lt_of_le_of_ne (G.c_nonneg x v) (Ne.symm hc))
  by_cases hvK : v ∈ K
  · have hvy : v ≠ y := fun he => hyK (he ▸ hvK)
    have he := G.energyMin_eqOn hG hA (G.indic y) (hKA hvK)
    change G.harmonicMeasure hG A v y = G.indic y v at he
    simp [he, ConductanceGraph.indic, hvy]
  · have hvC := SimpleGraph.ComponentCompl.mem_of_adj x v hxC hvK hadj
    rw [harmonicMeasure_eq_zero_of_separated G hG hA hKA C hvC hyK hyC, mul_zero]

end ReflectedGMS.CutFreeComponentStabilization
