import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurableLocal
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset

/-! # Countability of separated cell configurations -/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace ReflectedGMS.GMS

/-- A locally separated family in a second-countable subspace is countable. -/
theorem countable_of_locally_dCC_separated (T : Set GMSSpace)
    [SecondCountableTopology T] (S : Set T)
    (hsep : ∀ x ∈ S, ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ y ∈ S, x ≠ y → c ≤ CellConfig.dCC x.1.1 y.1.1) : S.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof S).countable
  apply discreteTopology_subtype_iff'.2
  intro x hx
  obtain ⟨c, hc, hcx⟩ := hsep x hx
  let U : Set GMSSpace := {y | CellConfig.dCC x.1.1 y.1 < c}
  have hU : IsOpen U := TopologicalSpace.isOpen_generateFrom_of_mem ⟨x.1, c, hc, rfl⟩
  refine ⟨Subtype.val ⁻¹' U, isOpen_induced hU, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyS⟩
    by_contra hne
    exact (not_le_of_gt hy) (hcx y hyS (Ne.symm hne))
  · intro hy
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨by simpa [U, CellConfig.dCC_self] using hc, hx⟩

end ReflectedGMS.GMS
