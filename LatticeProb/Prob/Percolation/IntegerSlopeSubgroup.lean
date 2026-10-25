import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Integer linear-gradient slopes

For a family of real coefficient vectors, the slopes whose linear evaluations are integers
form an additive subgroup. This subgroup is closed in the finite-dimensional product topology.
The coefficient family is arbitrary data; no harmonic-plane construction is assumed here.
-/

namespace LatticeProb.Prob.Percolation

open scoped BigOperators

variable {ι : Type*} {d : ℕ}

/-- Slopes whose evaluation against every coefficient vector is an integer. -/
def integerSlopeSubgroup (g : ι → Fin d → ℝ) : AddSubgroup (Fin d → ℝ) where
  carrier := {p | ∀ e, ∃ z : ℤ, ∑ j, p j * g e j = (z : ℝ)}
  zero_mem' := by
    intro e
    exact ⟨0, by simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Int.cast_zero]⟩
  add_mem' := by
    intro p q hp hq e
    obtain ⟨m, hm⟩ := hp e
    obtain ⟨n, hn⟩ := hq e
    refine ⟨m + n, ?_⟩
    simpa only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Int.cast_add] using
      congrArg₂ (· + ·) hm hn
  neg_mem' := by
    intro p hp e
    obtain ⟨m, hm⟩ := hp e
    refine ⟨-m, ?_⟩
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Int.cast_neg] using
      congrArg Neg.neg hm

/-- Membership is exactly the full family of integer linear-gradient constraints. -/
@[simp] theorem mem_integerSlopeSubgroup (g : ι → Fin d → ℝ) (p : Fin d → ℝ) :
    p ∈ integerSlopeSubgroup g ↔ ∀ e, ∃ z : ℤ, ∑ j, p j * g e j = (z : ℝ) :=
  Iff.rfl

/-- Integer-gradient slopes are closed under addition. -/
theorem add_mem_integerSlopeSubgroup (g : ι → Fin d → ℝ) {p q : Fin d → ℝ}
    (hp : p ∈ integerSlopeSubgroup g) (hq : q ∈ integerSlopeSubgroup g) :
    p + q ∈ integerSlopeSubgroup g :=
  (integerSlopeSubgroup g).add_mem hp hq

/-- Integer-gradient slopes are closed under negation. -/
theorem neg_mem_integerSlopeSubgroup (g : ι → Fin d → ℝ) {p : Fin d → ℝ}
    (hp : p ∈ integerSlopeSubgroup g) : -p ∈ integerSlopeSubgroup g :=
  (integerSlopeSubgroup g).neg_mem hp

/-- Each linear evaluation of a slope is continuous in the product topology. -/
theorem continuous_slopeEvaluation (g : ι → Fin d → ℝ) (e : ι) :
    Continuous (fun p : Fin d → ℝ => ∑ j, p j * g e j) :=
  continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const

/-- The subgroup of integer-gradient slopes is closed, for any index set. -/
theorem isClosed_integerSlopeSubgroup (g : ι → Fin d → ℝ) :
    IsClosed (integerSlopeSubgroup g : Set (Fin d → ℝ)) := by
  change IsClosed {p : Fin d → ℝ | ∀ e, ∃ z : ℤ, ∑ j, p j * g e j = (z : ℝ)}
  simp_rw [Set.setOf_forall]
  apply isClosed_iInter
  intro e
  have hclosed := Int.isClosedEmbedding_coe_real.isClosed_range
  convert hclosed.preimage (continuous_slopeEvaluation g e) using 1
  ext p
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩

/-- Coordinate basis coefficients impose precisely integer coordinates on a slope. -/
theorem mem_integerSlopeSubgroup_coordinate (p : Fin d → ℝ) :
    p ∈ integerSlopeSubgroup (fun e j : Fin d => if e = j then 1 else 0) ↔
      ∀ j, ∃ z : ℤ, p j = (z : ℝ) := by
  simp only [mem_integerSlopeSubgroup, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Zero coefficients impose no constraint on slopes. -/
@[simp] theorem integerSlopeSubgroup_zero :
    integerSlopeSubgroup (fun (_ : ι) (_ : Fin d) => (0 : ℝ)) = ⊤ := by
  ext p
  simp only [mem_integerSlopeSubgroup, mul_zero, Finset.sum_const_zero,
    AddSubgroup.mem_top, iff_true]
  intro e
  exact ⟨0, Int.cast_zero.symm⟩

end LatticeProb.Prob.Percolation
