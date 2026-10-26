import LatticeProb.Prob.Percolation.CorrectedPlaneLinearMap
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.Prob.Percolation.SupercriticalBondUniquenessConsumer

/-!
# An actual injective normalized corrected-plane map

The two explicit literature inputs provide a strictly supercritical parameter in dimension
two and an actual configuration in the intersection of their full-probability events.
On its unique infinite component the normalized linear map is characterized and injective,
and its first coordinate plane is nonzero. No measurable choice of maps is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External

/-- The same two cited inputs yield an actual dimension-two component and basepoint,
with a characterized injective normalized linear map and a nonzero coordinate plane. -/
theorem exists_two_dimensional_correctedPlane_linearMap_of_cited_inputs
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) :
    ∃ p : unitInterval, criticalProbability 2 < (p : ℝ) ∧ (p : ℝ) < 1 ∧
      ∃ (ω : Configuration 2) (h : HasUniqueInfiniteOpenComponent ω)
        (o : uniqueInfiniteComponent h)
        (F : (Fin 2 → ℝ) →ₗ[ℝ] (uniqueInfiniteComponent h → ℝ)),
        (∀ q, IsCorrectedPlane (uniqueInfiniteComponent h) q (F q) ∧ F q o = 0) ∧
        Function.Injective F ∧ F (Pi.single 0 1) ≠ 0 := by
  classical
  obtain ⟨p, hpc, hp1⟩ := exists_supercritical_parameter_of_classical_input hclassical 2
    (by decide)
  have hcluster : ∀ᵐ ω ∂latticeBondLaw 2 p, HasUniqueInfiniteOpenComponent ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent 2)).mpr
      (hclassical.2 2 (by decide) p hpc hp1)
  obtain ⟨ω, h, hplanes⟩ := (hcluster.and (hcorrector 2 (by decide) p hpc hp1)).exists
  obtain ⟨x, hx⟩ := (uniqueInfiniteComponent h).nonempty_supp
  let o : uniqueInfiniteComponent h := ⟨x, hx⟩
  have hnormalized := fun q => (hplanes h).1 q o
  obtain ⟨F, hF, _⟩ :=
    existsUnique_normalized_correctedPlane_linearMap (uniqueInfiniteComponent h) o hnormalized
  have hchar := fun q => (hF q).1
  have hq : (Pi.single 0 1 : Fin 2 → ℝ) ≠ 0 := by
    intro heq
    have := congrFun heq 0
    norm_num at this
  exact ⟨p, hpc, hp1, ω, h, o, F, hF,
    correctedPlane_linearMap_injective _ (hplanes h).2 F hchar,
    correctedPlane_linearMap_apply_ne_zero _ (hplanes h).2 F hchar _ hq⟩

end LatticeProb.Percolation
