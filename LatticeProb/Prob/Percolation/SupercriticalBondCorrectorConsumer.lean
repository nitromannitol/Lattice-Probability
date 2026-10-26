import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.Prob.Percolation.SupercriticalBondUniquenessConsumer
import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth

/-!
# Actual normalized planes conditional on the cited inputs

The classical uniqueness event and the common corrector event intersect under the
actual Bernoulli product law. Their intersection supplies an actual infinite component,
a component basepoint, and a normalized nonconstant plane of every nonzero slope.
Both literature propositions remain explicit hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External

/-- At any strictly supercritical source parameter, the two cited inputs supply an
actual normalized nonconstant corrected plane with the prescribed nonzero slope. -/
theorem exists_nonconstant_normalized_plane_of_cited_inputs
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (q : Fin d → ℝ) (hq : q ≠ 0) :
    ∃ (ω : Configuration d) (h : HasUniqueInfiniteOpenComponent ω)
      (o : uniqueInfiniteComponent h) (u : uniqueInfiniteComponent h → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0 ∧
        ∃ x y : uniqueInfiniteComponent h, u x ≠ u y := by
  classical
  have hcluster : ∀ᵐ ω ∂latticeBondLaw d p, HasUniqueInfiniteOpenComponent ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent d)).mpr
      (hclassical.2 d hd p hpc hp1)
  obtain ⟨ω, h, hplanes⟩ := (hcluster.and (hcorrector d hd p hpc hp1)).exists
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent h).nonempty_supp
  let basepoint : uniqueInfiniteComponent h := ⟨o, ho⟩
  obtain ⟨u, ⟨hu, hnorm⟩, _⟩ := (hplanes h).1 q basepoint
  refine ⟨ω, h, basepoint, u, hu, hnorm, ?_⟩
  by_contra hconstant
  have heq : u = fun _ => u basepoint := by
    funext x
    by_contra hx
    exact hconstant ⟨x, basepoint, hx⟩
  have hzero : IsCorrectedPlane (uniqueInfiniteComponent h) 0 u := by
    rw [heq]
    exact isCorrectedPlane_const _ _
  obtain ⟨s, _, hunique⟩ := (hplanes h).2 u hu.1
  exact hq ((hunique q hu).trans (hunique 0 hzero).symm)

/-- In dimension two the classical input also supplies the parameter. The coordinate
slope yields an actual nonconstant normalized harmonic function with uniform slope tail. -/
theorem exists_two_dimensional_plane_of_cited_inputs
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) :
    ∃ p : unitInterval, criticalProbability 2 < (p : ℝ) ∧ (p : ℝ) < 1 ∧
      ∃ (ω : Configuration 2) (h : HasUniqueInfiniteOpenComponent ω)
        (o : uniqueInfiniteComponent h) (u : uniqueInfiniteComponent h → ℝ),
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) ∧
        componentSlopeAsymptotics (uniqueInfiniteComponent h) (Pi.single 0 1) u ∧
        u o = 0 ∧ ∃ x y : uniqueInfiniteComponent h, u x ≠ u y := by
  obtain ⟨p, hpc, hp1⟩ := exists_supercritical_parameter_of_classical_input hclassical 2
    (by decide)
  have hq : (Pi.single 0 1 : Fin 2 → ℝ) ≠ 0 := by
    intro heq
    have := congrFun heq 0
    norm_num at this
  obtain ⟨ω, h, o, u, hu, hnorm, hnonconstant⟩ :=
    exists_nonconstant_normalized_plane_of_cited_inputs hclassical hcorrector 2
      (by decide) p hpc hp1 (Pi.single 0 1) hq
  have hfull := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ _ _).mp hu
  exact ⟨p, hpc, hp1, ω, h, o, u, hfull.1, hfull.2, hnorm, hnonconstant⟩

end LatticeProb.Percolation
