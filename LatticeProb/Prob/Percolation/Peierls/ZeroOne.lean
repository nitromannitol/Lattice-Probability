/-
# Almost sure planar site percolation

The Peierls estimate and the zero-one law imply that Bernoulli site
percolation on the planar lattice has an infinite open component almost surely
at sufficiently high density.
-/
import LatticeProb.Prob.Percolation.Peierls.Bound

open MeasureTheory ProbabilityTheory

namespace LatticeProb.Percolation

/-- At sufficiently high density, planar Bernoulli site percolation almost surely
has an infinite open component. -/
theorem peierls_hasInfiniteComponent_ae :
    ∃ p₀ : NNReal, p₀ < 1 ∧ ∀ p : NNReal, p₀ ≤ p → ∀ hp : p ≤ 1,
      ∀ᵐ ω ∂(sitePercolationLaw p hp), HasInfiniteComponent {z | ω z = true} := by
  obtain ⟨p₀, hp₀, hpos⟩ := peierls_origin_infinite_pos
  refine ⟨p₀, hp₀, fun p hp hp' => ?_⟩
  have : IsProbabilityMeasure (sitePercolationLaw p hp') := by
    unfold sitePercolationLaw
    infer_instance
  have hind : iIndepFun (fun v (ω : Site 2 → Bool) => ω v) (sitePercolationLaw p hp') := by
    unfold sitePercolationLaw
    exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hpositive : 0 < sitePercolationLaw p hp'
      {ω | HasInfiniteComponent {z | ω z = true}} := by
    apply (hpos p hp hp').trans_le
    apply measure_mono
    intro ω hinf
    have hopen : ω 0 = true := by
      by_contra h
      exact hinf (Set.finite_empty.subset fun _ hy => absurd hy.1 h)
    exact ⟨0, hopen, hinf⟩
  have hone := (GraphPercolation.hasInfiniteComponent_zero_one 2
    (sitePercolationLaw p hp') hind).resolve_left (ne_of_gt hpositive)
  have hmeas : MeasurableSet {ω : Site 2 → Bool | HasInfiniteComponent {z | ω z = true}} := by
    convert measurableSet_exists_infiniteOpenCluster 2 using 1
    ext ω
    exact (exists_infiniteOpenCluster_iff ω).symm
  exact (mem_ae_iff_prob_eq_one hmeas).2 hone

end LatticeProb.Percolation
