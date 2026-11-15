import LatticeProb.Prob.SelectorOuterRestriction
import LatticeProb.Prob.FinitePartitionCoupling

/-! # Coupling errors for restricted selectors -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Restriction adds at most the second marginal's mass in a region outside
which nearby points lie on the same side of the restricting set. -/
theorem measure_restrictSelector_error_le
    {X J : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (outer boundary : Set X) (f : X → Option J) (r : ℝ)
    (hboundary : ∀ x y, y ∉ boundary → dist x y < r → (x ∈ outer ↔ y ∈ outer))
    (π : Measure (X × X)) (hmeas : MeasurableSet boundary) :
    π {p | restrictSelector outer f p.1 ≠ restrictSelector outer f p.2 ∨
      r ≤ dist p.1 p.2} ≤
      π {p | f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2} + π.snd boundary := by
  classical
  calc
    π {p | restrictSelector outer f p.1 ≠ restrictSelector outer f p.2 ∨
        r ≤ dist p.1 p.2} ≤
      π ({p | f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2} ∪ Prod.snd ⁻¹' boundary) := by
        apply measure_mono
        intro p hp
        by_contra h
        have hnot : ¬ (f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2) ∧ p.2 ∉ boundary := by
          simpa only [mem_union, mem_ofPred_eq, mem_preimage, not_or] using h
        have heq : f p.1 = f p.2 := not_ne_iff.mp (fun hn => hnot.1 (Or.inl hn))
        have hdist : dist p.1 p.2 < r := lt_of_not_ge (fun hn => hnot.1 (Or.inr hn))
        have hside := hboundary p.1 p.2 hnot.2 hdist
        have hre : restrictSelector outer f p.1 = restrictSelector outer f p.2 := by
          by_cases hy : p.2 ∈ outer
          · have hx : p.1 ∈ outer := hside.mpr hy
            simpa only [restrictSelector, ite_eq_left hx, ite_eq_left hy] using heq
          · have hx : p.1 ∉ outer := fun hx => hy (hside.mp hx)
            simp only [restrictSelector, ite_eq_right hx, ite_eq_right hy]
        exact hp.elim (fun hn => hn hre) (fun hn => (not_le_of_gt hdist) hn)
    _ ≤ π {p | f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2} +
        π (Prod.snd ⁻¹' boundary) := measure_union_le _ _
    _ = _ := by rw [Measure.snd_apply hmeas]

/-- The same estimate for the explicit finite partition coupling, whose
second marginal is the specified probability measure. -/
theorem finitePartitionCoupling_restrictSelector_error_le
    {X J ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [Fintype ι]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : ι → Set X) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise (fun i j => Disjoint (E i) (E j)))
    (outer boundary : Set X) (f : X → Option J) (r : ℝ)
    (hboundary : ∀ x y, y ∉ boundary → dist x y < r → (x ∈ outer ↔ y ∈ outer))
    (hmeas : MeasurableSet boundary) :
    finitePartitionCoupling μ ν E E
      {p | restrictSelector outer f p.1 ≠ restrictSelector outer f p.2 ∨
        r ≤ dist p.1 p.2} ≤
      finitePartitionCoupling μ ν E E
        {p | f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2} + ν boundary := by
  have h := measure_restrictSelector_error_le outer boundary f r hboundary
    (finitePartitionCoupling μ ν E E) hmeas
  rw [(finitePartitionCoupling_spec μ ν hE hE hd hd).2.2.1] at h
  exact h

end LatticeProb
