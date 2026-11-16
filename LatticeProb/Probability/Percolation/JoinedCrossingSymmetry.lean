import LatticeProb.Probability.Percolation.EdgeCrossing
import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWLemma

/-!
# Symmetry of joined crossings

Edge-product probability transport for crossings connected to a third vertex set.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

/-- A crossing in a finite region joined to a target inside another finite region. -/
def joinedCrossingIn (S R : Finset (LatticeModels.Site 2))
    (A B T : Set (LatticeModels.Site 2)) :
    Set ((LatticeModels.zdGraph 2).edgeSet → Prop) :=
  extend (LatticeModels.zdGraph 2) ⁻¹' joinedCrossing S R A B T

/-- Joined crossings are independent of which end of the crossing is used as basepoint. -/
theorem joinedCrossing_swap (S R A B T : Set (LatticeModels.Site 2)) (hSR : S ⊆ R) :
    joinedCrossing S R A B T = joinedCrossing S R B A T := by
  suffices h : ∀ A B, joinedCrossing S R A B T ⊆ joinedCrossing S R B A T by
    exact Set.Subset.antisymm (h A B) (h B A)
  intro A B ω hω
  obtain ⟨a, ha, b, hb, t, ht, hab, hat⟩ := hω
  refine ⟨b, hb, a, ha, t, ht, ?_, ?_⟩
  · rwa [openConnIn_comm]
  · exact PlanarDuality.openConnIn_trans
      (openConnIn_mono hSR b a (by rwa [openConnIn_comm])) hat

/-- Edge-product and ambient probabilities agree for finite joined-crossing events. -/
theorem joinedCrossingIn_probability (p : unitInterval)
    (S R : Finset (LatticeModels.Site 2)) (A B T : Set (LatticeModels.Site 2)) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (joinedCrossingIn S R A B T) =
      (bondPercolation (LatticeModels.zdGraph 2) p).real (joinedCrossing S R A B T) := by
  have hm : MeasurableSet (joinedCrossingIn S R A B T) :=
    (measurableSet_joinedCrossing S R A B T).preimage (measurable_extend _)
  rw [← edge_product_law (LatticeModels.zdGraph 2) p, measureReal_def,
    Measure.map_apply (measurable_restrict _) hm, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [edge_support_ae (LatticeModels.zdGraph 2) p] with ω hω
  apply propext
  change (extend (LatticeModels.zdGraph 2) (restrict (LatticeModels.zdGraph 2) ω) ∈
    joinedCrossing S R A B T) ↔ ω ∈ joinedCrossing S R A B T
  rw [extend_restrict, hω]

/-- A lattice symmetry preserves joined-crossing probabilities, with the crossing ends swapped. -/
theorem joinedCrossingIn_probability_image_swap
    (φ : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2) (p : unitInterval)
    (S R : Finset (LatticeModels.Site 2)) (A B T : Set (LatticeModels.Site 2))
    (hSR : (S : Set (LatticeModels.Site 2)) ⊆ (R : Set (LatticeModels.Site 2))) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
      (joinedCrossingIn (S.image φ) (R.image φ) (φ '' B) (φ '' A) (φ '' T)) =
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (joinedCrossingIn S R A B T) := by
  rw [joinedCrossingIn_probability, joinedCrossingIn_probability]
  simp only [Finset.coe_image]
  rw [real_joinedCrossing_image, ← joinedCrossing_swap _ _ A B T hSR]

end EdgeCrossing
