import LatticeProb.Probability.Percolation.JoinedCrossingSymmetry
import LatticeProb.Prob.Harris

/-!
# Harris inequality for joined crossings

Finite families of edge-indexed joined crossings are positively associated under a
common Bernoulli product law.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

/-- A joined crossing in finite regions is measurable in the edge coordinates. -/
theorem measurableSet_joinedCrossingIn (S R : Finset (LatticeModels.Site 2))
    (A B T : Set (LatticeModels.Site 2)) : MeasurableSet (joinedCrossingIn S R A B T) :=
  (measurableSet_joinedCrossing S R A B T).preimage (measurable_extend _)

/-- Opening additional edges preserves a joined crossing. -/
theorem isUpperSet_joinedCrossingIn (S R : Finset (LatticeModels.Site 2))
    (A B T : Set (LatticeModels.Site 2)) : IsUpperSet (joinedCrossingIn S R A B T) := by
  intro η ξ hle hη
  apply isUpperSet_joinedCrossing S R A B T _ hη
  intro e he
  obtain ⟨h, hηe⟩ := he
  exact ⟨h, hle ⟨e, h⟩ hηe⟩

/-- The product of the probabilities of finitely many joined crossings is bounded by
    the probability of their intersection. -/
theorem joinedCrossingIn_prod_le (p : unitInterval) {ι : Type*} (s : Finset ι)
    (S R : ι → Finset (LatticeModels.Site 2))
    (A B T : ι → Set (LatticeModels.Site 2)) :
    (∏ i ∈ s, (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (joinedCrossingIn (S i) (R i) (A i) (B i) (T i))) ≤
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
        (⋂ i ∈ s, joinedCrossingIn (S i) (R i) (A i) (B i) (T i)) := by
  classical
  let : LinearOrder Prop := Prop.linearOrder
  let μ := Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
    bernoulliMeasure True False p)
  let E := fun i => joinedCrossingIn (S i) (R i) (A i) (B i) (T i)
  change (∏ i ∈ s, μ.real (E i)) ≤ μ.real (⋂ i ∈ s, E i)
  induction s using Finset.induction_on with
  | empty => simp [μ]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.set_biInter_insert]
    calc μ.real (E i) * ∏ j ∈ s, μ.real (E j)
        ≤ μ.real (E i) * μ.real (⋂ j ∈ s, E j) :=
          mul_le_mul_of_nonneg_left ih measureReal_nonneg
      _ ≤ μ.real (E i ∩ ⋂ j ∈ s, E j) :=
        LatticeProb.infinitePi_harris _ (isUpperSet_joinedCrossingIn _ _ _ _ _)
          (isUpperSet_iInter₂ fun j _ => isUpperSet_joinedCrossingIn _ _ _ _ _)
          (measurableSet_joinedCrossingIn _ _ _ _ _)
          (s.measurableSet_biInter fun j _ => measurableSet_joinedCrossingIn _ _ _ _ _)

end EdgeCrossing
