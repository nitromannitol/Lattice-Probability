import LatticeProb.Probability.Percolation.VerticalJoinedExposure
import LatticeProb.Prob.FiniteCellFactorization

/-!
# Independence for finite edge exposures

Events determined by disjoint finite sets of graph edges factor under the
Bernoulli edge product law.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

private abbrev Edge := (LatticeModels.zdGraph 2).edgeSet
private abbrev Config := Edge → Prop
private abbrev edgeMeasure (p : unitInterval) : Measure Config :=
  Measure.infinitePi (fun _ : Edge => bernoulliMeasure True False p)

/-- Events determined by disjoint finite edge sets are independent under the
Bernoulli product law. -/
theorem edge_product_real_inter_of_disjoint (p : unitInterval)
    (S T : Finset Edge) (hST : Disjoint S T) (A B : Set Config)
    (hA : ∀ ω τ, (∀ e ∈ S, ω e = τ e) → (ω ∈ A ↔ τ ∈ A))
    (hB : ∀ ω τ, (∀ e ∈ T, ω e = τ e) → (ω ∈ B ↔ τ ∈ B)) :
    (edgeMeasure p).real (A ∩ B) = (edgeMeasure p).real A * (edgeMeasure p).real B := by
  classical
  let X : Edge → Config → Prop := fun e ω => ω e
  let F : Config → (S → Prop) := fun ω e => X e ω
  let H : Config → (T → Prop) := fun ω e => X e ω
  have hAe : A = F ⁻¹' (F '' A) :=
    LatticeProb.Prob.FiniteCellFactorization.event_eq_preimage_image X S A hA
  have hBe : B = H ⁻¹' (H '' B) :=
    LatticeProb.Prob.FiniteCellFactorization.event_eq_preimage_image X T B hB
  have hi : iIndepFun X (edgeMeasure p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have h : IndepFun F H (edgeMeasure p) :=
    hi.indepFun_finset S T hST (fun _ => measurable_pi_apply _)
  have hmul := h.measure_inter_preimage_eq_mul (F '' A) (H '' B)
    (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet
  rw [← hAe, ← hBe] at hmul
  simp only [measureReal_def, hmul, ENNReal.toReal_mul]

/-- The disjoint-support factorization supplies the independence premise for
each member of a finite exposure family. -/
theorem exposure_real_inter_of_disjoint {ι : Type*} (s : Finset ι)
    (D E : ι → Set Config) (S T : ι → Finset Edge)
    (hST : ∀ i ∈ s, Disjoint (S i) (T i))
    (hD : ∀ i ∈ s, ∀ ω τ, (∀ e ∈ S i, ω e = τ e) → (ω ∈ D i ↔ τ ∈ D i))
    (hE : ∀ i ∈ s, ∀ ω τ, (∀ e ∈ T i, ω e = τ e) → (ω ∈ E i ↔ τ ∈ E i)) :
    ∀ i ∈ s, (edgeMeasure half).real (D i ∩ E i) =
      (edgeMeasure half).real (D i) * (edgeMeasure half).real (E i) := by
  intro i hi
  exact edge_product_real_inter_of_disjoint half (S i) (T i) (hST i hi)
    (D i) (E i) (hD i hi) (hE i hi)

end EdgeCrossing
