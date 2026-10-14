/-
Finite-cell event factorization for independent random variables with dependent alphabets.
An event determined by a finite set of cells is a measurable inverse image of a set of
finite tuples. Independence of disjoint tuples separates that event from prescribed
values on a second finite set of cells.
-/
import Mathlib.Probability.Independence.Basic

namespace LatticeProb.Prob.FiniteCellFactorization

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

noncomputable section

variable {Ω K : Type*} [MeasurableSpace Ω] {A : K → Type*}
variable [∀ q, MeasurableSpace (A q)] [∀ q, MeasurableSingletonClass (A q)]
variable [∀ q, Countable (A q)]

omit [MeasurableSpace Ω] [∀ q, MeasurableSpace (A q)] [∀ q, MeasurableSingletonClass (A q)]
  [∀ q, Countable (A q)] in
/-- An event invariant under agreement on `S` is the inverse image of its finite-tuple
image. This uses no choice of values outside `S`. -/
theorem event_eq_preimage_image (X : ∀ q, Ω → A q) (S : Finset K) (B : Set Ω)
    (hB : ∀ ω τ, (∀ q ∈ S, X q ω = X q τ) → (ω ∈ B ↔ τ ∈ B)) :
    B = (fun ω (q : S) => X q ω) ⁻¹' ((fun ω (q : S) => X q ω) '' B) := by
  ext ω
  constructor
  · intro hω
    exact ⟨ω, hω, rfl⟩
  · rintro ⟨τ, hτ, he⟩
    apply (hB τ ω ?_).mp hτ
    intro q hq
    exact congrFun he ⟨q, hq⟩

/-- An event determined by finitely many measurable countable-valued cells is measurable. -/
theorem measurableSet_event (X : ∀ q, Ω → A q) (hX : ∀ q, Measurable (X q))
    (S : Finset K) (B : Set Ω)
    (hB : ∀ ω τ, (∀ q ∈ S, X q ω = X q τ) → (ω ∈ B ↔ τ ∈ B)) :
    MeasurableSet B := by
  rw [event_eq_preimage_image X S B hB]
  exact (Set.to_countable _).measurableSet.preimage
    (measurable_pi_lambda _ (fun q => hX q))

/-- **Finite-cell factorization.** A finite-cell event and prescribed values on disjoint
cells factor into the event mass and the product of the actual one-cell masses. -/
theorem measure_event_inter_values (P : Measure Ω) (X : ∀ q, Ω → A q)
    (hX : ∀ q, Measurable (X q)) (hind : iIndepFun X P)
    (S T : Finset K) (hST : Disjoint S T) (B : Set Ω)
    (hB : ∀ ω τ, (∀ q ∈ S, X q ω = X q τ) → (ω ∈ B ↔ τ ∈ B))
    (a : ∀ q, A q) :
    P (B ∩ {ω | ∀ q ∈ T, X q ω = a q}) =
      P B * ∏ q ∈ T, P {ω | X q ω = a q} := by
  let F : Ω → ((q : S) → A q) := fun ω q => X q ω
  let H : Ω → ((q : T) → A q) := fun ω q => X q ω
  have heB : B = F ⁻¹' (F '' B) := event_eq_preimage_image X S B hB
  have heT : {ω | ∀ q ∈ T, X q ω = a q} = H ⁻¹' {fun q : T => a q} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext q
      exact h q q.property
    · intro h q hq
      exact congrFun h ⟨q, hq⟩
  have hi : IndepFun F H P := iIndepFun.indepFun_finset S T hST hind hX
  have hmul := hi.measure_inter_preimage_eq_mul (F '' B) {fun q : T => a q}
    (Set.to_countable _).measurableSet (measurableSet_singleton _)
  rw [← heB, ← heT] at hmul
  rw [hmul]
  congr 1
  have he : {ω | ∀ q ∈ T, X q ω = a q} = ⋂ q ∈ T, X q ⁻¹' {a q} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  rw [he]
  exact hind.measure_inter_preimage_eq_mul T (fun q _ => measurableSet_singleton (a q))

end

end LatticeProb.Prob.FiniteCellFactorization
