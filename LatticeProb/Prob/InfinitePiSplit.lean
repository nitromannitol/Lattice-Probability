/-
The head-tail decomposition of a product measure indexed by the natural numbers.

An i.i.d. sequence is one coordinate followed by an independent copy of itself.
`infinitePi_nat_head_tail` is that statement as an integral: an integral against
the product measure over `ℕ` is the integral over the first coordinate of the
integral over the rest.  Every first-step decomposition of a walk driven by
i.i.d. instructions is an instance of it.

The proof is the one the shift always gets: the first coordinate and the tail
are independent, because they read disjoint sets of coordinates, and the tail
has the law of the whole sequence, because shifting by one is an injective
reindexing that preserves the one-site laws.  So the joint law of the pair is
the product of the two laws, and Fubini finishes.
-/
import Mathlib.Probability.Independence.ZeroOne
import LatticeProb.Prob.ZeroOne

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- The sequence with head `u` and tail `ω`. -/
def consNat (u : X) (ω : ℕ → X) : ℕ → X := fun k => Nat.rec u (fun j _ => ω j) k

omit [MeasurableSpace X] in
@[simp] theorem consNat_zero (u : X) (ω : ℕ → X) : consNat u ω 0 = u := rfl

omit [MeasurableSpace X] in
@[simp] theorem consNat_succ (u : X) (ω : ℕ → X) (k : ℕ) : consNat u ω (k + 1) = ω k := rfl

/-- The tail of a sequence. -/
def tailNat (ω : ℕ → X) : ℕ → X := fun k => ω (k + 1)

omit [MeasurableSpace X] in
@[simp] theorem tailNat_apply (ω : ℕ → X) (k : ℕ) : tailNat ω k = ω (k + 1) := rfl

omit [MeasurableSpace X] in
theorem consNat_head_tail (ω : ℕ → X) : consNat (ω 0) (tailNat ω) = ω := by
  funext k
  cases k with
  | zero => rfl
  | succ k => rfl

theorem measurable_consNat : Measurable fun q : X × (ℕ → X) => consNat q.1 q.2 := by
  refine measurable_pi_lambda _ fun k => ?_
  cases k with
  | zero => exact measurable_fst
  | succ k => exact measurable_snd.eval

theorem measurable_tailNat : Measurable (tailNat (X := X)) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (k + 1)

omit [MeasurableSpace X] in
theorem tailNat_eq_coordShift : tailNat (X := X) = coordShift fun k : ℕ => k + 1 := rfl

/-- A map into sequence space is measurable for a sigma algebra as soon as each
of its coordinates is. -/
theorem comap_nat_le_of_coordinates {α : Type*} {m : MeasurableSpace α}
    (f : α → (ℕ → X))
    (h : ∀ j : ℕ, MeasurableSpace.comap (fun a => f a j) inferInstance ≤ m) :
    MeasurableSpace.comap f inferInstance ≤ m := by
  rw [show (inferInstance : MeasurableSpace (ℕ → X))
      = ⨆ j : ℕ, MeasurableSpace.comap (fun ω : ℕ → X => ω j) inferInstance from rfl,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact h j

variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The law of the sequence. -/
theorem measurePreserving_tailNat :
    MeasurePreserving (tailNat (X := X)) (Measure.infinitePi fun _ : ℕ => μ)
      (Measure.infinitePi fun _ : ℕ => μ) := by
  rw [tailNat_eq_coordShift]
  exact measurePreserving_coordShift _ (fun a b h => by omega) fun _ => rfl

/-- The first coordinate and the tail are independent. -/
theorem indepFun_head_tailNat :
    IndepFun (fun ω : ℕ → X => ω 0) (tailNat (X := X))
      (Measure.infinitePi fun _ : ℕ => μ) := by
  classical
  set P : Measure (ℕ → X) := Measure.infinitePi fun _ : ℕ => μ with hP
  set s : ℕ → MeasurableSpace (ℕ → X) := fun i =>
    MeasurableSpace.comap (fun ω : ℕ → X => ω i) inferInstance with hs
  have hcoord : iIndepFun (fun (i : ℕ) (ω : ℕ → X) => ω i) (Measure.infinitePi fun _ : ℕ => μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) fun _ => measurable_id
  have hind : iIndep s (Measure.infinitePi fun _ : ℕ => μ) :=
    (iIndepFun_iff_iIndep _ _ _).mp hcoord
  have hle : ∀ i : ℕ, s i ≤ (inferInstance : MeasurableSpace (ℕ → X)) := fun i =>
    (measurable_pi_apply i).comap_le
  have hsplit := ProbabilityTheory.indep_biSup_compl hle hind ({0} : Set ℕ)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le hsplit ?_ ?_
  · exact le_biSup s (show (0 : ℕ) ∈ ({0} : Set ℕ) from rfl)
  · refine comap_nat_le_of_coordinates _ fun k => ?_
    exact le_biSup s (show k + 1 ∈ ({0} : Set ℕ)ᶜ by simp)

/-- The joint law of the first coordinate and the tail is the product of the
one-coordinate law and the law of the whole sequence. -/
theorem map_head_tailNat :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun ω : ℕ → X => (ω 0, tailNat ω))
      = μ.prod (Measure.infinitePi fun _ : ℕ => μ) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
      measurable_tailNat.aemeasurable).mp (indepFun_head_tailNat μ),
    Measure.infinitePi_map_eval, (measurePreserving_tailNat μ).map_eq]

/-- Consing the head back onto the tail recovers the law of the sequence. -/
theorem map_consNat :
    (μ.prod (Measure.infinitePi fun _ : ℕ => μ)).map
        (fun q : X × (ℕ → X) => consNat q.1 q.2)
      = Measure.infinitePi fun _ : ℕ => μ := by
  have hmeas : Measurable fun ω : ℕ → X => (ω 0, tailNat ω) :=
    (measurable_pi_apply 0).prodMk measurable_tailNat
  rw [← map_head_tailNat μ, Measure.map_map measurable_consNat hmeas]
  have : ((fun q : X × (ℕ → X) => consNat q.1 q.2) ∘ fun ω : ℕ → X => (ω 0, tailNat ω))
      = id := by
    funext ω
    exact consNat_head_tail ω
  rw [this, Measure.map_id]

/-- **The head-tail decomposition.**  An integral against the product measure
over `ℕ` is the integral over the first coordinate of the integral over the
rest. -/
theorem integral_infinitePi_nat_head_tail {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (ℕ → X) → E)
    (hf : Integrable f (Measure.infinitePi fun _ : ℕ => μ)) :
    ∫ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => μ)
      = ∫ u, (∫ ω, f (consNat u ω) ∂(Measure.infinitePi fun _ : ℕ => μ)) ∂μ := by
  have hasm : AEStronglyMeasurable f
      ((μ.prod (Measure.infinitePi fun _ : ℕ => μ)).map fun q : X × (ℕ → X) =>
        consNat q.1 q.2) := by
    rw [map_consNat μ]
    exact hf.aestronglyMeasurable
  have hf' : Integrable f ((μ.prod (Measure.infinitePi fun _ : ℕ => μ)).map
      fun q : X × (ℕ → X) => consNat q.1 q.2) := by
    rw [map_consNat μ]; exact hf
  have hcons : Integrable (fun q : X × (ℕ → X) => f (consNat q.1 q.2))
      (μ.prod (Measure.infinitePi fun _ : ℕ => μ)) :=
    (integrable_map_measure hasm measurable_consNat.aemeasurable).mp hf'
  have h1 : ∫ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => μ)
      = ∫ q, f (consNat q.1 q.2) ∂(μ.prod (Measure.infinitePi fun _ : ℕ => μ)) := by
    conv_lhs => rw [← map_consNat μ]
    rw [integral_map measurable_consNat.aemeasurable hasm]
  rw [h1, integral_prod _ hcons]

/-- The head-tail decomposition for a lower integral. -/
theorem lintegral_infinitePi_nat_head_tail (f : (ℕ → X) → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => μ)
      = ∫⁻ u, (∫⁻ ω, f (consNat u ω) ∂(Measure.infinitePi fun _ : ℕ => μ)) ∂μ := by
  have h1 : ∫⁻ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => μ)
      = ∫⁻ q, f (consNat q.1 q.2) ∂(μ.prod (Measure.infinitePi fun _ : ℕ => μ)) := by
    conv_lhs => rw [← map_consNat μ]
    rw [lintegral_map hf measurable_consNat]
  have hm : AEMeasurable (fun q : X × (ℕ → X) => f (consNat q.1 q.2))
      (μ.prod (Measure.infinitePi fun _ : ℕ => μ)) :=
    (hf.comp measurable_consNat).aemeasurable
  rw [h1, MeasureTheory.lintegral_prod _ hm]

end LatticeProb

end
