import LatticeProb.Prob.CellConfigSeparatedCountable
import LatticeProb.Prob.CellConfigStableDistance

/-! # Countability of stable cell configuration invariants -/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace ReflectedGMS.GMS

/-- On a second-countable subspace, an invariant of admissible maps takes
countably many values on configurations with restrictions stable on a common interval. -/
theorem countable_image_of_stable_restrict {α : Type*} (T : Set GMSSpace)
    [SecondCountableTopology T] (S : Set T) (F : T → α) {a b s : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hstable : ∀ x ∈ S, ∀ r ∈ Ioo a b,
      x.1.1.restrict (Metric.ball 0 r) = x.1.1.restrict (Metric.ball 0 s))
    (hinv : ∀ x ∈ S, ∀ y ∈ S, ∀ f : Plane ≃ₜ Plane,
      CellConfig.AdmissibleAt x.1.1 y.1.1 s f → F x = F y) :
    (F '' S).Countable := by
  classical
  let rep : {z // z ∈ F '' S} → T := fun z => Classical.choose z.2
  have hrep (z : {z // z ∈ F '' S}) : rep z ∈ S ∧ F (rep z) = z.1 :=
    Classical.choose_spec z.2
  have hsep : ∀ x ∈ range rep, ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ y ∈ range rep, x ≠ y → c ≤ CellConfig.dCC x.1.1 y.1.1 := by
    rintro x ⟨u, rfl⟩
    refine ⟨ENNReal.ofReal ((b - a) * Real.exp (-b)), ?_, ?_⟩
    · exact ENNReal.ofReal_pos.mpr (mul_pos (sub_pos.mpr hab) (Real.exp_pos _))
    · rintro y ⟨v, rfl⟩ hne
      apply ofReal_interval_mul_exp_le_dCC_of_stable_restrict _ _ ha
        (hstable (rep u) (hrep u).1) (hstable (rep v) (hrep v).1)
      intro f hf
      have huv : u = v := Subtype.ext ((hrep u).2.symm.trans
        ((hinv (rep u) (hrep u).1 (rep v) (hrep v).1 f hf).trans (hrep v).2))
      exact hne (congrArg rep huv)
  have hc : (range rep).Countable := countable_of_locally_dCC_separated T (range rep) hsep
  have himage : F '' range rep = F '' S := by
    ext z
    constructor
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨rep u, (hrep u).1, rfl⟩
    · intro hz
      exact ⟨rep ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, (hrep ⟨z, hz⟩).2⟩
  rw [← himage]
  exact hc.image F

end ReflectedGMS.GMS
