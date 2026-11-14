/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Fatou at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Persistent
import Mathlib.Order.LiminfLimsup

 









set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneA3_fatou_eventual_visit_sum
    {ι : Type*} (s : Finset ι) (visit : ℕ → ι → Prop)
    (A : ι → ℝ≥0∞)
    (persistent : ι → Prop)
    (hpersistent : ∀ i ∈ s, persistent i →
      ∃ N : ℕ, ∀ j, N ≤ j → visit j i) :
    (∑ i ∈ s, if persistent i then A i else 0) ≤
      liminf (fun j : ℕ => ∑ i ∈ s, if visit j i then A i else 0) atTop := by
  classical
  have hev : ∀ᶠ j : ℕ in atTop,
      (∑ i ∈ s, if persistent i then A i else 0) ≤
        ∑ i ∈ s, if visit j i then A i else 0 := by
    have hall : ∃ N : ℕ, ∀ j, N ≤ j →
        ∀ i ∈ s, persistent i → visit j i := by
      let t := s.filter persistent
      have ht : ∀ i ∈ t, ∃ N : ℕ, ∀ j, N ≤ j → visit j i := by
        intro i hi
        exact hpersistent i (Finset.mem_filter.mp hi).1
          (Finset.mem_filter.mp hi).2
      obtain ⟨N, hN⟩ := laneA3_finite_persistent_visits t visit ht
      refine ⟨N, ?_⟩
      intro j hj i hi hpi
      exact hN j hj i (Finset.mem_filter.mpr ⟨hi, hpi⟩)
    obtain ⟨N, hN⟩ := hall
    filter_upwards [eventually_ge_atTop N] with j hj
    apply Finset.sum_le_sum
    intro i hi
    by_cases hpi : persistent i
    · simp only [if_pos hpi, if_pos (hN j hj i hi hpi)]
      exact le_refl _
    · simp only [if_neg hpi]
      exact bot_le
  exact le_liminf_of_le (h := hev)

 



theorem laneA3_eventual_visit_mass_of_near_cost
    {ι : Type*} (s : Finset ι) (visit : ℕ → ι → Prop)
    (A : ι → ℝ≥0∞) (persistent : ι → Prop)
    (hpersistent : ∀ i ∈ s, persistent i →
      ∃ N : ℕ, ∀ j, N ≤ j → visit j i)
    (cost : ℕ → ℝ≥0∞) (limit : ℝ≥0∞)
    (hpay : ∀ j, (∑ i ∈ s, if visit j i then A i else 0) ≤ cost j)
    (hcost : Tendsto cost atTop (nhds limit)) :
    (∑ i ∈ s, if persistent i then A i else 0) ≤ limit := by
  calc
    _ ≤ liminf (fun j : ℕ => ∑ i ∈ s, if visit j i then A i else 0)
        atTop := laneA3_fatou_eventual_visit_sum s visit A persistent hpersistent
    _ ≤ liminf cost atTop :=
      liminf_le_liminf (Filter.Eventually.of_forall hpay)
    _ = limit := hcost.liminf_eq

end SupercriticalLQGUniqueness.B2.DG20Conc
