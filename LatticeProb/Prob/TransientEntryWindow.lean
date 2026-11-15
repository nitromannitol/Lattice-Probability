import LatticeProb.Prob.GlobalEntryWindow

/-! # Finite entry windows for transient curves -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- A visit to a bounded set by a transient curve admits a finite window
containing the global entry and arbitrarily close visits after it. -/
theorem transient_globalOpenEntry_window_data
    (c : C(ℝ, ℂ)) (V : Set ℂ) (b : ℝ)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hV : Bornology.IsBounded V) (hb : c b ∈ V) :
    ∃ a : ℝ, a < b ∧ c a ∉ V ∧ (∀ t, c t ∈ V → a < t) ∧
      let e : ℝ := sInf {t ∈ Icc a b | c t ∈ V}
      globalOpenEntry (fun (_ : Unit) t => c t) V () = (e : EReal) ∧
        a ≤ e ∧ e ≤ b ∧
        (∀ u ∈ Icc a b, u < e → c u ∉ V) ∧
        (∀ δ : ℝ, 0 < δ →
          ∃ t ∈ Icc a b, c t ∈ V ∧ e ≤ t ∧ t < e + δ) ∧
        c e ∈ closure V := by
  obtain ⟨L, hL⟩ := MatedCRTHarmonic.GMS4c.exists_past_outside htr hV
  let a : ℝ := L - 1
  have haL : a < L := sub_lt_self L zero_lt_one
  have hhits : ∀ t, c t ∈ V → L ≤ t := by
    intro t ht
    exact le_of_not_gt (fun h => hL t h ht)
  have hastrict : ∀ t, c t ∈ V → a < t := by
    intro t ht
    exact haL.trans_le (hhits t ht)
  have haV : c a ∉ V := hL a haL
  refine ⟨a, hastrict b hb, haV, hastrict, ?_⟩
  exact globalOpenEntry_window_data c V a b
    (fun t ht => (hastrict t ht).le) haV hb c.continuous.continuousOn

end LatticeProb
