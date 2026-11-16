import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Analysis.LocalMinCountable

/-! # Repeated-side contour links -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace MatedCRTHarmonic.RouteM

/-- Two distinct direct chords of one contour sharing an endpoint put that
endpoint at a local minimum. -/
theorem isLocalMin_of_two_directRel {X : ℝ → ℝ} {a b c : ℝ}
    (hab : directRel X a b ∨ directRel X b a)
    (hbc : directRel X b c ∨ directRel X c b) (hac : a ≠ c) :
    IsLocalMin X b := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · filter_upwards [Ioo_mem_nhds hab.1 hbc.1] with t ht
    rcases lt_trichotomy t b with h | h | h
    · exact (hab.2.1 ▸ (hab.2.2 t ⟨ht.1, h⟩)).le
    · simp [h]
    · exact (hbc.2.2 t ⟨h, ht.2⟩).le
  · have hlt : a < c ∨ c < a := lt_or_gt_of_ne hac
    rcases hlt with h | h
    · have hcontra := hab.2.2 c ⟨h, hbc.1⟩
      linarith [hab.2.1, hbc.2.1]
    · have hcontra := hbc.2.2 a ⟨h, hab.1⟩
      linarith [hab.2.1, hbc.2.1]
  · have hlt : a < c ∨ c < a := lt_or_gt_of_ne hac
    rcases hlt with h | h
    · have hcontra := hbc.2.2 a ⟨hab.1, h⟩
      linarith [hab.2.1, hbc.2.1]
    · have hcontra := hab.2.2 c ⟨hbc.1, h⟩
      linarith [hab.2.1, hbc.2.1]
  · filter_upwards [Ioo_mem_nhds hbc.1 hab.1] with t ht
    rcases lt_trichotomy t b with h | h | h
    · exact (hbc.2.1 ▸ (hbc.2.2 t ⟨ht.1, h⟩)).le
    · simp [h]
    · exact (hab.2.2 t ⟨h, ht.2⟩).le

/-- The images of repeated-side chain turns form a countable set. -/
theorem Peanosphere.countable_repeated_side_turns
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) :
    {z | ∃ a b c, a ≠ c ∧
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b))) ∧ η b = z}.Countable := by
  have hL : {s | IsLocalMin (lCoord ω) s}.Countable := by
    apply LatticeProb.countable_localMin_of_distinct_values
    change ∀ a b, a ≠ b → IsLocalMin (fun t => (ω t).1) a →
      IsLocalMin (fun t => (ω t).1) b → (ω a).1 ≠ (ω b).1
    simpa [MatedCRT.lrCoord] using P.locMinDistinct (0 : Fin 2)
  have hR : {s | IsLocalMin (rCoord ω) s}.Countable := by
    apply LatticeProb.countable_localMin_of_distinct_values
    change ∀ a b, a ≠ b → IsLocalMin (fun t => (ω t).2) a →
      IsLocalMin (fun t => (ω t).2) b → (ω a).2 ≠ (ω b).2
    simpa [MatedCRT.lrCoord] using P.locMinDistinct (1 : Fin 2)
  apply ((hL.union hR).image η).mono
  rintro z ⟨a, b, c, hac, h, heq⟩
  refine ⟨b, ?_, heq⟩
  rcases h with h | h
  · exact Or.inl (isLocalMin_of_two_directRel h.1 h.2 hac)
  · exact Or.inr (isLocalMin_of_two_directRel h.1 h.2 hac)

end MatedCRTHarmonic.RouteM
