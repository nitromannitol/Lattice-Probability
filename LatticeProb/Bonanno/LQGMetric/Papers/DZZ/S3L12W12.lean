/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W11

/-!
# DZZ Lemma 3.12: in the harder case all four side rectangles are active (D93, P-5)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 1461 (the harder case
`𝖢_large ⊆ 𝕍°`): then none of the four side rectangles of the annulus of `HasCross` is clipped
(DEC-93 P-5, `interior_iff_active`, direction `→`), so the four crossings of `HasCross` all exist.

* `index_bounds_of_interior`: `𝖢_large ⊆ 𝕍°` gives `1 ≤ j, j + 2 ≤ 2^n` (and the same for `k`);
* **`active_of_interior`**.

Own elementary argument, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox PercClip

lemma index_bounds_of_interior {C : DyBox} (hint : C.largeBox ⊆ interior dzzV) :
    1 ≤ C.j ∧ C.j + 2 ≤ 2 ^ C.n ∧ 1 ≤ C.k ∧ C.k + 2 ≤ 2 ^ C.n := by
  have hV : C.largeBox ⊆ dzzV := hint.trans interior_subset
  have e := bx_side_mul (b := C) (N := C.n) le_rfl
  simp only [Nat.sub_self, pow_zero] at e
  have hs := C.side_pos'
  have hc : C.center ∈ C.largeBox := by
    simp only [DyBox.largeBox, mem_ofPred_eq, sub_self, abs_zero]; exact ⟨hs.le, hs.le⟩
  have mem : ∀ a b : ℝ, |a| ≤ C.side → |b| ≤ C.side →
      (⟨C.center.re + a, C.center.im + b⟩ : ℂ) ∈ dzzV := fun a b ha hb =>
    hV (by simp only [DyBox.largeBox, mem_ofPred_eq, add_sub_cancel_left]; exact ⟨ha, hb⟩)
  have hsabs : |C.side| ≤ C.side := (abs_of_pos hs).le
  have hsabs' : |-C.side| ≤ C.side := by rw [abs_neg]; exact hsabs
  have h0 : |(0 : ℝ)| ≤ C.side := by rw [abs_zero]; exact hs.le
  obtain ⟨a1, -, -, -⟩ := mem (-C.side) 0 hsabs' h0
  obtain ⟨-, a2, -, -⟩ := mem C.side 0 hsabs h0
  obtain ⟨-, -, a3, -⟩ := mem 0 (-C.side) h0 hsabs'
  obtain ⟨-, -, -, a4⟩ := mem 0 C.side h0 hsabs
  simp only [DyBox.center] at a1 a2 a3 a4
  have hp : (0 : ℝ) < 2 ^ C.n := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc; push Not at hc
    have : C.j = 0 := by omega
    rw [this] at a1; push_cast at a1; nlinarith
  · by_contra hc; push Not at hc
    have hj := C.hj
    have : C.j + 1 = 2 ^ C.n := by omega
    have : (C.j : ℝ) + 1 = 2 ^ C.n := by exact_mod_cast this
    nlinarith
  · by_contra hc; push Not at hc
    have : C.k = 0 := by omega
    rw [this] at a3; push_cast at a3; nlinarith
  · by_contra hc; push Not at hc
    have hk := C.hk
    have : C.k + 1 = 2 ^ C.n := by omega
    have : (C.k : ℝ) + 1 = 2 ^ C.n := by exact_mod_cast this
    nlinarith

/-- **In the harder case all four side rectangles are active.** -/
theorem active_of_interior {C : DyBox} (hint : C.largeBox ⊆ interior dzzV) {k h : ℕ}
    (hK : 2 ^ k = 2 * h) (d : PercDir) : 2 * (h : ℤ) - 2 < l37ext (C.n + k) (l37c C h) d := by
  obtain ⟨b1, b2, b3, b4⟩ := index_bounds_of_interior hint
  have e := l37_pow C hK
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0] at hK; exact absurd hK (by positivity)
    · exact h0
  have r1 : (1 : ℤ) ≤ C.j := by exact_mod_cast b1
  have r2 : (C.j : ℤ) + 2 ≤ 2 ^ C.n := by exact_mod_cast b2
  have r3 : (1 : ℤ) ≤ C.k := by exact_mod_cast b3
  have r4 : (C.k : ℤ) + 2 ≤ 2 ^ C.n := by exact_mod_cast b4
  have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
  cases d <;> simp only [l37ext, l37c] <;> (try rw [e]) <;> nlinarith

end DZZ
end LQGMetric
