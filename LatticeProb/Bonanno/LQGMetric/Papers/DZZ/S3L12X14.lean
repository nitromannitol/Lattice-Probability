/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X14 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X13

/-!
# DZZ Lemma 3.12: the coarse ring exists (D93 §2, packet P-6a) — `CoarseRingOfCross`

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, the harder case
`𝖢_large ⊆ 𝕍°` (l. 1461–1477), and Remark 3.15 (l. 1360–1363), in the ring form of DEC-93 §2
("producing each parent exactly once"): the four long-way crossings of `HasCross` (all four
side rectangles are active, `active_of_interior`) are cut at the outer-corner lines
(`side_pkg`), meet at the corners (`side_meet'`), and are walked around starting from the
corner of the home region (the parent box of `𝖢`, which lies in no parent cell); this gives the
coarse ring (`coarseRing_of_sideW`).

* `sideW_fwd`, `sideW_rev`; **`coarseRingOfCross_holds`**; **`dzz_lemma312_P6a`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma sideW_fwd {C : DyBox} {k h d : ℕ} (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    (hint : C.largeBox ⊆ interior dzzV) {e : PercDir} {G : Set (ℤ × ℤ)}
    (hG : ∀ z ∈ G, ∀ bt ∈ boxCollBdry (siteBox (C.n + k) (l37c C h) z) d, m bt < δ ^ 2)
    {A M B : List (ℤ × ℤ)} {cl ch mi mo : ℤ × ℤ} (hc : (A ++ M ++ B).IsChain PercAdj4)
    (hR : ∀ z ∈ A ++ M ++ B, z ∈ annRect ((h : ℤ) + 2) (2 * (h : ℤ) - 2) e)
    (hM : ∀ z ∈ M, z ∈ G ∧ ∀ P, IsParent m δ C P →
      ¬ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox)
    (hA : ∀ z ∈ A, (∃ P, IsParent m δ C P ∧
      (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
      ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
        (siteBox (C.n + k) (l37c C h) cl).closedBox ⊆ P.closedBox))
    (hB : ∀ z ∈ B, (∃ P, IsParent m δ C P ∧
      (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
      ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
        (siteBox (C.n + k) (l37c C h) ch).closedBox ⊆ P.closedBox))
    (hE : (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) cl).closedBox ⊆ P.closedBox) →
      (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) ch).closedBox ⊆ P.closedBox) →
      M = [])
    (hmi : mi ∈ A ∨ (A = [] ∧ mi ∈ M)) (hmo : mo ∈ B ∨ (B = [] ∧ mo ∈ M)) :
    SideW m δ C k h d A M B cl ch mi mo :=
  ⟨hc, hmi, hmo, fun z hz => ⟨inGrid_of_interior hK hh hint (hR z hz).1, (hR z hz).1, e,
    (hR z hz).2⟩, fun z hz => ⟨hG z (hM z hz).1, (hM z hz).2⟩, hA, hB, hE⟩

lemma sideW_rev {C : DyBox} {k h d : ℕ} (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    (hint : C.largeBox ⊆ interior dzzV) {e : PercDir} {G : Set (ℤ × ℤ)}
    (hG : ∀ z ∈ G, ∀ bt ∈ boxCollBdry (siteBox (C.n + k) (l37c C h) z) d, m bt < δ ^ 2)
    {A M B : List (ℤ × ℤ)} {cl ch mi mo : ℤ × ℤ} (hc : (A ++ M ++ B).IsChain PercAdj4)
    (hR : ∀ z ∈ A ++ M ++ B, z ∈ annRect ((h : ℤ) + 2) (2 * (h : ℤ) - 2) e)
    (hM : ∀ z ∈ M, z ∈ G ∧ ∀ P, IsParent m δ C P →
      ¬ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox)
    (hA : ∀ z ∈ A, (∃ P, IsParent m δ C P ∧
      (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
      ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
        (siteBox (C.n + k) (l37c C h) cl).closedBox ⊆ P.closedBox))
    (hB : ∀ z ∈ B, (∃ P, IsParent m δ C P ∧
      (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
      ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
        (siteBox (C.n + k) (l37c C h) ch).closedBox ⊆ P.closedBox))
    (hE : (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) cl).closedBox ⊆ P.closedBox) →
      (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) ch).closedBox ⊆ P.closedBox) →
      M = [])
    (hmi : mi ∈ B ∨ (B = [] ∧ mi ∈ M)) (hmo : mo ∈ A ∨ (A = [] ∧ mo ∈ M)) :
    SideW m δ C k h d B.reverse M.reverse A.reverse ch cl mi mo := by
  have er : B.reverse ++ M.reverse ++ A.reverse = (A ++ M ++ B).reverse := by simp
  have hmem : ∀ z, z ∈ B.reverse ++ M.reverse ++ A.reverse → z ∈ A ++ M ++ B := by
    intro z hz; rw [er, List.mem_reverse] at hz; exact hz
  refine ⟨by rw [er]; exact isChain_reverse_symm (fun x y h => percAdj4_symm h) hc, ?_, ?_,
    fun z hz => ⟨inGrid_of_interior hK hh hint (hR z (hmem z hz)).1, (hR z (hmem z hz)).1, e,
      (hR z (hmem z hz)).2⟩, fun z hz => ?_, fun z hz => hB z (List.mem_reverse.1 hz),
    fun z hz => hA z (List.mem_reverse.1 hz), fun h1 h2 => by rw [hE h2 h1]; rfl⟩
  · rcases hmi with h | ⟨h0, h⟩
    · exact Or.inl (List.mem_reverse.2 h)
    · exact Or.inr ⟨by rw [h0]; rfl, List.mem_reverse.2 h⟩
  · rcases hmo with h | ⟨h0, h⟩
    · exact Or.inl (List.mem_reverse.2 h)
    · exact Or.inr ⟨by rw [h0]; rfl, List.mem_reverse.2 h⟩
  · have := hM z (List.mem_reverse.1 hz); exact ⟨hG z this.1, this.2⟩

end DZZ
end LQGMetric
