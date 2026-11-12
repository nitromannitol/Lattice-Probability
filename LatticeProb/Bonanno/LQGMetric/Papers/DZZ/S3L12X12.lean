/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X11

/-!
# DZZ Lemma 3.12: one side of the coarse ring (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1461–1477),
ring form of DEC-93 §2: the long-way crossing of one side rectangle is cut at the outer-corner
line of its long coordinate (`side_slab_cut`), straight through each half whose region lies in
a parent cell; the three parts have the zone properties consumed by `coarseRing_of_sides`.

* **`side_pkg`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox Classical

variable {m : DyBox → ℝ} {δ : ℝ}

/-- **One side of the coarse ring.** `cl`, `ch` are sites of the regions of the low and the high
half of side `e` (split at `s` in the long coordinate). -/
theorem side_pkg {C : DyBox} {k h : ℕ} (hC : 1 ≤ C.n) (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    (hint : C.largeBox ⊆ interior dzzV) (e : PercDir) {s : ℤ} (hs₁ : -(2 * (h : ℤ) - 2) ≤ s)
    (hs₂ : s ≤ 2 * (h : ℤ) - 2 + 1) {G : Set (ℤ × ℤ)}
    (hX : PercClipCross ((h : ℤ) + 2) (2 * (h : ℤ) - 2) e (-(2 * (h : ℤ) - 2)) (2 * (h : ℤ) - 2) G)
    {cl ch : ℤ × ℤ} (hcl : annBox (2 * (h : ℤ) - 2) cl) (hch : annBox (2 * (h : ℤ) - 2) ch)
    (hregL : ∀ z, z ∈ annRect ((h : ℤ) + 2) (2 * (h : ℤ) - 2) e → annLong e z < s →
      farB C.j h z.1 = farB C.j h cl.1 ∧ farB C.k h z.2 = farB C.k h cl.2)
    (hregH : ∀ z, z ∈ annRect ((h : ℤ) + 2) (2 * (h : ℤ) - 2) e → s ≤ annLong e z →
      farB C.j h z.1 = farB C.j h ch.1 ∧ farB C.k h z.2 = farB C.k h ch.2) :
    ∃ A M B : List (ℤ × ℤ), (A ++ M ++ B) ≠ [] ∧ (A ++ M ++ B).IsChain PercAdj4 ∧
      (∀ a ∈ (A ++ M ++ B).head?, annLong e a = -(2 * (h : ℤ) - 2)) ∧
      (∀ b ∈ (A ++ M ++ B).getLast?, annLong e b = 2 * (h : ℤ) - 2) ∧
      (∀ z ∈ A ++ M ++ B, z ∈ annRect ((h : ℤ) + 2) (2 * (h : ℤ) - 2) e) ∧
      (∀ z ∈ M, z ∈ G ∧ ∀ P, IsParent m δ C P →
        ¬ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
      (∀ z ∈ A, (∃ P, IsParent m δ C P ∧
        (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
        ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
          (siteBox (C.n + k) (l37c C h) cl).closedBox ⊆ P.closedBox)) ∧
      (∀ z ∈ B, (∃ P, IsParent m δ C P ∧
        (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
        ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
          (siteBox (C.n + k) (l37c C h) ch).closedBox ⊆ P.closedBox)) ∧
      ((∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) cl).closedBox ⊆ P.closedBox) →
        (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) ch).closedBox ⊆ P.closedBox) →
        M = []) ∧
      (∀ z ∈ A ++ M ++ B, annLong e z < s → z ∈ A ∨ (A = [] ∧ z ∈ M)) ∧
      (∀ z ∈ A ++ M ++ B, s ≤ annLong e z → z ∈ B ∨ (B = [] ∧ z ∈ M)) := by
  set N : ℤ := 2 * (h : ℤ) - 2
  set sb := siteBox (C.n + k) (l37c C h)
  set act : ℤ × ℤ → Prop := fun z => ∃ P, IsParent m δ C P ∧ (sb z).closedBox ⊆ P.closedBox
  set t₁ : ℤ := if act cl then s else -N
  set t₂ : ℤ := if act ch then s else N + 1
  have ht₁ : -N ≤ t₁ := by simp only [t₁]; split_ifs <;> omega
  have ht₂ : t₂ ≤ N + 1 := by simp only [t₂]; split_ifs <;> omega
  obtain ⟨A, M, B, hne, hc, h0, hW, hR, hA, hM, hB⟩ :=
    side_slab_cut (by positivity) e ht₁ ht₂ hX
  have hgrid : ∀ z, z ∈ annRect ((h : ℤ) + 2) N e → InGrid (C.n + k) (l37c C h) z :=
    fun z hz => inGrid_of_interior hK hh hint hz.1
  have hreg : ∀ z c, z ∈ annRect ((h : ℤ) + 2) N e → annBox N c →
      farB C.j h z.1 = farB C.j h c.1 ∧ farB C.k h z.2 = farB C.k h c.2 →
      ∀ P, IsParent m δ C P → ((sb z).closedBox ⊆ P.closedBox ↔ (sb c).closedBox ⊆ P.closedBox) :=
    fun z c hz hc hzc P hP => sub_parent_iff_of_region hC hK hh hP (hgrid z hz) hz.1
      (inGrid_of_interior hK hh hint hc) hc hzc.1 hzc.2
  refine ⟨A, M, B, hne, hc, h0, hW, hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hzR := hR z (by simp [hz])
    obtain ⟨hzG, h1, h2⟩ := hM z hz
    refine ⟨hzG, fun P hP hsub => ?_⟩
    by_cases hzs : annLong e z < s
    · have hcl' := (hreg z cl hzR hcl (hregL z hzR hzs) P hP).1 hsub
      have : t₁ = s := by simp only [t₁]; rw [if_pos ⟨P, hP, hcl'⟩]
      omega
    · push Not at hzs
      have hch' := (hreg z ch hzR hch (hregH z hzR hzs) P hP).1 hsub
      have : t₂ = s := by simp only [t₂]; rw [if_pos ⟨P, hP, hch'⟩]
      omega
  · intro z hz
    have hzR := hR z (by simp [hz])
    have h1 := hA z hz
    have hact : act cl := by
      by_contra hn
      have : t₁ = -N := by simp only [t₁]; rw [if_neg hn]
      have := hzR.1; obtain ⟨a1, a2, a3, a4⟩ := this
      cases e <;> simp only [annLong] at h1 <;> omega
    have hzs : annLong e z < s := by
      have : t₁ = s := by simp only [t₁]; rw [if_pos hact]
      omega
    obtain ⟨P, hP, hPc⟩ := hact
    exact ⟨⟨P, hP, (hreg z cl hzR hcl (hregL z hzR hzs) P hP).2 hPc⟩,
      fun P hP => hreg z cl hzR hcl (hregL z hzR hzs) P hP⟩
  · intro z hz
    have hzR := hR z (by simp [hz])
    have h1 := hB z hz
    have hact : act ch := by
      by_contra hn
      have : t₂ = N + 1 := by simp only [t₂]; rw [if_neg hn]
      have := hzR.1; obtain ⟨a1, a2, a3, a4⟩ := this
      cases e <;> simp only [annLong] at h1 <;> omega
    have hzs : s ≤ annLong e z := by
      have : t₂ = s := by simp only [t₂]; rw [if_pos hact]
      omega
    obtain ⟨P, hP, hPc⟩ := hact
    exact ⟨⟨P, hP, (hreg z ch hzR hch (hregH z hzR hzs) P hP).2 hPc⟩,
      fun P hP => hreg z ch hzR hch (hregH z hzR hzs) P hP⟩
  · intro hl hh'
    have e1 : t₁ = s := by simp only [t₁]; rw [if_pos hl]
    have e2 : t₂ = s := by simp only [t₂]; rw [if_pos hh']
    exact List.eq_nil_iff_forall_not_mem.2 fun z hz => by
      have := hM z hz; omega
  · intro z hz hzs
    simp only [List.mem_append] at hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl hz
    · by_cases hl : act cl
      · have e1 : t₁ = s := by simp only [t₁]; rw [if_pos hl]
        have := hM z hz; omega
      · right
        refine ⟨List.eq_nil_iff_forall_not_mem.2 fun y hy => ?_, hz⟩
        have e1 : t₁ = -N := by simp only [t₁]; rw [if_neg hl]
        have hyR := hR y (by simp [hy])
        have := hA y hy; obtain ⟨a1, a2, a3, a4⟩ := hyR.1
        cases e <;> simp only [annLong] at this <;> omega
    · have := hB z hz
      have : s ≤ t₂ := by simp only [t₂]; split_ifs <;> omega
      omega
  · intro z hz hzs
    simp only [List.mem_append] at hz
    rcases hz with (hz | hz) | hz
    · have := hA z hz
      have : t₁ ≤ s := by simp only [t₁]; split_ifs <;> omega
      omega
    · by_cases hl : act ch
      · have e2 : t₂ = s := by simp only [t₂]; rw [if_pos hl]
        have := hM z hz; omega
      · right
        refine ⟨List.eq_nil_iff_forall_not_mem.2 fun y hy => ?_, hz⟩
        have e2 : t₂ = N + 1 := by simp only [t₂]; rw [if_neg hl]
        have hyR := hR y (by simp [hy])
        have := hB y hy; obtain ⟨a1, a2, a3, a4⟩ := hyR.1
        cases e <;> simp only [annLong] at this <;> omega
    · exact Or.inl hz

end DZZ
end LQGMetric
