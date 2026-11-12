/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7CountPsi at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Count

/-!
# DZZ Lemma 3.7: `Ψ_{B',δ'} ≤ |𝓑_∂(B', t/ε)|` when all boundary sub-boxes are light (P2-DZZ3E)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of Lemma 3.7, l. 990–996:
"`{M_s(B) ≤ δ²} ∩ 𝓔_{δ,α} ∩ 𝓔_{B'_i,open} ⊆ {Ψ_{B'_i,δ'} ≤ λ}`", using `4/t ≤ λ` (l. 999).
DZZ do not spell out the deterministic step; own elementary proof (DEVIATIONS): if every box of
`𝓑_∂(B', 2^{-k'})` has mass `< δ'²`, then no cell touching `∂B'` is finer than these boxes (its
ancestor at their level would be split), and choosing for each such cell a descendant of that level
touching `∂B'` is injective (cells form an antichain), so `Ψ_{B',δ'} ≤ |𝓑_∂(B', 2^{-k'})|`.

* `anc_self`, `anc_anc`, `closedBox_sub_anc`, `exists_desc`: dyadic ancestry geometry.
* `psiLe_of_bdry`: the deterministic bound `Ψ_{B',δ} ≤ 8 (2^{k'} + 2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

lemma anc_self {b : DyBox} {i : ℕ} (h : b.n ≤ i) : b.anc i = b := by
  ext <;> simp [DyBox.anc, Nat.sub_eq_zero_of_le h, h]

lemma anc_anc (b : DyBox) {i i' : ℕ} (h : i' ≤ i) : (b.anc i).anc i' = b.anc i' := by
  rcases le_total b.n i with hb | hb
  · rw [anc_self hb]
  · have e : 2 ^ (b.n - i) * 2 ^ (min i b.n - i') = 2 ^ (b.n - i') := by
      rw [← pow_add, min_eq_left hb]; congr 1; omega
    ext
    · simp only [DyBox.anc]; omega
    · simp only [DyBox.anc, Nat.div_div_eq_div_mul, e]
    · simp only [DyBox.anc, Nat.div_div_eq_div_mul, e]

lemma coord_anc {j D : ℕ} (hD : 0 < D) {s x : ℝ} (hs : 0 < s) (h1 : (j : ℝ) * s ≤ x)
    (h2 : x ≤ (j + 1) * s) :
    ((j / D : ℕ) : ℝ) * (D * s) ≤ x ∧ x ≤ ((j / D : ℕ) + 1) * (D * s) := by
  have a1 : j / D * D ≤ j := Nat.div_mul_le_self j D
  have a2 : j + 1 ≤ (j / D + 1) * D := by
    have := Nat.div_add_mod j D; have := Nat.mod_lt j hD; nlinarith
  constructor
  · refine le_trans ?_ h1
    rw [← mul_assoc]; gcongr; exact_mod_cast a1
  · refine h2.trans ?_
    rw [← mul_assoc]; gcongr; exact_mod_cast a2

lemma side_anc {b : DyBox} {i : ℕ} (h : i ≤ b.n) :
    (b.anc i).side = ((2 ^ (b.n - i) : ℕ) : ℝ) * b.side :=
  side_eq_pow_mul (by simp only [DyBox.anc, min_eq_left h]; omega)

lemma closedBox_sub_anc (b : DyBox) (i : ℕ) : b.closedBox ⊆ (b.anc i).closedBox := by
  rcases le_total b.n i with hb | hb
  · rw [anc_self hb]
  intro z ⟨h1, h2, h3, h4⟩
  have hD : 0 < 2 ^ (b.n - i) := by positivity
  have hs := side_anc hb
  obtain ⟨a1, a2⟩ := coord_anc hD b.side_pos' h1 h2
  obtain ⟨a3, a4⟩ := coord_anc hD b.side_pos' h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hs] <;> simp only [DyBox.anc] <;> assumption

lemma exists_sub_idx {cj D : ℕ} (hD : 0 < D) {s x : ℝ} (hs : 0 < s)
    (h1 : ((cj * D : ℕ) : ℝ) * s ≤ x) (h2 : x ≤ ((cj * D + D : ℕ) : ℝ) * s) :
    ∃ dj : ℕ, dj / D = cj ∧ (dj : ℝ) * s ≤ x ∧ x ≤ (dj + 1) * s := by
  have hx0 : 0 ≤ x / s := div_nonneg (le_trans (by positivity) h1) hs.le
  have hf1 : cj * D ≤ ⌊x / s⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hs]; exact h1)
  by_cases hf : ⌊x / s⌋₊ + 1 ≤ cj * D + D
  · refine ⟨⌊x / s⌋₊, Nat.div_eq_of_lt_le (by linarith) (by rw [Nat.succ_mul]; omega), ?_, ?_⟩
    · rw [← le_div_iff₀ hs]; exact Nat.floor_le hx0
    · rw [← div_le_iff₀ hs]; exact (Nat.lt_floor_add_one _).le
  · refine ⟨cj * D + D - 1, Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega), ?_, ?_⟩
    · have e : ((cj * D + D - 1 : ℕ) : ℝ) ≤ x / s := by
        have : cj * D + D - 1 ≤ ⌊x / s⌋₊ := by omega
        exact (Nat.cast_le.2 this).trans (Nat.floor_le hx0)
      rwa [le_div_iff₀ hs] at e
    · refine h2.trans (le_of_eq ?_)
      congr 1
      have : 1 ≤ cj * D + D := by omega
      push_cast [Nat.cast_sub this]; ring

/-- A point of a box `c` lies in a descendant of `c` at any finer level `L`. -/
lemma exists_desc (c : DyBox) {L : ℕ} (hL : c.n ≤ L) {z : ℂ} (hz : z ∈ c.closedBox) :
    ∃ d : DyBox, d.n = L ∧ d.anc c.n = c ∧ z ∈ d.closedBox := by
  set D := 2 ^ (L - c.n)
  have hD : 0 < D := by positivity
  have hsL : 0 < ((2 : ℝ)⁻¹ ^ L) := by positivity
  have hs : c.side = (D : ℝ) * (2 : ℝ)⁻¹ ^ L := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hL
    simp only [D, DyBox.side, hr, Nat.add_sub_cancel_left, pow_add]; push_cast
    rw [mul_left_comm, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have cast1 : ∀ x : ℕ, (x : ℝ) * c.side = ((x * D : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ L := by
    intro x; rw [hs]; push_cast; ring
  have cast2 : ∀ x : ℕ, ((x : ℝ) + 1) * c.side = ((x * D + D : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ L := by
    intro x; rw [hs]; push_cast; ring
  rw [cast1] at h1 h3; rw [cast2] at h2 h4
  obtain ⟨dj, hdj, e1, e2⟩ := exists_sub_idx hD hsL h1 h2
  obtain ⟨dk, hdk, e3, e4⟩ := exists_sub_idx hD hsL h3 h4
  have hDL : 2 ^ c.n * D = 2 ^ L := by rw [← pow_add]; congr 1; omega
  have hlt : ∀ x y : ℕ, x / D = y → y < 2 ^ c.n → x < 2 ^ L := by
    intro x y hxy hy
    rw [← hDL]
    have := Nat.lt_mul_div_succ x hD
    rw [hxy] at this
    nlinarith
  refine ⟨⟨L, dj, dk, hlt _ _ hdj c.hj, hlt _ _ hdk c.hk⟩, rfl, ?_, ⟨e1, e2, e3, e4⟩⟩
  ext
  · simp [DyBox.anc, hL]
  · simp only [DyBox.anc]; exact hdj
  · simp only [DyBox.anc]; exact hdk

variable (m : DyBox → ℝ) (δ : ℝ)

/-- Cells form an antichain: two cells with a common descendant coincide. -/
lemma isCell_eq_of_anc {c₁ c₂ d : DyBox} (h₁ : IsCell m δ c₁) (h₂ : IsCell m δ c₂)
    (hd₁ : d.anc c₁.n = c₁) (hd₂ : d.anc c₂.n = c₂) : c₁ = c₂ := by
  have key : ∀ {a b : DyBox}, IsCell m δ a → IsCell m δ b → d.anc a.n = a → d.anc b.n = b →
      a.n < b.n → False := by
    intro a b ha hb hda hdb hab
    have : b.anc a.n = a := by rw [← hdb, anc_anc d hab.le, hda]
    have := hb.2 a.n hab
    rw [‹b.anc a.n = a›] at this
    exact absurd ha.1 (not_lt.2 this)
  rcases lt_trichotomy c₁.n c₂.n with h | h | h
  · exact (key h₁ h₂ hd₁ hd₂ h).elim
  · rw [← hd₁, ← hd₂, h]
  · exact (key h₂ h₁ hd₂ hd₁ h).elim

/-- **`Ψ_{B',δ} ≤ 8 (2^{k'} + 2)`** when every box of `𝓑_∂(B', 2^{-k'})` has mass `< δ²`. -/
theorem psiLe_of_bdry (B' : DyBox) (k' : ℕ) (h : ∀ bt ∈ boxCollBdry B' k', m bt < δ ^ 2) :
    PsiLe m δ B' (8 * (2 ^ k' + 2)) := by
  classical
  unfold PsiLe cellPsi
  split_ifs with hcell
  · exact ⟨1, rfl, by have : (0 : ℝ) ≤ 2 ^ k' := by positivity
                      push_cast; linarith⟩
  set S := {c | IsCell m δ c ∧ c.closedBox ⊆ B'.closedBox ∧
    (c.closedBox ∩ frontier B'.closedBox).Nonempty}
  -- cells touching `∂B'` are not finer than level `B'.n + k'`
  have hlev : ∀ c ∈ S, c.n ≤ B'.n + k' := by
    rintro c ⟨hc, -, z, hz, hzf⟩
    by_contra hlt
    push_neg at hlt
    have ha : c.anc (B'.n + k') ∈ boxCollBdry B' k' :=
      ⟨by simp [DyBox.anc, hlt.le], z, closedBox_sub_anc c _ hz, hzf⟩
    exact absurd (h _ ha) (not_lt.2 (hc.2 _ hlt))
  have hex : ∀ c ∈ S, ∃ d : DyBox, d.n = B'.n + k' ∧ d.anc c.n = c ∧
      (d.closedBox ∩ frontier B'.closedBox).Nonempty := by
    intro c hcS
    obtain ⟨-, -, z, hz, hzf⟩ := id hcS
    obtain ⟨d, hdn, hda, hzd⟩ := exists_desc c (hlev c hcS) hz
    exact ⟨d, hdn, hda, z, hzd, hzf⟩
  set f : DyBox → DyBox := fun c => if hc : c ∈ S then (hex c hc).choose else c
  have hf : ∀ c ∈ S, f c ∈ boxCollBdry B' k' ∧ (f c).anc c.n = c := by
    intro c hc
    simp only [f, dite_eq_left_iff, hc, not_true_eq_false, IsEmpty.forall_iff, dif_pos hc]
    obtain ⟨h1, h2, h3⟩ := (hex c hc).choose_spec
    exact ⟨⟨h1, h3⟩, h2⟩
  have hmaps : MapsTo f S (boxCollBdry B' k') := fun c hc => (hf c hc).1
  have hinj : InjOn f S := by
    intro c₁ hc₁ c₂ hc₂ he
    have a1 := (hf c₁ hc₁).2
    have a2 := (hf c₂ hc₂).2
    rw [he] at a1
    exact isCell_eq_of_anc m δ hc₁.1 hc₂.1 a1 a2
  have hfin : S.Finite := Set.Finite.of_injOn hmaps hinj (boxCollBdry_finite B' k')
  refine ⟨S.ncard, (hfin.cast_ncard_eq).symm, ?_⟩
  have := (Set.ncard_le_ncard_of_injOn f hmaps hinj (boxCollBdry_finite B' k')).trans
    (boxCollBdry_ncard_le B' k')
  exact_mod_cast this

end DZZ
end LQGMetric
