/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EGlue

/-!
# DDDF Theorem 20, Step 4: the circuit around a box, clipped to `[0,1]²` (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105 (the circuit of four rectangles `Q_i(P)`
of size `2^{-K}(C K^{ε₀}, 3)` around `P^K`) and l. 1117–1119 (each crossed by a chain of
`O(K^{ε₀})` long `2^{-K}(3,1)` crossings), with the boundary convention D-DDDF-22: the strips of
the circuit are kept only when they fit in `[0,1]²`; a side of the box closer than three blocks
to `∂[0,1]²` is pushed to `∂[0,1]²`, and the strips along the other sides are extended to
`∂[0,1]²`.

In block units (`h = 2^{-K}`) the box is `[i₁, i₂] × [j₁, j₂]`; the four strips are
`[xlo, xhi] × [j₁−3, j₁]` (bottom), `[xlo, xhi] × [j₂, j₂+3]` (top), `[i₁−3, i₁] × [ylo, yhi]`
(left), `[i₂, i₂+3] × [ylo, yhi]` (right), `xlo = 0` if `i₁ < 3` (left side clipped) and
`i₁ − 3` otherwise, etc. `circR K i₁ i₂ j₁ j₂` is the finite set of long rectangles of their
chains. Here: they lie in `[0,1]²`, outside the open box, in the `3`-neighbourhood of the box
(`circR_props`), belong to `longFam K` (`circR_sub_longFam`), and there are `O(i₂ − i₁ + j₂ − j₁)`
of them (`card_circR_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

/-- the lower end of the horizontal strips -/
def lo (i₁ : ℤ) : ℤ := if i₁ < 3 then 0 else i₁ - 3
/-- the upper end of the horizontal strips -/
def hi (K : ℕ) (i₂ : ℤ) : ℤ := if (2 : ℤ) ^ K < i₂ + 3 then 2 ^ K else i₂ + 3

open Classical in
/-- the long rectangles of the chain of a horizontal strip -/
def hSet (K : ℕ) (p q : ℤ) (ℓ : ℕ) : Finset (Circle × ℂ) :=
  (Finset.range (2 * (ℓ - 3) + 1)).image (hChain K p q)

open Classical in
/-- the long rectangles of the chain of a vertical strip -/
def vSet (K : ℕ) (p q : ℤ) (ℓ : ℕ) : Finset (Circle × ℂ) :=
  (Finset.range (2 * (ℓ - 3) + 1)).image (vChain K p q)

open Classical in
/-- **the circuit around the box `[i₁, i₂] × [j₁, j₂]`**, clipped to `[0,1]²` -/
def circR (K : ℕ) (i₁ i₂ j₁ j₂ : ℤ) : Finset (Circle × ℂ) :=
  (if j₁ < 3 then ∅ else hSet K (lo i₁) (j₁ - 3) (hi K i₂ - lo i₁).toNat) ∪
  (if (2 : ℤ) ^ K < j₂ + 3 then ∅ else hSet K (lo i₁) j₂ (hi K i₂ - lo i₁).toNat) ∪
  (if i₁ < 3 then ∅ else vSet K (i₁ - 3) (lo j₁) (hi K j₂ - lo j₁).toNat) ∪
  (if (2 : ℤ) ^ K < i₂ + 3 then ∅ else vSet K i₂ (lo j₁) (hi K j₂ - lo j₁).toNat)

/-- the standing assumptions on one coordinate of the box -/
structure BoxOK (K : ℕ) (i₁ i₂ : ℤ) : Prop where
  le : i₁ ≤ i₂
  nonneg : 0 ≤ i₂
  le_two_pow : i₁ ≤ 2 ^ K
  not_both : ¬(i₁ < 3 ∧ (2 : ℤ) ^ K < i₂ + 3)

lemma BoxOK.len {K : ℕ} {i₁ i₂ : ℤ} (h : BoxOK K i₁ i₂) :
    3 ≤ (hi K i₂ - lo i₁).toNat ∧ ((hi K i₂ - lo i₁).toNat : ℤ) = hi K i₂ - lo i₁ ∧
      0 ≤ lo i₁ ∧ hi K i₂ ≤ 2 ^ K ∧ i₁ - 3 ≤ lo i₁ ∧ hi K i₂ ≤ i₂ + 3 := by
  have h0 := h.le; have h1 := h.nonneg; have h2 := h.le_two_pow; have h3 := h.not_both
  have hp : (0 : ℤ) < 2 ^ K := by positivity
  unfold lo hi
  split_ifs with a b b <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

lemma gRect_mono {K : ℕ} {a₀ a₁ b₀ b₁ a₀' a₁' b₀' b₁' : ℤ} (h1 : a₀' ≤ a₀) (h2 : a₁ ≤ a₁')
    (h3 : b₀' ≤ b₀) (h4 : b₁ ≤ b₁') : gRect K a₀ a₁ b₀ b₁ ⊆ gRect K a₀' a₁' b₀' b₁' := by
  intro z hz
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have r1 : (a₀' : ℝ) ≤ a₀ := by exact_mod_cast h1
  have r2 : (a₁ : ℝ) ≤ a₁' := by exact_mod_cast h2
  have r3 : (b₀' : ℝ) ≤ b₀ := by exact_mod_cast h3
  have r4 : (b₁ : ℝ) ≤ b₁' := by exact_mod_cast h4
  obtain ⟨⟨z1, z2⟩, ⟨z3, z4⟩⟩ := hz
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

lemma mem_hSet {K : ℕ} {p q : ℤ} {ℓ : ℕ} {e : Circle × ℂ} :
    e ∈ hSet K p q ℓ ↔ ∃ n ≤ 2 * (ℓ - 3), hChain K p q n = e := by
  classical
  simp only [hSet, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

lemma mem_vSet {K : ℕ} {p q : ℤ} {ℓ : ℕ} {e : Circle × ℂ} :
    e ∈ vSet K p q ℓ ↔ ∃ n ≤ 2 * (ℓ - 3), vChain K p q n = e := by
  classical
  simp only [vSet, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

/-- the four strips: every long rectangle of the circuit lies in one of them -/
lemma circR_cases {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} {e : Circle × ℂ} (he : e ∈ circR K i₁ i₂ j₁ j₂) :
    (¬ j₁ < 3 ∧ e ∈ hSet K (lo i₁) (j₁ - 3) (hi K i₂ - lo i₁).toNat) ∨
    (¬ (2 : ℤ) ^ K < j₂ + 3 ∧ e ∈ hSet K (lo i₁) j₂ (hi K i₂ - lo i₁).toNat) ∨
    (¬ i₁ < 3 ∧ e ∈ vSet K (i₁ - 3) (lo j₁) (hi K j₂ - lo j₁).toNat) ∨
    (¬ (2 : ℤ) ^ K < i₂ + 3 ∧ e ∈ vSet K i₂ (lo j₁) (hi K j₂ - lo j₁).toNat) := by
  classical
  simp only [circR, Finset.mem_union] at he
  rcases he with ((h | h) | h) | h <;> split_ifs at h with c <;>
    simp_all

/-- **Where the circuit lies**: in `[0,1]²`, outside the open box, within three blocks of it. -/
theorem circR_props {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂) (hy : BoxOK K j₁ j₂)
    {e : Circle × ℂ} (he : e ∈ circR K i₁ i₂ j₁ j₂) :
    T20D.RL K e ⊆ gRect K 0 (2 ^ K) 0 (2 ^ K) ∩ gRect K (i₁ - 3) (i₂ + 3) (j₁ - 3) (j₂ + 3) ∩
      ({x | x.im ≤ (j₁ : ℝ) * (2 : ℝ)⁻¹ ^ K} ∪ {x | (j₂ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ x.im} ∪
        {x | x.re ≤ (i₁ : ℝ) * (2 : ℝ)⁻¹ ^ K} ∪ {x | (i₂ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ x.re}) := by
  obtain ⟨lx3, lxe, lx0, hx1, lx1, hx2⟩ := hx.len
  obtain ⟨ly3, lye, ly0, hy1, ly1, hy2⟩ := hy.len
  have hi1 := hx.le; have hj1 := hy.le
  have hi2 := hx.nonneg; have hj2 := hy.nonneg
  have hi3 := hx.le_two_pow; have hj3 := hy.le_two_pow
  rcases circR_cases he with ⟨c, h⟩ | ⟨c, h⟩ | ⟨c, h⟩ | ⟨c, h⟩
  · obtain ⟨n, hn, rfl⟩ := mem_hSet.1 h
    have hs := hChain_sub K (lo i₁) (j₁ - 3) _ hn lx3
    rw [lxe] at hs
    refine fun x hx => ⟨⟨gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx),
      gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx)⟩, ?_⟩
    have := (hs hx).2.2
    exact Or.inl (Or.inl (Or.inl (by simpa using this)))
  · obtain ⟨n, hn, rfl⟩ := mem_hSet.1 h
    have hs := hChain_sub K (lo i₁) j₂ _ hn lx3
    rw [lxe] at hs
    refine fun x hx => ⟨⟨gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx),
      gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx)⟩, ?_⟩
    exact Or.inl (Or.inl (Or.inr (hs hx).2.1))
  · obtain ⟨n, hn, rfl⟩ := mem_vSet.1 h
    have hs := vChain_sub K (i₁ - 3) (lo j₁) _ hn ly3
    rw [lye] at hs
    refine fun x hx => ⟨⟨gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx),
      gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx)⟩, ?_⟩
    have := (hs hx).1.2
    exact Or.inl (Or.inr (by simpa using this))
  · obtain ⟨n, hn, rfl⟩ := mem_vSet.1 h
    have hs := vChain_sub K i₂ (lo j₁) _ hn ly3
    rw [lye] at hs
    refine fun x hx => ⟨⟨gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx),
      gRect_mono (by omega) (by omega) (by omega) (by omega) (hs hx)⟩, ?_⟩
    exact Or.inr (hs hx).1.1

end T20E
end DDDF
end LQGMetric
