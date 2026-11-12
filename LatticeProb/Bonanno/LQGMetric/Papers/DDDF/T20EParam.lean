/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EParam at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EFinal

/-!
# DDDF Theorem 20, Step 4: bookkeeping for the clipped circuit (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1117–1119 ("`O(K^{ε₀})` rectangle crossings of size
`2^{-K}(3,1)`"): the rectangles of `circR` belong to the grid family `longFam K`
(`circR_sub_longFam`) and there are at most `4(i₂ − i₁ + 7) + 4(j₂ − j₁ + 7)` of them
(`card_circR_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

lemma circR_form {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} {e : Circle × ℂ} (he : e ∈ circR K i₁ i₂ j₁ j₂) :
    ∃ a b : ℤ, e = eH K a b ∨ e = eV K a b := by
  rcases circR_cases he with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨n, -, rfl⟩ := mem_hSet.1 h
    rcases hChain_cases K (lo i₁) (j₁ - 3) n with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    exacts [⟨_, _, Or.inl rfl⟩, ⟨_, _, Or.inr rfl⟩]
  · obtain ⟨n, -, rfl⟩ := mem_hSet.1 h
    rcases hChain_cases K (lo i₁) j₂ n with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    exacts [⟨_, _, Or.inl rfl⟩, ⟨_, _, Or.inr rfl⟩]
  · obtain ⟨n, -, rfl⟩ := mem_vSet.1 h
    rcases vChain_cases K (i₁ - 3) (lo j₁) n with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    exacts [⟨_, _, Or.inr rfl⟩, ⟨_, _, Or.inl rfl⟩]
  · obtain ⟨n, -, rfl⟩ := mem_vSet.1 h
    rcases vChain_cases K i₂ (lo j₁) n with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    exacts [⟨_, _, Or.inr rfl⟩, ⟨_, _, Or.inl rfl⟩]

/-- the corner `c` of `u 2^{-K} R_{3,1} + c` lies in the rectangle -/
lemma corner_mem_RL (K : ℕ) (e : Circle × ℂ) : e.2 ∈ T20D.RL K e :=
  ⟨0, by rw [mem_rectAB_toSet]; simp, by simp [T20B.mot]⟩

lemma mem_longFam_of {K : ℕ} {u : Circle} (hu : u = 1 ∨ u = circI) {a b : ℤ}
    (ha : 0 ≤ a ∧ a ≤ 2 ^ K) (hb : 0 ≤ b ∧ b ≤ 2 ^ K) : (u, gp K a b) ∈ T20D.longFam K := by
  classical
  have hp : (0 : ℤ) < 2 ^ K := by positivity
  simp only [T20D.longFam, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_Icc]
  exact ⟨hu, (a, b), ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩

/-- **the circuit consists of grid rectangles** -/
theorem circR_sub_longFam {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂) (hy : BoxOK K j₁ j₂) :
    circR K i₁ i₂ j₁ j₂ ⊆ T20D.longFam K := by
  intro e he
  have hc := (circR_props hx hy he (corner_mem_RL K e)).1.1
  obtain ⟨a, b, rfl | rfl⟩ := circR_form he <;>
  · obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ := hc
    have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
    simp only [eH, eV, gp] at c1 c2 c3 c4
    have r1 : ((0 : ℤ) : ℝ) ≤ a := le_of_mul_le_mul_right c1 hp
    have r2 : (a : ℝ) ≤ ((2 ^ K : ℤ) : ℝ) := le_of_mul_le_mul_right c2 hp
    have r3 : ((0 : ℤ) : ℝ) ≤ b := le_of_mul_le_mul_right c3 hp
    have r4 : (b : ℝ) ≤ ((2 ^ K : ℤ) : ℝ) := le_of_mul_le_mul_right c4 hp
    exact mem_longFam_of (by simp) ⟨by exact_mod_cast r1, by exact_mod_cast r2⟩
      ⟨by exact_mod_cast r3, by exact_mod_cast r4⟩

lemma card_hSet_le (K : ℕ) (p q : ℤ) (ℓ : ℕ) : (hSet K p q ℓ).card ≤ 2 * ℓ + 1 := by
  classical
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_range]
  omega

lemma card_vSet_le (K : ℕ) (p q : ℤ) (ℓ : ℕ) : (vSet K p q ℓ).card ≤ 2 * ℓ + 1 := by
  classical
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_range]
  omega

/-- **the number of rectangles of the circuit** -/
theorem card_circR_le {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂) (hy : BoxOK K j₁ j₂) :
    ((circR K i₁ i₂ j₁ j₂).card : ℤ) ≤ 4 * (i₂ - i₁ + 7) + 4 * (j₂ - j₁ + 7) := by
  classical
  obtain ⟨-, lxe, -, -, lx1, hx2⟩ := hx.len
  obtain ⟨-, lye, -, -, ly1, hy2⟩ := hy.len
  have h1 := card_hSet_le K (lo i₁) (j₁ - 3) (hi K i₂ - lo i₁).toNat
  have h2 := card_hSet_le K (lo i₁) j₂ (hi K i₂ - lo i₁).toNat
  have h3 := card_vSet_le K (i₁ - 3) (lo j₁) (hi K j₂ - lo j₁).toNat
  have h4 := card_vSet_le K i₂ (lo j₁) (hi K j₂ - lo j₁).toNat
  have hU : (circR K i₁ i₂ j₁ j₂).card ≤
      (hSet K (lo i₁) (j₁ - 3) (hi K i₂ - lo i₁).toNat).card +
      (hSet K (lo i₁) j₂ (hi K i₂ - lo i₁).toNat).card +
      (vSet K (i₁ - 3) (lo j₁) (hi K j₂ - lo j₁).toNat).card +
      (vSet K i₂ (lo j₁) (hi K j₂ - lo j₁).toNat).card := by
    unfold circR
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
      (Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)) ?_)) ?_) <;>
    split_ifs <;> simp
  have : ((circR K i₁ i₂ j₁ j₂).card : ℤ) ≤ (2 * ((hi K i₂ - lo i₁).toNat : ℤ) + 1) +
      (2 * ((hi K i₂ - lo i₁).toNat : ℤ) + 1) + (2 * ((hi K j₂ - lo j₁).toNat : ℤ) + 1) +
      (2 * ((hi K j₂ - lo j₁).toNat : ℤ) + 1) := by
    have := hU.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4)
    exact_mod_cast this
  rw [lxe, lye] at this
  omega

end T20E
end DDDF
end LQGMetric
