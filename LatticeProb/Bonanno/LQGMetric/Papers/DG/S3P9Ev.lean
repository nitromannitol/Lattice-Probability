/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P9Ev at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9Det2

/-!
# DG Proposition 3.9: the event of Lemma 3.14 gives the crossing paths (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, proof of Proposition 3.9 (DG:1347–1350): "On the event `E^ε`,
we can choose for each `m ≥ log₂ ε^{-β}` and each `2^{-m+1} × 2^{-m}` (resp. `2^{-m} × 2^{-m+1}`)
rectangle `R ⊆ 𝕊` with corners in `2^{-m}ℤ²` a simple path `P_R` in `R'` from `∂_L R` to `∂_R R`
(resp. `∂_B R` to `∂_T R`) which can be covered by at most `M_m` balls of mass `≤ ε` in `R'`."
(`p39Hyp_of_event`: the bounds of DG Lemma 3.14 for the grid rectangles near `c + [0,L]²` give
`P39Hyp`; the path need not be simple.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open Classical

variable {μ : Measure ℂ} {ε : ℝ} {Q : Set ℂ} {c : ℂ} {L : ℝ}

lemma isClosed_l313Str (s : ℝ) (b : ℂ) (n : ℕ) : IsClosed (l313Str s b n) :=
  isClosed_Icc.reProdIm isClosed_Icc

lemma isClosed_l313StrV (s : ℝ) (b : ℂ) (n : ℕ) : IsClosed (l313StrV s b n) :=
  isClosed_Icc.reProdIm isClosed_Icc

lemma p39_H_of_set {m A B : ℕ} {M : ℝ}
    (hQ : l313Str (p39d m) (l313Corner c m (A, B)) 1 ⊆ Q)
    (h : (l313Set μ ε (l313Str (p39d m) (l313Corner c m (A, B)) 1)
      (l313Left (p39d m) (l313Corner c m (A, B)) 1)
      (l313Right (p39d m) (l313Corner c m (A, B)) 1) : ℝ≥0∞) ≤ ENNReal.ofReal M) :
    ∃ K, P39H μ ε Q M (c.re + p39d m * A) (c.re + p39d m * A + 2 * p39d m)
      (c.im + p39d m * B) (c.im + p39d m * B + p39d m) K := by
  obtain ⟨z, hz, w, hw, γ, hγ, hd⟩ := p39_path_of_set (isClosed_l313Str _ _ _) hQ h
  refine ⟨range γ, z, w, γ, rfl, ?_, ?_, fun t => ?_, hd⟩
  · simp only [l313Left, l313Corner, mem_ofPred_eq] at hz; rw [hz.1]
  · simp only [l313Right, l313Corner, mem_ofPred_eq] at hw; rw [hw.1]; simp
  · have := hγ t
    simp only [l313Str, l313Corner, Complex.mem_reProdIm, mem_Icc, Nat.cast_one,
      mul_one] at this
    exact ⟨this.2.1, this.2.2⟩

lemma p39_V_of_set {m A B : ℕ} {M : ℝ}
    (hQ : l313StrV (p39d m) (l313Corner c m (A, B)) 1 ⊆ Q)
    (h : (l313Set μ ε (l313StrV (p39d m) (l313Corner c m (A, B)) 1)
      (l313Bot (p39d m) (l313Corner c m (A, B)) 1)
      (l313Top (p39d m) (l313Corner c m (A, B)) 1) : ℝ≥0∞) ≤ ENNReal.ofReal M) :
    ∃ K, P39V μ ε Q M (c.re + p39d m * A) (c.re + p39d m * A + p39d m)
      (c.im + p39d m * B) (c.im + p39d m * B + 2 * p39d m) K := by
  obtain ⟨z, hz, w, hw, γ, hγ, hd⟩ := p39_path_of_set (isClosed_l313StrV _ _ _) hQ h
  refine ⟨range γ, z, w, γ, rfl, ?_, ?_, fun t => ?_, hd⟩
  · simp only [l313Bot, l313Corner, mem_ofPred_eq] at hz; rw [hz.1]
  · simp only [l313Top, l313Corner, mem_ofPred_eq] at hw; rw [hw.1]; simp
  · have := hγ t
    simp only [l313StrV, l313Corner, Complex.mem_reProdIm, mem_Icc, Nat.cast_one,
      mul_one] at this
    exact ⟨this.1.1, this.1.2⟩

lemma p39d_mul_two_pow (m : ℕ) : p39d m * (2 : ℝ) ^ m = 1 := by
  simp only [p39d]; rw [← mul_pow]; norm_num

lemma p39d_anti {k m : ℕ} (h : k ≤ m) : p39d m ≤ p39d k :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- an index with `A 2^{-m} ≤ L + 2^{-m} < 1` is `< 2^m` -/
lemma p39_idx_lt {m A : ℕ} {r : ℝ} (hLr : L + r ≤ 1) (hδ : 4 * p39d m ≤ r)
    (hA : (A : ℝ) * p39d m ≤ L + p39d m) : A ∈ Finset.range (2 ^ m) := by
  rw [Finset.mem_range]
  have h1 := p39d_mul_two_pow m
  have h0 := p39d_pos m
  have : (A : ℝ) < (2 : ℝ) ^ m := by
    by_contra hc
    push Not at hc
    nlinarith
  exact_mod_cast this

/-- the box `c + [−r, L + r]²` -/
def p39Box (c : ℂ) (L r : ℝ) : Set ℂ :=
  Icc (c.re - r) (c.re + L + r) ×ℂ Icc (c.im - r) (c.im + L + r)

/-- **DG:1347–1350**: the event of Lemma 3.14 (both orientations) gives `P39Hyp` -/
theorem p39Hyp_of_event {r : ℝ} {k₀ : ℕ} {Mf : ℕ → ℝ} (hLr : L + r ≤ 1)
    (hQ : p39Box c L r ⊆ Q) (h4 : 4 * p39d k₀ ≤ r)
    (hH : ∀ m, k₀ ≤ m → ∀ x ∈ l313Grid Q c m,
      (l313Set μ ε (l313Str (p39d m) (l313Corner c m x) 1) (l313Left (p39d m) (l313Corner c m x) 1)
        (l313Right (p39d m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal (Mf m))
    (hV : ∀ m, k₀ ≤ m → ∀ x ∈ l313GridV Q c m,
      (l313Set μ ε (l313StrV (p39d m) (l313Corner c m x) 1) (l313Bot (p39d m) (l313Corner c m x) 1)
        (l313Top (p39d m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal (Mf m)) :
    ∃ KH KV : ℕ → ℕ → ℕ → Set ℂ, P39Hyp μ ε Q c L k₀ Mf KH KV := by
  refine ⟨fun m A B => Classical.epsilon (P39H μ ε Q (Mf m) (c.re + p39d m * A)
      (c.re + p39d m * A + 2 * p39d m) (c.im + p39d m * B) (c.im + p39d m * B + p39d m)),
    fun m A B => Classical.epsilon (P39V μ ε Q (Mf m) (c.re + p39d m * A)
      (c.re + p39d m * A + p39d m) (c.im + p39d m * B) (c.im + p39d m * B + 2 * p39d m)),
    fun m A B hm hA hB => ?_, fun m A B hm hA hB => ?_⟩
  all_goals
    have hδ : 4 * p39d m ≤ r := le_trans (by linarith [p39d_anti hm]) h4
    have h0 := p39d_pos m
    have hA0 : (0 : ℝ) ≤ A * p39d m := by positivity
    have hB0 : (0 : ℝ) ≤ B * p39d m := by positivity
    have hAr := p39_idx_lt hLr hδ hA
    have hBr := p39_idx_lt hLr hδ hB
  · have hsub : l313Str (p39d m) (l313Corner c m (A, B)) 1 ⊆ Q := by
      refine Subset.trans ?_ hQ
      intro z hz
      simp only [l313Str, l313Corner, p39Box, Complex.mem_reProdIm, mem_Icc, Nat.cast_one,
        mul_one] at hz ⊢
      simp only [p39d] at hA hB hδ h0 hA0 hB0 hz
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
    have hx : (A, B) ∈ l313Grid Q c m :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hAr, hBr⟩, hsub⟩
    exact Classical.epsilon_spec (p39_H_of_set hsub (hH m hm _ hx))
  · have hsub : l313StrV (p39d m) (l313Corner c m (A, B)) 1 ⊆ Q := by
      refine Subset.trans ?_ hQ
      intro z hz
      simp only [l313StrV, l313Corner, p39Box, Complex.mem_reProdIm, mem_Icc, Nat.cast_one,
        mul_one] at hz ⊢
      simp only [p39d] at hA hB hδ h0 hA0 hB0 hz
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
    have hx : (A, B) ∈ l313GridV Q c m :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hAr, hBr⟩, hsub⟩
    exact Classical.epsilon_spec (p39_V_of_set hsub (hV m hm _ hx))

end DG
end LQGMetric
