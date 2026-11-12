/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22A2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22A1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9

/-!
# DG Proposition 3.22 assembly, part 2: the good event at `𝕍`-scale (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, proof of Proposition 3.22 (DG:1739–1771), deterministic part at
`𝕍`-scale, with `U = c + [−r, L+r]²` (the domain of Proposition 3.9, `p39Box`), the cells of the
Lemma 3.21 grid at level `M_ε = ⌈log₂ ε^{-β}⌉` (anchored at `0`, `S(1) ⊆ Q'`) and `φ` a continuous
field (DG: `ĥ_{ε^β}`):
* `p322a_cell`: the cells of side `δ ≤ r'/2` cover `U` when `U + [−r', r']² ⊆ Q' ⊆ [0,1)²`;
* `p322a_good`: on the events of Lemma 3.21 (eqn-square-dist), Lemma 3.8 (second condition of
  (eqn-lfpp-lower-event)) and Proposition 3.9 (`D^ε(z,w;U) ≤ T` on `𝕊`),
  `D^{LFPP}_{φ}(z,w;U) ≤ 3√2 δ_ε (2T / L_ε + e^{(γ/d) sup_{Q'} φ})` for `z, w ∈ 𝕊`,
  `L_ε = ε^{-1/d + β(2+γ²/2)/d + ζ}` ((eqn-lfpp-upper-path), (eqn-lfpp-upper-sum)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open Classical

/-- the cells of the Lemma 3.21 grid cover `U = c + [−r, L+r]²` (DG:1745, "`S_0` a square
containing `z`") -/
lemma p322a_cell {Q' : Set ℂ} {c : ℂ} {L r r' β ε : ℝ}
    (h0 : 0 ≤ c.re - r) (h0' : 0 ≤ c.im - r) (h1 : c.re + L + r < 1) (h1' : c.im + L + r < 1)
    (hδ : 2 * (2 : ℝ)⁻¹ ^ l321M β ε ≤ r')
    (hQ' : Icc (c.re - r - r') (c.re + L + r + r') ×ℂ Icc (c.im - r - r') (c.im + L + r + r') ⊆
      Q') :
    ∀ x ∈ p39Box c L r, ∃ i ∈ l321Grid Q' 0 β ε,
      x ∈ l321In ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner 0 (l321M β ε) i) 1 := by
  intro x hx
  simp only [p39Box, Complex.mem_reProdIm, mem_Icc] at hx
  set M := l321M β ε
  have hd := p39d_pos M
  have hd1 := p39d_mul_two_pow M
  have l1 := p39Idx_le (k := M) (t := x.re) (by linarith)
  have l2 := p39Idx_le (k := M) (t := x.im) (by linarith)
  have u1 := p39Idx_lt (k := M) x.re
  have u2 := p39Idx_lt (k := M) x.im
  simp only [p39d] at hd hd1 l1 l2 u1 u2
  have hlt : ∀ A : ℕ, (A : ℝ) * (2 : ℝ)⁻¹ ^ M < 1 → A ∈ Finset.range (2 ^ M) := by
    intro A hA
    rw [Finset.mem_range]
    have : (A : ℝ) < (2 : ℝ) ^ M := by
      by_contra hc; push Not at hc; nlinarith
    exact_mod_cast this
  refine ⟨(p39Idx M x.re, p39Idx M x.im), Finset.mem_filter.2 ⟨Finset.mem_product.2
    ⟨hlt _ (by linarith), hlt _ (by linarith)⟩, ?_⟩, ?_⟩
  · intro y hy
    apply hQ'
    simp only [l321Out, l313Corner, Complex.zero_re, Complex.zero_im, zero_add, Nat.cast_one,
      mul_one, Complex.mem_reProdIm, mem_Icc] at hy ⊢
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · simp only [l321In, l313Corner, Complex.zero_re, Complex.zero_im, zero_add, Nat.cast_one,
      mul_one, Complex.mem_reProdIm, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

lemma p39Box_closed (c : ℂ) (L r : ℝ) : IsClosed (p39Box c L r) :=
  isClosed_Icc.reProdIm isClosed_Icc

lemma p39Box_convex (c : ℂ) (L r : ℝ) : Convex ℝ (p39Box c L r) :=
  convex_reProdIm_of (convex_Icc _ _) (convex_Icc _ _)

/-- `D ≤ T` (real) gives `D ≤ ⌊T⌋₊` -/
lemma p322a_floor {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ} {z w : ℂ} {T : ℝ}
    (h : (dgLGD μ ε U z w : ℝ≥0∞) ≤ ENNReal.ofReal T) : dgLGD μ ε U z w ≤ (⌊T⌋₊ : ℕ∞) := by
  have hne : dgLGD μ ε U z w ≠ ⊤ := by
    intro e; rw [e, ENat.toENNReal_top] at h; exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hn] at h ⊢
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff'] at h
  rcases h with h | h
  · exact_mod_cast Nat.le_floor h
  · have : n = 0 := by exact_mod_cast le_antisymm h (Nat.cast_nonneg n)
    subst this; exact bot_le

/-- **DG Proposition 3.22 on the good event, `𝕍`-scale** (DG:1739–1771) -/
theorem p322a_good {μ : Measure ℂ} {Q' : Set ℂ} {c : ℂ} {L r r' β ε γ d ζ T : ℝ}
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hγ : 0 < γ) (hd : 0 < d) (hε : 0 < ε) (hT0 : 0 ≤ T)
    (hQ'c : IsCompact Q')
    (h0 : 0 ≤ c.re - r) (h0' : 0 ≤ c.im - r) (h1 : c.re + L + r < 1) (h1' : c.im + L + r < 1)
    (hδ : 2 * (2 : ℝ)⁻¹ ^ l321M β ε ≤ r')
    (hQ' : Icc (c.re - r - r') (c.re + L + r + r') ×ℂ Icc (c.im - r - r') (c.im + L + r + r') ⊆
      Q')
    (hcross : ∀ i ∈ l321Grid Q' 0 β ε, ENNReal.ofReal (l321Tgt γ d ζ β ε (sSup (φ ''
        l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner 0 (l321M β ε) i) 1))) ≤
      (l313Set μ ε univ (l321In ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner 0 (l321M β ε) i) 1)
        (frontier (l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner 0 (l321M β ε) i) 1)) : ℝ≥0∞))
    (hmass : ∀ x ∈ p39Box c L r, ENNReal.ofReal ε < μ (ball x ((2 : ℝ)⁻¹ ^ l321M β ε / 2)))
    (hT : ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L,
      (dgLGD μ ε (p39Box c L r) z w : ℝ≥0∞) ≤ ENNReal.ofReal T) :
    ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L, dgLFPP (γ / d) φ (p39Box c L r) z w ≤
      3 * Real.sqrt 2 * (2 : ℝ)⁻¹ ^ l321M β ε *
        (2 * T / ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ) +
          Real.exp (γ / d * sSup (φ '' Q'))) := by
  intro z hz w hw
  have hL : 0 < ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ) := Real.rpow_pos_of_pos hε _
  have h := p322a_good_l321 (p39Box_closed c L r) (p39Box_convex c L r) hφ
    (div_pos hγ hd).le hL (p322a_cell h0 h0' h1 h1' hδ hQ')
    (fun i hi v hv => le_csSup (hQ'c.image hφ).bddAbove ⟨v, (Finset.mem_filter.1 hi).2 hv, rfl⟩)
    hcross hmass (p322a_floor (hT z hz w hw))
  refine h.trans ?_
  have hA : 0 ≤ 3 * Real.sqrt 2 * (2 : ℝ)⁻¹ ^ l321M β ε := by positivity
  apply mul_le_mul_of_nonneg_left _ hA
  gcongr
  exact Nat.floor_le hT0

end DG
end LQGMetric
