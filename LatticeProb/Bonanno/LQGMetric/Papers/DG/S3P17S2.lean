/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17S2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17, Steps 1–2: the rectangle event gives the crossings of `Y_S` (P2-DG317S)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17
(DG:1543–1559): on the event of Lemma 3.13 (`lem-rectangle-dist`) for the `δ_ε × (δ_ε/2)` and
`(δ_ε/2) × δ_ε` rectangles `R ⊆ 𝕊` with corners in `(δ_ε/2) ℤ²` (both orientations), "we can
choose for each such rectangle a path `P_R` … which can be covered by at most `N` Euclidean
balls of `μ_ĥ`-mass at most `ε`, each of which is contained in `R'`" (DG:1557–1559).

Here the level of the rectangles is `m = M + 1` (`t = 2^{-m} = δ_ε/2`, `M = m_δ`), the grid is
`l313Grid Q 0 m` (corners `t (A, B)`, `A, B < 2^m`), and `Q ⊇ [−r, 1+r]²`, `2t ≤ r`. The bound of
each rectangle is DG's `l313Tgt … (min_{R'} ĥ_t)`; since `v_S ∈ R'` for each of the six rectangles
of `S`, it is at most `l313Tgt … (ĥ_t(v_S))` (`p17s_tgt_le`), which Step 1's field control bounds
further (file S3P17S3).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint Classical

variable {μ : Measure ℂ} {ε : ℝ} {Q : Set ℂ}

lemma P39H.mono {U : Set ℂ} {M M' x₀ x₁ y₀ y₁ : ℝ} {K : Set ℂ}
    (h : P39H μ ε U M x₀ x₁ y₀ y₁ K) (hM : M ≤ M') : P39H μ ε U M' x₀ x₁ y₀ y₁ K := by
  obtain ⟨z, w, γ, a, b, c, d, e⟩ := h
  exact ⟨z, w, γ, a, b, c, d, fun p hp q hq => (e p hp q hq).trans (ENNReal.ofReal_le_ofReal hM)⟩

lemma P39V.mono {U : Set ℂ} {M M' x₀ x₁ y₀ y₁ : ℝ} {K : Set ℂ}
    (h : P39V μ ε U M x₀ x₁ y₀ y₁ K) (hM : M ≤ M') : P39V μ ε U M' x₀ x₁ y₀ y₁ K := by
  obtain ⟨z, w, γ, a, b, c, d, e⟩ := h
  exact ⟨z, w, γ, a, b, c, d, fun p hp q hq => (e p hp q hq).trans (ENNReal.ofReal_le_ofReal hM)⟩

lemma l313Tgt_mono {γ d ζ ε : ℝ} (hd : 0 < d) (hγ : 0 < γ) (m : ℕ) {a b : ℝ} (hab : a ≤ b)
    (hε : 0 < ε) : l313Tgt γ d ζ ε m a ≤ l313Tgt γ d ζ ε m b := by
  unfold l313Tgt
  refine max_le_max le_rfl (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
  exact mul_le_mul_of_nonneg_left hab (by positivity)

/-- `min_{R'} f ≤ f(v)` for `v ∈ R'`, `f` continuous -/
lemma p17s_sInf_le {f : ℂ → ℝ} (hf : Continuous f) {a b c e : ℝ} {v : ℂ}
    (hv : v ∈ Icc a b ×ℂ Icc c e) : sInf (f '' (Icc a b ×ℂ Icc c e)) ≤ f v := by
  have hK : IsCompact (Icc a b ×ℂ Icc c e) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      (Metric.isBounded_Icc a b |>.reProdIm (Metric.isBounded_Icc c e))
  exact csInf_le (hK.bddBelow_image hf.continuousOn) ⟨v, hv, rfl⟩

lemma p17s_toNat_lt {M : ℕ} {k : ℤ × ℤ} (hk : k ∈ dgIdx M) {i j : ℕ} (hi : i ≤ 1) (hj : j ≤ 1) :
    2 * k.1.toNat + i < 2 ^ (M + 1) ∧ 2 * k.2.toNat + j < 2 ^ (M + 1) := by
  have e : ((2 : ℤ) ^ M) = ((2 ^ M : ℕ) : ℤ) := by push_cast; rfl
  have a1 := hk.1; have a2 := hk.2.1; have a3 := hk.2.2.1; have a4 := hk.2.2.2
  rw [e] at a2 a4
  have h1' : k.1.toNat < 2 ^ M := by omega
  have h2' : k.2.toNat < 2 ^ M := by omega
  rw [pow_succ]; omega

/-- a corner index `A < 2^m` has `t A ≤ 1 − t` -/
lemma p17s_idx_le {m A : ℕ} (hA : A < 2 ^ m) : p39d m * A ≤ 1 - p39d m := by
  have h1 := p39d_mul_two_pow m
  have h0 := p39d_pos m
  have : (A : ℝ) + 1 ≤ (2 : ℝ) ^ m := by exact_mod_cast hA
  nlinarith

lemma p17s_strH_sub {m A B : ℕ} {r : ℝ} (hQ : p39Box 0 1 r ⊆ Q) (hr : 2 * p39d m ≤ r)
    (hA : A < 2 ^ m) (hB : B < 2 ^ m) : l313Str (p39d m) (l313Corner 0 m (A, B)) 1 ⊆ Q := by
  refine Subset.trans ?_ hQ
  intro z hz
  have h0 := p39d_pos m
  have hA' := p17s_idx_le hA
  have hB' := p17s_idx_le hB
  have hA0 : (0 : ℝ) ≤ p39d m * A := by positivity
  have hB0 : (0 : ℝ) ≤ p39d m * B := by positivity
  simp only [l313Str, l313Corner, p39Box, Complex.mem_reProdIm, mem_Icc, Nat.cast_one,
    mul_one, Complex.zero_re, Complex.zero_im, zero_add, zero_sub] at hz ⊢
  simp only [p39d] at *
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma p17s_strV_sub {m A B : ℕ} {r : ℝ} (hQ : p39Box 0 1 r ⊆ Q) (hr : 2 * p39d m ≤ r)
    (hA : A < 2 ^ m) (hB : B < 2 ^ m) : l313StrV (p39d m) (l313Corner 0 m (A, B)) 1 ⊆ Q := by
  refine Subset.trans ?_ hQ
  intro z hz
  have h0 := p39d_pos m
  have hA' := p17s_idx_le hA
  have hB' := p17s_idx_le hB
  have hA0 : (0 : ℝ) ≤ p39d m * A := by positivity
  have hB0 : (0 : ℝ) ≤ p39d m * B := by positivity
  simp only [l313StrV, l313Corner, p39Box, Complex.mem_reProdIm, mem_Icc, Nat.cast_one,
    mul_one, Complex.zero_re, Complex.zero_im, zero_add, zero_sub] at hz ⊢
  simp only [p39d] at *
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- the centre `v_S` of the square `k` lies in `R'` for each of its rectangles -/
lemma p17s_center_mem {M : ℕ} {k : ℤ × ℤ} (hk : k ∈ dgIdx M) {i j : ℕ} (hi : i ≤ 1)
    (hj : j ≤ 1) :
    dgCenter M k ∈ l313Str (p39d (M + 1)) (l313Corner 0 (M + 1)
      (2 * k.1.toNat + i, 2 * k.2.toNat + j)) 1 ∧
    dgCenter M k ∈ l313StrV (p39d (M + 1)) (l313Corner 0 (M + 1)
      (2 * k.1.toNat + i, 2 * k.2.toNat + j)) 1 := by
  have ea : ((k.1.toNat : ℕ) : ℝ) = (k.1 : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk.1]
  have eb : ((k.2.toNat : ℕ) : ℝ) = (k.2 : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk.2.2.1]
  have es : (2 : ℝ)⁻¹ ^ M = 2 * p39d (M + 1) := by rw [p39d_succ]; ring
  have ht := p39d_pos (M + 1)
  have hi' : (i : ℝ) ≤ 1 := by exact_mod_cast hi
  have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  simp only [dgCenter, l313Str, l313StrV, l313Corner, Complex.mem_reProdIm, mem_Icc,
    Nat.cast_one, mul_one, Complex.zero_re, Complex.zero_im, zero_add, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, ea, eb, es]
  rw [show (2 : ℝ)⁻¹ ^ (M + 1) = p39d (M + 1) from rfl]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- **DG:1557–1559**: on the event of Lemma 3.13 (both orientations) at level `M + 1`, the
six rectangles of every square `S` carry crossings with bound `N_S` whenever
`l313Tgt … (ĥ_t(v_S)) ≤ N_S` -/
theorem p17s_hyp_of_event {γ d ζ : ℝ} (hd : 0 < d) (hγ : 0 < γ) (hε : 0 < ε) {M : ℕ}
    {f : ℂ → ℝ} (hf : Continuous f) {r : ℝ} (hQ : p39Box 0 1 r ⊆ Q)
    (hr : 2 * p39d (M + 1) ≤ r)
    (hH : ∀ x ∈ l313Grid Q 0 (M + 1),
      (l313Set μ ε (l313Str (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1)
        (l313Left (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1)
        (l313Right (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1) : ℝ≥0∞) ≤
      ENNReal.ofReal (l313Tgt γ d ζ ε (M + 1)
        (sInf (f '' l313Str (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1))))
    (hV : ∀ x ∈ l313GridV Q 0 (M + 1),
      (l313Set μ ε (l313StrV (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1)
        (l313Bot (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1)
        (l313Top (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1) : ℝ≥0∞) ≤
      ENNReal.ofReal (l313Tgt γ d ζ ε (M + 1)
        (sInf (f '' l313StrV (p39d (M + 1)) (l313Corner 0 (M + 1) x) 1))))
    {N : ℤ × ℤ → ℝ} (hN : ∀ k ∈ dgIdx M, l313Tgt γ d ζ ε (M + 1) (f (dgCenter M k)) ≤ N k) :
    ∃ KH KV : ℕ → ℕ → Set ℂ, P17SHyp μ ε Q M KH KV N := by
  set m := M + 1
  -- the bound of the rectangle `(A, B)`
  set MH : ℕ → ℕ → ℝ := fun A B =>
    l313Tgt γ d ζ ε m (sInf (f '' l313Str (p39d m) (l313Corner 0 m (A, B)) 1))
  set MV : ℕ → ℕ → ℝ := fun A B =>
    l313Tgt γ d ζ ε m (sInf (f '' l313StrV (p39d m) (l313Corner 0 m (A, B)) 1))
  refine ⟨fun A B => Classical.epsilon (P39H μ ε Q (MH A B) (p39d m * A)
      (p39d m * A + 2 * p39d m) (p39d m * B) (p39d m * B + p39d m)),
    fun A B => Classical.epsilon (P39V μ ε Q (MV A B) (p39d m * A)
      (p39d m * A + p39d m) (p39d m * B) (p39d m * B + 2 * p39d m)), fun k hk i j hi hj => ?_⟩
  obtain ⟨hA, hB⟩ := p17s_toNat_lt hk hi hj
  obtain ⟨cH, cV⟩ := p17s_center_mem hk hi hj
  have sH := p17s_strH_sub hQ hr hA hB
  have sV := p17s_strV_sub hQ hr hA hB
  have xH : (2 * k.1.toNat + i, 2 * k.2.toNat + j) ∈ l313Grid Q 0 m :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 hA, Finset.mem_range.2 hB⟩, sH⟩
  have xV : (2 * k.1.toNat + i, 2 * k.2.toNat + j) ∈ l313GridV Q 0 m :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 hA, Finset.mem_range.2 hB⟩, sV⟩
  have exH := p39_H_of_set sH (hH _ xH)
  have exV := p39_V_of_set sV (hV _ xV)
  simp only [Complex.zero_re, Complex.zero_im, zero_add] at exH exV
  exact ⟨(Classical.epsilon_spec exH).mono ((l313Tgt_mono hd hγ m (p17s_sInf_le hf cH) hε).trans
      (hN k hk)),
    (Classical.epsilon_spec exV).mono ((l313Tgt_mono hd hγ m (p17s_sInf_le hf cV) hε).trans
      (hN k hk))⟩

end LQGMetric.DG
