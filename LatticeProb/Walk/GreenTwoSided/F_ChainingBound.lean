import LatticeProb.Site
import LatticeProb.Graph.Zd
import LatticeProb.Graph.ExitDecomp
import LatticeProb.Network.Killed
import LatticeProb.Network.KilledGreen
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.LocalCLTOne
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.ExitBox
import LatticeProb.Walk.GreenTwoSided.C_UpperBound
import LatticeProb.Walk.GreenTwoSided.D_LazyWalk
import LatticeProb.Walk.GreenTwoSided.E_FreeLazyKernel

/-!
# Killed near-diagonal bound and chaining

The killed near-diagonal lower bound `lazyKilled B n a b ≥ c₁ / s ^ d`, obtained from the free
bound of `E_FreeLazyKernel` by subtracting an off-diagonal correction, and the chaining lemma that
composes such single-step bounds along a sequence of anchor points to give a lower bound at a
matching scale over a longer time.
-/

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

-- Choice of M: M : ℕ with (M : ℝ)^d ≥ 2 C / c₀ (M := ⌈2C/c₀⌉₊ + 1, M^d ≥ M).
/-- There is `M ≥ 1` with `C / M^d ≤ c₀/2`, the arithmetic input for absorbing the off-diagonal
correction into the near-diagonal lower bound. -/
private theorem exists_nat_div_pow_le_half (hd : 1 ≤ d) (C c₀ : ℝ) (_unused_hC : 0 < C)
    (hc₀ : 0 < c₀) :
    ∃ M : ℕ, 1 ≤ M ∧ C / (M : ℝ) ^ d ≤ c₀ / 2 := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max 1 (2 * C / c₀))
  have h1 : (1 : ℝ) ≤ (M : ℝ) := le_trans (le_max_left _ _) hM
  have h2 : 2 * C / c₀ ≤ (M : ℝ) := le_trans (le_max_right _ _) hM
  have h3 : 2 * C ≤ c₀ * (M : ℝ) := (mul_div_cancel₀ (2 * C) (ne_of_gt hc₀)).symm.trans_le
      (mul_le_mul_of_nonneg_left h2 (le_of_lt hc₀))
  have h4 : (M : ℝ) ≤ (M : ℝ) ^ d := le_self_pow₀ h1 (lt_of_lt_of_le Nat.zero_lt_one hd).ne'
  refine ⟨M, by exact_mod_cast h1, ?_⟩
  rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le one_pos h1) d)]
  nlinarith [h3, h4, hc₀]


-- le_lazyKilled_of_forall_le with S := C/(M s)^d: for z ∉ B, graphNorm (z - b) > M s
-- (contrapositive of hB),
-- so iterate_Q_delta0_le_div_pow_of_le_graphNorm with r := M s gives Q^[j] δ₀(z - b) ≤ C/(Ms)^d;
-- exists_const_le_iterate_Q_delta0_div_pow at w := a - b;
-- exists_nat_div_pow_le_half: c₀/s^d - C/(M s)^d ≥ (c₀/2)/s^d (mul_pow, div_div).  c₁ := c₀/2, s₁
-- := s₀.
/-- Given `C/M^d ≤ c₀/2`, the off-diagonal correction at scale `Ms` satisfies `C/(Ms)^d ≤
(c₀/2)/s^d`. -/
private theorem div_mul_pow_le_half_div_pow (C M s c0 : ℝ) (d : ℕ) (hM : C / M ^ d ≤ c0 / 2)
    (hs : 0 < s) : C / (M * s) ^ d ≤ (c0 / 2) / s ^ d := by
  have hl : C / (M * s) ^ d = (C / M ^ d) * (1 / s ^ d) := by
    rw [div_eq_mul_inv, mul_pow, mul_inv]; ring
  have hr : (c0 / 2) / s ^ d = (c0 / 2) * (1 / s ^ d) := by
    rw [div_eq_mul_inv]; ring
  rw [hl, hr]
  exact mul_le_mul_of_nonneg_right hM (by positivity)

/-- Algebraic identity: `c₀/s^d - (c₀/2)/s^d = (c₀/2)/s^d`. -/
private theorem sub_div_pow_eq_half_div_pow (c0 s : ℝ) (d : ℕ) : c0 / s ^ d - (c0 / 2) / s ^ d =
    (c0 / 2) / s ^ d := by
  rw [div_sub_div_same]; ring

/-- The killed near-diagonal lower bound: there are `c₁ > 0`, `M`, `s₁` such that `c₁/s^d ≤
lazyKilled B n a b` once `graphNorm (a-b) ≤ s` and `B` contains everything within `Ms` of
`b`, from the free bound minus the off-diagonal correction. -/
private theorem exists_const_le_lazyKilled_div_pow (hd : 1 ≤ d) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ M s₁ : ℕ, 1 ≤ M ∧ 1 ≤ s₁ ∧ ∀ s : ℕ, s₁ ≤ s → ∀ n : ℕ,
      s ^ 2 ≤ n → n ≤ 2 * s ^ 2 → ∀ (B : Finset (Site d)) (a b : Site d),
        graphNorm (a - b) ≤ s → (∀ z : Site d, graphNorm (z - b) ≤ M * s → z ∈ B) →
          c₁ / (s : ℝ) ^ d ≤ lazyKilled B n a b := by
  obtain ⟨C, hCpos, hC32⟩ := iterate_Q_delta0_le_div_pow_of_le_graphNorm hd
  obtain ⟨c0, hc0pos, s0, hs01, hc039⟩ := exists_const_le_iterate_Q_delta0_div_pow hd
  obtain ⟨M, hM1, hM⟩ := exists_nat_div_pow_le_half hd C c0 hCpos hc0pos
  refine ⟨c0 / 2, by linarith, M, max s0 1, hM1, le_max_right s0 1, ?_⟩
  intro s hs n hn1 hn2 B a b hab hB
  have hs1 : 1 ≤ s := le_trans (le_max_right s0 1) hs
  have hs0 : s0 ≤ s := le_trans (le_max_left s0 1) hs
  have hspos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hs1)
  have hMs1 : 1 ≤ M * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hM1) (Nat.one_le_iff_ne_zero.mp hs1))
  have hcast : ((M * s : ℕ) : ℝ) = (M : ℝ) * (s : ℝ) := Nat.cast_mul M s
  have hSnonneg : (0 : ℝ) ≤ C / ((M : ℝ) * (s : ℝ)) ^ d :=
    div_nonneg (le_of_lt hCpos)
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg s)) d)
  have hstep : ∀ j : ℕ, ∀ z : Site d, z ∉ B →
      Q^[j] (delta0 : Site d → ℝ) (z - b) ≤ C / ((M : ℝ) * (s : ℝ)) ^ d := fun j z hz => by
    have hnatgt : M * s < graphNorm (z - b) := Nat.lt_of_not_le (fun h => hz (hB z h))
    have hb := hC32 j (z - b) (M * s) hMs1 (le_of_lt hnatgt)
    rw [hcast] at hb
    exact hb
  have hS : ∀ j ≤ n, ∀ z : Site d, z ∉ B →
      Q^[j] (delta0 : Site d → ℝ) (z - b) ≤ C / ((M : ℝ) * (s : ℝ)) ^ d := fun j _ => hstep j
  have h29 := le_lazyKilled_of_forall_le hd B b (C / ((M : ℝ) * (s : ℝ)) ^ d) hSnonneg n hS a
  have h39 := hc039 s hs0 n hn1 hn2 (a - b) hab
  have hSle : C / ((M : ℝ) * (s : ℝ)) ^ d ≤ (c0 / 2) / (s : ℝ) ^ d :=
    div_mul_pow_le_half_div_pow C M (s : ℝ) c0 d hM hspos
  have hid := sub_div_pow_eq_half_div_pow c0 (s : ℝ) d
  linarith


-- One chaining step: f (k n + n) a b ≥ ∑_{z ∈ S} f (k n) a z * f n z b (hck) ≥ card S · β · α
-- (Finset.sum_le_sum, mul_le_mul, Finset.sum_const, nsmul_eq_mul).
/-- One chaining step: if `f` satisfies the Chapman-Kolmogorov super-additivity `hck` and is at
least `β`, `α` on `S` at times `p`, `n` respectively, then `|S| * β * α ≤ f (p+n) a b`. -/
private theorem card_mul_le_sum_add_of_forall_le (f : ℕ → Site d → Site d → ℝ)
    (hck : ∀ m n x y (S : Finset (Site d)), ∑ z ∈ S, f m x z * f n z y ≤ f (m + n) x y)
    (S : Finset (Site d)) (p n : ℕ) (a b : Site d) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : ∀ z ∈ S, β ≤ f p a z) (h2 : ∀ z ∈ S, α ≤ f n z b) :
    (S.card : ℝ) * β * α ≤ f (p + n) a b := by
  have hterm : ∀ z : Site d, z ∈ S → β * α ≤ f p a z * f n z b := fun z hz => mul_le_mul (h1 z hz)
      (h2 z hz) hα (le_trans hβ (h1 z hz))
  have hsum : (∑ z ∈ S, β * α) = (S.card : ℝ) * β * α := (Finset.sum_const (β * α)).trans
      ((nsmul_eq_mul (S.card) (β * α)).trans (mul_assoc _ _ _).symm)
  rw [← hsum]
  exact le_trans (Finset.sum_le_sum hterm) (hck p n a b S)


-- Chaining.  Induction on k from 1 (Nat.le_induction): k = 1 is hlink 0; step k → k+1 uses
-- card_mul_le_sum_add_of_forall_le with S := S k, p := k n (so (k+1) n = k n + n, Nat.succ_mul), β
-- := α^k σ^(k-1),
-- card ≥ σ (hcard k, 0 < k < N); pow_succ.
/-- Implementation lemma for `pow_mul_pow_sub_one_le_chain`. -/
private theorem pow_mul_pow_sub_one_le_chain' {d : ℕ} (f : ℕ → Site d → Site d → ℝ)
    (hck : ∀ m n x y (S : Finset (Site d)), ∑ z ∈ S, f m x z * f n z y ≤ f (m + n) x y)
    (S : ℕ → Finset (Site d)) (n N : ℕ) (α σ : ℝ) (hα : 0 ≤ α) (hσ : 0 ≤ σ)
    (hcard : ∀ i, 0 < i → i < N → σ ≤ ((S i).card : ℝ))
    (hlink : ∀ i < N, ∀ a ∈ S i, ∀ b ∈ S (i + 1), α ≤ f n a b) :
    ∀ k, 1 ≤ k → k ≤ N → ∀ a ∈ S 0, ∀ b ∈ S k, α ^ k * σ ^ (k - 1) ≤ f (k * n) a b := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
      intro hkN a ha b hb
      simpa using hlink 0 (by omega) a ha b hb
  | succ j hj ih =>
      intro hkN a ha b hb
      have hlt : j < N := by omega
      have hcardge : σ ≤ ((S j).card : ℝ) := hcard j (by omega) hlt
      have hBnn : 0 ≤ α ^ j * σ ^ (j - 1) :=
        mul_nonneg (pow_nonneg hα j) (pow_nonneg hσ (j - 1))
      have hstep42 := card_mul_le_sum_add_of_forall_le f hck (S j) (j * n) n a b α
          (α ^ j * σ ^ (j - 1)) hα hBnn
        (fun z hz => ih (by omega) a ha z hz)
        (fun z hz => hlink j hlt z hz b hb)
      have hstep42' : ((S j).card : ℝ) * (α ^ j * σ ^ (j - 1)) * α ≤ f ((j + 1) * n) a b := by
        simpa [Nat.succ_mul] using hstep42
      have hle1 : α ^ (j + 1) * σ ^ j
          ≤ ((S j).card : ℝ) * (α ^ j * σ ^ (j - 1)) * α := by
        have hσpow : σ ^ j = σ ^ (j - 1) * σ := by
          rw [← pow_succ, show j - 1 + 1 = j from by omega]
        rw [pow_succ, hσpow]
        calc α ^ j * α * (σ ^ (j - 1) * σ)
            = σ * (α ^ j * σ ^ (j - 1)) * α := by ring
          _ ≤ ((S j).card : ℝ) * (α ^ j * σ ^ (j - 1)) * α :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcardge hBnn) hα
      rw [Nat.add_sub_cancel j 1]
      exact le_trans hle1 hstep42'

/-- Chaining `card_mul_le_sum_add_of_forall_le` along `k` links: `α^k σ^{k-1} ≤ f (kn) a b` for
`a ∈ S 0`, `b ∈ S k`, given a uniform link bound `α` and cardinality bound `σ` on the
intermediate sets. -/
private theorem pow_mul_pow_sub_one_le_chain (f : ℕ → Site d → Site d → ℝ)
    (hck : ∀ m n x y (S : Finset (Site d)), ∑ z ∈ S, f m x z * f n z y ≤ f (m + n) x y)
    (S : ℕ → Finset (Site d)) (n N : ℕ) (α σ : ℝ) (hα : 0 ≤ α) (hσ : 0 ≤ σ)
    (hcard : ∀ i, 0 < i → i < N → σ ≤ ((S i).card : ℝ))
    (hlink : ∀ i < N, ∀ a ∈ S i, ∀ b ∈ S (i + 1), α ≤ f n a b) :
    ∀ k, 1 ≤ k → k ≤ N → ∀ a ∈ S 0, ∀ b ∈ S k, α ^ k * σ ^ (k - 1) ≤ f (k * n) a b := by
  exact pow_mul_pow_sub_one_le_chain' f hck S n N α σ hα hσ hcard hlink


-- Floor quotients of close numerators: Int.ediv_le_ediv (monotone, gives 0 ≤),
-- Int.mul_ediv_self_le (N (a/N) ≤ a), Int.lt_mul_ediv_self_add (b < N (b/N) + N), so
-- N (a/N - b/N) < N (T + 2); lt_of_mul_lt_mul_left, Int.lt_add_one_iff.
/-- For integers with `a - b ≤ N(T+1)`, the floor quotients satisfy `0 ≤ a/N - b/N ≤ T+1`. -/
private theorem sub_ediv_le_add_one_of_sub_le (N a b T : ℤ) (hN : 0 < N) (hba : b ≤ a)
    (hab : a - b ≤ N * (T + 1)) :
    0 ≤ a / N - b / N ∧ a / N - b / N ≤ T + 1 := by
  constructor
  · exact sub_nonneg.mpr (Int.ediv_le_ediv hN hba)
  · have h1 : a ≤ b + N * (T + 1) := by linarith
    have h2 : a / N ≤ (b + N * (T + 1)) / N := Int.ediv_le_ediv hN h1
    rw [Int.add_mul_ediv_left b (T + 1) hN.ne'] at h2
    linarith

-- le_total D 0; sub_ediv_le_add_one_of_sub_le with (a, b) := ((t+1) D, t D) if 0 ≤ D, else
-- (t D, (t+1) D) (abs_of_nonneg / abs_of_nonpos on D); abs_le, linarith.
/-- For `|D| ≤ N(T+1)`, consecutive floor quotients of `t*D` differ by at most `T+1`: `|(t+1)D/N
- tD/N| ≤ T+1`. -/
private theorem abs_sub_ediv_le_add_one (N D T t : ℤ) (hN : 0 < N) (hD : |D| ≤ N * (T + 1)) :
    |(t + 1) * D / N - t * D / N| ≤ T + 1 := by
  rcases le_total 0 D with hD0 | hD0
  · have h := sub_ediv_le_add_one_of_sub_le N ((t + 1) * D) (t * D) T hN (by nlinarith) (by
      have := abs_of_nonneg hD0
      rw [this] at hD
      nlinarith)
    rw [abs_of_nonneg h.1]
    exact h.2
  · have h := sub_ediv_le_add_one_of_sub_le N (t * D) ((t + 1) * D) T hN (by nlinarith) (by
      have := abs_of_nonpos hD0
      rw [this] at hD
      nlinarith)
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]

-- Int.ediv_nonneg (mul_nonneg), Int.ediv_le_of_le_mul (t D ≤ D N: mul_le_mul_of_nonneg_right,
-- mul_comm).
/-- For `0 ≤ t ≤ N` and `D ≥ 0`, `0 ≤ tD/N ≤ D`. -/
private theorem ediv_mem_Icc_of_nonneg (N t D : ℤ) (hN : 0 < N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (hD : 0 ≤ D) :
    0 ≤ t * D / N ∧ t * D / N ≤ D := by
  constructor
  · exact Int.ediv_nonneg (mul_nonneg ht0 hD) hN.le
  · exact Int.ediv_le_of_le_mul hN (by nlinarith)

-- Int.ediv_nonpos_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos),
-- Int.le_ediv_of_mul_le (D N ≤ t D: nlinarith).
/-- For `0 ≤ t ≤ N` and `D ≤ 0`, `D ≤ tD/N ≤ 0`. -/
private theorem ediv_mem_Icc_of_nonpos (N t D : ℤ) (hN : 0 < N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (hD : D ≤ 0) :
    D ≤ t * D / N ∧ t * D / N ≤ 0 := by
  constructor
  · exact Int.le_ediv_of_mul_le hN (by nlinarith)
  · exact Int.ediv_nonpos_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ht0 hD) hN

-- abs_le at ha hb and goal; le_total 0 (b - a) with ediv_mem_Icc_of_nonneg / ediv_mem_Icc_of_nonpos
-- (D := b - a); linarith.
/-- Interpolating between `a` and `b` by floor division stays within the bound: `|a + t(b-a)/N| ≤
m` when `|a|, |b| ≤ m`. -/
private theorem abs_add_mul_ediv_le (N t a b m : ℤ) (hN : 0 < N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (ha : |a| ≤ m) (hb : |b| ≤ m) : |a + t * (b - a) / N| ≤ m := by
  rw [abs_le] at ha hb ⊢
  rcases le_total 0 (b - a) with hD | hD
  · have h1 : 0 ≤ t * (b - a) / N := Int.ediv_nonneg (mul_nonneg ht0 hD) hN.le
    have h2 : t * (b - a) / N ≤ b - a := Int.ediv_le_of_le_mul hN (by nlinarith)
    constructor <;> linarith
  · have h1 : b - a ≤ t * (b - a) / N := Int.le_ediv_of_mul_le hN (by nlinarith)
    have h2 : t * (b - a) / N ≤ 0 :=
      Int.ediv_nonpos_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ht0 hD) hN
    constructor <;> linarith

-- Nat.lt_div_mul_add (0 < 4 d): s < s/(4d) * (4d) + 4d; then
-- 2 K' s ≤ 2 K' (4d (s/(4d)+1)) ≤ 8 d (K'+1) (s/(4d)+1) (Nat.mul_le_mul, nlinarith).
/-- An arithmetic bound `2K's ≤ 8d(K'+1)(s/(4d)+1)` from rounding `s` up to a multiple of `4d`. -/
private theorem two_mul_le_mul_div_add_one (hd : 1 ≤ d) (K' s : ℕ) :
    2 * K' * s ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
  have hd0 : 0 < 4 * d := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h5 : s < s / (4 * d) * (4 * d) + 4 * d := Nat.lt_div_mul_add hd0
  have h6 : s ≤ 4 * d * (s / (4 * d) + 1) := by
    have h7 : s / (4 * d) * (4 * d) = 4 * d * (s / (4 * d)) := Nat.mul_comm _ _
    rw [h7] at h5
    have h8 : 4 * d * (s / (4 * d) + 1) = 4 * d * (s / (4 * d)) + 4 * d := by ring
    rw [h8]
    omega
  calc 2 * K' * s ≤ 2 * K' * (4 * d * (s / (4 * d) + 1)) := Nat.mul_le_mul_left _ h6
    _ = 8 * d * K' * (s / (4 * d) + 1) := by ring
    _ ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
        have h9 : 8 * d * K' ≤ 8 * d * (K' + 1) := Nat.mul_le_mul_left _ (by omega)
        exact Nat.mul_le_mul_right _ h9

-- natAbs_sub_le_two_mul_of_abs_le m b a hb ha ((b - a).natAbs ≤ 2 m), Int.natCast_natAbs, 2 m ≤ 2
-- K' s
-- (Nat.mul_le_mul_left), two_mul_le_mul_div_add_one; exact_mod_cast / push_cast.
/-- For `m ≤ K's` and `|a|, |b| ≤ m`, `|b-a| ≤ 8d(K'+1)(s/(4d)+1)`. -/
private theorem abs_sub_le_mul_div_add_one (hd : 1 ≤ d) (K' s m : ℕ) (hm : m ≤ K' * s) (a b : ℤ)
    (ha : |a| ≤ (m : ℤ)) (hb : |b| ≤ (m : ℤ)) :
    |b - a| ≤ ((8 * d * (K' + 1) : ℕ) : ℤ) * (((s / (4 * d) : ℕ) : ℤ) + 1) := by
  have h1 : |b - a| ≤ 2 * (m : ℤ) := by
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith
  have h4 : 2 * (K' * s) ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
    have h := two_mul_le_mul_div_add_one hd K' s
    calc 2 * (K' * s) = 2 * K' * s := by ring
      _ ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := h
  have h2 : (2 * m : ℤ) ≤ ((8 * d * (K' + 1) * (s / (4 * d) + 1) : ℕ) : ℤ) := by
    have h3 : 2 * m ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
      have h10 : 2 * m ≤ 2 * (K' * s) := by omega
      omega
    exact_mod_cast h3
  have hgoal : ((8 * d * (K' + 1) : ℕ) : ℤ) * (((s / (4 * d) : ℕ) : ℤ) + 1)
      = ((8 * d * (K' + 1) * (s / (4 * d) + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hgoal]
  linarith

-- Anchor points: w i j := x j + (min i N * (y j - x j)) / N  (Int division), N := 8 d (K'+1).
-- w i between x and y coordinatewise, so in box m; consecutive difference ≤ |y j - x j|/N + 1
-- and |y j - x j| ≤ 2m ≤ 2K's, 2K's/(8d(K'+1)) ≤ s/(4d) (Int.ediv_le_ediv, Int.le_ediv_iff_mul_le,
-- omega/nlinarith).  SPLIT?
/-- There is a chain of anchor points `w : ℕ → Site d` from `x` to `y` inside `box d m`, taking
`8d(K'+1)` steps, each moving every coordinate by at most `s/(4d)+1`. -/
private theorem exists_path_le_div_add_one (K' s m : ℕ) (hd : 1 ≤ d) (_unused_hs : 4 * d ≤ s)
    (hm : m ≤ K' * s)
    (x y : Site d) (hx : x ∈ box d m) (hy : y ∈ box d m) :
    ∃ w : ℕ → Site d, w 0 = x ∧ w (8 * d * (K' + 1)) = y ∧ (∀ i, w i ∈ box d m) ∧
      ∀ i (j : Fin d), |w (i + 1) j - w i j| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ) := by
  have hNpos : (0 : ℤ) < ((8 * d * (K' + 1) : ℕ) : ℤ) := by
    have h : 0 < 8 * d * (K' + 1) := Nat.mul_pos (Nat.mul_pos (by norm_num) hd) (Nat.succ_pos K')
    exact_mod_cast h
  refine ⟨fun i j => x j + ((min i (8 * d * (K' + 1)) : ℕ) : ℤ) * (y j - x j)
      / ((8 * d * (K' + 1) : ℕ) : ℤ), ?_, ?_, ?_, ?_⟩
  · funext j
    simp
  · funext j
    simp only [min_self]
    rw [Int.mul_ediv_cancel_left _ hNpos.ne']
    ring
  · intro i j
    exact abs_add_mul_ediv_le _ _ (x j) (y j) m hNpos (Nat.cast_nonneg _)
      (by exact_mod_cast min_le_right _ _) (hx j) (hy j)
  · intro i j
    have hcast : (((s / (4 * d) + 1 : ℕ) : ℤ)) = ((s / (4 * d) : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [hcast]
    by_cases hi : i < 8 * d * (K' + 1)
    · have h1 : min (i + 1) (8 * d * (K' + 1)) = i + 1 := min_eq_left hi
      have h2 : min i (8 * d * (K' + 1)) = i := min_eq_left hi.le
      simp only [h1, h2, Nat.cast_succ, add_sub_add_left_eq_sub]
      exact abs_sub_ediv_le_add_one _ _ _ _ hNpos
        (abs_sub_le_mul_div_add_one hd K' s m hm (x j) (y j) (hx j) (hy j))
    · have h1 : min (i + 1) (8 * d * (K' + 1)) = 8 * d * (K' + 1) := min_eq_right (by omega)
      have h2 : min i (8 * d * (K' + 1)) = 8 * d * (K' + 1) := min_eq_right (by omega)
      simp only [h1, h2, sub_self, abs_zero]
      positivity

-- Link geometry: a = w + u, b = w' + v with u, v ∈ originBox t, t = s/(4d):
-- graphNorm (a - b) = ∑_j |..| ≤ d (s/(4d) + 1 + 2 t) ≤ s (4 d (s/(4d)) ≤ s, s/(4d) ≥ 1);
-- Int.natAbs_add_le, Finset.sum_le_card_nsmul; b ∈ box (m + t) ⊆ box (m + s).
/-- Two points built by adding small offsets `u, v` (from `originBox d (s/(4d))`) to nearby
anchors `w, w'` are within `graphNorm` distance `s` of each other. -/
private theorem graphNorm_add_sub_add_le (hd : 1 ≤ d) (s : ℕ) (hs : 4 * d ≤ s) (w w' : Site d)
    (hstep : ∀ j : Fin d, |w' j - w j| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ))
    (u v : Site d) (hu : u ∈ originBox d (s / (4 * d))) (hv : v ∈ originBox d (s / (4 * d))) :
    graphNorm ((w + u) - (w' + v)) ≤ s := by
  have h4d : 0 < 4 * d := by omega
  have ht1 : 1 ≤ s / (4 * d) := (Nat.one_le_div_iff h4d).mpr hs
  have hu_le : ∀ i : Fin d, |u i| ≤ ((s / (4 * d) : ℕ) : ℤ) := by
    intro i
    rw [originBox_eq] at hu
    exact abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hu i))
  have hv_le : ∀ i : Fin d, |v i| ≤ ((s / (4 * d) : ℕ) : ℤ) := by
    intro i
    rw [originBox_eq] at hv
    exact abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv i))
  have hfinal : d * (3 * (s / (4 * d)) + 1) ≤ s := by
    have h2 : d ≤ d * (s / (4 * d)) := by simpa using Nat.mul_le_mul_left d ht1
    calc d * (3 * (s / (4 * d)) + 1) = 3 * (d * (s / (4 * d))) + d := by ring
      _ ≤ 3 * (d * (s / (4 * d))) + d * (s / (4 * d)) := Nat.add_le_add_left h2 _
      _ = (s / (4 * d)) * (4 * d) := by ring
      _ ≤ s := Nat.div_mul_le_self s (4 * d)
  have hcoord : ∀ i : Fin d, ((w + u - (w' + v)) i).natAbs ≤ 3 * (s / (4 * d)) + 1 := by
    intro i
    have heq : (w + u - (w' + v)) i = (w i - w' i) + (u i - v i) := by
      simp only [Pi.sub_apply, Pi.add_apply]; ring
    have h1 : |w i - w' i| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ) := by
      simpa [abs_sub_comm] using hstep i
    have h2 : |u i - v i| ≤ 2 * ((s / (4 * d) : ℕ) : ℤ) := by
      rw [abs_sub_le_iff]
      constructor <;>
        linarith [neg_abs_le (u i), le_abs_self (u i), neg_abs_le (v i), le_abs_self (v i),
          hu_le i, hv_le i]
    have h3 : |(w + u - (w' + v)) i| ≤ ((3 * (s / (4 * d)) + 1 : ℕ) : ℤ) := by
      rw [heq]
      calc |(w i - w' i) + (u i - v i)| ≤ |w i - w' i| + |u i - v i| := abs_add_le _ _
        _ ≤ ((s / (4 * d) + 1 : ℕ) : ℤ) + 2 * ((s / (4 * d) : ℕ) : ℤ) := add_le_add h1 h2
        _ = ((3 * (s / (4 * d)) + 1 : ℕ) : ℤ) := by push_cast; ring
    refine Int.ofNat_le.mp ?_
    rw [Int.natCast_natAbs]
    exact h3
  calc ∑ i, ((w + u - (w' + v)) i).natAbs
      ≤ ∑ _i : Fin d, (3 * (s / (4 * d)) + 1) := Finset.sum_le_sum fun i _ => hcoord i
    _ = d * (3 * (s / (4 * d)) + 1) := by simp
    _ ≤ s := hfinal

/-- An offset point `w' + v` with `w' ∈ box d m` and `v ∈ originBox d (s/(4d))` lies in `box d
(m+s)`. -/
private theorem add_mem_box_add (_unused_hd : 1 ≤ d) (s m : ℕ) (_unused_hs : 4 * d ≤ s)
    (w' v : Site d)
    (hw' : w' ∈ box d m) (hv : v ∈ originBox d (s / (4 * d))) :
    w' + v ∈ box d (m + s) := by
  intro i
  have hv_le : ∀ i : Fin d, |v i| ≤ ((s / (4 * d) : ℕ) : ℤ) := by
    intro i
    rw [originBox_eq] at hv
    exact abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv i))
  have hts : ((s / (4 * d) : ℕ) : ℤ) ≤ (s : ℤ) := by
    exact_mod_cast Nat.div_le_self s (4 * d)
  calc |(w' + v) i| = |w' i + v i| := by simp
    _ ≤ |w' i| + |v i| := abs_add_le _ _
    _ ≤ (m : ℤ) + (s : ℤ) := add_le_add (hw' i) (le_trans (hv_le i) hts)
    _ = ((m + s : ℕ) : ℤ) := by push_cast; ring

/-- Combines `graphNorm_add_sub_add_le` and `add_mem_box_add`: points in the offset images of
adjacent anchors are within `s` of each other and the second lies in `box d (m+s)`. -/
private theorem graphNorm_sub_le_and_mem_box (hd : 1 ≤ d) (s m : ℕ) (hs : 4 * d ≤ s) (w w' : Site d)
    (hw' : w' ∈ box d m)
    (hstep : ∀ j : Fin d, |w' j - w j| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ))
    (a b : Site d) (ha : a ∈ (originBox d (s / (4 * d))).image (w + ·))
    (hb : b ∈ (originBox d (s / (4 * d))).image (w' + ·)) :
    graphNorm (a - b) ≤ s ∧ b ∈ box d (m + s) := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨graphNorm_add_sub_add_le hd s hs w w' hstep u v hu hv,
    add_mem_box_add hd s m hs w' v hw' hv⟩


-- If b ∈ box (m + s) and graphNorm (z - b) ≤ M s then z ∈ box (m + (M + 1) s)
-- (|z j| ≤ |b j| + |z j - b j| ≤ m + s + M s; single coordinate ≤ graphNorm: Finset.single_le_sum).
/-- If `b ∈ box d (m+s)` and `graphNorm (z-b) ≤ Ms`, then `z ∈ box d (m + (M+1)s)`. -/
private theorem mem_box_of_graphNorm_sub_le (s m M : ℕ) (b z : Site d) (hb : b ∈ box d (m + s))
    (hz : graphNorm (z - b) ≤ M * s) : z ∈ box d (m + (M + 1) * s) := by
  intro i
  have hb' : (b i).natAbs ≤ m + s := (by
    have h := hb i
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h)
  have hsub : ((z - b) i).natAbs ≤ M * s := (by
    have hs : ((z - b) i).natAbs ≤ graphNorm (z - b) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin d => ((z - b) j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega)
  have hkey : (z i).natAbs ≤ ((z - b) i).natAbs + (b i).natAbs := (by
    have h : z i = (z - b) i + b i := (by
      simp only [Pi.sub_apply]
      ring)
    rw [h]
    exact Int.natAbs_add_le _ _)
  have hfin : (z i).natAbs ≤ m + (M + 1) * s := (by
    have hMs : (M + 1) * s = M * s + s := Nat.succ_mul M s
    omega)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hfin


-- Translate of a box: Finset.card_image_of_injective (add_right_injective w), card_originBox'.
/-- Translating `originBox d t` by `w` preserves its cardinality `(2t+1)^d`. -/
private theorem card_image_add_originBox_eq (w : Site d) (t : ℕ) :
    ((originBox d t).image (w + ·)).card = (2 * t + 1) ^ d := by
  rw [Finset.card_image_of_injective _ (add_right_injective w), card_originBox']


-- split_ifs at ha (Finset.mem_singleton; subst with hw0 / hwN); Finset.mem_image.mpr ⟨0, _,
-- add_zero _⟩,
-- 0 ∈ originBox d t (originBox, Fintype.mem_piFinset, Finset.mem_Icc; simp).
/-- Membership in the piecewise target set (endpoints or a translated `originBox`) implies
membership in the translated `originBox` at interior indices. -/
private theorem mem_image_add_originBox_of_mem_ite (w : ℕ → Site d) (x y : Site d) (N t : ℕ)
    (hw0 : w 0 = x)
    (hwN : w N = y) (i : ℕ) (a : Site d)
    (ha : a ∈ (if i = 0 then {x} else if i = N then {y}
      else (originBox d t).image (w i + ·) : Finset (Site d))) :
    a ∈ (originBox d t).image (w i + ·) := by
  split_ifs at ha with h0 hN
  · rw [Finset.mem_singleton] at ha
    rw [ha, h0, ← hw0]
    exact Finset.mem_image.mpr ⟨0, by simp [originBox, Finset.mem_Icc], by simp⟩
  · rw [Finset.mem_singleton] at ha
    rw [ha, hN, ← hwN]
    exact Finset.mem_image.mpr ⟨0, by simp [originBox, Finset.mem_Icc], by simp⟩
  · exact ha

-- if_neg (i ≠ 0), if_neg (i ≠ N) (omega), card_image_add_originBox_eq; le_of_eq.
/-- At an interior index `i`, the piecewise target set has cardinality at least `(2t+1)^d`, by
`card_image_add_originBox_eq`. -/
private theorem two_mul_add_one_pow_le_card_ite (w : ℕ → Site d) (x y : Site d) (N t i : ℕ)
    (hi0 : 0 < i)
    (hiN : i < N) :
    (((2 * t + 1) ^ d : ℕ) : ℝ) ≤ ((if i = 0 then {x} else if i = N then {y}
      else (originBox d t).image (w i + ·) : Finset (Site d)).card : ℝ) := by
  rw [if_neg (by omega : ¬ i = 0), if_neg (by omega : ¬ i = N)]
  rw [card_image_add_originBox_eq (w i) t]

-- Nat.lt_div_mul_add (0 < 4 d): s < s/(4d) * (4d) + 4d; cast (exact_mod_cast), div_le_iff₀;
-- s/(4d) + 1 ≤ 2 (s/(4d)) + 1; push_cast, nlinarith.
/-- Rounding bound: `s/(4d) ≤ 2(s/(4d))+1` as real numbers. -/
private theorem div_le_two_mul_div_add_one (hd : 1 ≤ d) (s : ℕ) :
    (s : ℝ) / (4 * d) ≤ ((2 * (s / (4 * d)) + 1 : ℕ) : ℝ) := by
  have hd0 : 0 < 4 * d := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h1 : s < s / (4 * d) * (4 * d) + 4 * d := Nat.lt_div_mul_add hd0
  have h2 : (s : ℝ) < ((s / (4 * d) : ℕ) : ℝ) * (4 * (d : ℝ)) + 4 * (d : ℝ) := by
    exact_mod_cast h1
  have h3 : (0 : ℝ) < 4 * (d : ℝ) := by positivity
  have hq : (0 : ℝ) ≤ ((s / (4 * d) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ h3]
  push_cast
  nlinarith [h2, h3, hq]

-- ← div_pow, Nat.cast_pow; pow_le_pow_left₀ (div_nonneg) (div_le_two_mul_div_add_one hd s) d.
/-- Raising `div_le_two_mul_div_add_one` to the `d`-th power: `s^d/(4d)^d ≤ (2(s/(4d))+1)^d`. -/
private theorem pow_div_pow_le_two_mul_div_add_one_pow (hd : 1 ≤ d) (s : ℕ) :
    (s : ℝ) ^ d / (4 * (d : ℝ)) ^ d ≤ (((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ) := by
  have h3 := div_le_two_mul_div_add_one hd s
  have h4 : (0 : ℝ) ≤ (s : ℝ) / (4 * d) := by positivity
  have h5 : ((s : ℝ) / (4 * d)) ^ d ≤ (((2 * (s / (4 * d)) + 1 : ℕ) : ℝ)) ^ d :=
    pow_le_pow_left₀ h4 h3 d
  have h6 : (s : ℝ) ^ d / (4 * (d : ℝ)) ^ d = ((s : ℝ) / (4 * d)) ^ d := by rw [div_pow]
  have h7 : (((2 * (s / (4 * d)) + 1 : ℕ) : ℝ)) ^ d
      = (((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ) := by push_cast; ring
  rw [h6]
  rw [← h7]
  exact h5

-- div_pow, pow_succ, pow_mul / ← pow_mul; field_simp; ring.
/-- Algebraic identity: `(c/S^d)^{k+1} * (S^d/A^d)^k = c^{k+1}/(A^d)^k/S^d`. -/
private theorem pow_mul_pow_eq_pow_div (c A S : ℝ) (hA : A ≠ 0) (hS : S ≠ 0) (k : ℕ) :
    (c / S ^ d) ^ (k + 1) * (S ^ d / A ^ d) ^ k = c ^ (k + 1) / (A ^ d) ^ k / S ^ d := by
  rw [div_pow, div_pow, pow_succ]
  field_simp
  ring

-- N = k + 1 (Nat.exists_eq_add_of_le'), Nat.add_sub_cancel; ← pow_mul_pow_eq_pow_div;
-- mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hσ k) (pow_nonneg (div_nonneg ..)).
/-- Given `S^d/A^d ≤ σ`, `c^N/(A^d)^{N-1}/S^d ≤ (c/S^d)^N σ^{N-1}`. -/
private theorem pow_div_pow_div_le_pow_mul_pow (c A S σ : ℝ) (hc : 0 ≤ c) (hA : 0 < A) (hS : 0 < S)
    (hσ : S ^ d / A ^ d ≤ σ) (N : ℕ) (hN : 1 ≤ N) :
    c ^ N / (A ^ d) ^ (N - 1) / S ^ d ≤ (c / S ^ d) ^ N * σ ^ (N - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hsub : 1 + k - 1 = k := by omega
  rw [hsub]
  have hk : 1 + k = k + 1 := by omega
  rw [hk]
  rw [← pow_mul_pow_eq_pow_div c A S (ne_of_gt hA) (ne_of_gt hS) k]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hσ k) (by positivity)

-- Single-time lower bound at scale s.  M := M₁ + 1 (M₁ from exists_const_le_lazyKilled_div_pow); N
-- := 8 d (K'+1);
-- S i := {x} if i = 0, {y} if i = N, else (originBox d t).image (w i + ·)
-- (exists_path_le_div_add_one);
-- each S i ⊆ image of w i (x = w 0, y = w N, 0 ∈ originBox); pow_mul_pow_sub_one_le_chain with f :=
-- lazyKilled B
-- (hck = sum_lazyKilled_mul_le_lazyKilled_add), α := c₁/s^d (exists_const_le_lazyKilled_div_pow via
-- graphNorm_sub_le_and_mem_box, mem_box_of_graphNorm_sub_le),
-- σ := (2t+1)^d ≥ (s/(8d))^d (card_image_add_originBox_eq).  α^N σ^(N-1) ≥ c₂/s^d with
-- c₂ := c₁^N (8d)^{-d(N-1)}; s₂ := max s₁ (8 d).  SPLIT?
/-- The single-time chained lower bound: for every `K'` there are `c₂ > 0`, `s₂`, `N` such that
`c₂/s^d ≤ lazyKilled B (Nn) x y` for `x, y ∈ box d m` with `m ≤ K's`, provided `B` covers
`box d (m+Ms)`, by chaining `pow_mul_pow_sub_one_le_chain` over the anchor path of
`exists_path_le_div_add_one`. -/
private theorem exists_const_le_lazyKilled_mul_div_pow (hd : 1 ≤ d) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ K' : ℕ, ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ s₂ N : ℕ, 1 ≤ N ∧ 1 ≤ s₂ ∧
      ∀ s : ℕ, s₂ ≤ s → ∀ m : ℕ, m ≤ K' * s → ∀ B : Finset (Site d),
        (∀ z ∈ box d (m + M * s), z ∈ B) → ∀ n : ℕ, s ^ 2 ≤ n → n ≤ 2 * s ^ 2 →
          ∀ x ∈ box d m, ∀ y ∈ box d m, c₂ / (s : ℝ) ^ d ≤ lazyKilled B (N * n) x y := by
  obtain ⟨c₁, hc₁, M₁, s₁, _, hs₁, h41⟩ := exists_const_le_lazyKilled_div_pow hd
  refine ⟨M₁ + 1, by omega, fun K' => ?_⟩
  have hN1 : 1 ≤ 8 * d * (K' + 1) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hd) (Nat.succ_pos K')
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  refine ⟨c₁ ^ (8 * d * (K' + 1)) / ((4 * (d : ℝ)) ^ d) ^ (8 * d * (K' + 1) - 1),
    div_pos (pow_pos hc₁ _) (pow_pos (pow_pos h4d _) _),
    max s₁ (4 * d), 8 * d * (K' + 1), hN1, le_trans hs₁ (le_max_left _ _), ?_⟩
  intro s hs m hm B hB n hn1 hn2 x hx y hy
  have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs4 : 4 * d ≤ s := le_trans (le_max_right _ _) hs
  have hspos : (0 : ℝ) < (s : ℝ) := by
    have h : 0 < s := lt_of_lt_of_le (Nat.mul_pos (by norm_num) hd) hs4
    exact_mod_cast h
  obtain ⟨w, hw0, hwN, hwbox, hwstep⟩ := exists_path_le_div_add_one K' s m hd hs4 hm x y hx hy
  let S : ℕ → Finset (Site d) := fun i =>
    if i = 0 then {x} else if i = 8 * d * (K' + 1) then {y}
      else (originBox d (s / (4 * d))).image (w i + ·)
  have hlink : ∀ i < 8 * d * (K' + 1), ∀ a ∈ S i, ∀ b ∈ S (i + 1),
      c₁ / (s : ℝ) ^ d ≤ lazyKilled B n a b := by
    intro i _ a ha b hb
    have ha' := mem_image_add_originBox_of_mem_ite w x y _ (s / (4 * d)) hw0 hwN i a ha
    have hb' := mem_image_add_originBox_of_mem_ite w x y _ (s / (4 * d)) hw0 hwN (i + 1) b hb
    obtain ⟨h1, h2⟩ := graphNorm_sub_le_and_mem_box hd s m hs4 (w i) (w (i + 1)) (hwbox (i + 1))
        (hwstep i)
      a b ha' hb'
    exact h41 s hs1 n hn1 hn2 B a b h1
        (fun z hz => hB z (mem_box_of_graphNorm_sub_le s m M₁ b z h2 hz))
  have hcard : ∀ i, 0 < i → i < 8 * d * (K' + 1) →
      (((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ) ≤ ((S i).card : ℝ) :=
    fun i h0 hiN => two_mul_add_one_pow_le_card_ite w x y _ (s / (4 * d)) i h0 hiN
  have hx0 : x ∈ S 0 := by
    show x ∈ (if (0 : ℕ) = 0 then {x} else _ : Finset (Site d))
    rw [if_pos rfl]
    exact Finset.mem_singleton_self x
  have hyN : y ∈ S (8 * d * (K' + 1)) := by
    show y ∈ (if 8 * d * (K' + 1) = 0 then {x} else if 8 * d * (K' + 1) = 8 * d * (K' + 1)
      then {y} else _ : Finset (Site d))
    rw [if_neg (by omega), if_pos rfl]
    exact Finset.mem_singleton_self y
  have h43 := pow_mul_pow_sub_one_le_chain (lazyKilled B) (sum_lazyKilled_mul_le_lazyKilled_add B) S
      n (8 * d * (K' + 1))
    (c₁ / (s : ℝ) ^ d) ((((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ))
    (div_nonneg hc₁.le (pow_nonneg hspos.le d)) (Nat.cast_nonneg _) hcard hlink
    (8 * d * (K' + 1)) hN1 le_rfl x hx0 y hyN
  exact le_trans (pow_div_pow_div_le_pow_mul_pow c₁ (4 * (d : ℝ)) (s : ℝ) _ hc₁.le h4d hspos
    (pow_div_pow_le_two_mul_div_add_one_pow hd s) _ hN1) h43

-- Summing over n ∈ Icc (s²) (2 s²): T := (Icc (s^2) (2 s^2)).image (N * ·) (injective, N ≥ 1:
-- Finset.sum_image, mul_left_cancel₀); card = s² + 1 ≥ s²;
-- sum_lazyKilled_le_two_mul_tsum_killedHeat, killedGreenReal_eq_tsum_killedHeat_div:
-- g ≥ (1/(4d)) ∑_{r∈T} lazyKilled ≥ (s²/(4d)) c₂/s^d = (c₂/(4d)) s^{2-d} (zpow_sub₀, zpow_natCast).
/-- Summing `exists_const_le_lazyKilled_mul_div_pow` over `n ∈ [s^2, 2s^2]` gives the
Green-function lower bound `c₃ s^{2-d} ≤ killedGreenReal B x y`. -/
theorem exists_const_mul_rpow_le_killedGreenReal (hd : 1 ≤ d) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ K' : ℕ, ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ s₂ : ℕ, 1 ≤ s₂ ∧
      ∀ s : ℕ, s₂ ≤ s → ∀ m : ℕ, m ≤ K' * s → ∀ B : Finset (Site d),
        (∀ z ∈ box d (m + M * s), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
          c₃ * (s : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y :=
              by
  obtain ⟨M, hM1, h48⟩ := exists_const_le_lazyKilled_mul_div_pow hd
  refine ⟨M, hM1, fun K' => ?_⟩
  obtain ⟨c₂, hc₂, s₂, N, hN, hs₂, h48'⟩ := h48 K'
  have hdpos : (0:ℝ) < (d:ℝ) := (by
    have h : 0 < d := (by omega)
    exact_mod_cast h)
  have h4d : (0:ℝ) < 4 * (d:ℝ) := (by linarith)
  have h2d : (0:ℝ) < 2 * (d:ℝ) := (by linarith)
  refine ⟨c₂ / (4 * (d:ℝ)), div_pos hc₂ h4d, max s₂ 1, le_max_right s₂ 1, ?_⟩
  intro s hs m hm B hB x hx y hy
  have hs1 : 1 ≤ s := le_trans (le_max_right s₂ 1) hs
  have hs2 : s₂ ≤ s := le_trans (le_max_left s₂ 1) hs
  have hsd : (0:ℝ) < (s:ℝ) := (by exact_mod_cast hs1)
  have hsd0 : (s:ℝ) ≠ 0 := ne_of_gt hsd
  have hspow_nonneg : (0:ℝ) ≤ (s:ℝ)^d := pow_nonneg (le_of_lt hsd) d
  have hXnonneg : (0:ℝ) ≤ c₂ / (s:ℝ)^d := div_nonneg (le_of_lt hc₂) hspow_nonneg
  have hNinj : Function.Injective (fun a : ℕ => N * a) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hN hab
  have hTcard : s^2 ≤ ((Finset.Icc (s^2) (2 * s^2)).image (N * ·)).card := (by
    rw [Finset.card_image_of_injective _ hNinj, Nat.card_Icc]
    omega)
  have hcast : ((s^2 : ℕ) : ℝ) ≤ (((Finset.Icc (s^2) (2 * s^2)).image (N * ·)).card : ℝ) := (by
    exact_mod_cast hTcard)
  have hle : ∀ r ∈ (Finset.Icc (s^2) (2 * s^2)).image (N * ·),
      c₂ / (s:ℝ)^d ≤ lazyKilled B r x y := (by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    exact h48' s hs2 m hm B hB n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 x hx y hy)
  have hcardle : (((Finset.Icc (s^2) (2 * s^2)).image (N * ·)).card : ℝ) * (c₂ / (s:ℝ)^d)
      ≤ ∑ r ∈ (Finset.Icc (s^2) (2 * s^2)).image (N * ·), lazyKilled B r x y := (by
    have h := Finset.card_nsmul_le_sum ((Finset.Icc (s^2) (2 * s^2)).image (N * ·))
      (fun r => lazyKilled B r x y) (c₂ / (s:ℝ)^d) hle
    simpa [nsmul_eq_mul] using h)
  have hsum2 : (s:ℝ)^2 * (c₂ / (s:ℝ)^d)
      ≤ ∑ r ∈ (Finset.Icc (s^2) (2 * s^2)).image (N * ·), lazyKilled B r x y := (by
    have h1 : (s:ℝ)^2 = ((s^2 : ℕ) : ℝ) := (by rw [Nat.cast_pow])
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcast hXnonneg) hcardle)
  have hsum_le : (s:ℝ)^2 * (c₂ / (s:ℝ)^d)
      ≤ 2 * (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) :=
    le_trans hsum2
        (sum_lazyKilled_le_two_mul_tsum_killedHeat hd B x y ((Finset.Icc (s^2) (2 * s^2)).image (N *
            ·)))
  have hP : c₂ * ((s:ℝ)^2 / (s:ℝ)^d) = (s:ℝ)^2 * (c₂ / (s:ℝ)^d) := (by ring)
  rw [killedGreenReal_eq_tsum_killedHeat_div hd B x y]
  simp only [zpow_sub₀ hsd0, zpow_natCast]
  calc c₂ / (4 * (d:ℝ)) * ((s:ℝ)^2 / (s:ℝ)^d)
      = (c₂ * ((s:ℝ)^2 / (s:ℝ)^d)) / (4 * (d:ℝ)) := (by ring)
    _ = ((s:ℝ)^2 * (c₂ / (s:ℝ)^d)) / (4 * (d:ℝ)) := (by rw [hP])
    _ ≤ (2 * (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)) / (4 * (d:ℝ)) :=
          div_le_div_of_nonneg_right hsum_le (le_of_lt h4d)
    _ = (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) / (2 * (d:ℝ)) := (by ring)

end GreenTwoSided

end LatticeProb
