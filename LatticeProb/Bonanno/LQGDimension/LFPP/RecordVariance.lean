/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordVariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordVarianceAux3

/-!
# Node `V47`: the variance bound (4.7) of Lemma 4.1

We prove `Blueprint.Draft.RecordVariance` with `C = 32256` and `c₀ = 1/32`.

Proof (files `RecordVarianceAux1`–`RecordVarianceAux3`).

1. **Per configuration** (`local_good`, `cfgGood_cfgMap`).  A configuration
   `c_i = cfgMap (s i) c⁰` with `c⁰` in the normalized local family satisfies the hypotheses of
   Lemma 3.1 at scale `R_i = |α_i|`: chord and polygon are probability combinations with growth
   constant `7 g_i` (`g_i = gFactor M δ (1/32) (k i)`), coupled within `6 R_i δ √(k_i+1)`.
   * Small excess: the coupling pairs each edge with the chord piece of the same normalized
     arclength; the vertices are within `√(S² - R²)/2 ≤ 3 R δ √(k+1)` (`vert_close`,
     `excess_facts`).  The growth is `≤ 2m/S ≤ 7M` in general, and universal when
     `δ²(k+1) ≤ 1/(32M)`: then the excess `S - R ≤ 4RA` is at most a quarter of any edge, so
     every edge advances along the chord at rate `≥ 3/4` (`forward_of_excess`), and the
     projection onto the chord shows `μ(B(z,t)) ≤ 8t/(3S)` (`forward_growth`).
   * Large excess: `k = ⌊δ⁻²⌋` gives `δ√(k+1) > 1`, a coupling within `5R` of the two chords,
     and growth `O(M)` from the child chord of length `≥ R/(2M)`; here `g = M`.
2. **Pairs** (`pair_bound`, `pair_arith`).  For `i ≤ j`, Lemma 3.1 with the coarse pair `i`
   (`TwoScale.circCov_twoScale_bound`, and its reversed form for the entry `(j, i)`) and
   `R_j ≤ 4^{-(j-i)} R_i` give
   `δ⁻¹ |Cov_ij| ≤ 10752 (g_i (k_i+1)^{1/4}) (g_j (k_j+1)^{1/4}) 2^{-(j-i)}`.
3. **Summation** (`circCov_sumComb`, `quad_sum_le`): bilinearity and the geometric Schur test
   give `δ⁻¹ Var ≤ 3 · 10752 Σ g_i² √(k_i+1)`.

No blueprint hypotheses are needed: the two-scale bound is imported from the proved node `L31`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension

open Blueprint.Draft RecVar

/-- **Node `V47`** (`Blueprint.Draft.RecordVariance`, (4.7)). -/
theorem recordVariance : Blueprint.Draft.RecordVariance := by
  refine ⟨3 * 10752, 1 / 32, by norm_num, ?_⟩
  intro n hn δ hδ ε _ l s large k c hs hscale hlarge hc
  have hδ0 : 0 < δ := hδ.1
  -- per-configuration hypotheses of Lemma 3.1
  have hgood : ∀ i < l, CfgGood (7 * gFactor (16 ^ n) δ (1 / 32) (k i)) (‖(s i).1‖ * 1)
      (‖(s i).1‖ * (6 * δ * √((k i : ℝ) + 1))) (c i) := by
    intro i hi
    obtain ⟨c0, hc0, hci⟩ := hc i hi
    rw [← hci]
    exact cfgGood_cfgMap (hs i hi) (local_good hn hδ0 hδ.2 (hlarge i hi) hc0)
  have hg1 : ∀ i, 1 ≤ gFactor (16 ^ n) δ (1 / 32) (k i) := fun i => by
    have : (1 : ℝ) ≤ ((16 ^ n : ℕ) : ℝ) := by
      push_cast; exact one_le_pow₀ (by norm_num)
    unfold gFactor; split_ifs <;> linarith
  have hsc := scale_le hn hscale
  -- the pairwise bounds
  have hX : ∀ i j, i ≤ j → j < l →
      |δ⁻¹ * (cfgComb (c i)).circCov ε (cfgComb (c j))| ≤
          10752 * (gFactor (16 ^ n) δ (1 / 32) (k i) * √(√((k i : ℝ) + 1))) *
            (gFactor (16 ^ n) δ (1 / 32) (k j) * √(√((k j : ℝ) + 1))) * (1 / 2) ^ (j - i) ∧
      |δ⁻¹ * (cfgComb (c j)).circCov ε (cfgComb (c i))| ≤
          10752 * (gFactor (16 ^ n) δ (1 / 32) (k i) * √(√((k i : ℝ) + 1))) *
            (gFactor (16 ^ n) δ (1 / 32) (k j) * √(√((k j : ℝ) + 1))) * (1 / 2) ^ (j - i) := by
    intro i j hij hjl
    have hil : i < l := lt_of_le_of_lt hij hjl
    have hRi : 0 < ‖(s i).1‖ := norm_pos_iff.2 (hs i hil)
    have hRj : 0 < ‖(s j).1‖ := norm_pos_iff.2 (hs j hjl)
    have hw : ∀ m, 0 ≤ 6 * δ * √((k m : ℝ) + 1) := fun m =>
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    obtain ⟨b1, b2⟩ := pair_bound (by simpa using hRi) (by simpa using hRj)
      (mul_nonneg hRi.le (hw i)) (mul_nonneg hRj.le (hw j)) (hgood i hil) (hgood j hjl) ε
    exact ⟨pair_arith hδ0 hRi (hsc i j hij hjl) (hg1 i) (hg1 j) b1,
      pair_arith hδ0 hRi (hsc i j hij hjl) (hg1 i) (hg1 j) b2⟩
  have hsum := quad_sum_le (fun i j => δ⁻¹ * (cfgComb (c i)).circCov ε (cfgComb (c j)))
    (fun i => gFactor (16 ^ n) δ (1 / 32) (k i) * √(√((k i : ℝ) + 1))) (by norm_num) l hX
  rw [circCov_sumComb]
  calc δ⁻¹ * ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range l,
        (cfgComb (c i)).circCov ε (cfgComb (c j))
      = ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range l,
          δ⁻¹ * (cfgComb (c i)).circCov ε (cfgComb (c j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ 3 * 10752 * ∑ i ∈ Finset.range l,
          (gFactor (16 ^ n) δ (1 / 32) (k i) * √(√((k i : ℝ) + 1))) ^ 2 := hsum
    _ = 3 * 10752 * ∑ i ∈ Finset.range l,
          gFactor (16 ^ n) δ (1 / 32) (k i) ^ 2 * √((k i : ℝ) + 1) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by
          rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]

end LQGDimension
