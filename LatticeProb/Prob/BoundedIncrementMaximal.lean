import Mathlib.Probability.Moments.SubGaussian
import LatticeProb.Prob.SubGaussianMaximal

/-!
# Maximal Hoeffding bounds for bounded independent centred increments

For independent centred real random variables `ξ i` with `|ξ i| ≤ r` almost surely, the running
maximum of the absolute partial sums up to time `m` exceeds `n ≥ 0` with probability at most
`2 exp (-n² / (2 m r²))` (`measure_exists_abs_partialSum_ge_le`).  For independent increments in
`ℝ^d` whose coordinates are centred and bounded by `r`, the running maximum of the Euclidean norm of
the partial sums exceeds `n` with probability at most `2 d exp (-n² / (2 d m r²))`
(`measure_exists_sqNorm_partialSum_ge_le`, stated with the sum of squares of the coordinates).

The proofs combine Hoeffding's lemma (a centred variable in `[-r, r]` is sub-Gaussian with variance
proxy `r²`) with the maximal sub-Gaussian tail `measure_exists_partialSum_ge_le`, applied to the
increments and to their negatives, and a union bound over the coordinates.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- A centred random variable bounded by `r` almost surely is sub-Gaussian with variance proxy
`r ^ 2`. -/
lemma hasSubgaussianMGF_of_abs_le {X : Ω → ℝ} {r : ℝ≥0} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂P, |X ω| ≤ r) (h0 : ∫ ω, X ω ∂P = 0) :
    HasSubgaussianMGF X (r ^ 2) P := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := P) (X := X)
    (a := -(r : ℝ)) (b := r) hX.aemeasurable (hb.mono fun ω hω => abs_le.1 hω) h0
  have hn : ‖(r : ℝ) - -(r : ℝ)‖₊ = 2 * r := by
    apply NNReal.eq
    simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_ofNat]
    rw [sub_neg_eq_add, ← two_mul, Real.norm_of_nonneg (by positivity)]
  rwa [hn, mul_div_cancel_left₀ _ (two_ne_zero)] at h

/-- **Maximal Hoeffding bound.** For independent centred random variables bounded in absolute
value by `r`, the running maximum of the absolute partial sums over the first `m` increments
reaches `n ≥ 0` with probability at most `2 exp (-n² / (2 m r²))`. -/
theorem measure_exists_abs_partialSum_ge_le (ξ : ℕ → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ i, Measurable (ξ i)) {r : ℝ≥0} (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ r)
    (h0 : ∀ i, ∫ ω, ξ i ω ∂P = 0) (m : ℕ) (hm : 0 < m) {n : ℝ} (hn : 0 ≤ n) :
    P.real {ω | ∃ k ≤ m, n ≤ |∑ i ∈ Finset.range k, ξ i ω|} ≤
      2 * Real.exp (-(n ^ 2) / (2 * m * (r : ℝ) ^ 2)) := by
  have hsg : ∀ i, HasSubgaussianMGF (ξ i) (r ^ 2) P := fun i =>
    hasSubgaussianMGF_of_abs_le (hmeas i) (hb i) (h0 i)
  have h1 := measure_exists_partialSum_ge_le ξ hind hmeas (r ^ 2) hsg m hm hn
  have hind' : iIndepFun (fun i ω => -ξ i ω) P :=
    hind.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have h2 := measure_exists_partialSum_ge_le (fun i ω => -ξ i ω) hind'
    (fun i => (hmeas i).neg) (r ^ 2) (fun i => (hsg i).neg) m hm hn
  simp only [Finset.sum_neg_distrib, NNReal.coe_pow] at h1 h2
  calc P.real {ω | ∃ k ≤ m, n ≤ |∑ i ∈ Finset.range k, ξ i ω|}
      ≤ P.real ({ω | ∃ k ≤ m, n ≤ ∑ i ∈ Finset.range k, ξ i ω} ∪
          {ω | ∃ k ≤ m, n ≤ -∑ i ∈ Finset.range k, ξ i ω}) := by
        refine measureReal_mono ?_
        rintro ω ⟨k, hk, hω⟩
        rcases le_abs'.1 hω with h | h
        · exact Or.inr ⟨k, hk, by linarith⟩
        · exact Or.inl ⟨k, hk, h⟩
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- **Maximal Hoeffding bound in `ℝ^d`.** For independent random vectors `ξ i` in `Fin d → ℝ`
whose coordinates are centred and bounded in absolute value by `r`, the running maximum of the
squared Euclidean norm of the partial sums over the first `m` increments reaches `n² ≥ 0` with
probability at most `2 d exp (-n² / (2 d m r²))`. -/
theorem measure_exists_sqNorm_partialSum_ge_le {d : ℕ} (hd : 0 < d)
    (ξ : ℕ → Ω → Fin d → ℝ) (hind : iIndepFun ξ P) (hmeas : ∀ i, Measurable (ξ i))
    {r : ℝ≥0} (hb : ∀ i j, ∀ᵐ ω ∂P, |ξ i ω j| ≤ r)
    (h0 : ∀ i j, ∫ ω, ξ i ω j ∂P = 0) (m : ℕ) (hm : 0 < m) {n : ℝ} (hn : 0 ≤ n) :
    P.real {ω | ∃ k ≤ m, n ^ 2 ≤ ∑ j, (∑ i ∈ Finset.range k, ξ i ω j) ^ 2} ≤
      2 * d * Real.exp (-(n ^ 2) / (2 * d * m * (r : ℝ) ^ 2)) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hn' : 0 ≤ n / Real.sqrt d := div_nonneg hn (Real.sqrt_nonneg _)
  have hsq : (n / Real.sqrt d) ^ 2 = n ^ 2 / d := by
    rw [div_pow, Real.sq_sqrt hdR.le]
  have hcoord : ∀ j : Fin d, P.real {ω | ∃ k ≤ m, n / Real.sqrt d ≤
      |∑ i ∈ Finset.range k, ξ i ω j|} ≤
        2 * Real.exp (-(n ^ 2) / (2 * d * m * (r : ℝ) ^ 2)) := by
    intro j
    have hindj : iIndepFun (fun i ω => ξ i ω j) P :=
      hind.comp (fun _ => fun x : Fin d → ℝ => x j) (fun _ => measurable_pi_apply j)
    have := measure_exists_abs_partialSum_ge_le (fun i ω => ξ i ω j) hindj
      (fun i => (measurable_pi_apply j).comp (hmeas i)) (fun i => hb i j) (fun i => h0 i j) m hm hn'
    refine this.trans (le_of_eq ?_)
    rw [hsq]
    congr 2
    field_simp
  calc P.real {ω | ∃ k ≤ m, n ^ 2 ≤ ∑ j, (∑ i ∈ Finset.range k, ξ i ω j) ^ 2}
      ≤ P.real (⋃ j : Fin d, {ω | ∃ k ≤ m, n / Real.sqrt d ≤
          |∑ i ∈ Finset.range k, ξ i ω j|}) := by
        refine measureReal_mono ?_
        rintro ω ⟨k, hk, hω⟩
        by_contra hcon
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_and, not_le] at hcon
        have hlt : ∀ j : Fin d, (∑ i ∈ Finset.range k, ξ i ω j) ^ 2 < n ^ 2 / d := by
          intro j
          have := hcon j k hk
          rw [← hsq, ← sq_abs]
          exact pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
        have : ∑ j : Fin d, (∑ i ∈ Finset.range k, ξ i ω j) ^ 2 < ∑ _j : Fin d, n ^ 2 / d :=
          Finset.sum_lt_sum_of_nonempty ⟨⟨0, hd⟩, Finset.mem_univ _⟩ fun j _ => hlt j
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
        rw [mul_div_cancel₀ _ hdR.ne'] at this
        exact absurd hω (not_le.2 this)
    _ ≤ ∑ j : Fin d, P.real {ω | ∃ k ≤ m, n / Real.sqrt d ≤ |∑ i ∈ Finset.range k, ξ i ω j|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin d, 2 * Real.exp (-(n ^ 2) / (2 * d * m * (r : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end LatticeProb
