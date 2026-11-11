import Mathlib

/-!
# Deterministic estimates for measures with a power weight at the origin

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
the ingredients of the multiscale argument for arXiv:2208.11795, Lemma 2.4 near the logarithmic singularity (Berestycki and
Gwynne, Random walks on mated-CRT planar maps and Liouville Brownian motion, arXiv:2003.10320, Lemma A.1, p. 66 of v2).
Throughout, `m` and `m₀` are measures on
`ℂ` with `m({0}) = 0` and `m = |x|^e m₀` on `ℂ \ {0}`, the relation between `μ_h` and `μ_{h^ℂ}` for `e = -γα₀`.

* `measure_le_of_rpow_norm_le`, `le_measure_of_le_rpow_norm`: comparison of `m` and `m₀` on sets where the weight is bounded.
* `rpow_le_two_rpow_abs_mul`: `a^e ≤ 2^{|e|} b^e` for `a ∈ [b/2, 2b]`.
* `measure_ball_zero_le_of_dyadic`: the shells `{2^{-j-1} ≤ |x| < 2^{-j}}` bound the mass of `B_{2^{-j₀}}(0)` given bounds
  `m₀(B_{2^{-j}}(0)) ≤ K 2^{-j G₁}` at all dyadic scales `j ≥ j₀` and `G₁ + e > 0`.

Nothing is assumed: this file imports Mathlib only (import rule).
-/

namespace LatticeProb.LQG

open MeasureTheory Metric Set
open scoped ENNReal

/-- `a^e ≤ 2^{|e|} b^e` for `b > 0` and `b/2 ≤ a ≤ 2b`. -/
theorem rpow_le_two_rpow_abs_mul {a b e : ℝ} (hb : 0 < b) (h1 : b / 2 ≤ a) (h2 : a ≤ 2 * b) :
    a ^ e ≤ 2 ^ |e| * b ^ e := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) h1
  have hab : a = a / b * b := by field_simp
  rw [hab, Real.mul_rpow (div_pos ha hb).le hb.le]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hb.le _)
  rcases le_or_gt 0 e with he | he
  · rw [abs_of_nonneg he]
    exact Real.rpow_le_rpow (div_pos ha hb).le ((div_le_iff₀ hb).2 (by linarith)) he
  · rw [abs_of_neg he, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) ((le_div_iff₀ hb).2 (by linarith)) he.le

variable {m m₀ : Measure ℂ} {e : ℝ}

/-- Upper comparison: if `|x|^e ≤ c` on `A \ {0}`, then `m(A) ≤ c m₀(A)`. -/
theorem measure_le_of_rpow_norm_le
    (hW : m.restrict {0}ᶜ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (h0 : m {0} = 0) {A : Set ℂ} (hA : MeasurableSet A) {c : ℝ}
    (hc : ∀ x ∈ A, x ≠ 0 → ‖x‖ ^ e ≤ c) : m A ≤ ENNReal.ofReal c * m₀ A := by
  have hm : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  calc m A ≤ m (A ∩ {0}ᶜ) + m {0} := by
        refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
        by_cases hx0 : x = 0
        · exact Or.inr hx0
        · exact Or.inl ⟨hx, hx0⟩
    _ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)) (A ∩ {0}ᶜ) := by
        rw [h0, add_zero, ← Measure.restrict_apply hA, hW, Measure.restrict_apply hA]
    _ = ∫⁻ x in A ∩ {0}ᶜ, ENNReal.ofReal (‖x‖ ^ e) ∂m₀ := withDensity_apply _ (hA.inter hm)
    _ ≤ ∫⁻ _ in A ∩ {0}ᶜ, ENNReal.ofReal c ∂m₀ :=
        setLIntegral_mono' (hA.inter hm) fun x hx => ENNReal.ofReal_le_ofReal (hc x hx.1 hx.2)
    _ = ENNReal.ofReal c * m₀ (A ∩ {0}ᶜ) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal c * m₀ A := by gcongr; exact inter_subset_left

/-- Lower comparison: if `0 ∉ A` and `c ≤ |x|^e` on `A`, then `c m₀(A) ≤ m(A)`. -/
theorem le_measure_of_le_rpow_norm
    (hW : m.restrict {0}ᶜ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    {A : Set ℂ} (hA : MeasurableSet A) (hA0 : (0 : ℂ) ∉ A) {c : ℝ}
    (hc : ∀ x ∈ A, c ≤ ‖x‖ ^ e) : ENNReal.ofReal c * m₀ A ≤ m A := by
  have hm : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have hA' : A ∩ {0}ᶜ = A := inter_eq_left.2 fun x hx hx0 => hA0 (by rwa [mem_singleton_iff.1 hx0] at hx)
  calc ENNReal.ofReal c * m₀ A = ∫⁻ _ in A ∩ {0}ᶜ, ENNReal.ofReal c ∂m₀ := by
        rw [setLIntegral_const, hA']
    _ ≤ ∫⁻ x in A ∩ {0}ᶜ, ENNReal.ofReal (‖x‖ ^ e) ∂m₀ :=
        setLIntegral_mono' (hA.inter hm) fun x hx => ENNReal.ofReal_le_ofReal (hc x hx.1)
    _ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)) (A ∩ {0}ᶜ) :=
        (withDensity_apply _ (hA.inter hm)).symm
    _ = m A := by rw [← Measure.restrict_apply hA, ← hW, Measure.restrict_apply hA, hA']

/-- The mass of `B_{2^{-j₀}}(0)` from bounds at all dyadic scales `j ≥ j₀`: if
`m₀(B_{2^{-j}}(0)) ≤ K 2^{-j G₁}` for `j ≥ j₀` and `T₁ = G₁ + e > 0`, then
`m(B_{2^{-j₀}}(0)) ≤ 2^{|e|} K 2^{-j₀ T₁} / (1 - 2^{-T₁})`. -/
theorem measure_ball_zero_le_of_dyadic
    (hW : m.restrict {0}ᶜ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (h0 : m {0} = 0) {K G₁ : ℝ} (hK : 0 ≤ K) (hT : 0 < G₁ + e) {j₀ : ℕ}
    (hball : ∀ j : ℕ, j₀ ≤ j → m₀ (ball 0 ((2 : ℝ)⁻¹ ^ j)) ≤ ENNReal.ofReal (K * ((2 : ℝ)⁻¹ ^ j) ^ G₁)) :
    m (ball 0 ((2 : ℝ)⁻¹ ^ j₀)) ≤ ENNReal.ofReal (2 ^ |e| * K * ((2 : ℝ)⁻¹ ^ (G₁ + e)) ^ j₀ /
      (1 - (2 : ℝ)⁻¹ ^ (G₁ + e))) := by
  set q : ℝ := (2 : ℝ)⁻¹ ^ (G₁ + e) with hq_def
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hT
  set S : ℕ → Set ℂ := fun j => ball 0 ((2 : ℝ)⁻¹ ^ j) \ ball 0 ((2 : ℝ)⁻¹ ^ (j + 1)) with hS
  -- the ball minus the origin is covered by the shells `S (j₀ + n)`
  have hcover : ball (0 : ℂ) ((2 : ℝ)⁻¹ ^ j₀) ⊆ {0} ∪ ⋃ n : ℕ, S (j₀ + n) := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    refine Or.inr (mem_iUnion.2 ?_)
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hex : ∃ n : ℕ, (2 : ℝ)⁻¹ ^ (j₀ + n + 1) ≤ ‖x‖ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2 : ℝ)⁻¹ < 1)
      exact ⟨n, le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn.le⟩
    classical
    let n := Nat.find hex
    have hn : (2 : ℝ)⁻¹ ^ (j₀ + n + 1) ≤ ‖x‖ := Nat.find_spec hex
    refine ⟨n, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h, add_zero]; exact mem_ball_zero_iff.1 hx
      · have := Nat.find_min hex (Nat.sub_lt h one_pos)
        rw [not_le] at this
        convert this using 2
        omega
    · rw [mem_ball_zero_iff, not_lt]; exact hn
  have hshell : ∀ n : ℕ, m (S (j₀ + n)) ≤ ENNReal.ofReal (2 ^ |e| * K * q ^ j₀) * ENNReal.ofReal q ^ n := by
    intro n
    set j := j₀ + n
    have hb : 0 < (2 : ℝ)⁻¹ ^ j := by positivity
    have hmeas : MeasurableSet (S j) := measurableSet_ball.diff measurableSet_ball
    calc m (S j) ≤ ENNReal.ofReal (2 ^ |e| * ((2 : ℝ)⁻¹ ^ j) ^ e) * m₀ (S j) := by
          refine measure_le_of_rpow_norm_le hW h0 hmeas fun x hx _ => ?_
          obtain ⟨hx1, hx2⟩ := hx
          rw [mem_ball_zero_iff] at hx1
          rw [mem_ball_zero_iff, not_lt, pow_succ] at hx2
          exact rpow_le_two_rpow_abs_mul hb (by linarith) (by linarith)
      _ ≤ ENNReal.ofReal (2 ^ |e| * ((2 : ℝ)⁻¹ ^ j) ^ e) * ENNReal.ofReal (K * ((2 : ℝ)⁻¹ ^ j) ^ G₁) := by
          gcongr
          exact (measure_mono sdiff_subset).trans (hball j (Nat.le_add_right _ _))
      _ = ENNReal.ofReal (2 ^ |e| * K * q ^ j) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hq_def, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2⁻¹), Real.rpow_add hb]
          ring
      _ = ENNReal.ofReal (2 ^ |e| * K * q ^ j₀) * ENNReal.ofReal q ^ n := by
          rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity), pow_add]
          ring_nf
  calc m (ball 0 ((2 : ℝ)⁻¹ ^ j₀)) ≤ m {0} + m (⋃ n : ℕ, S (j₀ + n)) :=
        (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ 0 + ∑' n : ℕ, ENNReal.ofReal (2 ^ |e| * K * q ^ j₀) * ENNReal.ofReal q ^ n := by
        rw [h0]
        gcongr
        exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hshell)
    _ = ENNReal.ofReal (2 ^ |e| * K * q ^ j₀) * (1 - ENNReal.ofReal q)⁻¹ := by
        rw [zero_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (2 ^ |e| * K * q ^ j₀ / (1 - q)) := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul' (q := (1 - q)⁻¹) (inv_nonneg.2 (by linarith)),
          ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]

end LatticeProb.LQG
