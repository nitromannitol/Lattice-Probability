/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B2

/-!
# CONF Lemma 2.12 (1) as printed: `confLem2_12aP` (task P2-CONF35b)

Source and plan: see `S3L35B2.lean` (CONF C:785–795; LM Lemma 3.1 = `LM.lmLem3_1a`; D47's
`confLem2_12a_of_LM`). Own elementary reduction (sparse residue classes and a union bound),
proposed DV-CONF-212P.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **CONF Lemma 2.12 (1) as printed** from D47's mod-constant form. -/
theorem confLem2_12aP_of (H : CONFLem2_12a) : CONFLem2_12aP := by
  intro S₁ S₂ hS₁ h12 a ha b hb hb1
  have hS₂1 : 1 < S₂ := by linarith
  have hS₂0 : 0 < S₂ := by linarith
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (4 * S₂) hS₂1
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hm; linarith
    · exact h0
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set b' := (1 + b) / 2 with hb'
  have hbb : b < b' := by rw [hb']; linarith
  have hb'0 : 0 < b' := by linarith
  obtain ⟨p, c', hp, hp1, hc', HH⟩ := H 2 (4 * S₂) one_lt_two (by linarith) (a * m)
    (by positivity) b' hb'0 (by rw [hb']; linarith)
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (2 * b' * m / (b' - b))
  set c := Real.exp (a * K₀) + m * c' * Real.exp (2 * a * m) with hc
  refine ⟨p, c, hp, hp1, by positivity, ?_⟩
  intro Ω _ P _ h hh r E hr hrat hE hpE K
  choose E' hEE' hE'm using fun k => ae_eventMod hh.1 (hr k) hS₁ h12 (hE k)
  have hcnt : P {ω | (countOcc E K ω : ℝ) < b * K} = P {ω | (countOcc E' K ω : ℝ) < b * K} := by
    refine measure_congr ?_
    filter_upwards [ae_all_iff.2 hEE'] with ω hω
    have : ∀ k, (ω ∈ E k ↔ ω ∈ E' k) := fun k => by
      have := hω k
      exact Iff.of_eq this
    change ((countOcc E K ω : ℝ) < b * K) = ((countOcc E' K ω : ℝ) < b * K)
    rw [countOcc_congr' this K]
  have hpE' : ∀ k, ENNReal.ofReal p ≤ P (E' k) := fun k => by
    rw [← measure_congr (hEE' k)]; exact hpE k
  rw [hcnt]
  by_cases hK : (K : ℝ) < K₀
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 ≤ Real.exp (a * K₀) * Real.exp (-a * K) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have h2 : 0 ≤ m * c' * Real.exp (2 * a * m) * Real.exp (-a * K) := by positivity
    rw [hc, add_mul]
    linarith
  push Not at hK
  set K' := K / m - 1 with hK'
  have hdiv := Nat.div_mul_le_self K m
  have hlt := Nat.lt_div_mul_add (a := K) (b := m) (by omega)
  have hKK : ∀ i, 1 ≤ i → i ≤ K' → m * i + m ≤ K + 1 := by
    intro i hi1 hiK
    have h0 : 1 ≤ K / m := by omega
    have hmi : m * i ≤ m * K' := Nat.mul_le_mul_left m hiK
    have : m * K' + m = K / m * m := by
      rw [hK', Nat.mul_sub, mul_one, mul_comm m (K / m)]
      have : m ≤ K / m * m := by nlinarith
      omega
    omega
  have hK'r : (K : ℝ) / m - 2 ≤ K' := by
    have h3 : (K : ℝ) < (K / m : ℕ) * m + m := by exact_mod_cast hlt
    have h4 : ((K / m : ℕ) : ℝ) - 1 ≤ K' := by
      rw [hK']
      have := Nat.sub_le_sub_right (le_refl (K / m)) 1
      rcases Nat.eq_zero_or_pos (K / m) with h0 | h0
      · rw [h0]; simp
      · rw [Nat.cast_sub (by omega)]; simp
    have h5 : (K : ℝ) / m < (K / m : ℕ) + 1 := by
      rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  -- the union bound over residue classes
  have hsub : {ω | (countOcc E' K ω : ℝ) < b * K} ⊆
      ⋃ j ∈ Finset.range m, {ω | (countOcc (fun i => E' (m * i + j)) K' ω : ℝ) < b' * K'} := by
    intro ω hω
    by_contra hall
    simp only [mem_iUnion, mem_ofPred_eq, Finset.mem_range, not_exists, not_lt] at hall hω
    have hsum := sum_countOcc_le E' hm1 hKK ω
    have hsumR : ((∑ j ∈ Finset.range m, countOcc (fun i => E' (m * i + j)) K' ω : ℕ) : ℝ) ≤
        countOcc E' K ω := by exact_mod_cast hsum
    have hge : (m : ℝ) * (b' * K') ≤
        ((∑ j ∈ Finset.range m, countOcc (fun i => E' (m * i + j)) K' ω : ℕ) : ℝ) := by
      push_cast
      have := Finset.sum_le_sum (s := Finset.range m) fun j hj => hall j (Finset.mem_range.1 hj)
      simpa [Finset.sum_const, Finset.card_range] using this
    have hK₀' : 2 * b' * m ≤ (b' - b) * K := by
      have := (div_le_iff₀ (by linarith : 0 < b' - b)).1 hK₀
      nlinarith
    have : (m : ℝ) * (b' * ((K : ℝ) / m - 2)) ≤ m * (b' * K') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK'r hb'0.le) (by linarith)
    have e : (m : ℝ) * (b' * ((K : ℝ) / m - 2)) = b' * K - 2 * b' * m := by
      field_simp
    nlinarith
  have hj : ∀ j ∈ Finset.range m,
      P {ω | (countOcc (fun i => E' (m * i + j)) K' ω : ℝ) < b' * K'} ≤
        ENNReal.ofReal (c' * Real.exp (-(a * m) * K')) := fun j _ => by
    refine HH P h hh (fun i => r (m * i + j) / 4) (fun i => E' (m * i + j))
      (fun i => by have := hr (m * i + j); positivity) (fun i => ?_) (fun i ρ _ => ?_)
      (fun i => hpE' _) K'
    · have hk := rad_pow_le hS₂0.le hr hrat (m * i + j) m
      have e : m * i + j + m = m * (i + 1) + j := by ring
      rw [e] at hk
      have hpos := hr (m * i + j)
      rw [div_div_div_cancel_right₀ (by norm_num : (4 : ℝ) ≠ 0), le_div_iff₀ hpos]
      nlinarith
    · have e1 : 2 * (r (m * i + j) / 4) = r (m * i + j) / 2 := by ring
      have e2 : 4 * S₂ * (r (m * i + j) / 4) = S₂ * r (m * i + j) := by ring
      rw [e1, e2]
      exact hE'm _ fun ω => -circleAvg (h ω) ρ 0
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum hj).trans ?_))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : Real.exp (-(a * m) * K') ≤ Real.exp (2 * a * m) * Real.exp (-a * K) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : (m : ℝ) * ((K : ℝ) / m - 2) = K - 2 * m := by field_simp
    have h6 : (K : ℝ) - 2 * m ≤ m * K' := by
      rw [← this]; exact mul_le_mul_of_nonneg_left hK'r (by linarith)
    nlinarith
  have h7 : (m : ℝ) * (c' * Real.exp (-(a * m) * K')) ≤
      m * c' * Real.exp (2 * a * m) * Real.exp (-a * K) := by
    have := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ m * c')
    nlinarith
  have h8 : 0 ≤ Real.exp (a * K₀) * Real.exp (-a * K) := by positivity
  rw [hc, add_mul]
  linarith

/-- **CONF Lemma 2.12 (1) as printed** (C:785–795), proved from LM Lemma 3.1. -/
theorem confLem2_12aP : CONFLem2_12aP :=
  confLem2_12aP_of (confLem2_12a_of_LM LM.lmLem3_1a)

end LQGMetric.CONF
