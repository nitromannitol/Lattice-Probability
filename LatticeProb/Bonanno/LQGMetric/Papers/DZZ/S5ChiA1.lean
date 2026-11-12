/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiA1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls0

/-!
# Explicit failure rates for DZZ's "with high probability" steps (D129, packet P-129A, part 1)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`. DZZ Theorem 1.1 (l. 126–139) is an
almost-sure statement, while its inputs, Proposition 3.17 (l. 1505–1517, tails `δ^{cι²}` and
`e^{−(log δ⁻¹)^{0.7}}`) and Proposition 5.1 (l. 2254–2258), are bounds in probability at fixed
`δ`. Following decision D129 (`decisions/DEC-129.md` §2 (S0), §4 P-129A), we keep the rates
explicit (**DEVIATIONS DV-D129-1**: DZZ write "with high probability"; an a.s. statement needs
summable tails along dyadic `δ`, which DZZ's P3.17 provides).

* **`HasRate`**: `P(E_δᶜ) ≤ C(δ^c + e^{−(log δ⁻¹)^{0.7}})` for small `δ` (exactly D129 §4);
* `hasRate_of_le`, **`HasRate.inter`**, `hasRate_biInter_range`, **`HasRate.mono`**,
  `HasRate.of_measure_le`, `HasRate.comp_rpow` (`δ ↦ δ^p`, `p ≥ 1`),
  **`hasRate_of_alphaHighProb`**;
* **`HasRate.ae_eventually`**: Borel–Cantelli along `s·2^{−k}` (mathlib `ae_eventually_notMem`;
  the stretched exponential is summable since `e^{−t^{0.7}} ≤ 6 t^{−2.1}`, own elementary proof);
* rate forms of the concentration glue (proofs copied from `tendsto_prob_gt_of_conc'`,
  `tendsto_prob_lt_of_conc'` (S5Glue, P2-DZZ56) and `dzz_lgd_upper_whpIn'` (S5Walls0)):
  `hasRate_le_of_conc'`, `hasRate_ge_of_conc'`, **`hasRate_upper_of_conc`**,
  **`hasRate_lower_of_conc`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A polynomial-or-stretched-exponential failure rate, summable along every sequence `s·2^{−k}`
(D129 §4, DV-D129-1). -/
def HasRate (P : Measure Ω) (E : ℝ → Set Ω) : Prop :=
  ∃ c C δ₀ : ℝ, 0 < c ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    P (E δ)ᶜ ≤ ENNReal.ofReal (C * (δ ^ c + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ))))

lemma exists_Ioo_of_eventually_nhdsGT {p : ℝ → Prop} (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), p δ) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₁, p δ := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun δ hδ => hsub hδ⟩

lemma rate_le_rate {c c' C δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : c' ≤ c) :
    ENNReal.ofReal (C * (δ ^ c + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)))) ≤
      ENNReal.ofReal (max C 0 * (δ ^ c' + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)))) := by
  apply ENNReal.ofReal_le_ofReal
  have h1 : δ ^ c ≤ δ ^ c' := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hc
  have h2 : 0 ≤ δ ^ c := (Real.rpow_pos_of_pos hδ0 c).le
  have h3 := Real.exp_pos (-(Real.log δ⁻¹) ^ (0.7 : ℝ))
  calc C * (δ ^ c + _) ≤ max C 0 * (δ ^ c + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)

/-- the core estimate: a bound by two rates is a rate -/
lemma hasRate_of_le {P : Measure Ω} {F : ℝ → Set Ω} {c₁ c₂ C₁ C₂ δ₁ : ℝ} (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hδ₁ : 0 < δ₁)
    (h : ∀ δ ∈ Ioo (0 : ℝ) δ₁, P (F δ)ᶜ ≤
      ENNReal.ofReal (C₁ * (δ ^ c₁ + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)))) +
      ENNReal.ofReal (C₂ * (δ ^ c₂ + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ))))) :
    HasRate P F := by
  refine ⟨min c₁ c₂, max C₁ 0 + max C₂ 0, min δ₁ 1, lt_min hc₁ hc₂, lt_min hδ₁ one_pos,
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδ1 : δ < 1 := hδ.2.trans_le (min_le_right _ _)
  have he := Real.exp_pos (-(Real.log δ⁻¹) ^ (0.7 : ℝ))
  have hr := (Real.rpow_pos_of_pos hδ0 (min c₁ c₂)).le
  refine (h δ ⟨hδ0, hδ.2.trans_le (min_le_left _ _)⟩).trans ?_
  refine (add_le_add (rate_le_rate hδ0 hδ1 (min_le_left c₁ c₂))
    (rate_le_rate hδ0 hδ1 (min_le_right c₁ c₂))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_mul]

theorem HasRate.of_measure_le {P : Measure Ω} {E F : ℝ → Set Ω} (h : HasRate P E)
    (hle : ∀ᶠ δ in 𝓝[>] (0 : ℝ), P (F δ)ᶜ ≤ P (E δ)ᶜ) : HasRate P F := by
  obtain ⟨c, C, δ₀, hc, hδ₀, hb⟩ := h
  obtain ⟨δ₁, hδ₁, h1⟩ := exists_Ioo_of_eventually_nhdsGT hle
  refine hasRate_of_le (C₁ := C) (c₂ := 1) (C₂ := 0) hc one_pos (lt_min hδ₀ hδ₁) fun δ hδ => ?_
  rw [zero_mul, ENNReal.ofReal_zero, add_zero]
  exact (h1 δ ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩).trans
    (hb δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩)

theorem HasRate.mono {P : Measure Ω} {E F : ℝ → Set Ω} (h : HasRate P E)
    (hEF : ∀ᶠ δ in 𝓝[>] (0 : ℝ), E δ ⊆ F δ) : HasRate P F :=
  h.of_measure_le (hEF.mono fun _ hδ => measure_mono (compl_subset_compl.2 hδ))

theorem HasRate.inter {P : Measure Ω} {E F : ℝ → Set Ω} (h1 : HasRate P E) (h2 : HasRate P F) :
    HasRate P (fun δ => E δ ∩ F δ) := by
  obtain ⟨c, C, δ₀, hc, hδ₀, hb⟩ := h1
  obtain ⟨c', C', δ₀', hc', hδ₀', hb'⟩ := h2
  refine hasRate_of_le (C₁ := C) (C₂ := C') hc hc' (lt_min hδ₀ hδ₀') fun δ hδ => ?_
  rw [compl_inter]
  exact (measure_union_le _ _).trans (add_le_add
    (hb δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩)
    (hb' δ ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩))

theorem hasRate_biInter_range {P : Measure Ω} {E : ℕ → ℝ → Set Ω} (n : ℕ)
    (h : ∀ i < n, HasRate P (E i)) :
    HasRate P (fun δ => ⋂ i ∈ Finset.range n, E i δ) := by
  induction n with
  | zero =>
    refine ⟨1, 0, 1, one_pos, one_pos, fun δ _ => ?_⟩
    simp
  | succ n ih =>
    refine ((h n (by omega)).inter (ih fun i hi => h i (by omega))).mono
      (Eventually.of_forall fun δ ω hω => ?_)
    simp only [mem_iInter, Finset.mem_range, mem_inter_iff] at hω ⊢
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact hω.2 i hi
    · exact hi ▸ hω.1

theorem hasRate_of_alphaHighProb {P : Measure Ω} {E : ℝ → Set Ω} {α : ℝ} (hα : 0 < α)
    (h : AlphaHighProb P α E) : HasRate P E := by
  obtain ⟨δ₀, hδ₀, hb⟩ := h
  refine ⟨α, 1, δ₀, hα, hδ₀, fun δ hδ => (hb δ hδ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have := Real.exp_pos (-(Real.log δ⁻¹) ^ (0.7 : ℝ))
  linarith

/-- a rate survives `δ ↦ δ^p`, `p ≥ 1` -/
theorem HasRate.comp_rpow {P : Measure Ω} {E : ℝ → Set Ω} (h : HasRate P E) {p : ℝ}
    (hp : 1 ≤ p) : HasRate P (fun δ => E (δ ^ p)) := by
  obtain ⟨c, C, δ₀, hc, hδ₀, hb⟩ := h
  refine hasRate_of_le (C₁ := max C 0) (c₂ := 1) (C₂ := 0) hc one_pos (lt_min hδ₀ one_pos) fun δ hδ => ?_
  rw [zero_mul, ENNReal.ofReal_zero, add_zero]
  have hδ0 := hδ.1
  have hδ1 : δ < 1 := hδ.2.trans_le (min_le_right _ _)
  have hpδ : δ ^ p ≤ δ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hp
  have hpos := Real.rpow_pos_of_pos hδ0 p
  refine (hb _ ⟨hpos, hpδ.trans_lt (hδ.2.trans_le (min_le_left _ _))⟩).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hL : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (one_le_inv₀ hδ0 |>.2 hδ1.le)
  have hlog : Real.log (δ ^ p)⁻¹ = p * Real.log δ⁻¹ := by
    rw [Real.log_inv, Real.log_rpow hδ0, Real.log_inv]; ring
  have h1 : (δ ^ p) ^ c ≤ δ ^ c := Real.rpow_le_rpow hpos.le hpδ hc.le
  have h2 : Real.exp (-(Real.log (δ ^ p)⁻¹) ^ (0.7 : ℝ)) ≤
      Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)) := by
    rw [hlog]
    refine Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow hL ?_ (by norm_num)))
    nlinarith
  have h3 : 0 ≤ (δ ^ p) ^ c + Real.exp (-(Real.log (δ ^ p)⁻¹) ^ (0.7 : ℝ)) := by positivity
  calc C * ((δ ^ p) ^ c + _) ≤ max C 0 * ((δ ^ p) ^ c +
        Real.exp (-(Real.log (δ ^ p)⁻¹) ^ (0.7 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h3
    _ ≤ max C 0 * (δ ^ c + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (le_max_right _ _)

/-- `e^{−t^{0.7}} ≤ 6 t^{−2.1}` for `t > 0` (own elementary proof: `x³/3! ≤ eˣ`). -/
lemma exp_neg_rpow_le {t : ℝ} (ht : 0 < t) :
    Real.exp (-t ^ (0.7 : ℝ)) ≤ 6 * (t ^ (2.1 : ℝ))⁻¹ := by
  have hx : 0 ≤ t ^ (0.7 : ℝ) := (Real.rpow_pos_of_pos ht _).le
  have h := Real.pow_div_factorial_le_exp _ hx 3
  have h3 : (t ^ (0.7 : ℝ)) ^ 3 = t ^ (2.1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  rw [h3, show ((Nat.factorial 3 : ℕ) : ℝ) = 6 by norm_num] at h
  have hp := Real.rpow_pos_of_pos ht (2.1 : ℝ)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  rw [inv_le_iff_one_le_mul₀' (Real.exp_pos _)]
  rw [div_le_iff₀ (by norm_num)] at h
  rw [← mul_div_assoc, le_div_iff₀ hp]
  linarith

lemma summable_exp_neg_rpow_mul {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℕ => Real.exp (-((k : ℝ) * a) ^ (0.7 : ℝ)) := by
  refine (summable_nat_add_iff 1).1 ?_
  have hs : Summable fun k : ℕ => 6 * a⁻¹ ^ (2.1 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-(2.1 : ℝ)) := by
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : -(2.1 : ℝ) < -1))
    simpa using this
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun k => ?_) hs
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  refine (exp_neg_rpow_le (mul_pos hk ha)).trans (le_of_eq ?_)
  rw [Real.mul_rpow hk.le ha.le, Real.rpow_neg hk.le, Real.inv_rpow ha.le, mul_inv]
  ring

/-- **Borel–Cantelli along `s·2^{−k}`** (mathlib `ae_eventually_notMem`). -/
theorem HasRate.ae_eventually {P : Measure Ω} {E : ℝ → Set Ω} (h : HasRate P E) {s : ℝ}
    (hs : 0 < s) : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ E (s * (2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨c, C, δ₀, hc, hδ₀, hb⟩ := h
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (lt_min hδ₀ one_pos) hs)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hsN : s * (2 : ℝ)⁻¹ ^ N < min δ₀ 1 := by
    rw [lt_div_iff₀ hs] at hN; linarith
  have hsN0 : 0 < s * (2 : ℝ)⁻¹ ^ N := by positivity
  set g : ℕ → ℝ := fun k => max C 0 * (((2 : ℝ)⁻¹ ^ c) ^ k +
    Real.exp (-((k : ℝ) * Real.log 2) ^ (0.7 : ℝ))) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg (le_max_right _ _) (by positivity)
  have hgs : Summable g := by
    refine Summable.mul_left _ (Summable.add (summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one (by norm_num) (by norm_num) hc)) ?_)
    exact summable_exp_neg_rpow_mul (Real.log_pos (by norm_num))
  have hbound : ∀ k : ℕ, P (E (s * (2 : ℝ)⁻¹ ^ (k + N)))ᶜ ≤ ENNReal.ofReal (g k) := by
    intro k
    set δ := s * (2 : ℝ)⁻¹ ^ (k + N) with hδ
    have hδe : δ = (s * (2 : ℝ)⁻¹ ^ N) * (2 : ℝ)⁻¹ ^ k := by rw [hδ, pow_add]; ring
    have hδ0 : 0 < δ := by positivity
    have hδk : δ ≤ (2 : ℝ)⁻¹ ^ k := by
      rw [hδe]
      calc _ ≤ 1 * (2 : ℝ)⁻¹ ^ k := mul_le_mul_of_nonneg_right
            (hsN.le.trans (min_le_right _ _)) (by positivity)
        _ = _ := one_mul _
    have hδ1 : δ < min δ₀ 1 := by
      rw [hδe]
      calc _ ≤ s * (2 : ℝ)⁻¹ ^ N * 1 := mul_le_mul_of_nonneg_left
            (pow_le_one₀ (by norm_num) (by norm_num)) hsN0.le
        _ < min δ₀ 1 := by rw [mul_one]; exact hsN
    refine (hb δ ⟨hδ0, hδ1.trans_le (min_le_left _ _)⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    have hlog : (k : ℝ) * Real.log 2 ≤ Real.log δ⁻¹ := by
      have h1 : Real.log δ⁻¹ = Real.log (s * (2 : ℝ)⁻¹ ^ N)⁻¹ + k * Real.log 2 := by
        rw [hδe, mul_inv, Real.log_mul (by positivity) (by positivity)]
        congr 1
        rw [Real.log_inv, Real.log_pow, Real.log_inv]; ring
      have h2 : 0 ≤ Real.log (s * (2 : ℝ)⁻¹ ^ N)⁻¹ :=
        Real.log_nonneg ((one_le_inv₀ hsN0).2 (hsN.le.trans (min_le_right _ _)))
      linarith
    have hk0 : 0 ≤ (k : ℝ) * Real.log 2 := by positivity
    have h1 : δ ^ c ≤ ((2 : ℝ)⁻¹ ^ c) ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul
        (by norm_num), Real.rpow_natCast]
      exact Real.rpow_le_rpow hδ0.le hδk hc.le
    have h2 : Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)) ≤
        Real.exp (-((k : ℝ) * Real.log 2) ^ (0.7 : ℝ)) :=
      Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow hk0 hlog (by norm_num)))
    have h3 : 0 ≤ δ ^ c + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)) := by positivity
    calc C * (δ ^ c + _) ≤ max C 0 * (δ ^ c + Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ g k := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (le_max_right _ _)
  have htsum : (∑' k, P (E (s * (2 : ℝ)⁻¹ ^ (k + N)))ᶜ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hgs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨K + N, fun k hk => ?_⟩
  have := hK (k - N) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at this
  simpa using this

/-! ### Rate forms of the concentration glue -/

/-- rate form of `tendsto_prob_gt_of_conc'` (S5Glue), same proof -/
theorem hasRate_le_of_conc' {P : Measure Ω} {X : ℝ → Ω → ℝ} {χ c : ℝ} (hc : 0 < c)
    (hconc : ∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2)
      fun δ => {ω | |X δ ω - ∫ ω', X δ ω' ∂P| ≤ ι * Real.log δ⁻¹})
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ ω, X δ ω ∂P) / Real.log δ⁻¹ < χ + ε)
    {ι : ℝ} (hι : 0 < ι) :
    HasRate P (fun δ => {ω | X δ ω ≤ (χ + ι) * Real.log δ⁻¹}) := by
  set ι' := min (ι / 2) (1 / 2)
  have hι' : ι' ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num)⟩
  refine (hasRate_of_alphaHighProb (by have := hι'.1; positivity) (hconc ι' hι')).mono ?_
  filter_upwards [eventually_Ioo_nhdsGT one_pos, hup (ι / 2) (by linarith)] with δ hδ hEδ ω hω
  have hL := log_inv_pos_of_mem hδ
  simp only [mem_ofPred_eq] at hω ⊢
  rw [div_lt_iff₀ hL] at hEδ
  have : ι' * Real.log δ⁻¹ ≤ ι / 2 * Real.log δ⁻¹ :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le
  have := le_abs_self (X δ ω - ∫ ω', X δ ω' ∂P)
  nlinarith

/-- **rate form of `dzz_lgd_upper_whpIn`** (S5Walls0; DZZ P3.17 + the exponent of the mean):
`P[min D_δ(A_δ,B_δ) > δ^{−χ−ι}] ≤ rate`. -/
theorem hasRate_upper_of_conc {P : Measure Ω} {μ : Ω → Measure ℂ} {K : Set ℂ} {ξ χ : ℝ}
    (h317 : DZZProp317In P μ K ξ) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ)
    (hexp : Tendsto (fun δ => (∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ∂P) / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 χ))
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤)
    {ι : ℝ} (hι : 0 < ι) :
    HasRate P (fun δ => {ω | ((lgdMinSet (μ ω) δ (A δ) (B δ) : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι)))}) := by
  obtain ⟨c, hc, h⟩ := h317
  have hX := hasRate_le_of_conc' (χ := χ) hc (fun ι hι => (h A B hAB hin).1 ι hι)
    (fun ε hε => hexp (Iio_mem_nhds (by linarith))) hι
  refine hX.of_measure_le ?_
  filter_upwards [hfin, self_mem_nhdsWithin] with δ hfδ hδ
  have hnull : P {ω | ¬ lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤} = 0 := ae_iff.mp hfδ
  calc _ ≤ P ({ω | logMinLGD (μ ω) δ (A δ) (B δ) ≤ (χ + ι) * Real.log δ⁻¹}ᶜ ∪
        {ω | ¬ lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤}) := measure_mono (fun ω hω => ?_)
    _ ≤ _ + _ := measure_union_le _ _
    _ = _ := by rw [hnull, add_zero]
  by_cases htop : lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤
  · left
    simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop.ne
    have h1 := one_le_lgdMinSet (μ ω) δ (A δ) (B δ)
    rw [← hn] at h1 hω
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    intro hle
    apply hω
    have hlog : Real.log n ≤ (χ + ι) * Real.log δ⁻¹ := by
      unfold logMinLGD at hle; rw [← hn] at hle; simpa using hle
    have : (n : ℝ) ≤ δ ^ (-(χ + ι)) := by
      rw [← exp_mul_log_inv (mem_Ioi.mp hδ), ← Real.exp_log (by linarith : (0 : ℝ) < n)]
      exact Real.exp_le_exp.mpr hlog
    rw [show (((n : ℕ∞) : ℝ≥0∞)) = ENNReal.ofReal n by simp]
    exact ENNReal.ofReal_le_ofReal this
  · right; exact htop

end DZZ
end LQGMetric
