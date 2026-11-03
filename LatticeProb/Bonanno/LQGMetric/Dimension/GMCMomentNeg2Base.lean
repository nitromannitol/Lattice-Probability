/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg2Base at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg2Lap

/-!
# Laplace transform of discrete GMC sums: the inputs of the recursion (P2-NEGMOM)

For `lapGM Z P n j t = E e^{-t gM_n([0,1]²)}` (level-`j` Riemann sum):

* `DGMC.LogCorr.integral_gM_grid_rpow_le_apriori_neg` : the a priori bound
  `E gM_n(grid j)^q ≤ e^{q(q−1)(β n log 2 + c)/2}` for `q ≤ 0` (AM–GM and convexity of `exp`);
* `DGMC.LogCorr.lapGM_le_div` : `lapGM n j t ≤ e^{β n log 2 + c}/t` (from `e^{-x} ≤ 1/x`);
* `DGMC.LogCorr.exists_lapGM_le_one_sub` : Paley–Zygmund-type bound `lapGM n j t ≤ 1 − ε`
  for `t ≥ 2`, uniformly in `n ≤ j`, from `E gM = 1` and the uniform `q`-th moment (`q > 1`);
* `DGMC.LogCorr.lapGM_rec` : the recursion `lapGM (m+l) (m+k) t ≤ e^{3V}/t + lapGM l k (√t 4^{-m})^N`.

Molchan's Laplace-transform argument as adapted by Robert–Vargas (arXiv:0807.1030, proof of
Prop. 3.6, `main.tex` l. 1031–1037); see `GMCMomentNeg2Lap.lean` and decision D63.  The
Paley–Zygmund step (non-degeneracy of the limit) is the standard one (own elementary
arrangement, avoiding indicator functions).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

/-- the Laplace transform of the discrete chaos mass of `[0,1]²` -/
def lapGM (Z : ℕ → ℂ → Ω → ℝ) (P : Measure Ω) (n j : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (-(t * gM (Z n) P j (grid j) ω)) ∂P

lemma lapGM_nonneg (n j : ℕ) (t : ℝ) : 0 ≤ lapGM Z P n j t :=
  integral_nonneg fun _ => (Real.exp_pos _).le

lemma grid_nonempty' (j : ℕ) : (grid j).Nonempty :=
  ⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩

lemma card_grid_mul (j : ℕ) : ((grid j).card : ℝ) * (4 : ℝ)⁻¹ ^ j = 1 := by
  rw [card_grid, inv_pow, mul_inv_cancel₀ (by positivity)]

lemma card_grid_inv (j : ℕ) : ((grid j).card : ℝ)⁻¹ = (4 : ℝ)⁻¹ ^ j := by
  rw [card_grid, inv_pow]

/-- pointwise Jensen for `q ≤ 0`: `gM^q ≤ ∑ 4^{-j} e^{q(Z − Var/2)}` -/
lemma gM_grid_rpow_le_of_nonpos (Zn : ℂ → Ω → ℝ) (j : ℕ) {q : ℝ} (hq : q ≤ 0) (ω : Ω) :
    gM Zn P j (grid j) ω ^ q ≤ ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j *
      Real.exp (q * (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2)) := by
  have h := gM_ge_exp (P := P) Zn j (grid_nonempty' j) ω
  rw [card_grid_mul, one_mul, card_grid_inv] at h
  refine (Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) h hq).trans ?_
  rw [← Real.exp_mul]
  have hc := convexOn_exp.map_sum_le (t := grid j) (w := fun _ => (4 : ℝ)⁻¹ ^ j)
    (p := fun i => q * (Zn (cpt j i) ω - Var[Zn (cpt j i); P] / 2)) (fun _ _ => by positivity)
    (sum_grid_weight j) (fun _ _ => mem_univ _)
  simp only [smul_eq_mul] at hc
  refine le_trans (le_of_eq ?_) hc
  congr 1
  rw [Finset.sum_mul]
  exact sum_congr rfl fun i _ => by ring

/-- **a priori bound for negative moments** at fixed scale, uniform in the grid level -/
theorem LogCorr.integral_gM_grid_rpow_le_apriori_neg (hZ : LogCorr Z P β c) (n j : ℕ) {q : ℝ}
    (hq : q ≤ 0) :
    ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P ≤
      Real.exp (q * (q - 1) * (β * (n * Real.log 2) + c) / 2) := by
  have := hZ.isProb
  calc ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P
      ≤ ∫ ω, ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j *
          Real.exp (q * (Z n (cpt j i) ω - Var[Z n (cpt j i); P] / 2)) ∂P :=
        integral_mono (hZ.integrable_gM_rpow_nonpos n j (grid_nonempty' j) hq)
          (integrable_finsetSum _ fun i _ => ((hZ.integral_exp n (cpt j i) q).1.const_mul _))
          fun ω => gM_grid_rpow_le_of_nonpos _ j hq ω
    _ = ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j * Real.exp (q * (q - 1) * Var[Z n (cpt j i); P] / 2) := by
        rw [integral_finsetSum _ fun i _ => ((hZ.integral_exp n (cpt j i) q).1.const_mul _)]
        refine sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, (hZ.integral_exp n (cpt j i) q).2]
    _ ≤ ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j *
          Real.exp (q * (q - 1) * (β * (n * Real.log 2) + c) / 2) := by
        refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Real.exp_le_exp.2 ?_
        have h1 := hZ.variance_le n (cpt_mem_unitSq hi)
        have h2 : 0 ≤ q * (q - 1) := mul_nonneg_of_nonpos_of_nonpos hq (by linarith)
        have := mul_le_mul_of_nonneg_left h1 h2
        linarith
    _ = _ := by rw [← sum_mul, sum_grid_weight, one_mul]

lemma LogCorr.integrable_exp_neg_gM (hZ : LogCorr Z P β c) (n j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (-(t * gM (Z n) P j (grid j) ω))) P := by
  have := hZ.isProb
  refine Integrable.of_bound ((hZ.measurable_gM n j _).const_mul t).neg.exp.aestronglyMeasurable
    1 (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg ht (gM_nonneg _ _ _ _)

/-- **Laplace bound at a fixed scale** : `lapGM n j t ≤ e^{β n log 2 + c}/t` -/
lemma LogCorr.lapGM_le_div (hZ : LogCorr Z P β c) (n j : ℕ) {t : ℝ} (ht : 0 < t) :
    lapGM Z P n j t ≤ Real.exp (β * (n * Real.log 2) + c) / t := by
  have := hZ.isProb
  have hint := hZ.integrable_gM_rpow_nonpos n j (grid_nonempty' j) (q := -1) (by norm_num)
  have hpt : ∀ ω, Real.exp (-(t * gM (Z n) P j (grid j) ω)) ≤
      t⁻¹ * gM (Z n) P j (grid j) ω ^ (-1 : ℝ) := fun ω => by
    have hg := gM_pos (P := P) (Z n) j (grid_nonempty' j) ω
    rw [Real.rpow_neg_one, Real.exp_neg, ← mul_inv]
    refine inv_anti₀ (by positivity) ?_
    linarith [Real.add_one_le_exp (t * gM (Z n) P j (grid j) ω)]
  calc lapGM Z P n j t ≤ ∫ ω, t⁻¹ * gM (Z n) P j (grid j) ω ^ (-1 : ℝ) ∂P :=
        integral_mono (hZ.integrable_exp_neg_gM n j ht.le) (hint.const_mul _) hpt
    _ = t⁻¹ * ∫ ω, gM (Z n) P j (grid j) ω ^ (-1 : ℝ) ∂P := integral_const_mul _ _
    _ ≤ t⁻¹ * Real.exp (β * (n * Real.log 2) + c) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (hZ.integral_gM_grid_rpow_le_apriori_neg n j (by norm_num)).trans_eq ?_
        congr 1; ring
    _ = _ := by rw [div_eq_inv_mul]

/-- the pointwise Paley–Zygmund inequality -/
lemma exp_neg_le_one_sub {x t K q : ℝ} (hx : 0 ≤ x) (ht : 2 ≤ t) (hK : 1 ≤ K) (hq : 1 < q) :
    Real.exp (-(t * x)) ≤
      1 - (1 - Real.exp (-1)) * ((x - 1 / 2 - K ^ (1 - q) * x ^ q) / K) := by
  have hθ : 0 ≤ 1 - Real.exp (-1) := by
    have := Real.exp_le_one_iff.2 (by norm_num : (-1 : ℝ) ≤ 0); linarith
  have hK0 : 0 < K := by linarith
  by_cases h : 1 / 2 ≤ x ∧ x ≤ K
  · have h1 : Real.exp (-(t * x)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : (x - 1 / 2 - K ^ (1 - q) * x ^ q) / K ≤ 1 := by
      rw [div_le_one hK0]
      have : 0 ≤ K ^ (1 - q) * x ^ q := by positivity
      linarith
    nlinarith
  · have hr : (x - 1 / 2 - K ^ (1 - q) * x ^ q) / K ≤ 0 := by
      refine div_nonpos_of_nonpos_of_nonneg ?_ hK0.le
      rcases not_and_or.1 h with h | h
      · have : 0 ≤ K ^ (1 - q) * x ^ q := by positivity
        linarith
      · push Not at h
        have hxpos : 0 < x := hK0.trans h
        have : x ≤ K ^ (1 - q) * x ^ q := by
          have e : K ^ (1 - q) * x ^ q = x * (x / K) ^ (q - 1) := by
            have e1 : x ^ q = x * x ^ (q - 1) := by
              rw [← Real.rpow_one_add' hxpos.le (by linarith)]; congr 1; ring
            rw [Real.div_rpow hxpos.le hK0.le, show (1 - q) = -(q - 1) by ring,
              Real.rpow_neg hK0.le, e1]
            have : 0 < K ^ (q - 1) := Real.rpow_pos_of_pos hK0 _
            field_simp
          rw [e]
          have : 1 ≤ (x / K) ^ (q - 1) :=
            Real.one_le_rpow ((one_le_div hK0).2 h.le) (by linarith)
          nlinarith
        linarith
    have : Real.exp (-(t * x)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (by linarith) hx))
    nlinarith

/-- **Paley–Zygmund for the Laplace transform**, uniformly in `n ≤ j` -/
theorem LogCorr.exists_lapGM_le_one_sub (hZ : LogCorr Z P β c) (hβ : 0 < β) (hβ4 : β < 4) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ n j : ℕ, n ≤ j → ∀ t : ℝ, 2 ≤ t → lapGM Z P n j t ≤ 1 - ε := by
  have hP := hZ.isProb
  set q : ℝ := (1 + 4 / β) / 2
  have h4 : 1 < 4 / β := (one_lt_div hβ).2 hβ4
  have hq1 : 1 < q := by simp only [q]; linarith
  have hq : q < 4 / β := by simp only [q]; linarith
  obtain ⟨C, hC⟩ := hZ.exists_uniform_moment hβ hq1 hq
  set C' := max C 1
  set K : ℝ := max 1 ((4 * C') ^ (1 / (q - 1)))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hC'0 : 0 < 4 * C' := by have := le_max_right C 1; positivity
  have hKC : K ^ (1 - q) * C ≤ 1 / 4 := by
    have h1 : K ^ (1 - q) ≤ ((4 * C') ^ (1 / (q - 1))) ^ (1 - q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right _ _) (by linarith)
    rw [← Real.rpow_mul hC'0.le, show 1 / (q - 1) * (1 - q) = -1 by
      field_simp [show q - 1 ≠ 0 by linarith]; ring, Real.rpow_neg_one] at h1
    have h2 : C ≤ C' := le_max_left _ _
    have hC0 : 0 ≤ C := le_trans (integral_nonneg fun ω => by
      exact Real.rpow_nonneg (gM_nonneg _ _ _ _) _) (hC 0 0 le_rfl)
    have hC'p : 0 < C' := lt_of_lt_of_le one_pos (le_max_right C 1)
    calc K ^ (1 - q) * C ≤ (4 * C')⁻¹ * C' := mul_le_mul h1 h2 hC0 (by positivity)
      _ = 1 / 4 := by field_simp
  set θ : ℝ := 1 - Real.exp (-1)
  have hθ0 : 0 < θ := by
    have := Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0); simp only [θ]; linarith
  have hθ1 : θ < 1 := by have := Real.exp_pos (-1); simp only [θ]; linarith
  refine ⟨θ / (4 * K), by positivity, ?_, fun n j hnj t ht => ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  set M := fun ω => gM (Z n) P j (grid j) ω
  have hM := hZ.integrable_gM n j (grid j)
  have hMq := hZ.integrable_gM_grid_rpow n j hq1.le
  have hEM : ∫ ω, M ω ∂P = 1 := by
    rw [hZ.integral_gM, mul_comm, card_grid_mul]
  have hEMq : ∫ ω, M ω ^ q ∂P ≤ C := hC n j hnj
  have hpt : ∀ ω, Real.exp (-(t * M ω)) ≤
      (1 + θ / (2 * K)) + (-(θ / K)) * M ω + (θ * K ^ (1 - q) / K) * M ω ^ q := fun ω => by
    refine (exp_neg_le_one_sub (gM_nonneg _ _ _ _) ht hK1 hq1).trans_eq ?_
    field_simp
    ring
  calc lapGM Z P n j t
      ≤ ∫ ω, ((1 + θ / (2 * K)) + (-(θ / K)) * M ω + (θ * K ^ (1 - q) / K) * M ω ^ q) ∂P :=
        integral_mono (hZ.integrable_exp_neg_gM n j (by linarith))
          (((integrable_const _).add (hM.const_mul _)).add (hMq.const_mul _)) hpt
    _ = (1 + θ / (2 * K)) + (-(θ / K)) * ∫ ω, M ω ∂P +
          (θ * K ^ (1 - q) / K) * ∫ ω, M ω ^ q ∂P := by
        have i1 : Integrable (fun ω => (1 + θ / (2 * K)) + (-(θ / K)) * M ω) P :=
          (integrable_const _).add (hM.const_mul _)
        have i2 : Integrable (fun ω => (θ * K ^ (1 - q) / K) * M ω ^ q) P := hMq.const_mul _
        have i3 : Integrable (fun ω => (-(θ / K)) * M ω) P := hM.const_mul _
        rw [integral_add i1 i2, integral_add (integrable_const _) i3, integral_const,
          integral_const_mul, integral_const_mul]
        simp
    _ ≤ (1 + θ / (2 * K)) + (-(θ / K)) * 1 + (θ / K) * (K ^ (1 - q) * C) := by
        rw [hEM]
        have : (θ * K ^ (1 - q) / K) * ∫ ω, M ω ^ q ∂P ≤ (θ * K ^ (1 - q) / K) * C :=
          mul_le_mul_of_nonneg_left hEMq (by positivity)
        have e : (θ / K) * (K ^ (1 - q) * C) = (θ * K ^ (1 - q) / K) * C := by ring
        linarith
    _ ≤ (1 + θ / (2 * K)) + (-(θ / K)) * 1 + (θ / K) * (1 / 4) := by
        have := mul_le_mul_of_nonneg_left hKC (by positivity : 0 ≤ θ / K)
        linarith
    _ = 1 - θ / (4 * K) := by field_simp; ring

/-- the recursion for `lapGM` with `λ = 2`, `e^{a} = √t` -/
lemma LogCorr.lapGM_rec (hZ : LogCorr Z P β c) (hβ : 0 ≤ β) {t : ℝ} (ht : 0 < t) (m l k : ℕ) :
    lapGM Z P (m + l) (m + k) t ≤
      Real.exp (3 * (β * (m * Real.log 2) + 2 * c)) / t +
        lapGM Z P l k (Real.sqrt t * (4 : ℝ)⁻¹ ^ m) ^ (grp0 m).card := by
  have h := hZ.integral_exp_neg_gM_le hβ ht.le (lam := 2) (by norm_num) (Real.log (Real.sqrt t))
    m l k
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have e1 : t * Real.exp (-Real.log (Real.sqrt t)) = Real.sqrt t := by
    rw [Real.exp_neg, Real.exp_log hs]
    field_simp
    rw [Real.sq_sqrt ht.le]
  have e2 : Real.exp (2 * (2 + 1) * (β * (m * Real.log 2) + 2 * c) / 2 -
      2 * Real.log (Real.sqrt t)) = Real.exp (3 * (β * (m * Real.log 2) + 2 * c)) / t := by
    rw [Real.exp_sub, ← Real.log_rpow hs, Real.exp_log (by positivity), Real.rpow_two,
      Real.sq_sqrt ht.le]
    congr 2; ring
  simp only [e1, e2] at h
  exact h

lemma le_card_grp0 (m : ℕ) : m ≤ (grp0 m).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  have h1 : m ≤ 2 ^ (m - 1) := by
    have := Nat.lt_two_pow_self (n := m - 1); omega
  refine h1.trans ?_
  have h2 : (range (2 ^ (m - 1))).image (fun i => (2 * i, 0)) ⊆ grp0 m := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hu
    have hi' := mem_range.1 hi
    refine mem_filter.2 ⟨mem_grid.2 ⟨?_, by positivity⟩, ?_⟩
    · have : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    · simp [par]
  have h3 := Finset.card_le_card h2
  rwa [Finset.card_image_of_injective _ (fun a b h => by simpa using h), card_range] at h3

end DGMC

end LQGMetric
