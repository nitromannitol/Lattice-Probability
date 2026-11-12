/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1GaussMom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1Gauss

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.1, Step 4: first and second moments, Paley–Zygmund (T:2507–2536)

Source: Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, `lqg-metric-estimates-final.tex`,
proof of Proposition 4.1, Step 4. For a centered Gaussian vector `(X_k)_{k<n}` with
`Var X_k ≥ ℓ - A₀` and `Cov(X_j, X_k) ≤ ℓ - log(|j-k|+1) + A₀` (these are (4.6)–(4.7),
T:2508–2516, with `ℓ = log ε⁻¹`; for `j ≠ k`, `log(1/(ε|k-j|)) ≤ ℓ - log(|k-j|+1) + log 2`), and
`n ≥ κ e^ℓ` (`k₂ - k₁ ≍ ε⁻¹`), we get
* (T:2518–2521) `E ∑ e^{ξ X_k} ≥ n e^{ξ²(ℓ-A₀)/2}`,
* (T:2524–2531) `E (∑ e^{ξ X_k})² ≤ 2 e^{2ξ²(ℓ+A₀)} n^{2-ξ²}/(1-ξ²)` (uses `ξ < 1`),
* (T:2533–2536, Paley–Zygmund) `P[∑ e^{ξ X_k} ≥ a ε^{-1-ξ²/2}] ≥ a'` with `a, a'` depending only
  on `κ, ξ, A₀`: `probB_ge`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped NNReal

namespace LQGMetric.DFGPS.P41

/-- `|i - j|` on `ℕ` -/
def dN (i j : ℕ) : ℕ := i - j + (j - i)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
  {X : Ω → Fin n → ℝ}

omit [IsProbabilityMeasure P] in
lemma eval_gauss (hX : HasGaussianLaw X P) (i : Fin n) :
    HasGaussianLaw (fun ω => X ω i) P :=
  HasGaussianLaw.eval (X := fun i ω => X ω i) hX i

/-- `E[e^{ξX_i} e^{ξX_j}] = e^{ξ² Var(X_i+X_j)/2}` -/
lemma pair_moment (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) (ξ : ℝ)
    (i j : Fin n) :
    Integrable (fun ω => exp (ξ * X ω i) * exp (ξ * X ω j)) P ∧
      ∫ ω, exp (ξ * X ω i) * exp (ξ * X ω j) ∂P =
        exp (ξ ^ 2 * (Var[fun ω => X ω i; P] + 2 * cov[fun ω => X ω i, fun ω => X ω j; P] +
          Var[fun ω => X ω j; P]) / 2) := by
  have hY : HasGaussianLaw (fun ω => X ω i + X ω j) P :=
    (HasGaussianLaw.prodMk (X := fun i ω => X ω i) hX i j).fun_add
  have hm : ∫ ω, (X ω i + X ω j) ∂P = 0 := by
    rw [integral_add (eval_gauss hX i).integrable (eval_gauss hX j).integrable, h0, h0, add_zero]
  have e : (fun ω => exp (ξ * X ω i) * exp (ξ * X ω j)) = fun ω => exp (ξ * (X ω i + X ω j)) := by
    funext ω; rw [← exp_add, mul_add]
  rw [e, ← variance_fun_add (eval_gauss hX i).memLp_two (eval_gauss hX j).memLp_two]
  exact gauss_exp_moment hY hm ξ

/-- the sum `∑_k e^{ξ X_k}` -/
def sumExp (X : Ω → Fin n → ℝ) (ξ : ℝ) (ω : Ω) : ℝ := ∑ i, exp (ξ * X ω i)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
lemma sq_sumExp (ξ : ℝ) (ω : Ω) :
    sumExp X ξ ω ^ 2 = ∑ i, ∑ j, exp (ξ * X ω i) * exp (ξ * X ω j) := by
  rw [sumExp, sq, Finset.sum_mul_sum]

lemma integrable_sumExp (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) (ξ : ℝ) :
    Integrable (sumExp X ξ) P ∧
      ∫ ω, sumExp X ξ ω ∂P = ∑ i, exp (ξ ^ 2 * Var[fun ω => X ω i; P] / 2) := by
  have hi : ∀ i, Integrable (fun ω => exp (ξ * X ω i)) P := fun i =>
    (gauss_exp_moment (eval_gauss hX i) (h0 i) ξ).1
  have hs : sumExp X ξ = fun ω => ∑ i, exp (ξ * X ω i) := rfl
  refine ⟨?_, ?_⟩
  · rw [hs]; exact integrable_finsetSum _ fun i _ => hi i
  · rw [hs, integral_finsetSum _ fun i _ => hi i]
    exact Finset.sum_congr rfl fun i _ => (gauss_exp_moment (eval_gauss hX i) (h0 i) ξ).2

lemma integrable_sq_sumExp (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) (ξ : ℝ) :
    Integrable (fun ω => sumExp X ξ ω ^ 2) P ∧
      ∫ ω, sumExp X ξ ω ^ 2 ∂P = ∑ i, ∑ j,
        exp (ξ ^ 2 * (Var[fun ω => X ω i; P] + 2 * cov[fun ω => X ω i, fun ω => X ω j; P] +
          Var[fun ω => X ω j; P]) / 2) := by
  simp_rw [sq_sumExp]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (pair_moment hX h0 ξ i j).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (pair_moment hX h0 ξ i j).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (pair_moment hX h0 ξ i j).1]
  exact Finset.sum_congr rfl fun j _ => (pair_moment hX h0 ξ i j).2

/-- second moment bound (T:2524–2531) -/
lemma second_moment_le (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) {ξ ℓ A0 : ℝ}
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hcov : ∀ i j : Fin n, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
      ℓ - log ((dN i j : ℝ) + 1) + A0) :
    ∫ ω, sumExp X ξ ω ^ 2 ∂P ≤
      exp (2 * ξ ^ 2 * (ℓ + A0)) * (n * (2 * ((n : ℝ) ^ (1 - ξ ^ 2) / (1 - ξ ^ 2)))) := by
  rw [(integrable_sq_sumExp hX h0 ξ).2]
  have hs0 : 0 ≤ ξ ^ 2 := sq_nonneg ξ
  have hs1 : ξ ^ 2 < 1 := by nlinarith
  have hvar : ∀ i : Fin n, Var[fun ω => X ω i; P] ≤ ℓ + A0 := by
    intro i
    have := hcov i i
    rw [covariance_self (eval_gauss hX i).aemeasurable] at this
    simpa [dN] using this
  have hterm : ∀ i j : Fin n, exp (ξ ^ 2 * (Var[fun ω => X ω i; P] +
      2 * cov[fun ω => X ω i, fun ω => X ω j; P] + Var[fun ω => X ω j; P]) / 2) ≤
      exp (2 * ξ ^ 2 * (ℓ + A0)) * (((dN i j : ℕ) : ℝ) + 1) ^ (-ξ ^ 2) := by
    intro i j
    have hd : (0 : ℝ) < ((dN i j : ℕ) : ℝ) + 1 := by positivity
    rw [rpow_def_of_pos hd, ← exp_add]
    refine exp_le_exp.2 ?_
    have h1 := hvar i
    have h2 := hvar j
    have h3 := hcov i j
    nlinarith
  calc ∑ i, ∑ j, _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        exp (2 * ξ ^ 2 * (ℓ + A0)) * (((dN i j : ℕ) : ℝ) + 1) ^ (-ξ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = exp (2 * ξ ^ 2 * (ℓ + A0)) * ∑ i : Fin n, ∑ j : Fin n,
        (((dN i j : ℕ) : ℝ) + 1) ^ (-ξ ^ 2) := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
        have hrow : ∀ i : Fin n, ∑ j : Fin n, (((dN i j : ℕ) : ℝ) + 1) ^ (-ξ ^ 2) ≤
            2 * ((n : ℝ) ^ (1 - ξ ^ 2) / (1 - ξ ^ 2)) := by
          intro i
          have := sum_dist_le (g := fun d : ℕ => ((d : ℝ) + 1) ^ (-ξ ^ 2))
            (fun d => (rpow_pos_of_pos (by positivity) _).le) i.2
          rw [← Fin.sum_univ_eq_sum_range (fun j => ((((i : ℕ) - j + (j - i) : ℕ) : ℝ) + 1) ^
            (-ξ ^ 2)) n] at this
          refine this.trans ?_
          gcongr
          exact sum_rpow_neg_le hs0 hs1 n
        calc _ ≤ ∑ _i : Fin n, 2 * ((n : ℝ) ^ (1 - ξ ^ 2) / (1 - ξ ^ 2)) :=
              Finset.sum_le_sum fun i _ => hrow i
          _ = _ := by simp

/-- **Paley–Zygmund step** (T:2533–2536): `P[∑ e^{ξX_k} ≥ a e^{(1+ξ²/2)ℓ}] ≥ a'` with
`a = κ e^{-ξ²A₀/2}/2`, `a' = κ^{ξ²} e^{-3ξ²A₀} (1-ξ²)/8`. -/
theorem probB_ge (hXm : Measurable X) (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0)
    {ξ κ ℓ A0 : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hn : κ * exp ℓ ≤ n)
    (hvar : ∀ i, ℓ - A0 ≤ Var[fun ω => X ω i; P])
    (hcov : ∀ i j : Fin n, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
      ℓ - log ((dN i j : ℝ) + 1) + A0) :
    κ ^ (ξ ^ 2) * exp (-3 * ξ ^ 2 * A0) * (1 - ξ ^ 2) / 8 ≤
      P.real {ω | κ * exp (-ξ ^ 2 * A0 / 2) / 2 * exp ((1 + ξ ^ 2 / 2) * ℓ) ≤ sumExp X ξ ω} := by
  set s := ξ ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg ξ
  have hs1 : s < 1 := by nlinarith
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hn
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 ⟨⟨0, by exact_mod_cast hn0⟩⟩
  obtain ⟨hSi, hES⟩ := integrable_sumExp hX h0 ξ
  obtain ⟨hS2i, hES2⟩ := integrable_sq_sumExp hX h0 ξ
  have hM2 := second_moment_le hX h0 hξ0 hξ1 hcov
  set E := ∫ ω, sumExp X ξ ω ∂P
  set m2 := ∫ ω, sumExp X ξ ω ^ 2 ∂P
  set E1 := (n : ℝ) * exp (s * (ℓ - A0) / 2)
  have hE1 : E1 ≤ E := by
    rw [hES]
    calc E1 = ∑ _i : Fin n, exp (s * (ℓ - A0) / 2) := by simp [E1]
      _ ≤ _ := Finset.sum_le_sum fun i _ => exp_le_exp.2 (by
          have := mul_le_mul_of_nonneg_left (hvar i) hs0; linarith)
  have hm2 : 0 < m2 := by
    rw [hES2]
    exact Finset.sum_pos (fun i _ => Finset.sum_pos (fun j _ => exp_pos _) hne) hne
  have hSm : Measurable (sumExp X ξ) := by
    unfold sumExp
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_const.mul ((measurable_pi_apply i).comp hXm)).exp
  have hS0 : ∀ ω, 0 ≤ sumExp X ξ ω := fun ω =>
    Finset.sum_nonneg fun i _ => (exp_pos _).le
  have hPZ := paley_zygmund hSm hS0 hSi hS2i hm2 (θ := 1 / 2) (by norm_num) (by norm_num)
  set M2 := exp (2 * s * (ℓ + A0)) * (n * (2 * ((n : ℝ) ^ (1 - s) / (1 - s))))
  have h1s : 0 < 1 - s := by linarith
  have hM2pos : 0 < M2 := by positivity
  -- `κ^s e^{-3sA₀}(1-s)/2 ≤ E1²/M2`
  have hkey : κ ^ s * exp (-3 * s * A0) * (1 - s) / 2 * M2 ≤ E1 ^ 2 := by
    have hpow : (κ * exp ℓ) ^ s ≤ (n : ℝ) ^ s := rpow_le_rpow (by positivity) hn hs0
    rw [mul_rpow hκ.le (exp_pos ℓ).le, ← exp_mul] at hpow
    have hnn : (n : ℝ) ^ s * (n : ℝ) ^ (1 - s) = n := by
      rw [← rpow_add hn0, add_sub_cancel, rpow_one]
    have hq : 0 ≤ (n : ℝ) ^ (1 - s) := (rpow_pos_of_pos hn0 _).le
    have e1 : κ ^ s * exp (-3 * s * A0) * (1 - s) / 2 * M2 =
        (κ ^ s * exp (ℓ * s)) * (n : ℝ) ^ (1 - s) * ((n : ℝ) * exp (s * (ℓ - A0))) := by
      simp only [M2]
      have : exp (-3 * s * A0) * exp (2 * s * (ℓ + A0)) = exp (ℓ * s) * exp (s * (ℓ - A0)) := by
        rw [← exp_add, ← exp_add]; ring_nf
      have hc : (1 - s) / 2 * (2 * ((n : ℝ) ^ (1 - s) / (1 - s))) = (n : ℝ) ^ (1 - s) := by
        field_simp
      calc κ ^ s * exp (-3 * s * A0) * (1 - s) / 2 *
            (exp (2 * s * (ℓ + A0)) * (n * (2 * ((n : ℝ) ^ (1 - s) / (1 - s)))))
          = κ ^ s * (exp (-3 * s * A0) * exp (2 * s * (ℓ + A0))) * n *
            ((1 - s) / 2 * (2 * ((n : ℝ) ^ (1 - s) / (1 - s)))) := by ring
        _ = _ := by rw [this, hc]; ring
    have e2 : E1 ^ 2 = (n : ℝ) ^ s * (n : ℝ) ^ (1 - s) * ((n : ℝ) * exp (s * (ℓ - A0))) := by
      rw [hnn]; simp only [E1]; rw [mul_pow, sq (exp _), ← exp_add]; ring_nf
    rw [e1, e2]
    gcongr
  have hratio : κ ^ s * exp (-3 * s * A0) * (1 - s) / 8 ≤ (1 - 1 / 2) ^ 2 * E ^ 2 / m2 := by
    have h1 : κ ^ s * exp (-3 * s * A0) * (1 - s) / 2 ≤ E1 ^ 2 / M2 :=
      (le_div_iff₀ hM2pos).2 hkey
    have h2 : E1 ^ 2 / M2 ≤ E ^ 2 / m2 :=
      div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (by positivity) hE1 2) hm2 hM2
    have : (1 - 1 / 2 : ℝ) ^ 2 * E ^ 2 / m2 = (E ^ 2 / m2) / 4 := by ring
    rw [this]; linarith
  refine hratio.trans (hPZ.trans (measureReal_mono (fun ω hω => ?_)))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine le_trans ?_ hω
  have : κ * exp (-s * A0 / 2) / 2 * exp ((1 + s / 2) * ℓ) = (κ * exp ℓ) * exp (s * (ℓ - A0) / 2) / 2 := by
    rw [mul_div_assoc, mul_comm (κ * _) _]
    have : exp (-s * A0 / 2) * exp ((1 + s / 2) * ℓ) = exp ℓ * exp (s * (ℓ - A0) / 2) := by
      rw [← exp_add, ← exp_add]; ring_nf
    linear_combination (κ / 2) * this
  rw [this]
  have := mul_le_mul_of_nonneg_right hn (exp_pos (s * (ℓ - A0) / 2)).le
  linarith

end LQGMetric.DFGPS.P41
