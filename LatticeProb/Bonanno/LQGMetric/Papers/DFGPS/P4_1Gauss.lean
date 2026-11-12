/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1Gauss at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationVector

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.1, Step 4: tools (exponential moments, Paley–Zygmund, a power sum)

Source: Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
percolation*, arXiv:1905.00380, `lqg-metric-estimates-final.tex`, proof of Proposition 4.1,
Step 4 (T:2507–2582).

* `gauss_exp_moment`: "`E[e^X] = e^{Var(X)/2}` for a centered Gaussian `X`" (T:2512), from
  mathlib's `mgf_gaussianReal`.
* `paley_zygmund`: the Paley–Zygmund inequality (T:2533) `P[S ≥ θ E S] ≥ (1-θ)² (E S)²/E S²`
  for `S ≥ 0`; own elementary proof (AM–GM in place of Cauchy–Schwarz).
* `sum_rpow_neg_le`: `∑_{d<n} (d+1)^{-s} ≤ n^{1-s}/(1-s)` for `s ∈ [0,1)`, the bound behind
  `∑_k ∑_j |j-k|^{-ξ²} ≼ ε^{-2+ξ²}` (T:2527–2531); own elementary proof (Bernoulli).
* `sum_dist_le`: `∑_{j<n} g(|i-j|) ≤ 2 ∑_{d<n} g(d)` for `g ≥ 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped NNReal

namespace LQGMetric.DFGPS.P41

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `E[e^{tY}] = e^{t² Var(Y)/2}` for a centered real Gaussian `Y` (T:2512), with integrability. -/
lemma gauss_exp_moment [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (h0 : ∫ ω, Y ω ∂P = 0) (t : ℝ) :
    Integrable (fun ω => exp (t * Y ω)) P ∧
      ∫ ω, exp (t * Y ω) ∂P = exp (t ^ 2 * Var[Y; P] / 2) := by
  have hL : HasLaw Y (gaussianReal 0 Var[Y; P].toNNReal) P :=
    ⟨hY.aemeasurable, by rw [hY.map_eq_gaussianReal, h0]⟩
  have hm := mgf_gaussianReal hL t
  have hv : ((Var[Y; P].toNNReal : ℝ≥0) : ℝ) = Var[Y; P] :=
    Real.coe_toNNReal _ (variance_nonneg _ _)
  rw [hv] at hm
  refine ⟨?_, ?_⟩
  · rw [← mgf_pos_iff, hm]; exact exp_pos _
  · rw [← mgf, hm]; congr 1; ring

/-- **Paley–Zygmund** (T:2533): for `S ≥ 0` with `E S² > 0` and `θ ∈ [0,1]`,
`(1-θ)² (E S)² / E S² ≤ P[S ≥ θ E S]`. Own elementary proof. -/
lemma paley_zygmund [IsProbabilityMeasure P] {S : Ω → ℝ} (hSm : Measurable S)
    (hS0 : ∀ ω, 0 ≤ S ω) (hSi : Integrable S P) (hS2 : Integrable (fun ω => S ω ^ 2) P)
    (hm2 : 0 < ∫ ω, S ω ^ 2 ∂P) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, S ω ∂P) ^ 2 / ∫ ω, S ω ^ 2 ∂P ≤
      P.real {ω | θ * ∫ ω, S ω ∂P ≤ S ω} := by
  set m := ∫ ω, S ω ∂P
  set m2 := ∫ ω, S ω ^ 2 ∂P
  set A := {ω | θ * m ≤ S ω}
  have hA : MeasurableSet A := measurableSet_le measurable_const hSm
  have hm0 : 0 ≤ m := integral_nonneg hS0
  rcases hm0.eq_or_lt with hm | hm
  · rw [← hm]; simp
  set t := (1 - θ) * m / m2
  by_cases hθ : θ = 1
  · simp [hθ]
  have hθ1' : θ < 1 := lt_of_le_of_ne hθ1 hθ
  have ht : 0 < t := div_pos (mul_pos (by linarith) hm) hm2
  -- pointwise: `S ≤ θ m + (t S² + 1_A / t) / 2`
  have hpt : ∀ ω, S ω ≤ θ * m + (t * S ω ^ 2 + A.indicator (fun _ => (1 : ℝ)) ω / t) / 2 := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω]
      have : S ω ≤ (t * S ω ^ 2 + 1 / t) / 2 := by
        have h1 : 0 ≤ (t * S ω - 1) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
        have h2 : (t * S ω - 1) ^ 2 / t = t * S ω ^ 2 + 1 / t - 2 * S ω := by
          field_simp; ring
        linarith
      nlinarith [mul_nonneg hθ0 hm.le]
    · rw [indicator_of_notMem hω, zero_div, add_zero]
      have : S ω < θ * m := not_le.1 hω
      nlinarith [mul_nonneg ht.le (sq_nonneg (S ω))]
  have hint : m ≤ θ * m + (t * m2 + P.real A / t) / 2 := by
    have hI : Integrable (fun ω => θ * m + (t * S ω ^ 2 + A.indicator (fun _ => (1 : ℝ)) ω / t)
        / 2) P := by
      refine (integrable_const _).add (((hS2.const_mul t).add ?_).div_const 2)
      exact ((integrable_const (1 : ℝ)).indicator hA).div_const t
    have := integral_mono hSi hI hpt
    have hJ1 : Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω / t) P :=
      ((integrable_const (1 : ℝ)).indicator hA).div_const t
    have hJ2 : Integrable (fun ω => t * S ω ^ 2) P := hS2.const_mul t
    have hJ3 : Integrable (fun ω => (t * S ω ^ 2 + A.indicator (fun _ => (1 : ℝ)) ω / t) / 2) P :=
      (hJ2.add hJ1).div_const 2
    rw [integral_add (integrable_const _) hJ3, integral_div, integral_add hJ2 hJ1,
      integral_const_mul, integral_div, integral_indicator_const _ hA] at this
    simp only [integral_const_mul] at this
    simpa [smul_eq_mul] using this
  -- solve for `P(A)`
  have hkey : (1 - θ) * m - t * m2 / 2 ≤ P.real A / t / 2 := by linarith
  have htm2 : t * m2 = (1 - θ) * m := by
    simp only [t]; field_simp
  rw [htm2] at hkey
  have : (1 - θ) * m * t ≤ P.real A := by
    have h3 : (1 - θ) * m / 2 ≤ P.real A / t / 2 := by linarith
    have h4 : (1 - θ) * m ≤ P.real A / t := by linarith
    rwa [le_div_iff₀ ht] at h4
  calc (1 - θ) ^ 2 * m ^ 2 / m2 = (1 - θ) * m * t := by simp only [t]; ring
    _ ≤ _ := this

/-- `∑_{d<n} (d+1)^{-s} ≤ n^{1-s}/(1-s)` for `0 ≤ s < 1`. Own elementary proof (Bernoulli). -/
lemma sum_rpow_neg_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (n : ℕ) :
    ∑ d ∈ Finset.range n, ((d : ℝ) + 1) ^ (-s) ≤ (n : ℝ) ^ (1 - s) / (1 - s) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero]
    rw [zero_rpow (by linarith)]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    -- `n^{1-s} ≤ (n+1)^{1-s} - (1-s)(n+1)^{-s}` (Bernoulli)
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb : (n : ℝ) ^ (1 - s) ≤ ((n : ℝ) + 1) ^ (1 - s) - (1 - s) * ((n : ℝ) + 1) ^ (-s) := by
      have hx : (-1 : ℝ) ≤ -((n : ℝ) + 1)⁻¹ := by
        rw [neg_le_neg_iff]; exact inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
      have hB := rpow_one_add_le_one_add_mul_self hx (p := 1 - s) (by linarith) (by linarith)
      have e1 : (n : ℝ) = ((n : ℝ) + 1) * (1 + -((n : ℝ) + 1)⁻¹) := by field_simp; ring
      have e2 : ((n : ℝ) + 1) ^ (-s) = ((n : ℝ) + 1) ^ (1 - s) * ((n : ℝ) + 1)⁻¹ := by
        rw [show -s = (1 - s) + (-1 : ℝ) by ring, rpow_add hN, rpow_neg_one]
      have hpos : 0 < ((n : ℝ) + 1) ^ (1 - s) := rpow_pos_of_pos hN _
      have hx' : 0 ≤ 1 + -((n : ℝ) + 1)⁻¹ := by linarith
      calc (n : ℝ) ^ (1 - s) = ((n : ℝ) + 1) ^ (1 - s) * (1 + -((n : ℝ) + 1)⁻¹) ^ (1 - s) := by
            conv_lhs => rw [e1]
            exact mul_rpow hN.le hx'
        _ ≤ ((n : ℝ) + 1) ^ (1 - s) * (1 + (1 - s) * -((n : ℝ) + 1)⁻¹) :=
            mul_le_mul_of_nonneg_left hB hpos.le
        _ = _ := by rw [e2]; ring
    have h1s : 0 < 1 - s := by linarith
    push_cast
    calc _ ≤ (n : ℝ) ^ (1 - s) / (1 - s) + ((n : ℝ) + 1) ^ (-s) := by linarith
      _ ≤ ((n : ℝ) + 1) ^ (1 - s) / (1 - s) := by
          rw [div_add' _ _ _ h1s.ne', div_le_div_iff_of_pos_right h1s]; linarith

/-- `∑_{j<n} g(|i-j|) ≤ 2 ∑_{d<n} g(d)` for `g ≥ 0` and `i < n`. -/
lemma sum_dist_le {g : ℕ → ℝ} (hg : ∀ d, 0 ≤ g d) {n i : ℕ} (hi : i < n) :
    ∑ j ∈ Finset.range n, g ((i - j + (j - i))) ≤ 2 * ∑ d ∈ Finset.range n, g d := by
  have hsplit : ∑ j ∈ Finset.range n, g ((i - j + (j - i))) =
      ∑ j ∈ (Finset.range n).filter (· ≤ i), g (i - j) +
        ∑ j ∈ (Finset.range n).filter (fun j => ¬ j ≤ i), g (j - i) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (· ≤ i)]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_filter] at hj
      congr 1; omega
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_filter] at hj
      congr 1; omega
  have h1 : ∑ j ∈ (Finset.range n).filter (· ≤ i), g (i - j) ≤ ∑ d ∈ Finset.range n, g d := by
    rw [← Finset.sum_image (f := g) (s := (Finset.range n).filter (· ≤ i)) (g := (i - ·))
      (fun a ha b hb hab => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
        simp only at hab; omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => hg d)
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd ⊢
    obtain ⟨j, ⟨hj, hji⟩, rfl⟩ := hd
    omega
  have h2 : ∑ j ∈ (Finset.range n).filter (fun j => ¬ j ≤ i), g (j - i) ≤
      ∑ d ∈ Finset.range n, g d := by
    rw [← Finset.sum_image (f := g) (s := (Finset.range n).filter (fun j => ¬ j ≤ i))
      (g := (· - i))
      (fun a ha b hb hab => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
        simp only at hab; omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => hg d)
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd ⊢
    obtain ⟨j, ⟨hj, hji⟩, rfl⟩ := hd
    omega
  rw [hsplit]; linarith

end LQGMetric.DFGPS.P41
