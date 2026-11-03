/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4Iter at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# LM Lemma 3.4 / MQ Prop 4.3: the counting step (iteration over scales)

Source: LM arXiv:1905.00379 (`literature/src/1905.00379/local-metrics-final.tex`), Lemma 3.4
(l. 696–706), which refers to MQ arXiv:1812.03913 (`lqg_geodesics.tex`), Prop 4.3 and its proof
(l. 664–733).

MQ explore the field from outside in: the harmonic part at scale `r_{k+j}` equals the harmonic
part at scale `r_k` (whose oscillation on `B_{r_{k+j}}` decays geometrically in `j`, MQ l. 677–681,
"derivative estimate") plus the harmonic part of an independent zero-boundary GFF (MQ l. 693–700,
Remark eq. `(zero-boundary)`, Gaussian tail). They then dominate the waiting time to the next good
scale by a geometric sum of i.i.d. Gaussian-tailed variables and conclude by Markov's inequality
for `exp(a ∑ k_i)` (MQ l. 711–733).

We use the same two inputs (geometric decay of the outer harmonic part, independent increments
with an exponential moment) but replace MQ's stopping-time/geometric-sum bookkeeping by a direct
linear bound (own argument, recorded in `DEVIATIONS.md`): if at every bad scale `k ≤ K`
`M < C ∑_{j ≤ k} q^{k-j} W_j` with `W_j ≥ 0`, `W_j` `𝓕_j`-measurable and independent of `𝓕_{j-1}`,
then summing over the bad scales gives `(1-q)(1-b) M K / C ≤ ∑_{j ≤ K} W_j` on
`{#good < bK}`, and Markov's inequality for `exp(∑ W_j)` (as in MQ l. 728–733) gives
`P[#good < bK] ≤ A^{K+1} e^{-(1-q)(1-b) M K / C}` with `A ≥ sup_j E e^{W_j}`.

* `count_good_tail` — the abstract counting bound above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- the linear filter `T_k = ∑_{j ≤ k} q^{k-j} w_j` -/
def linFilt (q : ℝ) (w : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), q ^ (k - j) * w j

lemma linFilt_succ (q : ℝ) (w : ℕ → ℝ) (k : ℕ) :
    linFilt q w (k + 1) = q * linFilt q w k + w (k + 1) := by
  unfold linFilt
  rw [sum_range_succ, Nat.sub_self, pow_zero, one_mul, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]; ring

lemma linFilt_nonneg {q : ℝ} (hq : 0 ≤ q) {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (k : ℕ) :
    0 ≤ linFilt q w k :=
  sum_nonneg fun j _ => mul_nonneg (pow_nonneg hq _) (hw j)

/-- `(1-q) ∑_{k ≤ K} T_k + q T_K = ∑_{j ≤ K} w_j` -/
lemma linFilt_sum (q : ℝ) (w : ℕ → ℝ) (K : ℕ) :
    (1 - q) * ∑ k ∈ range (K + 1), linFilt q w k + q * linFilt q w K =
      ∑ j ∈ range (K + 1), w j := by
  induction K with
  | zero => simp [linFilt]; ring
  | succ K ih =>
    rw [sum_range_succ, sum_range_succ (fun j => w j), ← ih, linFilt_succ]; ring

/-- the pointwise step: on `{#good < bK}` the sum `∑_{j ≤ K} w_j` is large -/
lemma linFilt_count {Ω : Type} (E : ℕ → Set Ω) (ω : Ω) {q C M b : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (hC : 0 < C) (hM : 0 ≤ M) {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (K : ℕ)
    (hE : ∀ k, 1 ≤ k → ω ∉ E k → M < C * linFilt q w k)
    (hcount : (countOcc E K ω : ℝ) < b * K) :
    (1 - q) * (1 - b) * M / C * K ≤ ∑ j ∈ range (K + 1), w j := by
  classical
  set good := Finset.filter (fun k => ω ∈ E k) (Icc 1 K)
  set bad := Finset.filter (fun k => ω ∉ E k) (Icc 1 K)
  have hcard : (good.card : ℝ) + bad.card = K := by
    have := card_filter_add_card_filter_not (s := Icc 1 K) (fun k => ω ∈ E k)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hgood : (countOcc E K ω : ℝ) = good.card := by
    unfold countOcc; congr 2
  have hT := fun k => linFilt_nonneg hq0 hw k
  have h1 : (bad.card : ℝ) * M ≤ C * ∑ k ∈ range (K + 1), linFilt q w k := by
    calc (bad.card : ℝ) * M = ∑ k ∈ bad, M := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ bad, C * linFilt q w k := sum_le_sum fun k hk => by
          rw [mem_filter, Finset.mem_Icc] at hk
          exact (hE k hk.1.1 hk.2).le
      _ ≤ ∑ k ∈ range (K + 1), C * linFilt q w k := by
          refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => by
            have := hT k; positivity
          rw [mem_filter, Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      _ = C * ∑ k ∈ range (K + 1), linFilt q w k := by rw [mul_sum]
  have h2 := linFilt_sum q w K
  have h3 : 0 ≤ q * linFilt q w K := mul_nonneg hq0 (hT K)
  have h4 : (1 - b) * K * M ≤ bad.card * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have h5 : 0 ≤ 1 - q := by linarith
  have h6 : (1 - q) * ((1 - b) * K * M) ≤ (1 - q) * (C * ∑ k ∈ range (K + 1), linFilt q w k) :=
    mul_le_mul_of_nonneg_left (h4.trans h1) h5
  nlinarith

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- `E[∏_{j ≤ n} e^{W_j}] = ∏_{j ≤ n} E[e^{W_j}]` for adapted increments independent of the past -/
lemma lintegral_prod_exp_indep (P : Measure Ω) (F : ℕ → MeasurableSpace Ω) (hF : Monotone F)
    (hFle : ∀ j, F j ≤ mΩ) (W : ℕ → Ω → ℝ) (hWm : ∀ j, Measurable[F j] (W j))
    (hWi : ∀ j, Indep (MeasurableSpace.comap (W (j + 1)) inferInstance) (F j) P) (n : ℕ) :
    ∫⁻ ω, ∏ j ∈ range (n + 1), ENNReal.ofReal (Real.exp (W j ω)) ∂P =
      ∏ j ∈ range (n + 1), ∫⁻ ω, ENNReal.ofReal (Real.exp (W j ω)) ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : ∀ g : ℕ → ℝ≥0∞, ∏ j ∈ range (n + 1 + 1), g j = (∏ j ∈ range (n + 1), g j) * g (n + 1) :=
      fun g => prod_range_succ g (n + 1)
    simp only [hs]
    rw [← ih]
    have hf : Measurable[F n] fun ω => ∏ j ∈ range (n + 1), ENNReal.ofReal (Real.exp (W j ω)) :=
      Finset.measurable_prod (m := F n) _ fun j hj =>
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          ((hWm j).mono (hF (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) le_rfl))
    have hg : Measurable[MeasurableSpace.comap (W (n + 1)) inferInstance]
        fun ω => ENNReal.ofReal (Real.exp (W (n + 1) ω)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.of_comap_le le_rfl))
    exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace (hFle n)
      ((hWm (n + 1)).comap_le.trans (hFle (n + 1))) (hWi n).symm hf hg

/-- **The counting step of MQ Prop 4.3 / LM Lemma 3.4** (linear-filter form, own bookkeeping):
if at every bad scale `k ∈ [1,K]` `M < C ∑_{j ≤ k} q^{k-j} W_j`, with `W_j ≥ 0` adapted to a
filtration `𝓕`, `W_{j+1}` independent of `𝓕_j` and `E e^{W_j} ≤ A`, then
`P[#good < bK] ≤ A^{K+1} e^{-(1-q)(1-b) M K / C}`. -/
theorem count_good_tail (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → MeasurableSpace Ω)
    (hF : Monotone F) (hFle : ∀ j, F j ≤ mΩ) (W : ℕ → Ω → ℝ) (hW0 : ∀ j ω, 0 ≤ W j ω)
    (hWm : ∀ j, Measurable[F j] (W j))
    (hWi : ∀ j, Indep (MeasurableSpace.comap (W (j + 1)) inferInstance) (F j) P)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ j, ∫⁻ ω, ENNReal.ofReal (Real.exp (W j ω)) ∂P ≤ ENNReal.ofReal A)
    {q C M b : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (hC : 0 < C) (hM : 0 ≤ M) (E : ℕ → Set Ω)
    (hE : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, ω ∉ E k → M < C * ∑ j ∈ range (k + 1), q ^ (k - j) * W j ω)
    (K : ℕ) :
    P.real {ω | (countOcc E K ω : ℝ) < b * K} ≤
      A ^ (K + 1) * Real.exp (-((1 - q) * (1 - b) * M / C * K)) := by
  set θ := (1 - q) * (1 - b) * M / C * K
  set S : Ω → ℝ := fun ω => ∑ j ∈ range (K + 1), W j ω
  have hWm' : ∀ j, Measurable (W j) := fun j => (hWm j).mono (hFle j) le_rfl
  have hS : Measurable S := Finset.measurable_sum _ fun j _ => hWm' j
  have hE' : ∀ᵐ ω ∂P, ∀ k, 1 ≤ k → ω ∉ E k → M < C * linFilt q (fun j => W j ω) k := by
    rw [ae_all_iff]; intro k
    by_cases hk : 1 ≤ k
    · filter_upwards [hE k hk] with ω hω _ h; exact hω h
    · exact Eventually.of_forall fun ω h => absurd h hk
  have hsub : {ω | (countOcc E K ω : ℝ) < b * K} ≤ᵐ[P]
      {ω | ENNReal.ofReal (Real.exp θ) ≤ ENNReal.ofReal (Real.exp (S ω))} := by
    filter_upwards [hE'] with ω hω hc
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (linFilt_count E ω hq0 hq hC hM (fun j => hW0 j ω) K hω hc))
  have hexpS : ∀ ω, ENNReal.ofReal (Real.exp (S ω)) =
      ∏ j ∈ range (K + 1), ENNReal.ofReal (Real.exp (W j ω)) := fun ω => by
    simp only [S, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le
  have hint : ∫⁻ ω, ENNReal.ofReal (Real.exp (S ω)) ∂P ≤ ENNReal.ofReal A ^ (K + 1) := by
    simp_rw [hexpS]
    rw [lintegral_prod_exp_indep P F hF hFle W hWm hWi K]
    exact (prod_le_pow_card _ _ _ fun j _ => hA j).trans_eq (by rw [card_range])
  have hmeas : P {ω | (countOcc E K ω : ℝ) < b * K} ≤
      ENNReal.ofReal (A ^ (K + 1) * Real.exp (-θ)) := by
    refine (measure_mono_ae hsub).trans ((meas_ge_le_lintegral_div
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hS)).aemeasurable
      (by simpa using Real.exp_pos θ) ENNReal.ofReal_ne_top).trans ?_)
    refine (ENNReal.div_le_div_right hint _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow hA0, ← ENNReal.ofReal_div_of_pos (Real.exp_pos θ), Real.exp_neg,
      div_eq_mul_inv]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hmeas

end LQGMetric.LM
