/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/BinomialDomination.lean.
-/
import LatticeProb.Prob.BinomialTail
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Binomial domination by iterated conditioning

Let `ℱ` be a filtration indexed by `ℕ`, let `G k ∈ ℱ k` be selection events, and let `A k ∈ ℱ (k + 1)` be
events with `P[A k | ℱ k] ≥ p` almost surely on `G k`. Then, among the first `j` selected indices, the number
of those at which `A k` occurs stochastically dominates `Bin(j, p)`. This file proves the tail bounds that
follow from this domination, by iterated conditioning. The coupling that gives the domination itself is not
formalized.

With `φ = 1 - p + p e^{-λ}`, the process `Z_n = exp(Σ_{k<n} 1_{G k} (-λ 1_{A k} - log φ))` satisfies
`E[Z_n] ≤ 1` (`integral_binomDomWeight_le_one`). By Markov's inequality,
`P[#{k<n : G k} ≥ j, #{k<n : G k ∩ A k} ≤ x] ≤ e^{λx} φ^j` (`measureReal_binomDom_le`), which is the
exponential-Markov bound for `Bin(j, p)`. Taking `λ = 4δ` and applying Hoeffding's lemma in the form
`bernoulli_hoeffding` gives the bound `e^{-2δ²j}` (`measureReal_binomDom_hoeffding`).
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace LatticeProb

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Number of selected indices `k < n` (`ω ∈ G k`). -/
noncomputable def binomDomCount (G : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range n, (G k).indicator 1 ω

/-- Number of selected indices `k < n` at which `A k` occurs. -/
noncomputable def binomDomHits (G A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range n, (G k ∩ A k).indicator 1 ω

/-- The exponential weight `Z_n = exp(Σ_{k<n} 1_{G k} (-λ 1_{A k} - L))`. -/
noncomputable def binomDomWeight (G A : ℕ → Set Ω) (l L : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ k ∈ range n, (G k).indicator (fun ω => -l * (A k).indicator 1 ω - L) ω)

/-- The exponential weight is `exp(-λ · hits - L · count)`. -/
lemma binomDomWeight_eq (G A : ℕ → Set Ω) (l L : ℝ) (n : ℕ) (ω : Ω) :
    binomDomWeight G A l L n ω =
      Real.exp (-l * binomDomHits G A n ω - L * binomDomCount G n ω) := by
  unfold binomDomWeight binomDomHits binomDomCount
  congr 1
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  by_cases hG : ω ∈ G k <;> by_cases hA : ω ∈ A k <;> simp [hG, hA, Set.indicator]

variable (ℱ : Filtration ℕ m0)

/-- The exponential weight `Z_n` is `ℱ n`-measurable when the selection events are adapted and the
success events are adapted one step ahead. -/
lemma measurable_binomDomWeight {G A : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) (l L : ℝ) (n : ℕ) :
    Measurable[ℱ n] (binomDomWeight G A l L n) := by
  unfold binomDomWeight
  refine Measurable.exp (Finset.measurable_sum _ fun k hk => ?_)
  have hk : k + 1 ≤ n := Finset.mem_range.1 hk
  have hA' : MeasurableSet[ℱ n] (A k) := ℱ.mono hk _ (hA k)
  have hG' : MeasurableSet[ℱ n] (G k) := ℱ.mono (by omega) _ (hG k)
  exact Measurable.indicator
    (((measurable_const.indicator hA').const_mul (-l)).sub_const L) hG'

/-- Pointwise upper bound `Z_n ≤ exp(n · (-L))` for `λ ≥ 0` and `L ≤ 0`. -/
lemma binomDomWeight_le {G A : ℕ → Set Ω} {l L : ℝ} (hl : 0 ≤ l) (hL : L ≤ 0) (n : ℕ)
    (ω : Ω) : binomDomWeight G A l L n ω ≤ Real.exp (n * (-L)) := by
  unfold binomDomWeight
  apply Real.exp_le_exp.2
  have : ∀ k ∈ range n, (G k).indicator (fun ω => -l * (A k).indicator 1 ω - L) ω ≤ -L := by
    intro k _
    by_cases hG : ω ∈ G k <;> by_cases hA : ω ∈ A k <;>
      simp [hG, hA, Set.indicator] <;> nlinarith
  calc _ ≤ ∑ k ∈ range n, (-L) := sum_le_sum this
    _ = n * (-L) := by simp

/-- **Iterated conditioning**: `E[Z_n] ≤ 1` for `Z_n = exp(Σ_{k<n} 1_{G k}(-λ 1_{A k} - log φ))`,
`φ = 1 - p + p e^{-λ}`, when `P[A k | ℱ k] ≥ p` a.s. on `G k`. -/
theorem integral_binomDomWeight_le_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G A : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) {p l : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hl : 0 ≤ l)
    (hp : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → p ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω) (n : ℕ) :
    ∫ ω, binomDomWeight G A l (Real.log (1 - p + p * Real.exp (-l))) n ω ∂μ ≤ 1 := by
  set φ := 1 - p + p * Real.exp (-l) with hφ
  have he1 : Real.exp (-l) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hφ0 : 0 < φ := by
    have := Real.exp_pos (-l); nlinarith
  have hφ1 : φ ≤ 1 := by nlinarith
  have hL : Real.log φ ≤ 0 := Real.log_nonpos hφ0.le hφ1
  set L := Real.log φ
  have hAm : ∀ k, MeasurableSet (A k) := fun k => ℱ.le (k + 1) _ (hA k)
  induction n with
  | zero => simp [binomDomWeight]
  | succ n ih =>
    set Z := binomDomWeight G A l L n
    set W : Ω → ℝ := fun ω => Z ω * (G n).indicator 1 ω
    set I : Ω → ℝ := (A n).indicator (fun _ => (1 : ℝ))
    have hZm : Measurable[ℱ n] Z := measurable_binomDomWeight ℱ hG hA l L n
    have hWm : Measurable[ℱ n] W := hZm.mul (measurable_const.indicator (hG n))
    have hZb : ∀ ω, ‖Z ω‖ ≤ Real.exp (n * (-L)) := fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (by simp only [Z, binomDomWeight]; exact Real.exp_pos _)]
      exact binomDomWeight_le hl hL n ω
    have hW0 : ∀ ω, 0 ≤ W ω := fun ω =>
      mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hWb : ∀ ω, ‖W ω‖ ≤ Real.exp (n * (-L)) := fun ω => by
      have h1 : (G n).indicator (1 : Ω → ℝ) ω ≤ 1 := Set.indicator_le_self' (fun _ _ => zero_le_one) ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 ω)]
      calc W ω ≤ Z ω * 1 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ _ := by rw [mul_one]; exact binomDomWeight_le hl hL n ω
    have hZi : Integrable Z μ := Integrable.of_bound
      (hZm.mono (ℱ.le n) le_rfl).aestronglyMeasurable _ (Filter.Eventually.of_forall hZb)
    have hWi : Integrable W μ := Integrable.of_bound
      (hWm.mono (ℱ.le n) le_rfl).aestronglyMeasurable _ (Filter.Eventually.of_forall hWb)
    have hIi : Integrable I μ := (integrable_const (1 : ℝ)).indicator (hAm n)
    have hWIi : Integrable (fun ω => W ω * I ω) μ := by
      refine Integrable.of_bound ((hWm.mono (ℱ.le n) le_rfl).mul
        (measurable_const.indicator (hAm n))).aestronglyMeasurable (Real.exp (n * (-L)))
        (Filter.Eventually.of_forall fun ω => ?_)
      have : I ω ≤ 1 := Set.indicator_le_self' (fun _ _ => zero_le_one) ω
      have : 0 ≤ I ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hW0 ω) this)]
      calc W ω * I ω ≤ W ω * 1 := mul_le_mul_of_nonneg_left (by assumption) (hW0 ω)
        _ ≤ _ := by rw [mul_one]; exact (abs_le.1 (by simpa using hWb ω)).2
    -- pointwise one-step identity
    have hstep : ∀ ω, binomDomWeight G A l L (n + 1) ω =
        Z ω + (φ⁻¹ - 1) * W ω - φ⁻¹ * (1 - Real.exp (-l)) * (W ω * I ω) := by
      intro ω
      have hZ : binomDomWeight G A l L (n + 1) ω =
          Z ω * Real.exp ((G n).indicator (fun ω => -l * (A n).indicator 1 ω - L) ω) := by
        simp only [binomDomWeight, Z, sum_range_succ, Real.exp_add]
      rw [hZ]
      have hexpL : Real.exp (-L) = φ⁻¹ := by rw [Real.exp_neg, Real.exp_log hφ0]
      by_cases hG' : ω ∈ G n <;> by_cases hA' : ω ∈ A n
      · simp only [W, I, Set.indicator_of_mem hG', Set.indicator_of_mem hA', Pi.one_apply]
        rw [show -l * 1 - L = -l + -L by ring, Real.exp_add, hexpL]; ring
      · simp only [W, I, Set.indicator_of_mem hG', Set.indicator_of_notMem hA', Pi.one_apply]
        rw [show -l * 0 - L = -L by ring, hexpL]; ring
      · simp [W, I, Set.indicator_of_notMem hG']
      · simp [W, I, Set.indicator_of_notMem hG']
    -- pull-out: ∫ W I = ∫ W μ[I | ℱ n]
    have hpull : ∫ ω, W ω * I ω ∂μ = ∫ ω, W ω * μ[I | ℱ n] ω ∂μ := by
      rw [← integral_condExp (ℱ.le n) (f := fun ω => W ω * I ω)]
      exact integral_congr_ae (condExp_stronglyMeasurable_mul_of_bound (ℱ.le n)
        hWm.stronglyMeasurable hIi _ (Filter.Eventually.of_forall hWb))
    have hlow : ∫ ω, W ω * p ∂μ ≤ ∫ ω, W ω * μ[I | ℱ n] ω ∂μ := by
      refine integral_mono_ae (hWi.mul_const p) ?_ ?_
      · exact (integrable_condExp (m := ℱ n) (f := I)).bdd_mul (c := Real.exp (n * (-L)))
          (hWm.mono (ℱ.le n) le_rfl).aestronglyMeasurable (Filter.Eventually.of_forall hWb)
      · filter_upwards [hp n] with ω hω
        by_cases hG' : ω ∈ G n
        · exact mul_le_mul_of_nonneg_left (hω hG') (hW0 ω)
        · simp [W, Set.indicator_of_notMem hG']
    have hcoef : 0 ≤ φ⁻¹ * (1 - Real.exp (-l)) := mul_nonneg (inv_nonneg.2 hφ0.le) (by linarith)
    have hkey : (φ⁻¹ - 1) - φ⁻¹ * (1 - Real.exp (-l)) * p = 0 := by
      have h1 : 1 - (1 - Real.exp (-l)) * p = φ := by rw [hφ]; ring
      calc (φ⁻¹ - 1) - φ⁻¹ * (1 - Real.exp (-l)) * p = φ⁻¹ * (1 - (1 - Real.exp (-l)) * p) - 1 := by
            ring
        _ = 0 := by rw [h1, inv_mul_cancel₀ hφ0.ne', sub_self]
    calc ∫ ω, binomDomWeight G A l L (n + 1) ω ∂μ
        = ∫ ω, Z ω ∂μ + (φ⁻¹ - 1) * ∫ ω, W ω ∂μ
            - φ⁻¹ * (1 - Real.exp (-l)) * ∫ ω, W ω * I ω ∂μ := by
          simp_rw [hstep]
          rw [integral_sub (f := fun ω => Z ω + (φ⁻¹ - 1) * W ω)
              (g := fun ω => φ⁻¹ * (1 - Real.exp (-l)) * (W ω * I ω))
              (hZi.add (hWi.const_mul _)) (hWIi.const_mul _),
            integral_add (f := Z) (g := fun ω => (φ⁻¹ - 1) * W ω) hZi (hWi.const_mul _),
            integral_const_mul, integral_const_mul]
      _ ≤ ∫ ω, Z ω ∂μ + (φ⁻¹ - 1) * ∫ ω, W ω ∂μ
            - φ⁻¹ * (1 - Real.exp (-l)) * ∫ ω, W ω * p ∂μ := by
          rw [hpull]; gcongr
      _ = ∫ ω, Z ω ∂μ + ((φ⁻¹ - 1) - φ⁻¹ * (1 - Real.exp (-l)) * p) * ∫ ω, W ω ∂μ := by
          rw [integral_mul_const]; ring
      _ ≤ 1 := by rw [hkey, zero_mul, add_zero]; exact ih

/-- **Binomial domination, exponential form.** Under the iterated-conditioning hypothesis,
`P[#{k<n : G k} ≥ j, #{k<n : G k ∩ A k} ≤ x] ≤ e^{λx} (1 - p + p e^{-λ})^j` for `λ ≥ 0`; the
right side is the exponential-Markov bound for `P[Bin(j,p) ≤ x]`. -/
theorem measureReal_binomDom_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G A : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) {p l : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hl : 0 ≤ l)
    (hp : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → p ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω)
    (n j : ℕ) (x : ℝ) :
    μ.real {ω | (j : ℝ) ≤ binomDomCount G n ω ∧ binomDomHits G A n ω ≤ x} ≤
      Real.exp (l * x) * (1 - p + p * Real.exp (-l)) ^ j := by
  set φ := 1 - p + p * Real.exp (-l) with hφ
  have he1 : Real.exp (-l) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hφ0 : 0 < φ := by
    have := Real.exp_pos (-l); nlinarith
  have hL : Real.log φ ≤ 0 := Real.log_nonpos hφ0.le (by nlinarith)
  set L := Real.log φ
  set Z := binomDomWeight G A l L n
  set ε := Real.exp (-l * x - L * j)
  have hZm : Measurable[ℱ n] Z := measurable_binomDomWeight ℱ hG hA l L n
  have hZi : Integrable Z μ := Integrable.of_bound
    (hZm.mono (ℱ.le n) le_rfl).aestronglyMeasurable (Real.exp (n * (-L)))
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (by simp only [Z, binomDomWeight]; exact Real.exp_pos _)]
      exact binomDomWeight_le hl hL n ω)
  have hZ0 : 0 ≤ᵐ[μ] Z := Filter.Eventually.of_forall fun ω => by
    simp only [Z, binomDomWeight, Pi.zero_apply]; exact (Real.exp_pos _).le
  have hsub : {ω | (j : ℝ) ≤ binomDomCount G n ω ∧ binomDomHits G A n ω ≤ x} ⊆
      {ω | ε ≤ Z ω} := by
    intro ω ⟨h1, h2⟩
    simp only [Set.mem_setOf_eq, Z, binomDomWeight_eq, ε]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hmk := mul_meas_ge_le_integral_of_nonneg hZ0 hZi ε
  have hint := integral_binomDomWeight_le_one ℱ hG hA hp0 hp1 hl hp n
  have hε : 0 < ε := Real.exp_pos _
  have h3 : ε * μ.real {ω | (j : ℝ) ≤ binomDomCount G n ω ∧ binomDomHits G A n ω ≤ x} ≤ 1 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hε.le).trans (hmk.trans hint)
  have h4 : Real.exp (l * x) * φ ^ j = ε⁻¹ := by
    rw [← Real.exp_log hφ0, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
    congr 1; ring
  rw [h4]
  calc μ.real {ω | (j : ℝ) ≤ binomDomCount G n ω ∧ binomDomHits G A n ω ≤ x}
      = ε⁻¹ * (ε * μ.real {ω | (j : ℝ) ≤ binomDomCount G n ω ∧ binomDomHits G A n ω ≤ x}) :=
        (inv_mul_cancel_left₀ hε.ne' _).symm
    _ ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hε.le)
    _ = ε⁻¹ := mul_one _

/-- **Binomial domination + Hoeffding's inequality**: for `q ∈ [0,1]` and `δ ≥ 0`,
`P[#{k<n : G k} ≥ j, #{k<n : G k ∩ A k} ≤ (q - δ) j] ≤ e^{-2δ²j}`. -/
theorem measureReal_binomDom_hoeffding {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G A : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) {q δ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : 0 ≤ δ)
    (hq : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → q ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω)
    (n j : ℕ) :
    μ.real {ω | (j : ℝ) ≤ binomDomCount G n ω ∧ binomDomHits G A n ω ≤ (q - δ) * j} ≤
      Real.exp (-2 * δ ^ 2 * j) := by
  have hmain := measureReal_binomDom_le ℱ hG hA hq0 hq1 (by linarith : (0 : ℝ) ≤ 4 * δ) hq n j
    ((q - δ) * j)
  refine hmain.trans ?_
  have hφ0 : 0 ≤ 1 - q + q * Real.exp (-(4 * δ)) := by
    have := Real.exp_pos (-(4 * δ)); nlinarith
  calc Real.exp (4 * δ * ((q - δ) * j)) * (1 - q + q * Real.exp (-(4 * δ))) ^ j
      ≤ Real.exp (4 * δ * ((q - δ) * j)) * Real.exp (-(4 * δ) * q + (4 * δ) ^ 2 / 8) ^ j := by
        gcongr; exact bernoulli_hoeffding hq0 hq1 _
    _ = Real.exp (-2 * δ ^ 2 * j) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

namespace BinomialDominationExample

/-- The constant filtration on a measurable space `m`: every `seq k` is `m`. -/
def constFiltration {Ω : Type*} (m : MeasurableSpace Ω) : Filtration ℕ m :=
  ⟨fun _ => m, monotone_const, fun _ => le_rfl⟩

/-- Nonvacuity of the hypotheses of `measureReal_binomDom_hoeffding`: on a one-point space with the
constant filtration, the selection and success events `G k = A k = univ` satisfy the adapted-eligibility
hypotheses for every `q ∈ [0, 1]`, since `P[univ | ℱ k] = 1 ≥ q` almost surely. -/
example (μ : Measure Unit) [IsProbabilityMeasure μ] {q δ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : 0 ≤ δ) (n j : ℕ) :
    μ.real {ω | (j : ℝ) ≤ binomDomCount (fun _ => Set.univ) n ω ∧
      binomDomHits (fun _ => Set.univ) (fun _ => Set.univ) n ω ≤ (q - δ) * j} ≤
      Real.exp (-2 * δ ^ 2 * j) :=
  measureReal_binomDom_hoeffding (constFiltration _) (fun _ => MeasurableSet.univ)
    (fun _ => MeasurableSet.univ) hq0 hq1 hδ
    (fun k => Filter.Eventually.of_forall fun _ _ => by
      rw [Set.indicator_univ, condExp_const ((constFiltration _).le k)]
      exact hq1) n j

end BinomialDominationExample

end LatticeProb
