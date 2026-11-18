import LatticeProb.Prob.KernelProkhorovChain

/-!
# Many steps of two Markov chains in the one-sided Prokhorov distance

Let `κ, κ'` be two Markov kernels on a metric space `E`. Write `chainStepLaw κ μ n` for the law
after `n` steps of the chain with kernel `κ` started from the law `μ`. Iterating the one-step
comparison `prokhorovLE_bind_split` gives the `n`-step comparison: if

* the kernels are uniformly `ε`-close, `ProkhorovLE (κ y) (κ' y) ε ε` for every `y`;
* `κ'` is continuous at the thickening radius `r_c` with mass error `η`, at scale `ε + r_c`,
  between starting points `y ∈ H` and `b ∈ G n`;
* the `n`-step laws of `κ` are carried by the measurable set `H` and the `n`-step laws of `κ'`
  give mass at most `ρ` to `(G n)ᶜ`;
* the initial laws satisfy `ProkhorovLE μ ν (ε + r_c) e`,

then `ProkhorovLE (chainStepLaw κ μ n) (chainStepLaw κ' ν n) (ε + r_c) (n * (ε + η + ρ) + e)`
for every `n` (`prokhorovLE_chainStepLaw`): the radius does not grow and the additive errors add up
linearly in the number of steps. For two chains with the same initial law the initial error is
`0` as soon as `0 < ε + r_c` (`prokhorovLE_chainStepLaw_same_start`); with Dirac initial laws this
is the comparison for every starting point.

## Main results

* `chainStepLaw`, `chainStepLaw_zero`, `chainStepLaw_succ`, `isProbabilityMeasure_chainStepLaw`.
* `prokhorovLE_refl`: `ProkhorovLE μ μ r 0` for `0 < r`.
* `prokhorovLE_chainStepLaw`: the `n`-step comparison.
* `prokhorovLE_chainStepLaw_same_start`: the `n`-step comparison from a common initial law.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

variable {E : Type*} [MeasurableSpace E]

/-- The law after `n` steps of the Markov chain with kernel `κ` started from the law `μ`. -/
noncomputable def chainStepLaw (κ : E → Measure E) (μ : Measure E) (n : ℕ) : Measure E :=
  (fun m : Measure E => m.bind κ)^[n] μ

@[simp]
theorem chainStepLaw_zero (κ : E → Measure E) (μ : Measure E) : chainStepLaw κ μ 0 = μ :=
  rfl

theorem chainStepLaw_succ (κ : E → Measure E) (μ : Measure E) (n : ℕ) :
    chainStepLaw κ μ (n + 1) = (chainStepLaw κ μ n).bind κ :=
  Function.iterate_succ_apply' _ n μ

/-- The `n`-step laws of a Markov kernel started from a probability measure are probability
measures. -/
theorem isProbabilityMeasure_chainStepLaw {κ : E → Measure E} (hκ : Measurable κ)
    [∀ y, IsProbabilityMeasure (κ y)] {μ : Measure E} [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (chainStepLaw κ μ n) := by
  induction n with
  | zero => rw [chainStepLaw_zero]; infer_instance
  | succ n ih =>
    rw [chainStepLaw_succ]
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
    simp

variable [PseudoMetricSpace E]

/-- A measure is `(r, 0)`-close to itself in the one-sided Prokhorov sense for every `0 < r`. -/
theorem prokhorovLE_refl (μ : Measure E) {r : ℝ} (hr : 0 < r) : ProkhorovLE μ μ r 0 :=
  fun A _ => le_add_right (measure_mono (self_subset_thickening hr A))

variable [OpensMeasurableSpace E]

/-- **`n` steps of two Markov chains in the one-sided Prokhorov sense.** The kernels `κ, κ'` are
uniformly `ε`-close, `κ'` is continuous at radius `r_c` with mass error `η` at scale `ε + r_c`
between the starting points of `H` and those of `G n`, the `n`-step laws of `κ` are carried by `H`
and the `n`-step laws of `κ'` give mass at most `ρ` to `(G n)ᶜ`. If the initial laws are
`(ε + r_c, e)`-close, the `n`-step laws are `(ε + r_c, n (ε + η + ρ) + e)`-close. -/
theorem prokhorovLE_chainStepLaw {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {κ κ' : E → Measure E} (hκ : Measurable κ) (hκ' : Measurable κ')
    [∀ y, IsProbabilityMeasure (κ y)] [∀ y, IsProbabilityMeasure (κ' y)]
    {ε r_c η ρ e : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hρ0 : 0 ≤ ρ) (he : 0 ≤ e)
    (hP : ProkhorovLE μ ν (ε + r_c) e) (hK : ∀ y, ProkhorovLE (κ y) (κ' y) ε ε)
    {H : Set E} {G : ℕ → Set E} (hH : MeasurableSet H)
    (hμH : ∀ n, chainStepLaw κ μ n Hᶜ = 0)
    (hG : ∀ n, chainStepLaw κ' ν n (G n)ᶜ ≤ ENNReal.ofReal ρ)
    (hcont : ∀ n, ∀ b ∈ G n, ∀ y ∈ H, dist y b < ε + r_c → ∀ A : Set E, MeasurableSet A →
      κ' y A ≤ κ' b (thickening r_c A) + ENNReal.ofReal η) (n : ℕ) :
    ProkhorovLE (chainStepLaw κ μ n) (chainStepLaw κ' ν n) (ε + r_c)
      (n * (ε + η + ρ) + e) := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    have hμn := isProbabilityMeasure_chainStepLaw hκ (μ := μ) n
    have hνn := isProbabilityMeasure_chainStepLaw hκ' (μ := ν) n
    have he' : 0 ≤ (n : ℝ) * (ε + η + ρ) + e :=
      add_nonneg (mul_nonneg n.cast_nonneg (add_nonneg (add_nonneg hε hη) hρ0)) he
    have h := prokhorovLE_bind_split hκ hκ' hε hη hρ0 he' ih hK hH (hμH n) (hG n) (hcont n)
    have heq : ε + η + ρ + ((n : ℝ) * (ε + η + ρ) + e) =
        ((n + 1 : ℕ) : ℝ) * (ε + η + ρ) + e := by
      push_cast
      ring
    rw [chainStepLaw_succ, chainStepLaw_succ]
    rwa [heq] at h

/-- **`n` steps of two Markov chains from a common initial law.** As `prokhorovLE_chainStepLaw`
with `μ = ν` and `0 < ε + r_c`: the `n`-step laws are `(ε + r_c, n (ε + η + ρ))`-close. With
`μ = Measure.dirac z` this compares the two chains started at any point `z`. -/
theorem prokhorovLE_chainStepLaw_same_start {μ : Measure E} [IsProbabilityMeasure μ]
    {κ κ' : E → Measure E} (hκ : Measurable κ) (hκ' : Measurable κ')
    [∀ y, IsProbabilityMeasure (κ y)] [∀ y, IsProbabilityMeasure (κ' y)]
    {ε r_c η ρ : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hρ0 : 0 ≤ ρ) (hr : 0 < ε + r_c)
    (hK : ∀ y, ProkhorovLE (κ y) (κ' y) ε ε)
    {H : Set E} {G : ℕ → Set E} (hH : MeasurableSet H)
    (hμH : ∀ n, chainStepLaw κ μ n Hᶜ = 0)
    (hG : ∀ n, chainStepLaw κ' μ n (G n)ᶜ ≤ ENNReal.ofReal ρ)
    (hcont : ∀ n, ∀ b ∈ G n, ∀ y ∈ H, dist y b < ε + r_c → ∀ A : Set E, MeasurableSet A →
      κ' y A ≤ κ' b (thickening r_c A) + ENNReal.ofReal η) (n : ℕ) :
    ProkhorovLE (chainStepLaw κ μ n) (chainStepLaw κ' μ n) (ε + r_c) (n * (ε + η + ρ)) := by
  have h := prokhorovLE_chainStepLaw hκ hκ' hε hη hρ0 le_rfl (prokhorovLE_refl μ hr) hK hH hμH
    hG hcont n
  rwa [add_zero] at h

end LatticeProb
