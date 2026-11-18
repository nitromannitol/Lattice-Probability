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
* `chainSeqLaw`, `chainSeqLaw_zero`, `chainSeqLaw_succ`, `isProbabilityMeasure_chainSeqLaw`,
  `chainSeqLaw_const`: the time-inhomogeneous chain, with kernel `κ n` at step `n`.
* `prokhorovLE_chainSeqLaw`: the `n`-step comparison of two time-inhomogeneous chains with
  step-dependent closeness `ε n`, continuity radius `r n`, mass errors `η n` and `ρ n`; the radius
  follows `R (n + 1) = ε n + r n` and the error `e (n + 1) = ε n + η n + ρ n + e n`.
* `prokhorovLE_chainSeqLaw_sum`: the same with the error in closed form
  `e₀ + ∑_{m < n} (ε m + η m + ρ m)`.

## Time-inhomogeneous chains

When the continuity of `κ'` is only available with an error proportional to the distance of the
starting points (a Lipschitz modulus of harmonic measure in the base point, say), the comparison
radius must be allowed to grow from step to step: the continuity scale at step `n` is the radius
`R n` reached after `n` steps, and the thickening radius `r n` may be as large as `R n`, so that
`R (n + 1) = ε n + R n`. The kernels may also depend on the step, which covers chains on
histories of a fixed length whose `n`-th step only changes the coordinates after `n`.
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

/-- The law after `n` steps of the time-inhomogeneous Markov chain that uses the kernel `κ m` at
step `m`, started from the law `μ`. -/
noncomputable def chainSeqLaw (κ : ℕ → E → Measure E) (μ : Measure E) : ℕ → Measure E
  | 0 => μ
  | n + 1 => (chainSeqLaw κ μ n).bind (κ n)

@[simp]
theorem chainSeqLaw_zero (κ : ℕ → E → Measure E) (μ : Measure E) : chainSeqLaw κ μ 0 = μ :=
  rfl

theorem chainSeqLaw_succ (κ : ℕ → E → Measure E) (μ : Measure E) (n : ℕ) :
    chainSeqLaw κ μ (n + 1) = (chainSeqLaw κ μ n).bind (κ n) :=
  rfl

/-- With the same kernel at every step, the time-inhomogeneous chain is the chain of
`chainStepLaw`. -/
theorem chainSeqLaw_const (κ : E → Measure E) (μ : Measure E) (n : ℕ) :
    chainSeqLaw (fun _ => κ) μ n = chainStepLaw κ μ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chainSeqLaw_succ, chainStepLaw_succ, ih]

/-- The `n`-step laws of a time-inhomogeneous chain of Markov kernels started from a probability
measure are probability measures. -/
theorem isProbabilityMeasure_chainSeqLaw {κ : ℕ → E → Measure E} (hκ : ∀ n, Measurable (κ n))
    [∀ n y, IsProbabilityMeasure (κ n y)] {μ : Measure E} [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (chainSeqLaw κ μ n) := by
  induction n with
  | zero => rw [chainSeqLaw_zero]; infer_instance
  | succ n ih =>
    rw [chainSeqLaw_succ]
    constructor
    rw [Measure.bind_apply MeasurableSet.univ (hκ n).aemeasurable]
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

/-- **`n` steps of two time-inhomogeneous Markov chains in the one-sided Prokhorov sense.** At
step `m` the kernels `κ m, κ' m` are uniformly `ε m`-close, the `m`-step law of the first chain is
carried by the measurable set `H m`, the `m`-step law of the second chain gives mass at most `ρ m`
to `(G m)ᶜ`, and `κ' m` is continuous at the thickening radius `r m` with mass error `η m` between
starting points `y ∈ H m` and `b ∈ G m` at distance less than the current radius `R m`. If the
initial laws are `(R 0, e 0)`-close, `R (m + 1) = ε m + r m` and
`e (m + 1) = ε m + η m + ρ m + e m`, then the `n`-step laws are `(R n, e n)`-close. -/
theorem prokhorovLE_chainSeqLaw {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {κ κ' : ℕ → E → Measure E} (hκ : ∀ n, Measurable (κ n))
    (hκ' : ∀ n, Measurable (κ' n)) [∀ n y, IsProbabilityMeasure (κ n y)]
    [∀ n y, IsProbabilityMeasure (κ' n y)] {ε r η ρ R e : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hη : ∀ n, 0 ≤ η n) (hρ : ∀ n, 0 ≤ ρ n) (he0 : 0 ≤ e 0) (hR : ∀ n, R (n + 1) = ε n + r n)
    (he : ∀ n, e (n + 1) = ε n + η n + ρ n + e n) (hP : ProkhorovLE μ ν (R 0) (e 0))
    (hK : ∀ n y, ProkhorovLE (κ n y) (κ' n y) (ε n) (ε n)) {H G : ℕ → Set E}
    (hH : ∀ n, MeasurableSet (H n)) (hμH : ∀ n, chainSeqLaw κ μ n (H n)ᶜ = 0)
    (hG : ∀ n, chainSeqLaw κ' ν n (G n)ᶜ ≤ ENNReal.ofReal (ρ n))
    (hcont : ∀ n, ∀ b ∈ G n, ∀ y ∈ H n, dist y b < R n → ∀ A : Set E, MeasurableSet A →
      κ' n y A ≤ κ' n b (thickening (r n) A) + ENNReal.ofReal (η n)) (n : ℕ) :
    ProkhorovLE (chainSeqLaw κ μ n) (chainSeqLaw κ' ν n) (R n) (e n) := by
  have hen : ∀ m, 0 ≤ e m := by
    intro m
    induction m with
    | zero => exact he0
    | succ m ih =>
      rw [he m]
      exact add_nonneg (add_nonneg (add_nonneg (hε m) (hη m)) (hρ m)) ih
  induction n with
  | zero => exact hP
  | succ n ih =>
    have hμn := isProbabilityMeasure_chainSeqLaw hκ (μ := μ) n
    have hνn := isProbabilityMeasure_chainSeqLaw hκ' (μ := ν) n
    have h := prokhorovLE_bind_split (hκ n) (hκ' n) (hε n) (hη n) (hρ n) (hen n) ih (hK n)
      (hH n) (hμH n) (hG n) (hcont n)
    rw [chainSeqLaw_succ, chainSeqLaw_succ, hR n, he n]
    exact h

/-- **Closed form of the error.** As `prokhorovLE_chainSeqLaw`, with initial error `e₀` and the
error after `n` steps written as `e₀ + ∑_{m < n} (ε m + η m + ρ m)`. -/
theorem prokhorovLE_chainSeqLaw_sum {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {κ κ' : ℕ → E → Measure E} (hκ : ∀ n, Measurable (κ n))
    (hκ' : ∀ n, Measurable (κ' n)) [∀ n y, IsProbabilityMeasure (κ n y)]
    [∀ n y, IsProbabilityMeasure (κ' n y)] {ε r η ρ R : ℕ → ℝ} {e₀ : ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hη : ∀ n, 0 ≤ η n) (hρ : ∀ n, 0 ≤ ρ n) (he₀ : 0 ≤ e₀) (hR : ∀ n, R (n + 1) = ε n + r n)
    (hP : ProkhorovLE μ ν (R 0) e₀) (hK : ∀ n y, ProkhorovLE (κ n y) (κ' n y) (ε n) (ε n))
    {H G : ℕ → Set E} (hH : ∀ n, MeasurableSet (H n)) (hμH : ∀ n, chainSeqLaw κ μ n (H n)ᶜ = 0)
    (hG : ∀ n, chainSeqLaw κ' ν n (G n)ᶜ ≤ ENNReal.ofReal (ρ n))
    (hcont : ∀ n, ∀ b ∈ G n, ∀ y ∈ H n, dist y b < R n → ∀ A : Set E, MeasurableSet A →
      κ' n y A ≤ κ' n b (thickening (r n) A) + ENNReal.ofReal (η n)) (n : ℕ) :
    ProkhorovLE (chainSeqLaw κ μ n) (chainSeqLaw κ' ν n) (R n)
      (e₀ + ∑ m ∈ Finset.range n, (ε m + η m + ρ m)) := by
  refine prokhorovLE_chainSeqLaw (e := fun n => e₀ + ∑ m ∈ Finset.range n, (ε m + η m + ρ m))
    hκ hκ' hε hη hρ (by simpa using he₀) hR (fun m => ?_) (by simpa using hP) hK hH hμH hG
    hcont n
  simp only [Finset.sum_range_succ]
  ring

end LatticeProb
