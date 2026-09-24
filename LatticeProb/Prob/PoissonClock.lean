/-
# The rate-two Poisson clock: weight, generator, mean, and variance

Moved from `manhattan-formalization`
(`Manhattan.Paper.{Poisson,TimeDerivative}`, plus one lemma,
`poissonWeightPrev_nonneg`, from `Manhattan.Paper.L2Decay`), where it supplied
the two halves of the paper's time-derivative estimate `prop:time` for a
Poisson-subordinated Markov chain. Nothing here refers to the paper's
directed lattice: `poissonWeight t n = e^{-2t}(2t)^n/n!` is `P(N_t = n)` for
the rate-two Poisson process, and every theorem below is real-variable
calculus about that one function. Left behind: everything past
`Manhattan.Paper.TimeDerivative`'s "generator applied to the subordinated
kernel" section, which pairs the weights here with the paper's own directed
walk kernel `ck`/`dk` on `Environment`/`Site`.

The rate `2` is a fixed literal rather than a parameter `r`, matching the
source exactly; reparametrizing to a general rate is easy future work (every
proof only uses that `2` is a positive real number) but was not done here, to
avoid re-deriving hypotheses that were not already checked at that
generality.

Content:

* `hasSum_poissonWeight`: the weights have total mass one, i.e. are a
  genuine probability distribution on `ℕ`, for every real `t` (even
  negative, since this is a formal power-series identity).
* `hasDerivAt_poissonWeight`: the time derivative of `w_n` is
  `2 (w_{n-1} - w_n)`, i.e. the generator of the Poisson-subordinated
  semigroup is `2 (Q - I)` for the underlying discrete kernel `Q`.
* `tsum_nat_mul_poissonWeight`/`tsum_nat_sq_mul_poissonWeight`/
  `tsum_centered_sq`: the exact mean `2t`, second moment `(2t)^2 + 2t`, and
  variance `2t` of the Poisson clock.
* `tsum_abs_dPoissonWeight_le`: the `L¹` concentration bound
  `∑_n |w_n'(t)| ≤ √(2/t)`, i.e. `E|N_t/t - 2| ≤ √(2/t)`, proved from the
  exact mean and variance via Cauchy-Schwarz.

`Manhattan.Model.Subordination` also has a companion `ℝ≥0∞`-valued weight
`rateTwoPoissonWeight`, identifying the time profile of each Poisson
coefficient with (half) an Erlang/Gamma density. It was not moved here: the
underlying Mathlib Poisson-distribution API changed from a real-valued pmf
(`poissonPMFReal`, `poissonPMF : ℝ≥0 → PMF ℕ`) to a measure-valued one
(`poissonMeasure : ℝ≥0 → Measure ℕ`) between the source's Lean 4.26 pin and
this library's Mathlib revision, and re-deriving the same facts against the
new API is a genuine rewrite, not a mechanical port.
-/
import Mathlib
import LatticeProb.Prob.CauchySchwarzTsum

namespace LatticeProb

/-! ### The rate-two Poisson weight -/

/-- `P(N_t = n)` for a rate-two Poisson clock. -/
noncomputable def poissonWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(2 * t)) * (2 * t) ^ n / (n.factorial : ℝ)

/-- The weight is nonnegative at nonnegative times. -/
theorem poissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeight t n := by
  have h1 : (0:ℝ) ≤ (2 * t) ^ n := pow_nonneg (by linarith) n
  have h2 : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le h1) h2.le

/-- The Poisson weights have total mass one, for every real `t`. -/
theorem hasSum_poissonWeight (t : ℝ) : HasSum (poissonWeight t) 1 := by
  have h : HasSum (fun n : ℕ => (2 * t) ^ n / (n.factorial : ℝ)) (Real.exp (2 * t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (2 * t)
  have h2 := h.mul_left (Real.exp (-(2 * t)))
  rw [← Real.exp_add] at h2
  simp only [neg_add_cancel, Real.exp_zero] at h2
  refine h2.congr_fun fun n => ?_
  rw [poissonWeight]
  ring

/-- The Poisson weights sum to one. -/
theorem tsum_poissonWeight (t : ℝ) : ∑' n, poissonWeight t n = 1 :=
  (hasSum_poissonWeight t).tsum_eq

/-- The Poisson weight sequence is summable. -/
theorem summable_poissonWeight (t : ℝ) : Summable (poissonWeight t) :=
  (hasSum_poissonWeight t).summable

/-- Each weight is at most the total mass. -/
theorem poissonWeight_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : poissonWeight t n ≤ 1 := by
  have h := (summable_poissonWeight t).le_tsum n fun j _ => poissonWeight_nonneg ht j
  rwa [tsum_poissonWeight] at h

/-- The previous Poisson weight, with the convention `w_{-1} = 0`. -/
noncomputable def poissonWeightPrev (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => poissonWeight t n

/-- The previous weight is nonnegative at nonnegative times. -/
theorem poissonWeightPrev_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeightPrev t n := by
  cases n with
  | zero => simp [poissonWeightPrev]
  | succ m => exact poissonWeight_nonneg ht m

/-- The time derivative of the `n`-th Poisson weight. -/
noncomputable def dPoissonWeight (t : ℝ) (n : ℕ) : ℝ :=
  2 * (poissonWeightPrev t n - poissonWeight t n)

/-- The generator identity: `w_n'(t) = 2 (w_{n-1}(t) - w_n(t))`. -/
theorem hasDerivAt_poissonWeight (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => poissonWeight s n) (dPoissonWeight t n) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(2 * s))) (-2 * Real.exp (-(2 * t))) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) t := by
      simpa using (hasDerivAt_id t).const_mul (-2:ℝ)
    have h2 : HasDerivAt (Real.exp ∘ fun s : ℝ => -(2 * s)) (Real.exp (-(2 * t)) * (-2)) t :=
      (Real.hasDerivAt_exp (-(2 * t))).comp t h1
    exact h2.congr_deriv (by ring)
  have hpow : HasDerivAt (fun s : ℝ => (2 * s) ^ n) ((n : ℝ) * (2 * t) ^ (n - 1) * 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2:ℝ)
    exact (hasDerivAt_pow n (2 * t)).comp t h1
  have hmul := (hexp.mul hpow).div_const ((n.factorial : ℝ))
  refine hmul.congr_deriv ?_
  cases n with
  | zero => simp [dPoissonWeight, poissonWeightPrev, poissonWeight]
  | succ m =>
      have hfacm : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hmfac : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
      simp only [dPoissonWeight, poissonWeightPrev, poissonWeight, Nat.add_sub_cancel, hfacm]
      field_simp
      ring

/-! ### Mean, variance, and the `L¹` concentration bound -/

/-- One step of the Poisson recursion `(n+1) w_{n+1}(t) = 2t \cdot w_n(t)`. -/
theorem poissonWeight_succ_mul (s : ℝ) (m : ℕ) :
    ((m : ℝ) + 1) * poissonWeight s (m + 1) = 2 * s * poissonWeight s m := by
  have hm : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  rw [poissonWeight, poissonWeight, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `n \mapsto n \cdot w_n(t)` is summable. -/
theorem summable_nat_mul_poissonWeight (s : ℝ) :
    Summable fun n : ℕ => (n : ℝ) * poissonWeight s n := by
  refine (summable_nat_add_iff 1).1 ?_
  refine ((summable_poissonWeight s).mul_left (2 * s)).congr fun m => ?_
  rw [← poissonWeight_succ_mul s m]
  push_cast
  ring

/-- The mean of the rate-two Poisson clock at time `t` is `2t`. -/
theorem tsum_nat_mul_poissonWeight (s : ℝ) :
    ∑' n : ℕ, (n : ℝ) * poissonWeight s n = 2 * s := by
  rw [(summable_nat_mul_poissonWeight s).tsum_eq_zero_add]
  have h0 : ((0:ℕ) : ℝ) * poissonWeight s 0 = 0 := by simp
  rw [h0, zero_add]
  have hterm : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) * poissonWeight s (m + 1)
      = 2 * s * poissonWeight s m := by
    intro m
    rw [← poissonWeight_succ_mul s m]
    push_cast
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_poissonWeight, mul_one]

/-- `n \mapsto n^2 \cdot w_n(t)` is summable. -/
theorem summable_nat_sq_mul_poissonWeight (s : ℝ) :
    Summable fun n : ℕ => (n : ℝ) ^ 2 * poissonWeight s n := by
  refine (summable_nat_add_iff 1).1 ?_
  refine (((summable_nat_mul_poissonWeight s).add (summable_poissonWeight s)).mul_left
    (2 * s)).congr fun m => ?_
  have h := poissonWeight_succ_mul s m
  have : ((m + 1 : ℕ) : ℝ) ^ 2 * poissonWeight s (m + 1)
      = ((m : ℝ) + 1) * (((m : ℝ) + 1) * poissonWeight s (m + 1)) := by push_cast; ring
  rw [this, h]
  ring

/-- The second moment of the rate-two Poisson clock at time `t` is
`(2t)^2 + 2t`. -/
theorem tsum_nat_sq_mul_poissonWeight (s : ℝ) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * poissonWeight s n = (2 * s) ^ 2 + 2 * s := by
  rw [(summable_nat_sq_mul_poissonWeight s).tsum_eq_zero_add]
  have h0 : ((0:ℕ) : ℝ) ^ 2 * poissonWeight s 0 = 0 := by simp
  rw [h0, zero_add]
  have hterm : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) ^ 2 * poissonWeight s (m + 1)
      = 2 * s * ((m : ℝ) * poissonWeight s m) + 2 * s * poissonWeight s m := by
    intro m
    have h := poissonWeight_succ_mul s m
    have h2 : ((m + 1 : ℕ) : ℝ) ^ 2 * poissonWeight s (m + 1)
        = ((m : ℝ) + 1) * (((m : ℝ) + 1) * poissonWeight s (m + 1)) := by push_cast; ring
    rw [h2, h]
    ring
  rw [tsum_congr hterm, Summable.tsum_add
    ((summable_nat_mul_poissonWeight s).mul_left (2 * s))
    ((summable_poissonWeight s).mul_left (2 * s)), tsum_mul_left, tsum_mul_left,
    tsum_nat_mul_poissonWeight, tsum_poissonWeight]
  ring

/-- `n \mapsto w_n(t) \cdot (n - 2t)^2` is summable. -/
theorem summable_centered_sq (s : ℝ) :
    Summable fun n : ℕ => poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2 := by
  refine (((summable_nat_sq_mul_poissonWeight s).sub
    ((summable_nat_mul_poissonWeight s).mul_left (2 * (2 * s)))).add
    ((summable_poissonWeight s).mul_left ((2 * s) ^ 2))).congr fun n => ?_
  ring

/-- The variance of the rate-two Poisson clock at time `t` is `2t`. -/
theorem tsum_centered_sq (s : ℝ) :
    ∑' n : ℕ, poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2 = 2 * s := by
  have hterm : ∀ n : ℕ, poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2
      = ((n : ℝ) ^ 2 * poissonWeight s n - 2 * (2 * s) * ((n : ℝ) * poissonWeight s n))
        + (2 * s) ^ 2 * poissonWeight s n := by
    intro n; ring
  rw [tsum_congr hterm, Summable.tsum_add
      ((summable_nat_sq_mul_poissonWeight s).sub
        ((summable_nat_mul_poissonWeight s).mul_left (2 * (2 * s))))
      ((summable_poissonWeight s).mul_left ((2 * s) ^ 2)),
    Summable.tsum_sub (summable_nat_sq_mul_poissonWeight s)
      ((summable_nat_mul_poissonWeight s).mul_left (2 * (2 * s))),
    tsum_mul_left, tsum_mul_left, tsum_nat_sq_mul_poissonWeight, tsum_nat_mul_poissonWeight,
    tsum_poissonWeight]
  ring

/-- The generator's action on the weight, as a multiple of the weight itself:
`w_n'(t) = w_n(t) \cdot (n/t - 2)`. -/
theorem dPoissonWeight_eq_mul {s : ℝ} (hs : 0 < s) (n : ℕ) :
    dPoissonWeight s n = poissonWeight s n * ((n : ℝ) / s - 2) := by
  cases n with
  | zero => simp [dPoissonWeight, poissonWeightPrev]; ring
  | succ m =>
      have h := poissonWeight_succ_mul s m
      have hkey : poissonWeight s (m + 1) * (((m : ℝ) + 1) / s) = 2 * poissonWeight s m := by
        field_simp
        linarith [h]
      simp only [dPoissonWeight, poissonWeightPrev]
      push_cast
      linear_combination -hkey

/-- The previous-weight sequence is summable. -/
theorem summable_poissonWeightPrev (s : ℝ) : Summable (poissonWeightPrev s) := by
  refine (summable_nat_add_iff 1).1 ?_
  exact (summable_poissonWeight s).congr fun m => rfl

/-- `|w_n'(t)|` is summable in `n`. -/
theorem summable_abs_dPoissonWeight {s : ℝ} (hs : 0 ≤ s) :
    Summable fun n => |dPoissonWeight s n| := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    (((summable_poissonWeightPrev s).add (summable_poissonWeight s)).mul_left 2)
  have h1 : 0 ≤ poissonWeightPrev s n := poissonWeightPrev_nonneg hs n
  have h2 : 0 ≤ poissonWeight s n := poissonWeight_nonneg hs n
  rw [dPoissonWeight, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h3 : |poissonWeightPrev s n - poissonWeight s n|
      ≤ poissonWeightPrev s n + poissonWeight s n := by
    rw [abs_le]; constructor <;> linarith
  linarith

/-- **The `L¹` concentration bound**, `E|N_t/t - 2| ≤ √(2/t)`, proved from the
exact Poisson mean and variance via Cauchy-Schwarz. -/
theorem tsum_abs_dPoissonWeight_le {s : ℝ} (hs : 0 < s) :
    ∑' n, |dPoissonWeight s n| ≤ Real.sqrt (2 / s) := by
  have hs0 : (0:ℝ) ≤ s := hs.le
  have hsq : ∀ n : ℕ, Real.sqrt (poissonWeight s n) * Real.sqrt (poissonWeight s n)
      = poissonWeight s n := fun n => Real.mul_self_sqrt (poissonWeight_nonneg hs0 n)
  have hprod : ∀ n : ℕ, Real.sqrt (poissonWeight s n)
      * (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) = |dPoissonWeight s n| := by
    intro n
    rw [show Real.sqrt (poissonWeight s n) * (Real.sqrt (poissonWeight s n)
        * |(n : ℝ) / s - 2|)
      = (Real.sqrt (poissonWeight s n) * Real.sqrt (poissonWeight s n)) * |(n : ℝ) / s - 2| from
      by ring, hsq n, dPoissonWeight_eq_mul hs n, abs_mul,
      abs_of_nonneg (poissonWeight_nonneg hs0 n)]
  have hbsq : ∀ n : ℕ, (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) ^ 2
      = poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2 / s ^ 2 := by
    intro n
    rw [mul_pow, Real.sq_sqrt (poissonWeight_nonneg hs0 n), sq_abs]
    field_simp
  have hb : Summable fun n : ℕ => (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) ^ 2 :=
    ((summable_centered_sq s).div_const (s ^ 2)).congr fun n => (hbsq n).symm
  have ha : Summable fun n : ℕ => Real.sqrt (poissonWeight s n) ^ 2 :=
    (summable_poissonWeight s).congr fun n => (Real.sq_sqrt (poissonWeight_nonneg hs0 n)).symm
  have hab : Summable fun n : ℕ => Real.sqrt (poissonWeight s n)
      * (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) :=
    (summable_abs_dPoissonWeight hs0).congr fun n => (hprod n).symm
  have hcs := tsum_mul_le_sqrt_mul_sqrt (fun n : ℕ => Real.sqrt (poissonWeight s n))
    (fun n : ℕ => Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|)
    (fun n => Real.sqrt_nonneg _)
    (fun n => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hab ha hb
  rw [tsum_congr hprod] at hcs
  have hA : (∑' n : ℕ, Real.sqrt (poissonWeight s n) ^ 2) = 1 := by
    rw [tsum_congr fun n => Real.sq_sqrt (poissonWeight_nonneg hs0 n), tsum_poissonWeight]
  have hB : (∑' n : ℕ, (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) ^ 2) = 2 / s := by
    rw [tsum_congr hbsq, tsum_div_const, tsum_centered_sq]
    field_simp
  rw [hA, hB, Real.sqrt_one, one_mul] at hcs
  exact hcs

/-- The triangle inequality for `tsum`, dominating termwise. -/
theorem abs_tsum_le {ι : Type*} (f g : ι → ℝ) (hf : Summable fun i => |f i|)
    (hg : Summable g) (h : ∀ i, |f i| ≤ g i) : |∑' i, f i| ≤ ∑' i, g i := by
  have h1 : |∑' i, f i| ≤ ∑' i, |f i| := by
    have h2 := norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using hf)
    simpa only [Real.norm_eq_abs] using h2
  exact h1.trans (Summable.tsum_le_tsum h hf hg)

end LatticeProb
