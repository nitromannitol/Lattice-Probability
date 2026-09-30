/-
A finite step function taking value `a n` on the `n`-th of `N` consecutive intervals of equal
length `h`, its integral, its pointwise formula via `Nat.floor`, and its integral against a
second measure after multiplying by a further, coordinate-dependent integrand.

Moved from Parking-Sharpness.
-/
import Mathlib
open MeasureTheory Set
noncomputable section
namespace LatticeProb.Scaling.TimeCell

/-- A finite step function on consecutive intervals of equal positive length. -/
def step (h : ℝ) (N : ℕ) (a : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (Ico ((n : ℝ) * h) (((n : ℝ) + 1) * h)).indicator
    (fun _ => a n) s

/-- A finite step function is integrable, as a finite sum of integrable indicators. -/
theorem integrable_step {h : ℝ} (N : ℕ) (a : ℕ → ℝ) : Integrable (step h N a) := by
  apply integrable_finsetSum
  intro n _
  exact (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (C := a n) (μ := volume) (s := Ico ((n : ℝ) * h) (((n : ℝ) + 1) * h))
      (ne_of_lt measure_Ico_lt_top))

/-- The integral of a finite step function is `h` times the sum of its values. -/
theorem integral_step {h : ℝ} (hh : 0 ≤ h) (N : ℕ) (a : ℕ → ℝ) :
    ∫ s, step h N a s = h * ∑ n ∈ Finset.range N, a n := by
  unfold step
  rw [integral_finsetSum]
  · simp only [integral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul,
      Measure.real, Real.volume_Ico]
    have he : ∀ n : ℕ, (((n : ℝ) + 1) * h - (n : ℝ) * h) = h := fun n => by ring
    simp only [he, ENNReal.toReal_ofReal hh, ← Finset.mul_sum]
  · intro n _
    exact (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (C := a n) (μ := volume) (s := Ico ((n : ℝ) * h) (((n : ℝ) + 1) * h))
      (ne_of_lt measure_Ico_lt_top))

/-- Inside the covered range, the step function reads off the value of the cell containing
`s`, located by `Nat.floor (s / h)`. -/
theorem step_eq {h s : ℝ} (hh : 0 < h) (N : ℕ) (a : ℕ → ℝ)
    (hs : s ∈ Ico 0 ((N : ℝ) * h)) : step h N a s = a ⌊s / h⌋₊ := by
  classical
  have hn : ⌊s / h⌋₊ < N := (Nat.floor_lt (div_nonneg hs.1 hh.le)).mpr
    ((div_lt_iff₀ hh).mpr hs.2)
  have hm : s ∈ Ico ((⌊s / h⌋₊ : ℝ) * h) (((⌊s / h⌋₊ : ℝ) + 1) * h) := by
    constructor
    · exact (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hs.1 hh.le))
    · exact (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (s / h))
  unfold step
  rw [Finset.sum_eq_single ⌊s / h⌋₊]
  · exact indicator_of_mem hm _
  · intro n hn' hne
    apply indicator_of_notMem
    intro hmem
    have heq : ⌊s / h⌋₊ = n := Nat.floor_eq_iff (div_nonneg hs.1 hh.le) |>.mpr
      ⟨(le_div_iff₀ hh).mpr hmem.1, (div_lt_iff₀ hh).mpr hmem.2⟩
    exact hne heq.symm
  · simp [Finset.mem_range.mpr hn]

/-- Outside the covered range `Ico 0 (N*h)`, the step function vanishes. -/
theorem step_eq_zero {h s : ℝ} (hh : 0 ≤ h) (N : ℕ) (a : ℕ → ℝ)
    (hs : s ∉ Ico 0 ((N : ℝ) * h)) : step h N a s = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro n hn
  apply indicator_of_notMem
  intro hp
  apply hs
  refine ⟨(mul_nonneg (Nat.cast_nonneg n) hh).trans hp.1, hp.2.trans_le ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.mem_range.mp hn) hh

/-- The step function equals the indicator of its covered range times the floor-indexed
value, combining `step_eq` and `step_eq_zero` into a single closed form. -/
theorem step_eq_indicator {h : ℝ} (hh : 0 < h) (N : ℕ) (a : ℕ → ℝ) :
    step h N a = (Ico 0 ((N : ℝ) * h)).indicator (fun s => a ⌊s / h⌋₊) := by
  classical
  funext s
  by_cases hs : s ∈ Ico 0 ((N : ℝ) * h)
  · rw [indicator_of_mem hs, step_eq hh N a hs]
  · rw [indicator_of_notMem hs, step_eq_zero hh.le N a hs]

/-- A step function in the first coordinate, multiplied by an integrable function of the
second coordinate on each cell, is integrable on the product space. -/
theorem integrable_step_prod {E : Type*} [MeasurableSpace E] (μ : Measure E)
    {h : ℝ} (N : ℕ) (f : ℕ → E → ℝ) (hf : ∀ n < N, Integrable (f n) μ) :
    Integrable (fun p : ℝ × E => step h N (fun n => f n p.2) p.1) (volume.prod μ) := by
  classical
  have he : (fun p : ℝ × E => step h N (fun n => f n p.2) p.1) =
      fun p => ∑ n ∈ Finset.range N,
        (Ico ((n : ℝ) * h) (((n : ℝ) + 1) * h)).indicator (fun _ => (1 : ℝ)) p.1 * f n p.2 := by
    funext p
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : p.1 ∈ Ico ((n : ℝ) * h) (((n : ℝ) + 1) * h) <;> simp [hp]
  rw [he]
  apply integrable_finsetSum
  intro n hn
  have hi : Integrable ((Ico ((n : ℝ) * h) (((n : ℝ) + 1) * h)).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (ne_of_lt measure_Ico_lt_top))
  exact hi.mul_prod (hf n (Finset.mem_range.mp hn))

/-- The product-space integral of a step function times a second-coordinate integrand equals
`h` times the sum, over cells, of the second-coordinate integrals. -/
theorem integral_step_prod {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [SFinite μ] {h : ℝ} (hh : 0 ≤ h) (N : ℕ) (f : ℕ → E → ℝ)
    (hf : ∀ n < N, Integrable (f n) μ) :
    (∫ p : ℝ × E, step h N (fun n => f n p.2) p.1 ∂volume.prod μ) =
      h * ∑ n ∈ Finset.range N, ∫ x, f n x ∂μ := by
  rw [integral_prod _ (integrable_step_prod μ (h := h) N f hf),
    integral_integral_swap (integrable_step_prod μ (h := h) N f hf)]
  simp_rw [integral_step hh]
  rw [integral_const_mul, integral_finsetSum _ (fun n hn => hf n (Finset.mem_range.mp hn))]

end LatticeProb.Scaling.TimeCell
