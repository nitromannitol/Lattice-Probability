import Mathlib
import LatticeProb.Prob.KernelIndepIncrements

/-!
# Conditionally independent increments of a continuous nondecreasing process are determined

Let `A` be a process with continuous nondecreasing paths on `[s, t]` on a standard Borel space
with a probability measure `P`, and let `m` be a sub-σ-algebra.  Suppose that for every `n` the
increments of `A` over the cells of the uniform partition of `[s, t]` into `n + 1` cells are
conditionally independent given `m`.  Then `A t - A s` is almost surely equal to an
`m`-measurable random variable.

* `LatticeProb.ae_eq_condExp_of_condExp_sq_eq`: a square-integrable `Z` with
  `E[Z² | m] = E[Z | m]²` almost surely is almost surely equal to `E[Z | m]`.
* `LatticeProb.exists_measurable_ae_eq_of_condIndep_increments`: the conclusion above.  The
  argument applies the kernel statement `ae_ae_eq_integral_of_kernel_indepIncrements` to the
  regular conditional probability `condExpKernel P m` and to the bounded variable
  `Z = exp (-(A t - A s))`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- A square-integrable variable whose conditional second moment is the square of its
conditional mean is almost surely equal to its conditional mean. -/
theorem ae_eq_condExp_of_condExp_sq_eq {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P) (h : P[Z ^ 2 | m] =ᵐ[P] P[Z | m] ^ 2) :
    Z =ᵐ[P] P[Z | m] := by
  have hv : Var[Z; P | m] =ᵐ[P] 0 := by
    filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hZ, h] with ω h1 h2
    rw [h1]
    simp [h2]
  have hW : MemLp (P[Z | m]) 2 P := hZ.condExp one_le_two
  have hsq : Integrable (fun ω => (Z ω - P[Z | m] ω) ^ 2) P := (hZ.sub hW).integrable_sq
  have hint : ∫ ω, (Z ω - P[Z | m] ω) ^ 2 ∂P = 0 := by
    have h1 : ∫ ω, Var[Z; P | m] ω ∂P = ∫ ω, (Z ω - P[Z | m] ω) ^ 2 ∂P :=
      integral_condExp hm (f := fun ω => (Z ω - P[Z | m] ω) ^ 2)
    rw [← h1, integral_congr_ae hv]
    simp
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hsq).1 hint
  filter_upwards [h0] with ω hω
  have : (Z ω - P[Z | m] ω) ^ 2 = 0 := hω
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- **Conditionally independent increments of a continuous nondecreasing process are
determined.**  Let `A` have continuous nondecreasing paths on `[s, t]`, let `m` be a sub-σ-algebra
of a standard Borel space with probability measure `P`, and suppose that for every `n` the
increments of `A` over the cells of the uniform partition of `[s, t]` into `n + 1` cells are
conditionally independent given `m`.  Then `A t - A s` is almost surely equal to an
`m`-measurable random variable. -/
theorem exists_measurable_ae_eq_of_condIndep_increments [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) {A : ℝ → Ω → ℝ} {s t : ℝ}
    (hst : s ≤ t) (hmeas : ∀ u, Measurable (A u))
    (hcont : ∀ ω, ContinuousOn (fun u => A u ω) (Set.Icc s t))
    (hmono : ∀ ω, MonotoneOn (fun u => A u ω) (Set.Icc s t))
    (hind : ∀ n : ℕ,
      iCondIndepFun m hm (fun k : Fin (n + 1) => cellIncrement A s t n k) P) :
    ∃ g : Ω → ℝ, Measurable[m] g ∧ (fun ω => A t ω - A s ω) =ᵐ[P] g := by
  set X : Ω → ℝ := fun ω => A t ω - A s ω with hX
  have hXm : Measurable X := (hmeas t).sub (hmeas s)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => sub_nonneg.2 (hmono ω ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst)
  set Z : Ω → ℝ := fun ω => Real.exp (-X ω) with hZ
  have hZm : Measurable Z := Real.measurable_exp.comp hXm.neg
  have hZb : ∀ ω, ‖Z ω‖ ≤ 1 := fun ω => by
    rw [hZ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith [hX0 ω])
  have hZ2 : MemLp Z 2 P := MemLp.of_bound hZm.aestronglyMeasurable 1 (ae_of_all _ hZb)
  have h1 := ae_ae_eq_integral_of_kernel_indepIncrements (κ := condExpKernel P m)
    (ν := P.trim hm) hst hmeas hcont hmono hind
  have h1' := ae_of_ae_trim hm h1
  have hint1 : P[Z | m] =ᵐ[P] fun a => ∫ y, Z y ∂condExpKernel P m a :=
    condExp_ae_eq_integral_condExpKernel hm (hZ2.integrable one_le_two)
  have hint2 : P[Z ^ 2 | m] =ᵐ[P] fun a => ∫ y, (Z ^ 2) y ∂condExpKernel P m a :=
    condExp_ae_eq_integral_condExpKernel hm hZ2.integrable_sq
  have hsq : P[Z ^ 2 | m] =ᵐ[P] P[Z | m] ^ 2 := by
    filter_upwards [h1', hint1, hint2] with a ha h1a h2a
    have hZc : Z =ᵐ[condExpKernel P m a]
        fun _ => Real.exp (-∫ y, X y ∂condExpKernel P m a) :=
      ha.mono fun y hy => by
        have hy' : X y = ∫ z, X z ∂condExpKernel P m a := hy
        simp only [hZ]
        rw [hy']
    have e1 : ∫ y, Z y ∂condExpKernel P m a = Real.exp (-∫ y, X y ∂condExpKernel P m a) := by
      rw [integral_congr_ae hZc]
      simp
    have e2 : ∫ y, (Z ^ 2) y ∂condExpKernel P m a =
        Real.exp (-∫ y, X y ∂condExpKernel P m a) ^ 2 := by
      rw [integral_congr_ae (hZc.mono fun y hy => by simp only [Pi.pow_apply]; rw [hy])]
      simp
    rw [Pi.pow_apply, h1a, h2a, e1, e2]
  have hZW := ae_eq_condExp_of_condExp_sq_eq hm hZ2 hsq
  have hWm : Measurable[m] (P[Z | m]) := stronglyMeasurable_condExp.measurable
  refine ⟨fun ω => -Real.log (P[Z | m] ω), (Real.measurable_log.comp hWm).neg, ?_⟩
  filter_upwards [hZW] with ω hω
  have : X ω = -Real.log (Z ω) := by simp [hZ, Real.log_exp]
  rw [this, hω]

/-- **Conditionally independent increments given a random variable `B`.**  If the increments of
`A` over the cells of the uniform partitions of `[s, t]` are conditionally independent given the
σ-algebra generated by `B`, then `A t - A s` is almost surely equal to `g ∘ B` for a measurable
function `g`. -/
theorem exists_measurable_comp_ae_eq_of_condIndep_increments [StandardBorelSpace Ω]
    {E : Type*} [MeasurableSpace E] {B : Ω → E} (hB : Measurable B)
    {P : Measure Ω} [IsProbabilityMeasure P] {A : ℝ → Ω → ℝ} {s t : ℝ}
    (hst : s ≤ t) (hmeas : ∀ u, Measurable (A u))
    (hcont : ∀ ω, ContinuousOn (fun u => A u ω) (Set.Icc s t))
    (hmono : ∀ ω, MonotoneOn (fun u => A u ω) (Set.Icc s t))
    (hind : ∀ n : ℕ, iCondIndepFun (MeasurableSpace.comap B inferInstance) hB.comap_le
      (fun k : Fin (n + 1) => cellIncrement A s t n k) P) :
    ∃ g : E → ℝ, Measurable g ∧ (fun ω => A t ω - A s ω) =ᵐ[P] g ∘ B := by
  obtain ⟨g0, hg0, hae⟩ := exists_measurable_ae_eq_of_condIndep_increments hB.comap_le hst hmeas
    hcont hmono hind
  obtain ⟨h, hh, hgh⟩ := Measurable.exists_eq_measurable_comp (f := B) hg0
  exact ⟨h, hh, hgh ▸ hae⟩

end LatticeProb
