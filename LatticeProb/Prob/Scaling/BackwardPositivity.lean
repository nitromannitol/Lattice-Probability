import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Strict positivity from propagation of zeros backwards in time.

Moved from Parking-Sharpness.
-/

namespace LatticeProb.Scaling.BackwardPositivity

/-- A monotone function starting at zero can be positive only at positive times. -/
theorem time_pos {f : ℝ → ℝ} (hf : Monotone f) (hzero : f 0 = 0)
    {s : ℝ} (hs : 0 < f s) : 0 < s := by
  by_contra h
  have := hf (le_of_not_gt h)
  rw [hzero] at this
  exact (not_lt_of_ge this) hs

/-- The positive set of a time-monotone field vanishing at time zero lies
entirely in positive times. -/
theorem positive_set_subset_positive_time {X : Type*} {u : ℝ → X → ℝ}
    (hzero : ∀ x, u 0 x = 0) (hmono : ∀ x, Monotone fun s => u s x) :
    {p : ℝ × X | 0 < u p.1 p.2} ⊆ {p | 0 < p.1} := by
  intro p hp
  exact time_pos (hmono p.2) (hzero p.2) hp

/-- If zeros of the derivative propagate backwards through the positive set,
the derivative is strictly positive there. The intermediate value theorem
provides an earlier positive level, and the mean value theorem contradicts
constancy between that level and the proposed zero. -/
theorem derivative_pos {f v : ℝ → ℝ} (hcont : Continuous f)
    (hmono : Monotone f) (hzero : f 0 = 0)
    (hderiv : ∀ s, 0 < f s → HasDerivAt f (v s) s)
    (hback : ∀ s₀, 0 < f s₀ → v s₀ = 0 →
      ∀ τ, τ < s₀ → (∀ s ∈ Set.Ioc τ s₀, 0 < f s) →
        ∀ s ∈ Set.Ioc τ s₀, v s = 0)
    {s₀ : ℝ} (hpos : 0 < f s₀) : 0 < v s₀ := by
  have hs₀ := time_pos hmono hzero hpos
  have hvnonneg := (hderiv s₀ hpos).nonneg_of_monotone hmono
  by_contra hv
  have hvzero : v s₀ = 0 := le_antisymm (le_of_not_gt hv) hvnonneg
  obtain ⟨τ, hτ, hlevel⟩ := intermediate_value_Icc hs₀.le hcont.continuousOn
    (show f s₀ / 2 ∈ Set.Icc (f 0) (f s₀) by rw [hzero]; constructor <;> linarith)
  have hτlt : τ < s₀ := lt_of_le_of_ne hτ.2 (by
    intro heq
    rw [heq] at hlevel
    linarith)
  have hτpos : 0 < f τ := by rw [hlevel]; linarith
  have hinterval : ∀ s ∈ Set.Ioc τ s₀, 0 < f s :=
    fun s hs => lt_of_lt_of_le hτpos (hmono hs.1.le)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f v hτlt hcont.continuousOn
    (fun s hs => hderiv s (hinterval s ⟨hs.1, hs.2.le⟩))
  rw [hback s₀ hpos hvzero τ hτlt hinterval c ⟨hc.1, hc.2.le⟩] at hslope
  have := (div_eq_zero_iff).mp hslope.symm
  rcases this with h | h
  · linarith
  · linarith

end LatticeProb.Scaling.BackwardPositivity
