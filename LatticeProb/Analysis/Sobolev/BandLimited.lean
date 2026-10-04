/-
# Band-limited functions: the low-frequency norm is the full norm

The frequency-truncation step of the Rellich–Kondrachov argument produces a
function whose Fourier transform is supported in a ball.  This module records
the defining property of such a *band-limited* function and proves the two
norm identities the truncation operator `P_Λ` must satisfy:

* the high-frequency part `‖φ‖_{H^s, ‖ξ‖>Λ}` vanishes for every order `s`, and
* therefore the low-frequency integral `sobolevNormSqLow d s Λ φ` is the whole
  `H^s` norm of `φ`.

Both are stated through the a.e. vanishing of the Fourier transform off the
ball, which is the mathematically honest form of "band-limited" and avoids any
choice of representative.
-/
import LatticeProb.Analysis.Sobolev.Truncation

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- A function is `Λ`-band-limited when its Fourier transform vanishes almost
everywhere outside the ball of radius `Λ`.  This is the property the
frequency-truncated field of the Rellich–Kondrachov argument has by
construction. -/
def IsBandLimited {d : ℕ} (Λ : ℝ) (φ : Space d → ℝ) : Prop :=
  ∀ᵐ ξ : Space d, Λ < ‖ξ‖ → 𝓕 (fun x => (φ x : ℂ)) ξ = 0

/-- For a band-limited function the high-frequency part of the `H^s` norm
vanishes at every order `s`: the integrand is zero almost everywhere on the
tail set, so the set integral is zero. -/
theorem sobolevNormSqHigh_eq_zero_of_isBandLimited {d : ℕ} {Λ s : ℝ} {φ : Space d → ℝ}
    (h : IsBandLimited Λ φ) : sobolevNormSqHigh d s Λ φ = 0 := by
  change ∀ᵐ ξ : Space d, Λ < ‖ξ‖ → 𝓕 (fun x => (φ x : ℂ)) ξ = 0 at h
  have hs : MeasurableSet {ξ : Space d | Λ < ‖ξ‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  unfold sobolevNormSqHigh
  apply MeasureTheory.lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hs] with ξ hξ hmem
  rw [hξ hmem]
  simp

/-- For a band-limited function the low-frequency integral is the full `H^s`
norm: the high-frequency part is zero and the two parts add up to the whole. -/
theorem sobolevNormSq_eq_low_of_isBandLimited {d : ℕ} {Λ s : ℝ} {φ : Space d → ℝ}
    (h : IsBandLimited Λ φ) :
    sobolevNormSq d s φ = sobolevNormSqLow d s Λ φ := by
  have hhigh := sobolevNormSqHigh_eq_zero_of_isBandLimited (s := s) h
  have hsplit := sobolevNormSqLow_add_high d s Λ φ
  rw [hhigh, add_zero] at hsplit
  exact hsplit.symm

/-- The band-limited predicate is monotone in the radius: a function that is
band-limited at `Λ` is band-limited at every larger `Λ'`. -/
theorem isBandLimited_mono {d : ℕ} {Λ Λ' : ℝ} {φ : Space d → ℝ} (hΛ : Λ ≤ Λ')
    (h : IsBandLimited Λ φ) : IsBandLimited Λ' φ := by
  change ∀ᵐ ξ : Space d, Λ' < ‖ξ‖ → 𝓕 (fun x => (φ x : ℂ)) ξ = 0
  change ∀ᵐ ξ : Space d, Λ < ‖ξ‖ → 𝓕 (fun x => (φ x : ℂ)) ξ = 0 at h
  filter_upwards [h] with ξ hξ hmem
  exact hξ (lt_of_le_of_lt hΛ hmem)

end LatticeProb.Sobolev
