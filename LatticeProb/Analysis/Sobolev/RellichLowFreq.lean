/-
The mollification sub-step of the Rellich–Kondrachov low-frequency argument.

The total-boundedness statement `aux_rk_low_freq_statement` of the Rellich
decomposition asks that the unit ball of `H^s(D)` test functions be covered by
finitely many `H^{s₀}` balls.  The classical route replaces a test function
`φ` by a mollification `φ ⋆ K`, which is smooth, compactly supported, and
close to `φ` in every Sobolev order.  This file proves the first, purely
topological half of that sub-step: convolution with a compactly supported
smooth kernel sends test functions to test functions on any domain containing
the Minkowski sum of the two supports.

Mathlib already supplies the analytic ingredients used here:
`HasCompactSupport.contDiff_convolution_right` (smoothness of the convolution)
and `HasCompactSupport.convolution` / `support_convolution_subset` (compact
support and the support containment).  What is added below is their packaging
for `IsTestFn`, together with the `tsupport` (closure-of-support) form of the
support containment, which is the form `IsTestFn` reads.

The quantitative `H^{s₀}` closeness `sobolevNormSq d s₀ (φ - φ ⋆ K) → 0` is a
separate analytic obligation; it is not proved here.  It needs the Fourier
convolution identity plus dominated convergence against the weight
`(1 + (2π‖ξ‖)²)^{s₀}`, and is recorded as the remaining obstruction in the
comment at the end of this file.
-/
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory ContinuousLinearMap Set
open scoped ENNReal FourierTransform Convolution Pointwise

namespace LatticeProb.Sobolev

variable {d : ℕ}

/-- **Support of a convolution, in `tsupport` form.**  The closure of the
support of a convolution is contained in the Minkowski sum of the closures of
the two supports.  This strengthens Mathlib's `support_convolution_subset`
from supports to their closures; the closure is taken using that the sum of
two compact sets in a proper space is compact, hence closed. -/
theorem tsupport_convolution_subset (f g : Space d → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    tsupport (f ⋆[lsmul ℝ ℝ, volume] g) ⊆ tsupport f + tsupport g := by
  refine closure_minimal ((support_convolution_subset (L := lsmul ℝ ℝ)).trans ?_)
    (hf.isCompact.add hg.isCompact).isClosed
  exact add_subset_add subset_closure subset_closure

/-- **Mollification preserves test functions.**  If `φ ∈ C_c^∞(D)` and `K` is
`C^∞` with compact support, then `φ ⋆ K` is `C^∞`, compactly supported, and
supported in `tsupport φ + tsupport K`; in particular it is a test function on
any domain `D'` containing that Minkowski sum. -/
theorem IsTestFn.convolution {D D' : Set (Space d)} {φ K : Space d → ℝ}
    (hφ : IsTestFn D φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (hsub : tsupport φ + tsupport K ⊆ D') :
    IsTestFn D' (φ ⋆[lsmul ℝ ℝ, volume] K) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hKc.contDiff_convolution_right (lsmul ℝ ℝ) hφ.1.continuous.locallyIntegrable hK
  · exact HasCompactSupport.convolution (L := lsmul ℝ ℝ) (μ := volume) hφ.2.1 hKc
  · exact (tsupport_convolution_subset φ K hφ.2.1 hKc).trans hsub

/-- **Unshrunk form.**  With `D' = D`, convolution with a kernel supported in
`{0}` (e.g. `K = 0`, or a bump of radius zero) preserves the test-function
class on the same domain.  More usefully, it records the exact Minkowski-sum
support bound that a shrinkage of `D` by the kernel radius must absorb. -/
theorem IsTestFn.convolution_of_add_support_subset {D : Set (Space d)} {φ K : Space d → ℝ}
    (hφ : IsTestFn D φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (hsub : tsupport φ + tsupport K ⊆ D) :
    IsTestFn D (φ ⋆[lsmul ℝ ℝ, volume] K) :=
  hφ.convolution hK hKc hsub

/-! ### Remaining obstruction: the quantitative `H^{s₀}` closeness

The support/smoothness half above is complete.  What is *not* proved is the
companion quantitative statement that makes the mollified family a net for the
unit ball: for a fixed normalised kernel `K` and `K_Λ x = Λ^d K (Λ x)`,

  `sobolevNormSq d s₀ (fun x => φ x - (φ ⋆[lsmul ℝ ℝ, volume] K_Λ) x) → 0`
  as `Λ → ∞`, uniformly over `{φ : IsTestFn D φ, sobolevNormSq d s φ ≤ 1}`.

The exact missing ingredients are:

1. **Fourier transform of the real convolution.**  Mathlib has
   `MeasureTheory.fourier_smul_convolution_eq` and
   `MeasureTheory.fourier_mul_convolution_eq`
   (`Mathlib/Analysis/Fourier/Convolution.lean:107,119`), stated for `ℂ`-valued
   (or `ℂ`-scalar) functions, but `sobolevNormSq` reads `𝓕 (fun x => (φ x : ℂ))`.
   There is no statement that the real-to-complex coercion of
   `φ ⋆[lsmul ℝ ℝ, volume] K` has Fourier transform `𝓕(↑φ) * 𝓕(↑K)`; that
   coercion compatibility is the first missing lemma.

2. **The scaled-kernel limit.**  With `𝓕 K_Λ(ξ) = 𝓕 K (ξ / Λ)` and
   `𝓕 K 0 = ∫ K = 1`, the pointwise convergence
   `w(ξ) ‖𝓕 φ ξ‖² ‖1 - 𝓕 K (ξ/Λ)‖² → 0` must be dominated by
   `C · sup_η ‖𝓕 K η‖² · w(ξ) ‖𝓕 φ ξ‖²` and integrated with a
   dominated-convergence lemma.  The dominating integral is finite because
   `φ ∈ H^{s₀}` (from `H^s`, since `s₀ < s`).  Mathlib has the
   dominated-convergence lemmas; the work is to wire the scaled family and the
   `H^{s₀}` integrability.

3. **The support shrinkage.**  `IsTestFn.convolution` enlarges `tsupport φ` by
   `tsupport K_Λ`, a ball of radius `O(1/Λ)`.  Since `φ` may sit arbitrarily
   close to `∂D`, a fixed `φ`-independent shrinkage of `D` does not absorb the
   enlargement; a `Λ`-dependent (but `φ`-independent) smooth cutoff of a
   slightly shrunk copy of `D` is needed, which is why the low-frequency step
   is not `IsTestFn.convolution` alone.

None of these is a missing Mathlib *definition*; each is a missing quantitative
lemma, and together they are exactly the content of
`aux_rk_low_freq_statement`. -/

end LatticeProb.Sobolev
