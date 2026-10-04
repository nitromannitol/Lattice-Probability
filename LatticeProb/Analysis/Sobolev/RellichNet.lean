/-
# The finite-net step of Rellich–Kondrachov, reduced to its quantitative content

`rkResidual_holds` (`RellichEstimate.lean`) gives, for a compact set `K` and an
order `s₀`, an exponent `m` and a constant `C ≥ 0` such that every smooth `g`
supported in `K` whose derivatives up to order `m` are bounded by `1` satisfies
`sobolevNormSq d s₀ g ≤ ENNReal.ofReal C`.  This file de-normalises that
estimate by homogeneity (`sobolevNormSq_const_mul`) and packages it as the
conversion the finite-net argument consumes: a finite `ε`-net in the
`C^m`-norm on `K` yields a finite net in the `sobolevNormSq d s₀` (semi)norm
with the *same centres* and explicit accuracy `C ε²`.

This is the largest sub-lemma of `rkLowFrequencyStatement` that is available
from the existing truncation and Fourier-decay lemmas; the remaining gap is
recorded in the docstring of `rk_finite_net_of_Cm_net`.
-/
import LatticeProb.Analysis.Sobolev.RellichEstimate
import LatticeProb.Analysis.Sobolev.Scaling

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The de-normalised quantitative residual: for a compact `K` there are `m`
and `C ≥ 0` such that a smooth `g` supported in `K` whose derivatives up to
order `m` are bounded by `ε > 0` has `sobolevNormSq d s₀ g ≤ ofReal (C * ε²)`.
This is `rkResidual_holds` applied to `(1/ε) • g`, using that the squared norm
is homogeneous of degree two (`sobolevNormSq_const_mul`). -/
theorem rkResidual_diff_bound {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    (s₀ : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (g : Space d → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → tsupport g ⊆ K →
        ∀ (ε : ℝ), 0 < ε →
          (∀ k ≤ m, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ ε) →
            sobolevNormSq d s₀ g ≤ ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨m, C, hC0, hC⟩ := rkResidual_holds d K hK s₀
  refine ⟨m, C, hC0, ?_⟩
  intro g hg hsupp ε hε hbd
  have hgsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => (1 / ε) * g x) := hg.const_smul (1 / ε)
  have hgsupp : tsupport (fun x => (1 / ε) * g x) ⊆ K :=
    (tsupport_mul_subset_right (f := fun _ : Space d => 1 / ε) (g := g)).trans hsupp
  have hgbd : ∀ k ≤ m, ∀ x : Space d,
      ‖iteratedFDeriv ℝ k (fun x => (1 / ε) * g x) x‖ ≤ 1 := by
    intro k hk x
    have hcont : ContDiffAt ℝ (k : ℕ∞) g x :=
      hg.contDiffAt.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    change ‖iteratedFDeriv ℝ k (fun x : Space d => (1 / ε) • g x) x‖ ≤ 1
    rw [iteratedFDeriv_const_smul_apply' hcont, norm_smul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ε)]
    calc (1 / ε) * ‖iteratedFDeriv ℝ k g x‖ ≤ (1 / ε) * ε :=
          mul_le_mul_of_nonneg_left (hbd k hk x) (by positivity)
      _ = 1 := by field_simp
  have hkey : ENNReal.ofReal ((1 / ε) ^ 2) * sobolevNormSq d s₀ g ≤ ENNReal.ofReal C := by
    have h := hC (fun x => (1 / ε) * g x) hgsm hgsupp hgbd
    rwa [sobolevNormSq_const_mul] at h
  have hb : (0 : ℝ) ≤ ε ^ 2 := by positivity
  have hfac : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ 2) := bot_le
  have hba : ε ^ 2 * (1 / ε) ^ 2 = 1 := by
    rw [← mul_pow]; field_simp
  calc sobolevNormSq d s₀ g
      = ENNReal.ofReal (ε ^ 2) *
          (ENNReal.ofReal ((1 / ε) ^ 2) * sobolevNormSq d s₀ g) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hb, hba, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal C :=
          mul_le_mul_of_nonneg_left hkey hfac
    _ = ENNReal.ofReal (C * ε ^ 2) := by
          rw [← ENNReal.ofReal_mul hb]
          congr 1
          ring

/-- **Finite-net-from-uniform-bound.**  For a compact `K` and an order `s₀`
there are `m` and `C ≥ 0` such that: given a finite family `ψ` of smooth
functions supported in `K` that is an `ε`-net in the `C^m(K)` norm for the
family of smooth functions supported in `K`, the same centres `ψ` form a finite
net in the `sobolevNormSq d s₀` (semi)norm with accuracy `C ε²`.  This is the
analytic content `rkResidual` was introduced for, and the only step of the
finite-net argument that is available in the library.

## The precise remaining gap to `rkLowFrequencyStatement`

To deduce `rkLowFrequencyStatement` from this reduction one still needs the
unit ball of `H^s(D)` to *have* a finite `C^m(K)`-net, i.e. its band-limited
piece must be totally bounded in `C^m(K)`.  That needs two facts absent from
Mathlib:

* a **frequency-truncation operator** `P_Λ` (the Fourier multiplier by
  `1_{‖ξ‖ ≤ Λ}`) with `sobolevNormSqLow d s Λ φ = sobolevNormSq d s (P_Λ φ)`,
  giving the low-frequency part as an honest function; and
* a **band-limited Bernstein / `H^s → C^m` bound**: a uniform `C^m(K)` bound
  for `{P_Λ φ | IsTestFn D φ, sobolevNormSq d s φ ≤ 1}`.  For `s ≥ 0` this is
  Fourier analysis; for `s < 0` it is the genuine Bernstein inequality and is
  not derivable from `sobolevNormSq` alone.

Arzelà–Ascoli (`BoundedContinuousFunction.arzela_ascoli`) then turns the
`C^m(K)` total boundedness into the required finite net.  A support/mollification
repair is still needed because band-limited functions are not compactly
supported and so the resulting centres are not `IsTestFn D` without further
work. -/
theorem rk_finite_net_of_Cm_net :
    ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ s₀ : ℝ,
      ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
        ∀ (N : ℕ) (ψ : Fin N → Space d → ℝ),
          (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) →
          (∀ i, tsupport (ψ i) ⊆ K) →
          ∀ ε : ℝ, 0 < ε →
            (∀ g : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → tsupport g ⊆ K →
              ∃ i, ∀ k ≤ m, ∀ x : Space d,
                ‖iteratedFDeriv ℝ k (fun x => g x - ψ i x) x‖ ≤ ε) →
            ∀ g : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → tsupport g ⊆ K →
              ∃ i, sobolevNormSq d s₀ (fun x => g x - ψ i x)
                ≤ ENNReal.ofReal (C * ε ^ 2) := by
  intro d K hK s₀
  obtain ⟨m, C, hC0, hres⟩ := rkResidual_diff_bound hK s₀
  refine ⟨m, C, hC0, ?_⟩
  intro N ψ hψ hψK ε hε hnet g hg hgK
  obtain ⟨i, hi⟩ := hnet g hg hgK
  refine ⟨i, hres (fun x => g x - ψ i x) (hg.sub (hψ i)) ?_ ε hε hi⟩
  exact (tsupport_sub g (ψ i)).trans (Set.union_subset hgK (hψK i))

end LatticeProb.Sobolev
