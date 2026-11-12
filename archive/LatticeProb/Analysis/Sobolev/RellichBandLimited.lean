/-
# Rellich–Kondrachov: the low-frequency statement from a band-limited `C^m`-net

`rk_finite_net_of_Cm_net` (`RellichNet.lean`) turns a finite `C^m(K)`-net of a
family of smooth functions supported in a compact `K` into a finite net in the
`sobolevNormSq d s₀` (semi)norm.  What `rkLowFrequencyStatement` still needs is
the *existence* of that `C^m(K)`-net for the unit ball of `H^s(D)`, i.e. the
band-limited compactness step of the classical proof.

This module isolates that step as the named proposition `rkBandLimitedCmNet`
and proves that it implies the low-frequency statement, and hence the external
`LatticeProb.External.RellichKondrachovNegSobolev`.  The proposition is the
precise remaining gap: its two missing inputs are the frequency-truncation
operator `P_Λ` and the band-limited Bernstein/`H^s → C^m` bound, neither of which
exists in Mathlib (see the docstring of `rk_finite_net_of_Cm_net`).
-/
import LatticeProb.Analysis.Sobolev.RellichNet
import LatticeProb.Analysis.Sobolev.RellichEquiv

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The band-limited `C^m`-net residual.**  For a bounded domain `D` and
`s₀ < s`, every `m`, and every accuracy `ε > 0`, the unit ball of `H^s(D)` admits
a finite family of test functions on `D` that is an `ε`-net in the `C^m` norm.
This is exactly the compactness input `rkLowFrequencyStatement` consumes; it is
where the frequency-truncation operator and the Bernstein bound are needed. -/
def rkBandLimitedCmNet : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ s₀ s : ℝ, s₀ < s →
    ∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ),
        (∀ i, IsTestFn D (ψ i)) ∧
        ∀ φ : Space d → ℝ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
          ∃ i, ∀ k ≤ m, ∀ x : Space d,
            ‖iteratedFDeriv ℝ k (fun x => φ x - ψ i x) x‖ ≤ ε

/-- The band-limited `C^m`-net residual implies the low-frequency finite-net
statement: choose `m` and `C` from the quantitative Fourier-decay residual
`rkResidual_diff_bound` (on the compact set `closure D`), take the `C^m`-net at
accuracy `ε` small enough that `C ε² ≤ δ`, and convert it back to
`sobolevNormSq d s₀` closeness with the residual. -/
theorem rkLowFrequencyStatement_of_rkBandLimitedCmNet
    (h : rkBandLimitedCmNet) : rkLowFrequencyStatement := by
  intro d D hD s₀ s hss δ hδ
  have hbdd : Bornology.IsBounded D := hD.2.1
  obtain ⟨m, C, hC0, hres⟩ :=
    rkResidual_diff_bound (d := d) (K := closure D) hbdd.isCompact_closure s₀
  have hCp1 : (0 : ℝ) < C + 1 := by linarith
  set ε : ℝ := Real.sqrt (δ / (C + 1)) with hεdef
  have hεpos : 0 < ε := Real.sqrt_pos_of_pos (by positivity)
  have hεδ : C * ε ^ 2 ≤ δ := by
    have h1 : ε ^ 2 = δ / (C + 1) := by
      rw [hεdef, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / (C + 1))]
    rw [h1]
    have h2 : C * (δ / (C + 1)) = δ * (C / (C + 1)) := by ring
    rw [h2]
    have h3 : C / (C + 1) ≤ 1 := by
      rw [div_le_one hCp1]
      linarith
    calc δ * (C / (C + 1)) ≤ δ * 1 := mul_le_mul_of_nonneg_left h3 hδ.le
      _ = δ := mul_one _
  obtain ⟨N, ψ, hψ, hnet⟩ := h d D hD s₀ s hss m ε hεpos
  refine ⟨N, ψ, hψ, fun φ hφ hφn => ?_⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hφn
  refine ⟨i, ?_⟩
  have hsub : tsupport (fun x => φ x - ψ i x) ⊆ closure D :=
    (tsupport_sub φ (ψ i)).trans
      ((Set.union_subset hφ.2.2 (hψ i).2.2).trans subset_closure)
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x - ψ i x) := hφ.1.sub (hψ i).1
  exact (hres (fun x => φ x - ψ i x) hdiff hsub ε hεpos hi).trans
    (ENNReal.ofReal_le_ofReal hεδ)

/-- With the band-limited `C^m`-net residual, the external
`RellichKondrachovNegSobolev` is discharged unconditionally through the
equivalence `rellichKondrachov_iff_rkLowFrequencyStatement`. -/
theorem rellichKondrachov_of_rkBandLimitedCmNet
    (h : rkBandLimitedCmNet) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachov_of_rkLowFrequencyStatement (rkLowFrequencyStatement_of_rkBandLimitedCmNet h)

end LatticeProb.Sobolev
