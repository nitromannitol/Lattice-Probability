/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.GFF.Kernels at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Green's functions on `ℍ` and admissible measures

Sheffield §3.2: the zero-boundary Green's function on `ℍ` is `G^{ℍ_0}(x,y) = log|x-ȳ| -
log|x-y|`, the free-boundary one differs only in the sign of the reflection term,
`G^{ℍ_F}(x,y) = -log|x-y| - log|x-ȳ|`. See `notes/section3_4.md` §A.4, formulas (3.5)-(3.6).

Fields are `Measure ℂ → ℝ` (this is `FieldSample`, defined in `QuantumZipper.Field.Sample`,
not imported here). A field pairs with a measure by "evaluating" it; `kernelCov` computes the
covariance of two such pairings for a Gaussian field with kernel `G`.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace QuantumZipper

/-- The zero-boundary Green's function on `ℍ`, `G^{ℍ_0}(x,y) = log|x-ȳ| - log|x-y|`
(Sheffield (3.5)). -/
def greenH (x y : ℂ) : ℝ := Real.log ‖x - conj y‖ - Real.log ‖x - y‖

/-- The free-boundary Green's function on `ℍ` (modulo additive constants),
`G^{ℍ_F}(x,y) = -log|x-y| - log|x-ȳ|` (Sheffield (3.6)). The sign of the reflection term is
the only difference from `greenH`; flipping it silently swaps zero/free boundary conditions. -/
def neumannH (x y : ℂ) : ℝ := -Real.log ‖x - y‖ - Real.log ‖x - conj y‖

/-- Covariance of the pairings of a `G`-kernel Gaussian field against `μ` and `ν`. -/
def kernelCov (G : ℂ → ℂ → ℝ) (μ ν : Measure ℂ) : ℝ := ∫ x, ∫ y, G x y ∂ν ∂μ

/-- Bilinear expansion of `kernelCov G` on the signed measures `p.1 - p.2` and `q.1 - q.2`,
used for the free-boundary field modulo additive constants. -/
def kernelCov2 (G : ℂ → ℂ → ℝ) (p q : Measure ℂ × Measure ℂ) : ℝ :=
  kernelCov G p.1 q.1 - kernelCov G p.1 q.2 - kernelCov G p.2 q.1 + kernelCov G p.2 q.2

/-- Admissible measures for fields on `ℍ`: finite, with compact support in the closed upper
half-plane, and with **bounded singular logarithmic potential**:
`sup_y ∫ log⁻ ‖x - y‖ dμ(x) < ∞`, where `log⁻ t = max(0, -log t)`
(written `ENNReal.ofReal (-Real.log ‖x - y‖)`).

Only the singular part is bounded: the full `∫ |log ‖x - y‖| dμ(x)` grows like
`μ(ℂ) log |y|` as `y → ∞` for every nonzero `μ`. The non-singular part `log⁺` is bounded on
the compact support, so this condition gives integrability of `greenH` and `neumannH` against
`μ.prod ν` for admissible `μ, ν` (Tonelli; for `x, y ∈ Hbar`, `‖x - y‖ ≤ ‖x - ȳ‖`, so the
reflected term has no worse singularity).

This class contains every measure the paper pairs a field with: bounded densities with
compact support, uniform measures on circles and semicircles (a circle measure has
`∫ log|x - y| = log max(r, |z - y|) ≥ log r`), their mixtures, and their pushforwards under
bi-Lipschitz maps. It excludes atoms (near an atom `a` the potential is at least
`μ{a} log⁻ |a - y|`), which matters: mathlib's junk value `Real.log 0 = 0` would otherwise
give a Dirac mass a finite (even negative) "energy" and make the GFF predicates
unsatisfiable. Restricting the index class only weakens the GFF hypotheses; every true GFF
satisfies them, and all regularized quantities (`avgReg`, `evalReg`, `pairTest`) only use
admissible measures. -/
def IsAdmissibleH (μ : Measure ℂ) : Prop :=
  IsFiniteMeasure μ ∧ (∃ K, IsCompact K ∧ K ⊆ Hbar ∧ μ Kᶜ = 0) ∧
    ∃ C : ENNReal, C < ⊤ ∧ ∀ y : ℂ, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ ≤ C

/-! ## Symmetry -/

/-- Reflecting across the real axis commutes with swapping: `‖x - ȳ‖ = ‖y - x̄‖`. -/
theorem norm_sub_conj_comm (x y : ℂ) : ‖x - conj y‖ = ‖y - conj x‖ := by
  have h : conj (x - conj y) = -(y - conj x) := by
    rw [map_sub, starRingEnd_self_apply]; ring
  calc ‖x - conj y‖ = ‖conj (x - conj y)‖ := (Complex.norm_conj _).symm
    _ = ‖-(y - conj x)‖ := by rw [h]
    _ = ‖y - conj x‖ := norm_neg _

theorem greenH_symm (x y : ℂ) : greenH x y = greenH y x := by
  simp only [greenH, norm_sub_conj_comm x y, norm_sub_rev x y]

theorem neumannH_symm (x y : ℂ) : neumannH x y = neumannH y x := by
  simp only [neumannH, norm_sub_conj_comm x y, norm_sub_rev x y]

/-! ## Measurability -/

theorem measurable_greenH : Measurable (fun p : ℂ × ℂ => greenH p.1 p.2) := by
  have h1 : Continuous (fun p : ℂ × ℂ => ‖p.1 - conj p.2‖) :=
    continuous_norm.comp (continuous_fst.sub (Complex.continuous_conj.comp continuous_snd))
  have h2 : Continuous (fun p : ℂ × ℂ => ‖p.1 - p.2‖) :=
    continuous_norm.comp (continuous_fst.sub continuous_snd)
  exact (Real.measurable_log.comp h1.measurable).sub (Real.measurable_log.comp h2.measurable)

theorem measurable_neumannH : Measurable (fun p : ℂ × ℂ => neumannH p.1 p.2) := by
  have h1 : Continuous (fun p : ℂ × ℂ => ‖p.1 - conj p.2‖) :=
    continuous_norm.comp (continuous_fst.sub (Complex.continuous_conj.comp continuous_snd))
  have h2 : Continuous (fun p : ℂ × ℂ => ‖p.1 - p.2‖) :=
    continuous_norm.comp (continuous_fst.sub continuous_snd)
  exact (Real.measurable_log.comp h2.measurable).neg.sub (Real.measurable_log.comp h1.measurable)

/-! ## The reflection inequality on `Hbar`, and its consequences -/

/-- On the closed upper half-plane, reflecting `y` across the real axis can only move it
farther from `x`: `‖x - y‖ ≤ ‖x - ȳ‖`. -/
theorem norm_sub_le_norm_sub_conj {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar) :
    ‖x - y‖ ≤ ‖x - conj y‖ := by
  have hb : 0 ≤ x.im := hx
  have hd : 0 ≤ y.im := hy
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith [mul_nonneg hb hd]

/-- `greenH` is nonnegative off the diagonal on `Hbar`.

Note: the hypothesis `x ≠ y` is necessary and is *not* implied by `x, y ∈ Hbar` alone: at
`x = y` the formula reads `greenH x x = log ‖x - x̄‖ - log 0 = log (2 * x.im) - 0` (`Real.log`
being junk-valued `0` at `0`), which is negative for e.g. `x = y = I / 4 ∈ Hbar`
(`log (1/2) < 0`). This is a genuine feature of the junk-value convention, not a bug in
`greenH`; the task's "`x y ∈ Hbar`" hypothesis is completed here to "`x y ∈ Hbar`, `x ≠ y`". -/
theorem greenH_nonneg {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar) (hxy : x ≠ y) :
    0 ≤ greenH x y := by
  have h1 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h2 : ‖x - y‖ ≤ ‖x - conj y‖ := norm_sub_le_norm_sub_conj hx hy
  have := Real.log_le_log h1 h2
  unfold greenH
  linarith

/-- Off the diagonal on `Hbar`, the reflection term dominates the ordinary log kernel:
`log ‖x-y‖ ≤ log ‖x - ȳ‖`. This is the lower bound used for the integrability of `greenH`,
`neumannH`. -/
theorem le_log_norm_sub_conj_of_ne {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar) (hxy : x ≠ y) :
    Real.log ‖x - y‖ ≤ Real.log ‖x - conj y‖ :=
  Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) (norm_sub_le_norm_sub_conj hx hy)

/-- On a compact set of radius `R`, the reflection term is bounded above by an absolute
constant. This is the upper bound used for the integrability of `greenH`, `neumannH`. -/
theorem log_norm_sub_conj_le_of_compact {K : Set ℂ} {R : ℝ}
    (hR : K ⊆ Metric.closedBall (0 : ℂ) R) {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    Real.log ‖x - conj y‖ ≤ Real.log (max (2 * R) 1) := by
  rcases eq_or_ne (x - conj y) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]
    exact Real.log_nonneg (le_max_right _ _)
  · apply Real.log_le_log (norm_pos_iff.mpr h0)
    have hxR : ‖x‖ ≤ R := by simpa using hR hx
    have hyR : ‖y‖ ≤ R := by simpa using hR hy
    calc ‖x - conj y‖ ≤ ‖x‖ + ‖conj y‖ := norm_sub_le _ _
      _ = ‖x‖ + ‖y‖ := by rw [Complex.norm_conj]
      _ ≤ R + R := add_le_add hxR hyR
      _ = 2 * R := by ring
      _ ≤ max (2 * R) 1 := le_max_left _ _

end QuantumZipper
