/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.FerniqueDZZ at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueFinite
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Fernique criterion of Ding–Zeitouni–Zhang (DZZ Lemma 2.3) for continuous fields

J. Ding, O. Zeitouni, F. Zhang, *Heat kernel for Liouville Brownian motion and Liouville graph
distance*, arXiv:1807.00422, Lemma 2.3 (LaTeX lines 364–373): there is a universal `C_F > 0`
such that if `B` is a box of side `b` and `{G_v}_{v ∈ B}` is a mean-zero Gaussian field with
`E (G_v - G_u)² ≤ |u - v| / b` on `B`, then (for the continuous version) `E max_B G ≤ C_F`.

Here `B = [x₀.re, x₀.re + b] ×ℂ [x₀.im, x₀.im + b]` (`ferniqueBox`), `|u - v|` is the Euclidean
norm of `ℂ`, and `C_F = 20 √5 √(3 √2)` (`ferniqueCF`). This file proves the bound for a field
whose paths are continuous on `B` (`dzz_lemma23_continuous`); DZZ's remark after the lemma
(line 375) says the continuous version is always the one used. The proof: the finite-family
chaining bound `SupTail.integral_iSup_family_le` (Dudley chaining from LQGDimension, applied
with parameters `(Re v, Im v) ∈ ℝ²`, `a = b`, `L² = √2 / b`, using `|z| ≤ √2 max(|Re z|, |Im z|)`),
then monotone convergence along a dense sequence (`SupTail.integrable_iSup_of_continuous`).
DZZ quote the lemma from Adler 1990, Thm 4.1 (entropy bound), which is not formalized; the
Dudley chaining is the standard proof of that bound in this setting.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ComplexOrder

namespace LQGMetric

namespace SupTail

/-- The closed square `[x₀.re, x₀.re + b] × [x₀.im, x₀.im + b]` of side `b` in `ℂ`. -/
def ferniqueBox (x₀ : ℂ) (b : ℝ) : Set ℂ :=
  Icc x₀.re (x₀.re + b) ×ℂ Icc x₀.im (x₀.im + b)

/-- The universal constant of DZZ Lemma 2.3 obtained from the chaining bound. -/
def ferniqueCF : ℝ := 20 * √5 * √(3 * √2)

lemma isCompact_ferniqueBox (x₀ : ℂ) (b : ℝ) : IsCompact (ferniqueBox x₀ b) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma mem_ferniqueBox_self {x₀ : ℂ} {b : ℝ} (hb : 0 ≤ b) : x₀ ∈ ferniqueBox x₀ b :=
  ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩

/-- Real and imaginary parts as a point of `ℝ²` (sup norm). -/
def reIm (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

lemma norm_le_sqrt_two_mul_norm_reIm (z w : ℂ) : ‖z - w‖ ≤ √2 * ‖reIm z - reIm w‖ := by
  refine (Complex.norm_le_sqrt_two_mul_max (z - w)).trans ?_
  gcongr
  refine max_le ?_ ?_
  · have h := norm_le_pi_norm (reIm z - reIm w) 0
    simpa [reIm] using h
  · have h := norm_le_pi_norm (reIm z - reIm w) 1
    simpa [reIm] using h

lemma norm_reIm_sub_le {x₀ : ℂ} {b : ℝ} (hb : 0 ≤ b) {z w : ℂ} (hz : z ∈ ferniqueBox x₀ b)
    (hw : w ∈ ferniqueBox x₀ b) : ‖reIm z - reIm w‖ ≤ b := by
  obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
  obtain ⟨⟨hw1, hw2⟩, hw3, hw4⟩ := hw
  refine (pi_norm_le_iff_of_nonneg hb).2 fun i => ?_
  fin_cases i
  · simp only [reIm, Pi.sub_apply, Real.norm_eq_abs]
    simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [abs_le]; constructor <;> linarith
  · simp only [reIm, Pi.sub_apply, Real.norm_eq_abs]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [abs_le]; constructor <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **DZZ Lemma 2.3, continuous field** (arXiv:1807.00422, lines 364–373): if
`{G_v}_{v ∈ B}` is a centered Gaussian field on the square `B` of side `b > 0` with
`E (G_v - G_u)² ≤ |u - v| / b` and continuous paths on `B`, then `max_B G` is integrable and
`E max_B G ≤ C_F`. -/
theorem dzz_lemma23_continuous {x₀ : ℂ} {b : ℝ} (hb : 0 < b) {G : ℂ → Ω → ℝ}
    (hG : IsGaussianProcess (fun v : ferniqueBox x₀ b => G v) P)
    (h0 : ∀ v ∈ ferniqueBox x₀ b, ∫ ω, G v ω ∂P = 0)
    (hinc : ∀ u ∈ ferniqueBox x₀ b, ∀ v ∈ ferniqueBox x₀ b,
      ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ ‖u - v‖ / b)
    (hc : ∀ ω, ContinuousOn (fun v => G v ω) (ferniqueBox x₀ b)) :
    Integrable (fun ω => ⨆ v : ferniqueBox x₀ b, G v ω) P ∧
      ∫ ω, (⨆ v : ferniqueBox x₀ b, G v ω) ∂P ≤ ferniqueCF := by
  set B := ferniqueBox x₀ b
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox x₀ b)
  have : Nonempty B := ⟨⟨x₀, mem_ferniqueBox_self hb.le⟩⟩
  have hc' : ∀ ω, Continuous fun v : B => G v ω := fun ω =>
    (continuousOn_iff_continuous_domRestrict.1 (hc ω))
  refine integrable_iSup_of_continuous hG hc' fun n t => ?_
  have hL : (√(√2 / b)) ^ 2 = √2 / b := sq_sqrt (by positivity)
  have h := integral_iSup_family_le hG (fun v => h0 v v.2) (Nat.succ_pos n) t
    (fun v => reIm (v : ℂ)) (L := √(√2 / b)) (a := b) (sqrt_nonneg _)
    (fun i j => norm_reIm_sub_le hb.le (t i).2 (t j).2) (fun i j => by
      rw [hL]
      refine (hinc _ (t j).2 _ (t i).2).trans ?_
      rw [norm_sub_rev, div_mul_eq_mul_div, mul_comm (√2)]
      gcongr
      rw [mul_comm]
      exact norm_le_sqrt_two_mul_norm_reIm _ _)
  refine h.trans_eq ?_
  unfold ferniqueCF
  rw [mul_assoc, ← sqrt_mul (by positivity)]
  congr 2
  push_cast
  field_simp
  ring

end SupTail

end LQGMetric
