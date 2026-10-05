/-
# Structural properties of the mollified family `f ⋆ ρ`

The first half of `FrechetKolmogorovMollifiedCompact` (`FrechetKolmogorovReduce.lean`) needs the
mollified family `{f ⋆ ρ}` to be smooth and compactly supported, so that Arzelà–Ascoli
applies on the fixed compact `tsupport f + tsupport ρ`.  This module lands those two structural
facts for `convReal`, directly from Mathlib's convolution API.

* `hasCompactSupport_convReal` — `tsupport (f ⋆ ρ) ⊆ tsupport f + tsupport ρ`;
* `contDiff_convReal` — `f ⋆ ρ` is `C^∞` when `ρ` is `C^∞` compactly supported and `f`
  is locally integrable.
-/
import LatticeProb.Analysis.Sobolev.FrechetKolmogorovReduce

open MeasureTheory
open scoped Topology

namespace LatticeProb.Sobolev

/-- **Support of the mollified function.** -/
theorem hasCompactSupport_convReal {d : ℕ} {f ρ : Space d → ℝ} (hf : HasCompactSupport f)
    (hρ : HasCompactSupport ρ) : HasCompactSupport (convReal f ρ) := by
  unfold convReal
  exact hf.convolution (ContinuousLinearMap.mul ℝ ℝ) hρ

/-- **Smoothness of the mollified function.** -/
theorem contDiff_convReal {d : ℕ} {f ρ : Space d → ℝ} (hf : LocallyIntegrable f volume)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (convReal f ρ) := by
  unfold convReal
  exact hρcs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hρ

end LatticeProb.Sobolev
