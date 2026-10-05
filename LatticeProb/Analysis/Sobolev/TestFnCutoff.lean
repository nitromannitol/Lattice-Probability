/-
# The support cut-off: a test function equal to `1` on a compact subset of a domain

The Rellich support repair needs, for a compact `K` strictly inside a bounded domain `D`, a test
function `η` on `D` that is identically `1` on `K`: the cut-off that keeps the mollification of the
low-frequency centres inside `D`.  This module lands it from Mathlib's
`exists_contMDiffMap_one_nhds_of_subset_interior`, applied to an open set `t` with `K ⊆ t` and
`closure t ⊆ D`.

The remaining elementary step (not taken here) is the construction of such a `t` from `IsDomain D`
and compact `K ⊆ D`, which is the standard separation of a compact set from the closed complement
of an open set.
-/
import Mathlib
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory Set

namespace LatticeProb.Sobolev

/-- **The support cut-off.**  For a bounded domain `D`, a compact `K` and an open `t` with
`K ⊆ t`, `closure t ⊆ D`, there is a test function `η` on `D` with `η = 1` on `K` and
`0 ≤ η ≤ 1` everywhere. -/
theorem exists_isTestFn_eqOn_one {d : ℕ} {D K t : Set (Space d)} (hD : IsDomain D)
    (hK : IsCompact K) (ht : IsOpen t) (hKt : K ⊆ t) (htD : closure t ⊆ D) :
    ∃ η : Space d → ℝ, IsTestFn D η ∧ (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) ∧
      EqOn η 1 K := by
  obtain ⟨f, h1, h0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := modelWithCornersSelf ℝ (Space d)) (n := ⊤) hK.isClosed
    (by rwa [ht.interior_eq])
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (f : Space d → ℝ) :=
    contMDiff_iff_contDiff.mp f.contMDiff
  have hsupp : Function.support (f : Space d → ℝ) ⊆ t := by
    intro x hx
    by_contra hxt
    exact hx (h0 x hxt)
  have htsupp : tsupport (f : Space d → ℝ) ⊆ D :=
    (closure_mono hsupp).trans htD
  have hcs : HasCompactSupport (f : Space d → ℝ) :=
    IsCompact.of_isClosed_subset hD.2.1.isCompact_closure (isClosed_tsupport _)
      (htsupp.trans subset_closure)
  refine ⟨f, ⟨hcont, hcs, htsupp⟩, hf, fun x hx => ?_⟩
  exact h1.self_of_nhdsSet x hx

end LatticeProb.Sobolev
