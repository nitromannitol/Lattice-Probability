import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Gluing differentiable functions on closed sets

A function and its derivative can be glued along a closed cover when the
corresponding values agree on the overlap.
-/

namespace LatticeProb.Elliptic.HolderExtension

open Set
open scoped ContDiff

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contDiff_succ_of_cover {n : ℕ} {s t : Set E} {f : E → F}
    {f' : E → E →L[ℝ] F} (hcover : s ∪ t = univ)
    (hf' : ContDiff ℝ n f')
    (hs : ∀ x, HasFDerivWithinAt f (f' x) s x)
    (ht : ∀ x, HasFDerivWithinAt f (f' x) t x) :
    ContDiff ℝ (n + 1) f := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨f', hf', fun x => ?_⟩
  exact hasFDerivWithinAt_univ.mp (hcover ▸ (hs x).union (ht x))

/-- Derivatives on a closed cover combine into a global derivative. -/
theorem contDiff_succ_of_closed_cover {n : ℕ} {s t : Set E} {f : E → F}
    {f' : E → E →L[ℝ] F} (hcover : s ∪ t = univ) (hsclosed : IsClosed s)
    (htclosed : IsClosed t) (hf' : ContDiff ℝ n f')
    (hs : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (ht : ∀ x ∈ t, HasFDerivWithinAt f (f' x) t x) :
    ContDiff ℝ (n + 1) f := by
  apply contDiff_succ_of_cover hcover hf'
  · intro x
    by_cases hx : x ∈ s
    · exact hs x hx
    · apply HasFDerivWithinAt.of_notMem_closure
      rwa [hsclosed.closure_eq]
  · intro x
    by_cases hx : x ∈ t
    · exact ht x hx
    · apply HasFDerivWithinAt.of_notMem_closure
      rwa [htclosed.closure_eq]

/-- Piecewise functions with matching first derivatives are continuously differentiable. -/
theorem contDiff_one_piecewise_of_closed_cover {s t : Set E} [∀ x, Decidable (x ∈ s)]
    {f g : E → F}
    {f' g' : E → E →L[ℝ] F} (hcover : s ∪ t = univ)
    (hsclosed : IsClosed s) (htclosed : IsClosed t)
    (hfg : ∀ x ∈ s ∩ t, f x = g x)
    (hfg' : ∀ x ∈ s ∩ t, f' x = g' x)
    (hf' : ContinuousOn f' s) (hg' : ContinuousOn g' t)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hg : ∀ x ∈ t, HasFDerivWithinAt g (g' x) t x) :
    ContDiff ℝ 1 (s.piecewise f g) := by
  classical
  have hfs : EqOn (s.piecewise f g) f s := s.piecewise_eqOn f g
  have hgt : EqOn (s.piecewise f g) g t := by
    intro x hx
    by_cases hxs : x ∈ s
    · rw [piecewise_eq_of_mem _ _ _ hxs]
      exact hfg x ⟨hxs, hx⟩
    · exact piecewise_eq_of_notMem _ _ _ hxs
  have hfs' : EqOn (s.piecewise f' g') f' s := s.piecewise_eqOn f' g'
  have hgt' : EqOn (s.piecewise f' g') g' t := by
    intro x hx
    by_cases hxs : x ∈ s
    · rw [piecewise_eq_of_mem _ _ _ hxs]
      exact hfg' x ⟨hxs, hx⟩
    · exact piecewise_eq_of_notMem _ _ _ hxs
  have hc : Continuous (s.piecewise f' g') := by
    rw [← continuousOn_univ, ← hcover]
    exact (hf'.congr hfs').union_of_isClosed (hg'.congr hgt') hsclosed htclosed
  apply contDiff_succ_of_closed_cover (n := 0) hcover hsclosed htclosed
    (contDiff_zero.mpr hc)
  · intro x hx
    rw [hfs' hx]
    exact (hf x hx).congr' hfs hx
  · intro x hx
    rw [hgt' hx]
    exact (hg x hx).congr' hgt hx

/-- Higher regularity follows from regularity of the glued derivative. -/
theorem contDiff_succ_piecewise_of_closed_cover {n : ℕ} {s t : Set E}
    [∀ x, Decidable (x ∈ s)] {f g : E → F} {f' g' : E → E →L[ℝ] F}
    (hcover : s ∪ t = univ) (hsclosed : IsClosed s) (htclosed : IsClosed t)
    (hfg : ∀ x ∈ s ∩ t, f x = g x)
    (hfg' : ∀ x ∈ s ∩ t, f' x = g' x)
    (hf' : ContDiff ℝ n (s.piecewise f' g'))
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hg : ∀ x ∈ t, HasFDerivWithinAt g (g' x) t x) :
    ContDiff ℝ (n + 1) (s.piecewise f g) := by
  have hfs : EqOn (s.piecewise f g) f s := s.piecewise_eqOn f g
  have hgt : EqOn (s.piecewise f g) g t := by
    intro x hx
    by_cases hxs : x ∈ s
    · rw [piecewise_eq_of_mem _ _ _ hxs]
      exact hfg x ⟨hxs, hx⟩
    · exact piecewise_eq_of_notMem _ _ _ hxs
  have hfs' : EqOn (s.piecewise f' g') f' s := s.piecewise_eqOn f' g'
  have hgt' : EqOn (s.piecewise f' g') g' t := by
    intro x hx
    by_cases hxs : x ∈ s
    · rw [piecewise_eq_of_mem _ _ _ hxs]
      exact hfg' x ⟨hxs, hx⟩
    · exact piecewise_eq_of_notMem _ _ _ hxs
  apply contDiff_succ_of_closed_cover (n := n) hcover hsclosed htclosed hf'
  · intro x hx
    rw [hfs' hx]
    exact (hf x hx).congr' hfs hx
  · intro x hx
    rw [hgt' hx]
    exact (hg x hx).congr' hgt hx

end
end LatticeProb.Elliptic.HolderExtension
