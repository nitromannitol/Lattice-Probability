/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.Harmonic at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects

open scoped Topology InnerProductSpace
open InnerProductSpace Laplacian

namespace BouRabeeGwynne

/--
Classical `C²` harmonicity on an open Euclidean set.  This uses mathlib's
finite-dimensional inner-product-space Laplacian, hence is the standard
continuum notion used in Theorem B.
-/
def IsHarmonicOn {d : ℕ} (h : Euc d → ℝ) (U : Set (Euc d)) : Prop :=
  ContDiffOn ℝ 2 h U ∧ ∀ x ∈ U, Δ h x = 0

lemma IsHarmonicOn.contDiffOn {d : ℕ} {h : Euc d → ℝ} {U : Set (Euc d)}
    (hh : IsHarmonicOn h U) : ContDiffOn ℝ 2 h U := hh.1

lemma IsHarmonicOn.laplacian_eq_zero {d : ℕ} {h : Euc d → ℝ} {U : Set (Euc d)}
    (hh : IsHarmonicOn h U) {x : Euc d} (hx : x ∈ U) : Δ h x = 0 :=
  hh.2 x hx

/-- Harmonicity in a neighborhood of `closure U`, as in Theorem B(a). -/
def HarmonicNearClosure {d : ℕ} (h : Euc d → ℝ) (U : Set (Euc d)) : Prop :=
  ∃ W : Set (Euc d), IsOpen W ∧ closure U ⊆ W ∧ IsHarmonicOn h W

lemma HarmonicNearClosure.harmonicOn {d : ℕ} {h : Euc d → ℝ} {U : Set (Euc d)}
    (hh : HarmonicNearClosure h U) : IsHarmonicOn h U := by
  rcases hh with ⟨W, hWopen, hUW, hhW⟩
  constructor
  · exact hhW.1.mono (subset_closure.trans hUW)
  · intro x hx
    exact hhW.2 x (hUW (subset_closure hx))

/-- Continuity up to the boundary, the extra analytic hypothesis in Theorem B(b). -/
def ContinuousOnClosure {d : ℕ} (h : Euc d → ℝ) (U : Set (Euc d)) : Prop :=
  ContinuousOn h (closure U)

end BouRabeeGwynne
