/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Analysis.Removability at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Bornology.Basic

/-!
# Conformal removability and Hölder domains

Definitions only.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace QuantumZipper

/-- A compact set `K ⊆ ℂ` is *conformally removable* if every homeomorphism of `ℂ` that is
holomorphic off `K` is holomorphic everywhere (hence affine). -/
def IsConformallyRemovable (K : Set ℂ) : Prop :=
  IsCompact K ∧ ∀ φ : ℂ ≃ₜ ℂ, DifferentiableOn ℂ φ Kᶜ → Differentiable ℂ φ

/-- The complement `ℂ̂ \ K` of the compact set `K` in the Riemann sphere is a *Hölder domain*:
there is a conformal bijection `φ` from the exterior disk `{z | 1 < ‖z‖}` onto `Kᶜ`, conformal
at `∞` (`φ z / z → c ≠ 0` as `z → ∞`), which is uniformly Hölder on the annulus
`1 < ‖z‖ ≤ 2` (equivalently, extends Hölder-continuously to the unit circle).
This is the notion used in Jones–Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000), Corollary 2, for the domain `ℂ̂ \ K`.
We also require `K` compact, as the notion presupposes. -/
def IsHolderDomainSphere (K : Set ℂ) : Prop :=
  IsCompact K ∧ ∃ φ : ℂ → ℂ,
    DifferentiableOn ℂ φ {z | 1 < ‖z‖} ∧ BijOn φ {z | 1 < ‖z‖} Kᶜ ∧
    (∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun z => φ z / z) (Bornology.cobounded ℂ) (𝓝 c)) ∧
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, ∀ z w : ℂ, 1 < ‖z‖ → ‖z‖ ≤ 2 → 1 < ‖w‖ → ‖w‖ ≤ 2 →
      ‖φ z - φ w‖ ≤ C * ‖z - w‖ ^ α

end QuantumZipper
