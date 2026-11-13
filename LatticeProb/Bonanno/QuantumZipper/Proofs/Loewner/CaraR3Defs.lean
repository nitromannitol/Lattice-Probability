/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR3Defs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Loewner.Reverse

/-!
# EXT-CA node R3, interface: the boundary extension of `revMap` in `H`-coordinates

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R3**. Fix a continuous driver `W` with
`W 0 = 0`, a time `T > 0`, and a simple arc `γ` (continuous and injective on `[0,1]`, `γ 0`
real, `γ (0,1] ⊆ ℍ`) with `revHull W T = γ '' Ioc 0 1`.

`RevExt W T γ F` collects what the Carathéodory boundary theory (nodes C3–C7, applied in the
bounded model `cayley ∘ revMap W T` with `E = sphere 0 1 ∪ cayley '' γ '' Icc 0 1`) says about
the continuous extension `F` of `revMap W T` to `Hbar`, translated back to `H`-coordinates:

* `eqOn`, `cont`: `F = revMap W T` on `ℍ`, `F` continuous on `ℍ̄` (C3);
* `bdry`, `surj`: `F` maps `ℝ` into, and onto, `ℝ ∪ γ [0,1]` (C3, C7);
* `noConst`: `F` is not constant on a nondegenerate real interval (C4);
* `inj_real`, `inj_tip`: a real value other than `γ 0`, and the tip `γ 1`, are attained at most
  once on `ℝ` (C6: `E \ {q}` is connected for these `q`);
* `fold`: the fold lemma C5 in `H`-coordinates (the value at `∞` is dropped).

The existence of such an `F` is node R3 (`CaraR3.lean`).
-/

noncomputable section

open Set

namespace QuantumZipper

namespace CaraR

/-- The continuous boundary extension `F` of `revMap W T` for a simple hull
`revHull W T = γ '' Ioc 0 1`, with the boundary correspondence facts C3–C7 in `H`-coordinates.
See the module docstring. -/
structure RevExt (W : ℝ → ℝ) (T : ℝ) (γ : ℝ → ℂ) (F : ℂ → ℂ) : Prop where
  eqOn : EqOn F (revMap W T) H
  cont : ContinuousOn F Hbar
  bdry : ∀ x : ℝ, (F x).im = 0 ∨ F x ∈ γ '' Icc 0 1
  surj : ∀ p : ℂ, (p.im = 0 ∨ p ∈ γ '' Icc 0 1) → ∃ x : ℝ, F x = p
  noConst : ∀ a b : ℝ, a < b → ∀ c : ℂ, ¬ ∀ t ∈ Ioo a b, F t = c
  inj_real : ∀ p : ℂ, p.im = 0 → p ≠ γ 0 → ∀ x y : ℝ, F x = p → F y = p → x = y
  inj_tip : ∀ x y : ℝ, F x = γ 1 → F y = γ 1 → x = y
  fold : ∀ x y : ℝ, x < y → ∀ q : ℂ, F x = q → F y = q →
    ∀ Z : Set ℂ, Z ⊆ {p : ℂ | p.im = 0 ∨ p ∈ γ '' Icc 0 1} \ {q} → IsPreconnected Z →
      (∀ t ∈ Ioo x y, F t ∉ Z) ∨ (∀ s : ℝ, s ∉ Icc x y → F s ∉ Z)

/-- The statement of node R3: every simple reverse hull has a boundary extension `RevExt`.
Proved as `CaraR.extExists` (`CaraR3.lean`); used as a hypothesis only by intermediate lemmas
(R5, R7) that apply R3 to shifted drivers. -/
def ExtExists : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ T : ℝ, 0 < T → ∀ γ : ℝ → ℂ,
    ContinuousOn γ (Icc 0 1) → InjOn γ (Icc 0 1) → (γ 0).im = 0 →
    (∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H) → revHull W T = γ '' Ioc 0 1 →
    ∃ F : ℂ → ℂ, RevExt W T γ F

end CaraR

end QuantumZipper
