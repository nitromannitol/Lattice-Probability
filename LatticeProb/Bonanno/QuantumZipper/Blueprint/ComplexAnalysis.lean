/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Blueprint.ComplexAnalysis at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Loewner.Reverse
import LatticeProb.Bonanno.QuantumZipper.Loewner.Curves

/-!
# Complex-analysis blueprint items for deterministic welding uniqueness

`Prop`-valued statements of standard results of geometric function theory that are used in the
proof of deterministic conformal-welding uniqueness (blueprint node A3,
`QuantumZipper.Proofs.Zipper.WeldingUniqueness`). Nothing is proved here.
-/

noncomputable section

open Set

namespace QuantumZipper.Blueprint

/-- The welding relation on boundary points of `ℍ̄` induced by a welding homeomorphism
`φ : [a, 0] → [0, φ a]`: the two (complex) points `x, y` are the two real points `s ∈ [a, 0]`
and `φ s`, in some order. -/
def WeldingRel (a : ℝ) (φ : ℝ → ℝ) (x y : ℂ) : Prop :=
  ∃ s ∈ Icc a 0, (x = (s : ℂ) ∧ y = (φ s : ℂ)) ∨ (x = (φ s : ℂ) ∧ y = (s : ℂ))

/-- `F` is the Carathéodory boundary extension of the reverse Loewner map `revMap W T` to the
closed upper half-plane `ℍ̄ = Hbar`, with the two-sided boundary correspondence of a simple
arc from `0`:

* `F = revMap W T` on `ℍ` and `F` is continuous on `ℍ̄`;
* `F` maps `ℍ̄` onto `ℍ̄` (onto `ℍ \ K` from `ℍ`, onto `ℝ ∪ K̄` from `ℝ`);
* `F (0₋) = 0` and the welding homeomorphism sends `0₋` to `0₊`;
* a real point `x` is sent to `ℝ` iff `x ∉ (0₋, 0₊)` (the interval `(0₋, 0₊)` is sent onto the
  arc `K ⊆ ℍ`);
* two points of `ℍ̄` have the same image iff they are equal or are welded to each other by
  `weldingHom W T` (the two sides of the arc are glued by the welding homeomorphism
  `[0₋, 0] → [0, 0₊]`, the tip being the image of `0`). -/
def IsCaratheodoryRevExt (W : ℝ → ℝ) (T : ℝ) (F : ℂ → ℂ) : Prop :=
  EqOn F (revMap W T) H ∧ ContinuousOn F Hbar ∧ SurjOn F Hbar Hbar ∧
    F (zeroMinus W T) = 0 ∧ weldingHom W T (zeroMinus W T) = zeroPlus W T ∧
    (∀ x : ℝ, (F x).im = 0 ↔ (x ≤ zeroMinus W T ∨ zeroPlus W T ≤ x)) ∧
    ∀ x ∈ Hbar, ∀ y ∈ Hbar,
      F x = F y ↔ (x = y ∨ WeldingRel (zeroMinus W T) (weldingHom W T) x y)

/-- **Carathéodory extension for the complement of a simple arc** (applied to the reverse Loewner
map). If the reverse hull `revHull W T` is a simple curve from a real point, then `revMap W T`,
a conformal map of `ℍ` onto the Jordan-type domain `ℍ \ K` whose boundary is locally connected,
extends continuously to `ℍ̄`, and the extension has the two-sided boundary correspondence onto
the arc described in `IsCaratheodoryRevExt`.

References: Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer 1992, Theorem 2.1
(Carathéodory–Torhorst: continuous extension iff the boundary is locally connected) and
Proposition 2.5 / Theorem 2.6 (the preimages of a boundary point, i.e. the prime-end
correspondence for a slit domain); G. Lawler, *Conformally Invariant Processes in the Plane*,
AMS 2005, §4.1 (reverse Loewner maps of simple curves and their welding);
S. Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.3–1.4. -/
def RevMapCaratheodory : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ T : ℝ, 0 < T → IsSimpleCurveHull (revHull W T) →
    ∃ F : ℂ → ℂ, IsCaratheodoryRevExt W T F

/-- **Painlevé's theorem for a line** (the analytic core of the Schwarz reflection principle):
a function continuous on an open set `U` and holomorphic on `U` off the real axis is holomorphic
on `U`. Reference: L. Ahlfors, *Complex Analysis*, 3rd ed., §4.6.5 (proof via Morera's
theorem); J. B. Conway, *Functions of One Complex Variable I*, Theorem IX.1.1.
Proved (not assumed) in `QuantumZipper.Proofs.Zipper.WeldingUniqueness` as `painleveRealLine`. -/
def PainleveRealLine : Prop :=
  ∀ (g : ℂ → ℂ) (U : Set ℂ), IsOpen U → ContinuousOn g U →
    DifferentiableOn ℂ g (U \ {z | z.im = 0}) → DifferentiableOn ℂ g U

end QuantumZipper.Blueprint
