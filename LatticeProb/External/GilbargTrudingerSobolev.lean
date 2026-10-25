import LatticeProb.Analysis.Elliptic.WeakDirichlet

/-!
# Sobolev inputs from Gilbarg–Trudinger

These are propositions describing two cited book inputs, with no asserted proofs.
The Sobolev space is represented by the actual L² function and all its L² weak
coordinate derivatives. The operator has coefficients `aᵢⱼ = a₀ δᵢⱼ`, `b = c = 0`,
and zeroth-order coefficient `−μ` in the book's convention.
-/

namespace LatticeProb.External

open MeasureTheory LatticeProb.Elliptic.WeakDirichlet
open scoped Topology

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics in Mathematics (2001), §7.5, printed p. 154, final paragraph before §7.6:
a W¹,² function vanishing continuously on the boundary belongs to W¹,²₀.
All coordinates are actual L² elements; the displayed identities assert every
coordinate weak derivative against every supported smooth test. Their integrals
are finite by `integrable_mul_test`. The connected open set is the book's domain;
no boundary smoothness is required. -/
def GilbargTrudingerZeroBoundaryApproximation : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (U : Set (Fin d → ℝ)),
    IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∀ (v : H1Product U),
        (∀ (ψ : TestFunction U) (i : Fin d),
          (∫ x in U, v 0 x * (ψ.deriv i).val x) =
            -(∫ x in U, v i.succ x * ψ.val x)) →
        ∀ (u : (Fin d → ℝ) → ℝ), ContinuousOn u (closure U) →
          Set.EqOn u (fun _ => 0) (frontier U) →
          (fun x => v 0 x) =ᵐ[volume.restrict U] u →
          v ∈ closure (Set.range (TestFunction.graph (U := U)))

/-- Gilbarg–Trudinger, same edition, Corollary 8.2, printed p. 180, with
(8.2)–(8.8), pp. 177–179: a homogeneous zero-boundary weak solution is zero
as a Sobolev element, hence in every coordinate of its Sobolev graph.
Strict ellipticity is `a₀ > 0`; the sign condition (8.8) is `−μ ≤ 0` and permits
`μ = 0`. The bounded constant coefficients satisfy (8.6). Smooth compactly
supported tests are used here. The continuous-functional argument (8.7), p. 178,
and the defining H¹₀ closure extend the equation to H¹₀ tests; this extension is
proved in `WeakDirichletAlgebra`. There is no existence or classical-solution claim. -/
def GilbargTrudingerWeakHomogeneousUniqueness : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (U : Set (Fin d → ℝ)),
    IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ → ∀ (u : H10 U),
        IsWeakSolution U μ a₀ (fun _ => 0) u → u.val = 0

end LatticeProb.External
