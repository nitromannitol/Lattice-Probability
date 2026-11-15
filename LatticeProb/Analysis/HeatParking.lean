import LatticeProb.Analysis.HeatKernelBounds
import LatticeProb.Analysis.HeatDuhamel
import LatticeProb.Analysis.HeatRepresentation
import LatticeProb.Analysis.HeatInterior
import LatticeProb.Analysis.HeatCompactness

/-!
# Interior regularity and compactness for the heat equation `∂ₛu = (2d)⁻¹Δu`

Unconditional versions of the two heat-equation statements in the form used for the parking
estimates, where the space-time variable is `(s, x)` and `L = (2d)⁻¹Δ` is `contOp`:

* `heat_interior_regularity`: a continuous weak solution in an open set `U ⊆ {s > 0}`, tested against
  the space-time test functions supported in `U`, agrees on `U` with a smooth classical solution.
* `heat_compactness`: a sequence of nonnegative classical solutions in an open set `U` whose
  integrals over the compact subsets of `U` are bounded has a subsequence converging uniformly on
  the compact subsets of `U` to a nonnegative classical solution.

Both are obtained by composing the conditional theorems `heatInteriorRegularity_of_representation`
and `heatCompactness_of_interiorBounds` with the smoothness and decay of the heat kernel off the
hyperplane `x = 0` (`contDiffOn_heatKernel_off_origin`, `iteratedFDeriv_heatKernel_bound`), the
Duhamel formula (`heatDuhamel`), the local representation formula
(`heatRepresentation_of_duhamel`) and the interior bounds (`heatInteriorBounds_of_duhamel`).
-/

open MeasureTheory Metric Filter Topology
open scoped ContDiff
open LatticeProb.Heat

namespace LatticeProb.WhiteNoise

private theorem heatDuhamel_forall :
    ∀ d : ℕ, 1 ≤ d → ∀ v : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
      HasCompactSupport v → ∀ (t : ℝ) (x : Fin d → ℝ), v (t, x) =
        ∫ q : ℝ × (Fin d → ℝ), heatKernel d (t - q.1) (x - q.2) *
          (deriv (fun s => v (s, q.2)) q.1 - contOp d (fun y => v (q.1, y)) q.2) :=
  fun _ hd _ hv hvc t x => heatDuhamel hd hv hvc t x

private theorem heatKernel_iteratedFDeriv_bound_forall :
    ∀ (d : ℕ) (n : ℕ) (ρ T : ℝ), 1 ≤ d → 0 < ρ → 0 < T → ∃ C : ℝ, ∀ p : ℝ × (Fin d → ℝ),
      0 < p.1 → p.1 ≤ T → ρ ≤ ‖p.2‖ →
        ‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) p‖ ≤ C :=
  fun d n ρ T hd hρ hT => iteratedFDeriv_heatKernel_bound d n ρ T hd hρ hT

private theorem contDiffOn_heatKernel_forall :
    ∀ d : ℕ, 1 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) {p | p.2 ≠ 0} :=
  fun _ hd => contDiffOn_heatKernel_off_origin hd

/-- **Interior regularity of weak solutions of the heat equation.** A continuous weak solution of
`∂ₛu = (2d)⁻¹Δu` in an open set `U ⊆ {s > 0}` agrees on `U` with a smooth classical solution. -/
theorem heat_interior_regularity :
    ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
      U ⊆ {p : ℝ × (Fin d → ℝ) | 0 < p.1} →
      ∀ u : ℝ × (Fin d → ℝ) → ℝ, Continuous u →
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ U →
          -∫ p : ℝ × (Fin d → ℝ), u p * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), u p * contOp d (fun x => ψ (p.1, x)) p.2) →
        ∃ v : ℝ × (Fin d → ℝ) → ℝ,
          ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
          (∀ p ∈ U, u p = v p) ∧
          (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
            (contOp d (fun x => v (p.1, x)) p.2) p.1) :=
  heatInteriorRegularity_of_representation contDiffOn_heatKernel_forall
    (heatRepresentation_of_duhamel contDiffOn_heatKernel_forall
      heatKernel_iteratedFDeriv_bound_forall heatDuhamel_forall)

/-- **Compactness of nonnegative classical solutions of the heat equation.** A sequence of
nonnegative classical solutions of `∂ₛu = (2d)⁻¹Δu` in an open set `U` with bounded integrals over
the compact subsets of `U` has a subsequence converging uniformly on the compact subsets of `U` to a
nonnegative classical solution. -/
theorem heat_compactness :
    ∀ (d : ℕ), 1 ≤ d → ∀ (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
      ∀ f : ℕ → ℝ × (Fin d → ℝ) → ℝ,
        (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) U) →
        (∀ n p, p ∈ U → 0 ≤ f n p) →
        (∀ n p, p ∈ U → HasDerivAt (fun s => f n (s, p.2))
          (contOp d (fun x => f n (p.1, x)) p.2) p.1) →
        (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
          ∃ C : ℝ, ∀ n, IntegrableOn (f n) K ∧ (∫ p in K, ‖f n p‖) ≤ C) →
        ∃ (r : ℕ → ℕ) (v : ℝ × (Fin d → ℝ) → ℝ), StrictMono r ∧
          ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
          (∀ p ∈ U, 0 ≤ v p) ∧
          (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
            (contOp d (fun x => v (p.1, x)) p.2) p.1) ∧
          (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
            TendstoUniformlyOn (fun n => f (r n)) v atTop K) :=
  heatCompactness_of_interiorBounds
    (heatInteriorBounds_of_duhamel contDiffOn_heatKernel_forall
      heatKernel_iteratedFDeriv_bound_forall heatDuhamel_forall)
    (heatWeakRegularity_of_representation contDiffOn_heatKernel_forall
      (heatRepresentation_of_duhamel contDiffOn_heatKernel_forall
        heatKernel_iteratedFDeriv_bound_forall heatDuhamel_forall))

end LatticeProb.WhiteNoise
