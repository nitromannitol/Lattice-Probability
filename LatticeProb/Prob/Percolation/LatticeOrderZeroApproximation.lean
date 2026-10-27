import LatticeProb.External.ArmstrongDarioOrderZero
import Mathlib.LinearAlgebra.FiniteDimensional.Basic


/-!
# Approximation by constants

The rank-one order-zero harmonic growth space consists of constants. The cited
order-zero input therefore gives a local approximation by one constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb.Percolation

namespace LatticeProb.Percolation

/-- A rank-one order-zero harmonic growth space contains only constant functions. -/
theorem harmonicGrowthSpace_zero_eq_const {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (_finite : FiniteDimensional ℝ (harmonicGrowthSpace C 0))
    (rank_one : Module.finrank ℝ (harmonicGrowthSpace C 0) = 1)
    (u : C → ℝ) (hu : u ∈ harmonicGrowthSpace C 0) :
    ∃ c : ℝ, u = fun _ => c := by
  let one : harmonicGrowthSpace C 0 := ⟨fun _ => 1, const_mem_harmonicGrowthSpace C 0 1⟩
  obtain ⟨x, hx⟩ := C.nonempty_supp
  let xC : C := ⟨x, hx⟩
  have hone : one ≠ 0 := by
    intro h
    have hv := congrArg (fun f : harmonicGrowthSpace C 0 => f.val xC) h
    norm_num [one] at hv
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one rank_one hone ⟨u, hu⟩
  refine ⟨c, ?_⟩
  have hv := congrArg Subtype.val hc
  simpa [one, funext_iff] using hv.symm

/-- The order-zero cited input gives one constant approximant for all eligible radii. -/
theorem exists_origin_constant_approximation (input : LatticeProb.External.ArmstrongDarioOrderZero)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration d → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              ∀ (R : ℝ), 2 * X ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ c : ℝ, ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                    componentBallL2 (uniqueInfiniteComponent h') 0 r (u - fun _ => c) ≤
                      C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXmeas, hXnonneg, hXint, hXmoment, hAE⟩ :=
    input d hd p hp hp1
  refine ⟨s, θ, C, hs, hθ, hC, X, hXmeas, hXnonneg, hXint, hXmoment, ?_⟩
  filter_upwards [hAE] with ω hω
  obtain ⟨hex, hω⟩ := hω
  refine ⟨hex, ?_⟩
  intro h R hR u hu
  obtain ⟨hfinite, hrank, happ⟩ := hω h
  obtain ⟨φ, hφ, happrox⟩ := happ R hR u hu
  obtain ⟨c, hc⟩ := harmonicGrowthSpace_zero_eq_const _ hfinite hrank φ hφ
  refine ⟨c, ?_⟩
  intro r hr hRr
  simpa only [hc] using happrox r hr hRr

end LatticeProb.Percolation
