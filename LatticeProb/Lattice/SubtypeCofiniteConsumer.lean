import LatticeProb.Lattice.SubtypeCofinite

/-!
# Concrete consumers of subtype cofinite decay

A reciprocal profile on the whole one-dimensional lattice converges cofinitely to zero.
Finite subsets, the empty subset, and dimension zero satisfy the same epsilon formulation,
including functions which are nonzero everywhere on a nonempty finite carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Lattice.SubtypeCofiniteConsumer

open Filter Topology
open LatticeProb.Lattice.SubtypeCofinite

/-- The nonzero reciprocal ℓ¹ profile decays on the whole one-dimensional lattice. -/
theorem tendsto_reciprocal_univ_one :
    Tendsto (fun x : (Set.univ : Set (Fin 1 → ℤ)) =>
      1 / ((Int.natAbs (x.val 0) : ℝ) + 1)) cofinite (𝓝 0) := by
  apply (tendsto_zero_iff_natAbs_decay _).mpr
  intro ε hε
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / ε)
  refine ⟨R, fun x hx => ?_⟩
  simp only [Fin.sum_univ_one] at hx
  have hxR : (R : ℝ) < (Int.natAbs (x.val 0) : ℝ) := by exact_mod_cast hx
  have hden : 0 < (Int.natAbs (x.val 0) : ℝ) + 1 := by positivity
  rw [abs_of_pos (div_pos zero_lt_one hden), div_lt_iff₀ hden]
  have hmul : 1 < (R : ℝ) * ε := (div_lt_iff₀ hε).mp hR
  nlinarith

/-- On any finite lattice subset every real function satisfies the explicit decay condition. -/
theorem natAbs_decay_of_finite {d : ℕ} {S : Set (Fin d → ℤ)} (hS : S.Finite)
    (u : S → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : S, R < ∑ j, Int.natAbs (x.val j) → |u x| < ε := by
  haveI : Finite S := hS.to_subtype
  apply (tendsto_zero_iff_natAbs_decay u).mp
  rw [cofinite_eq_bot]
  exact tendsto_bot

/-- The constant seven on a singleton decays outside an ℓ¹ radius. -/
theorem singleton_seven_decay :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : ({(0 : Fin 1 → ℤ)} : Set (Fin 1 → ℤ)),
        R < ∑ j, Int.natAbs (x.val j) → |(7 : ℝ)| < ε :=
  natAbs_decay_of_finite (Set.finite_singleton _) (fun _ => 7)

/-- Every function on the empty lattice subset satisfies the decay condition in every dimension. -/
theorem empty_decay (d : ℕ) (u : (∅ : Set (Fin d → ℤ)) → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : (∅ : Set (Fin d → ℤ)),
        R < ∑ j, Int.natAbs (x.val j) → |u x| < ε :=
  natAbs_decay_of_finite Set.finite_empty u

/-- Dimension zero requires no separate nonemptiness or infinitude hypothesis. -/
theorem zero_dimension_decay (S : Set (Fin 0 → ℤ)) (u : S → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : S, R < ∑ j, Int.natAbs (x.val j) → |u x| < ε :=
  natAbs_decay_of_finite (Set.toFinite S) u

end LatticeProb.Lattice.SubtypeCofiniteConsumer
