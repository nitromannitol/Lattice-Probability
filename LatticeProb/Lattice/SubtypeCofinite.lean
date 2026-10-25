import LatticeProb.Walk.MaxDisp
import LatticeProb.ParticleHoleLemmas

/-!
# Cofinite decay on arbitrary subsets of the integer lattice

Bounded coordinate ℓ¹ sums give finite subsets of any lattice subtype. Consequently,
cofinite convergence to zero is exactly epsilon decay outside a natural ℓ¹ radius.
The existing `graphNorm` and its real-cast identity fix the norm convention explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Lattice.SubtypeCofinite

open Filter Topology

variable {d : ℕ} {S : Set (Fin d → ℤ)}

/-- Every ℓ¹ sublevel set in an arbitrary lattice subtype is finite. -/
theorem finite_graphNorm_le (S : Set (Fin d → ℤ)) (R : ℕ) :
    {x : S | graphNorm x.val ≤ R}.Finite := by
  have hbox := (boxFinset (0 : Site d) R).finite_toSet.preimage
    (f := fun x : S => x.val) Subtype.val_injective.injOn
  refine hbox.subset fun x hx => ?_
  change x.val ∈ boxFinset (0 : Site d) R
  rw [mem_boxFinset_iff]
  intro j
  have hj : (x.val j).natAbs ≤ graphNorm x.val :=
    Finset.single_le_sum (f := fun k => (x.val k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hle : (x.val j).natAbs ≤ R := hj.trans hx
  simpa only [Pi.zero_apply, sub_zero, Int.abs_eq_natAbs] using
    (show ((x.val j).natAbs : ℤ) ≤ (R : ℤ) from Nat.cast_le.mpr hle)

/-- Any subset of a lattice subtype with a bounded ℓ¹ sum is finite. -/
theorem finite_of_graphNorm_bounded {A : Set S}
    (hA : ∃ R : ℕ, ∀ x ∈ A, graphNorm x.val ≤ R) : A.Finite := by
  obtain ⟨R, hR⟩ := hA
  exact (finite_graphNorm_le S R).subset hR

/-- A predicate holds cofinitely precisely when it holds outside an ℓ¹ radius. -/
theorem eventually_cofinite_iff_exists_radius (p : S → Prop) :
    (∀ᶠ x in cofinite, p x) ↔
      ∃ R : ℕ, ∀ x : S, R < ∑ j, Int.natAbs (x.val j) → p x := by
  classical
  rw [eventually_cofinite]
  constructor
  · intro hp
    obtain ⟨R, hR⟩ := (hp.image (fun x : S => graphNorm x.val)).bddAbove
    refine ⟨R, fun x hx => ?_⟩
    by_contra hpx
    exact (not_le_of_gt hx) (hR (Set.mem_image_of_mem _ hpx))
  · rintro ⟨R, hR⟩
    refine (finite_graphNorm_le S R).subset fun x hx => ?_
    exact le_of_not_gt (fun hgt => hx (hR x hgt))

/-- Cofinite convergence is exactly decay beyond a natural coordinate ℓ¹ radius. -/
theorem tendsto_zero_iff_natAbs_decay (u : S → ℝ) :
    Tendsto u cofinite (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
        ∀ x : S, R < ∑ j, Int.natAbs (x.val j) → |u x| < ε := by
  rw [Metric.tendsto_nhds]
  simp only [Real.dist_eq, sub_zero]
  exact forall_congr' fun ε => imp_congr_right fun _ =>
    eventually_cofinite_iff_exists_radius (fun x => |u x| < ε)

/-- The same decay statement uses the real sum of absolute coordinates, via `graphNorm_cast`.
Natural radii suffice also for this real-valued ℓ¹ sum. -/
theorem tendsto_zero_iff_real_abs_decay (u : S → ℝ) :
    Tendsto u cofinite (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
        ∀ x : S, (R : ℝ) < ∑ j, |(x.val j : ℝ)| → |u x| < ε := by
  rw [tendsto_zero_iff_natAbs_decay]
  have hcast (x : S) (R : ℕ) :
      R < ∑ j, Int.natAbs (x.val j) ↔ (R : ℝ) < ∑ j, |(x.val j : ℝ)| := by
    rw [← graphNorm_cast]
    exact_mod_cast (Iff.rfl : R < graphNorm x.val ↔ R < graphNorm x.val)
  simp only [← hcast]

end LatticeProb.Lattice.SubtypeCofinite
