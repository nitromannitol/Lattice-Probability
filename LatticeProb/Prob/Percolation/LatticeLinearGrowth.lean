import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth
import LatticeProb.Lattice.SubtypeCofinite
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Pointwise linear growth on actual lattice components

The source pointwise condition is big O of the literal coordinate ℓ¹ sum along the
cofinite filter. Finite ℓ¹ sublevels identify this with radial infinity. Mathlib's
cofinite bound theorem absorbs every finite exception into a global affine bound,
which feeds the accepted producer for the harmonic growth space A₁.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open Filter Asymptotics
open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- Pointwise source growth `u(x) = O(|x|)` with the literal ℓ¹ norm.
On finite components the cofinite filter is bottom, so every function satisfies it. -/
def componentPointwiseLinearGrowth (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  u =O[cofinite] (fun x : C => ∑ i : Fin d, |(x.val i : ℝ)|)

/-- A positive constant bounds the function outside a finite exceptional set. -/
theorem componentPointwiseLinearGrowth_iff_finite (C : OpenComponent ω) (u : C → ℝ) :
    componentPointwiseLinearGrowth C u ↔ ∃ M : ℝ, 0 < M ∧
      {x : C | ¬ |u x| ≤ M * (∑ i : Fin d, |(x.val i : ℝ)|)}.Finite := by
  have hn (x : C) : 0 ≤ ∑ i : Fin d, |(x.val i : ℝ)| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  constructor
  · intro h
    obtain ⟨M, hM, hb⟩ := h.exists_pos
    refine ⟨M, hM, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using
      (eventually_cofinite.mp hb.bound)
  · rintro ⟨M, _, hM⟩
    apply IsBigO.of_bound M
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using
      (eventually_cofinite.mpr hM)

/-- The cofinite condition is exactly a bound outside a natural ℓ¹ radius. -/
theorem componentPointwiseLinearGrowth_iff_tail (C : OpenComponent ω) (u : C → ℝ) :
    componentPointwiseLinearGrowth C u ↔ ∃ M : ℝ, 0 < M ∧ ∃ R : ℕ,
      ∀ x : C, (R : ℝ) < ∑ i : Fin d, |(x.val i : ℝ)| →
        |u x| ≤ M * (∑ i : Fin d, |(x.val i : ℝ)|) := by
  have hr (x : C) (R : ℕ) :
      R < ∑ i, Int.natAbs (x.val i) ↔
        (R : ℝ) < ∑ i : Fin d, |(x.val i : ℝ)| := by
    rw [← graphNorm_cast]
    exact_mod_cast (Iff.rfl : R < graphNorm x.val ↔ R < graphNorm x.val)
  rw [componentPointwiseLinearGrowth_iff_finite]
  have ht (M : ℝ) :=
    Lattice.SubtypeCofinite.eventually_cofinite_iff_exists_radius (S := C.supp)
      (fun x => |u x| ≤ M * (∑ i : Fin d, |(x.val i : ℝ)|))
  constructor
  · rintro ⟨M, hM, hb⟩
    obtain ⟨R, hR⟩ := (ht M).mp (eventually_cofinite.mpr hb)
    exact ⟨M, hM, R, fun x hx => hR x ((hr x R).mpr hx)⟩
  · rintro ⟨M, hM, R, hR⟩
    refine ⟨M, hM, eventually_cofinite.mp ((ht M).mpr ⟨R, ?_⟩)⟩
    exact fun x hx => hR x ((hr x R).mp hx)

/-- An equivalent epsilon-tail form allows every positive slack in the growth constant. -/
theorem componentPointwiseLinearGrowth_iff_epsilon_tail
    (C : OpenComponent ω) (u : C → ℝ) :
    componentPointwiseLinearGrowth C u ↔ ∃ M : ℝ, 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ x : C,
        (R : ℝ) < ∑ i : Fin d, |(x.val i : ℝ)| →
          |u x| ≤ (M + ε) * (∑ i : Fin d, |(x.val i : ℝ)|) := by
  rw [componentPointwiseLinearGrowth_iff_tail]
  constructor
  · rintro ⟨M, hM, R, hb⟩
    refine ⟨M, hM.le, fun ε hε => ⟨R, fun x hx => ?_⟩⟩
    exact (hb x hx).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Finset.sum_nonneg (fun i _ => abs_nonneg _)))
  · rintro ⟨M, hM, hb⟩
    exact ⟨M + 1, by linarith, hb 1 zero_lt_one⟩

/-- The finite-component convention is explicit: no vertices remain at radial infinity. -/
theorem componentPointwiseLinearGrowth_of_finite (C : OpenComponent ω) [Finite C]
    (u : C → ℝ) : componentPointwiseLinearGrowth C u := by
  rw [componentPointwiseLinearGrowth_iff_finite]
  exact ⟨1, zero_lt_one, Set.toFinite _⟩

/-- Every finite exceptional value is absorbed into one nonnegative global affine bound.
Mathlib's cofinite bound theorem controls the finite exceptions without extra hypotheses. -/
theorem componentPointwiseLinearGrowth_global_bound (C : OpenComponent ω) (u : C → ℝ)
    (hu : componentPointwiseLinearGrowth C u) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : C, |u x| ≤ M * (1 + ∑ i : Fin d, |(x.val i : ℝ)|) := by
  have hcompare : (fun x : C => ∑ i : Fin d, |(x.val i : ℝ)|) =O[cofinite]
      (fun x : C => 1 + ∑ i : Fin d, |(x.val i : ℝ)|) := by
    apply IsBigO.of_bound 1
    apply Eventually.of_forall
    intro x
    have hs : 0 ≤ ∑ i : Fin d, |(x.val i : ℝ)| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs,
      abs_of_nonneg (by linarith : 0 ≤ 1 + ∑ i : Fin d, |(x.val i : ℝ)|), one_mul]
      using (by linarith : (∑ i : Fin d, |(x.val i : ℝ)|) ≤
        1 + ∑ i : Fin d, |(x.val i : ℝ)|)
  obtain ⟨M, hM, hb⟩ := bound_of_isBigO_cofinite (hu.trans hcompare)
  refine ⟨M, hM.le, fun x => ?_⟩
  have hs : 0 ≤ ∑ i : Fin d, |(x.val i : ℝ)| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by linarith :
    0 ≤ 1 + ∑ i : Fin d, |(x.val i : ℝ)|)] using
      (hb (x := x) (by linarith : 1 + (∑ i : Fin d, |(x.val i : ℝ)|) ≠ 0))

/-- Actual harmonicity and source pointwise linear growth imply membership in A₁. -/
theorem mem_harmonicGrowthSpace_one_of_pointwise_linear_growth (C : OpenComponent ω)
    (u : C → ℝ) (hu : ∀ x, componentLaplacian C u x = 0)
    (hg : componentPointwiseLinearGrowth C u) : u ∈ harmonicGrowthSpace C 1 := by
  obtain ⟨M, hM, hb⟩ := componentPointwiseLinearGrowth_global_bound C u hg
  exact mem_harmonicGrowthSpace_one_of_global_l1_bound C u hu hM hb

end

end LatticeProb.Percolation
