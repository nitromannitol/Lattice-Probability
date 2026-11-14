import LatticeProb.Prob.BrownianParentBlockClockBound
import LatticeProb.Prob.BrownianParentBlockInitialGeometry

/-!
# Finite active clock bounds from initial square membership

The geometry of the first excursion follows from its finite exit time.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace BouRabeeGwynne

/-- The probability of an active finite parent-block clock has a scale-normalized
bound when the starting point belongs to the initial square. -/
theorem measure_active_parentBlock_clock_le_of_initial_square
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → Euc 2), LatticeProb.IsBrownianSpace 2 0 B P →
      ∀ (path : Ω → BrownianPath 2), (∀ t ω, path ω t = B t ω) →
      ∀ {J : Type*} [Countable J] [MeasurableSpace (Option J)]
        [MeasurableSingletonClass (Option J)] (centres : J → ℂ)
        (z : Euc 2) (c : ℂ) (S s : ℝ≥0), 0 < S → 0 < s → s ≤ S →
      Complex.orthonormalBasisOneI.repr.symm z ∈ LatticeProb.ParentBlock.closedSquare c S →
      ∀ (j₀ : J),
      Complex.orthonormalBasisOneI.repr.symm z ∈
        LatticeProb.ParentBlock.closedSquare (centres j₀) s →
      ∀ (selector : ℕ → Euc 2 → Option J),
      (∀ n x j, selector n x = some j →
        Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.closedSquare (centres j) s) →
      ∀ K : ℕ, ⌊((s / (18 * S) : ℝ≥0) : ℝ) ^ (-(2 + ζ))⌋₊ ≤ K + 1 →
      P {ω | let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
        let clock := brownianSkeletonClock U z j₀ selector
        (clock K (path ω)).1 = false ∧ (clock K (path ω)).2 ≠ ∞} ≤
        ENNReal.ofReal (C * (((s / (18 * S) : ℝ≥0) : ℝ) ^ p)) := by
  obtain ⟨C, hC⟩ := measure_active_parentBlock_clock_le.{u} hζ0 hζ1 p
  refine ⟨C, ?_⟩
  intro Ω _ P _ B hB path hpath J _ _ _ centres z c S s hS hs hsS hz j₀ hz₀ selector hselector K hK
  have hbound := hC Ω P B hB path hpath centres z c S s hS hs hsS hz j₀ selector hselector K hK
  apply le_trans (measure_mono_ae ?_) hbound
  filter_upwards [hB.start] with ω hzero hω
  have hpathzero : path ω 0 = 0 := by rw [hpath, hzero]
  have hstart : Complex.orthonormalBasisOneI.repr.symm (z + path ω 0) ∈
      LatticeProb.ParentBlock.closedSquare (centres j₀) s := by simpa only [hpathzero, add_zero] using hz₀
  have houter : Complex.orthonormalBasisOneI.repr.symm (z + path ω 0) ∈
      LatticeProb.ParentBlock.parentBlock c S := by
    rw [hpathzero, add_zero]
    apply interior_subset
    apply LatticeProb.ParentBlock.ball_subset_interior_parentBlock (by exact_mod_cast hS.le) hz
    exact mem_ball_self (by exact_mod_cast hS)
  let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  have hfinite : continuousExitTime (U j₀) z (path ω) ≠ ∞ := by
    exact brownianSkeletonClock_finite_of_le U z j₀ selector (path ω) (Nat.zero_le K) hω.2
  have hgeom := initial_parentBlock_exit_geometry (centres j₀) s (by exact_mod_cast hs)
    z (path ω) hstart hfinite
  exact ⟨hω.1, hω.2, houter, hstart, hgeom.1, hgeom.2⟩

end BouRabeeGwynne
