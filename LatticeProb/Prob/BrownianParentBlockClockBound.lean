import LatticeProb.Prob.BrownianParentBlockInitialChain
import LatticeProb.Prob.BrownianParentBlockScaleBound

/-!
# Bounds for active parent-block exit clocks

A finite active clock with a controlled initial excursion gives a bounded chain.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace BouRabeeGwynne

/-- An active finite clock has the scale-normalized chain bound when its initial
excursion has the stated geometry. -/
theorem measure_active_parentBlock_clock_le {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → Euc 2), LatticeProb.IsBrownianSpace 2 0 B P →
      ∀ (path : Ω → BrownianPath 2), (∀ t ω, path ω t = B t ω) →
      ∀ {J : Type*} [Countable J] [MeasurableSpace (Option J)]
        [MeasurableSingletonClass (Option J)] (centres : J → ℂ)
        (z : Euc 2) (c : ℂ) (S s : ℝ≥0), 0 < S → 0 < s → s ≤ S →
      Complex.orthonormalBasisOneI.repr.symm z ∈ LatticeProb.ParentBlock.closedSquare c S →
      ∀ (j₀ : J) (selector : ℕ → Euc 2 → Option J),
      (∀ n x j, selector n x = some j →
        Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.closedSquare (centres j) s) →
      ∀ K : ℕ, ⌊((s / (18 * S) : ℝ≥0) : ℝ) ^ (-(2 + ζ))⌋₊ ≤ K + 1 →
      P {ω | let γ := path ω
        let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
        let clock := brownianSkeletonClock U z j₀ selector
        let t₀ := (clock 0 γ).2.toNNReal
        (clock K γ).1 = false ∧ (clock K γ).2 ≠ ∞ ∧
        Complex.orthonormalBasisOneI.repr.symm (z + γ 0) ∈ LatticeProb.ParentBlock.parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm (z + γ 0) ∈ LatticeProb.ParentBlock.closedSquare (centres j₀) s ∧
        Complex.orthonormalBasisOneI.repr.symm (z + γ t₀) ∉ interior (LatticeProb.ParentBlock.parentBlock (centres j₀) s) ∧
        ∀ t ∈ Icc 0 t₀, ‖Complex.orthonormalBasisOneI.repr.symm (z + γ t) -
          Complex.orthonormalBasisOneI.repr.symm (z + γ 0)‖ ≤ 4 * (s : ℝ)} ≤
        ENNReal.ofReal (C * (((s / (18 * S) : ℝ≥0) : ℝ) ^ p)) := by
  obtain ⟨C, hC⟩ := LatticeProb.ParentBlock.measure_buffered_parentBlock_chain_ratio_superpoly.{u} hζ0 hζ1 p
  refine ⟨C, ?_⟩
  intro Ω _ P _ B hB path hpath J _ _ _ centres z c S s hS hs hsS hz j₀ selector hselector K hK
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hbound := hC Ω P B hB (Complex.orthonormalBasisOneI.repr.symm z) c S s hS hs hsS hz
  apply le_trans (measure_mono_ae ?_) hbound
  filter_upwards [hB.start] with ω hzero hω
  obtain ⟨T, selected, hmono, hT0, hsteps⟩ :=
    brownianSkeletonClock_active_parentBlock_chain centres s hs'
      (LatticeProb.ParentBlock.parentBlock c S) z j₀ selector hselector K (path ω)
      hω.1 hω.2.1 hω.2.2
  refine ⟨T, fun n => centres (selected n), hmono, hT0, ?_, ?_, ?_, ?_⟩
  · rw [hzero]
    simp
  · intro n hn
    have h := hsteps n (lt_of_lt_of_le hn hK)
    constructor
    · simpa only [map_add, hpath] using h.2.1
    · simpa only [map_add, hpath] using h.2.2.1
  · intro n hn
    have h := hsteps n (lt_of_lt_of_le hn hK)
    simpa only [map_add, hpath] using h.1
  · intro n hn t ht
    have h := hsteps n (lt_of_lt_of_le hn hK)
    simpa only [map_add, hpath] using h.2.2.2 t ht

end BouRabeeGwynne
