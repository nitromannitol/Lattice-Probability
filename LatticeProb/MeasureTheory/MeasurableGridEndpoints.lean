import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith

/-! # Measurable endpoints of equal-length grid intervals -/

set_option autoImplicit false

namespace LatticeProb

/-- A measurable origin and cell length determine measurable grid endpoints at
    a fixed point. Recovery holds for a positive-length half-open cell. -/
theorem exists_measurable_grid_endpoints
    {Θ : Type*} [MeasurableSpace Θ] (u : ℝ) (c ℓ : Θ → ℝ)
    (hc : Measurable c) (hℓ : Measurable ℓ) :
    ∃ E : Θ → ℝ × ℝ, Measurable E ∧
      ∀ (θ : Θ) (n : ℤ), 0 < ℓ θ →
        c θ + (n : ℝ) * ℓ θ ≤ u → u < c θ + ((n : ℝ) + 1) * ℓ θ →
        E θ = (c θ + (n : ℝ) * ℓ θ, c θ + ((n : ℝ) + 1) * ℓ θ) := by
  let L : Θ → ℝ := fun θ => c θ + (⌊(u - c θ) / ℓ θ⌋ : ℤ) * ℓ θ
  have hL : Measurable L := by
    have hf : Measurable (fun θ => (⌊(u - c θ) / ℓ θ⌋ : ℤ)) :=
      (measurable_const.sub hc |>.div hℓ).floor
    have hcast : Measurable (fun θ => ((⌊(u - c θ) / ℓ θ⌋ : ℤ) : ℝ)) :=
      (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hf
    exact hc.add (hcast.mul hℓ)
  refine ⟨fun θ => (L θ, L θ + ℓ θ), hL.prodMk (hL.add hℓ), ?_⟩
  intro θ n hp hl hr
  have hn : ⌊(u - c θ) / ℓ θ⌋ = n := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hp).2
      linarith
    · apply (div_lt_iff₀ hp).2
      linarith
  simp only [L, hn]
  apply Prod.ext
  · rfl
  · dsimp
    ring

end LatticeProb
