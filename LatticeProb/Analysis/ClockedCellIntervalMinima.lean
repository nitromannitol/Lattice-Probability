import LatticeProb.Analysis.ClockedAdjacentIntervalMinima

/-! # Matching minima in clocked shifted cell intervals -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- For two nonconsecutive cells, the phases where either cell's minimum
matches the minimum between them form a countable set. -/
theorem countable_clocked_cell_interval_minima (f : ℝ → ℝ) (hf : Continuous f)
    (ψ : ℝ ≃o ℝ) (ε : ℝ) (hε : 0 < ε) (i j : ℤ) (hij : i + 1 < j)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y) :
    {θ : ℝ |
      let a := ψ (ε * ((i : ℝ) - 1 + θ))
      let b := ψ (ε * ((i : ℝ) + θ))
      let c := ψ (ε * ((j : ℝ) - 1 + θ))
      let d := ψ (ε * ((j : ℝ) + θ))
      sInf (f '' Icc a b) = sInf (f '' Icc b c) ∨
      sInf (f '' Icc b c) = sInf (f '' Icc c d)}.Countable := by
  have hij' : (i : ℝ) + 1 < (j : ℝ) := by exact_mod_cast hij
  let β : ℝ := ε * ((j : ℝ) - (i : ℝ) - 1)
  have hβ : 0 < β := by
    dsimp [β]
    exact mul_pos hε (by linarith)
  let ρ : ℝ → ℝ := fun θ => ε * ((i : ℝ) - 1 + θ)
  have hρ : Function.Injective ρ := by
    intro x y hxy
    dsimp [ρ] at hxy
    nlinarith
  have hleft := countable_clocked_adjacent_interval_minima f hf ψ ρ hρ ε (ε + β)
    hε (by linarith) hdist
  let σ : ℝ → ℝ := fun θ => ε * ((i : ℝ) + θ)
  have hσ : Function.Injective σ := by
    intro x y hxy
    dsimp [σ] at hxy
    nlinarith
  have hright := countable_clocked_adjacent_interval_minima f hf ψ σ hσ β (β + ε)
    hβ (by linarith) hdist
  have hρb (θ : ℝ) : ρ θ + ε = ε * ((i : ℝ) + θ) := by dsimp [ρ]; ring
  have hρc (θ : ℝ) : ρ θ + (ε + β) = ε * ((j : ℝ) - 1 + θ) := by
    dsimp [ρ, β]; ring
  have hσc (θ : ℝ) : σ θ + β = ε * ((j : ℝ) - 1 + θ) := by
    dsimp [σ, β]; ring
  have hσd (θ : ℝ) : σ θ + (β + ε) = ε * ((j : ℝ) + θ) := by
    dsimp [σ, β]; ring
  have hl : {θ : ℝ | sInf (f '' Icc (ψ (ε * ((i : ℝ) - 1 + θ)))
      (ψ (ε * ((i : ℝ) + θ)))) = sInf (f '' Icc (ψ (ε * ((i : ℝ) + θ)))
      (ψ (ε * ((j : ℝ) - 1 + θ))))}.Countable := by
    simpa only [ρ, hρb, hρc] using hleft
  have hr : {θ : ℝ | sInf (f '' Icc (ψ (ε * ((i : ℝ) + θ)))
      (ψ (ε * ((j : ℝ) - 1 + θ)))) = sInf (f '' Icc
      (ψ (ε * ((j : ℝ) - 1 + θ))) (ψ (ε * ((j : ℝ) + θ))))}.Countable := by
    simpa only [σ, hσc, hσd] using hright
  exact hl.union hr

/-- For a fixed mesh, the exceptional phases are countable simultaneously
over all pairs of nonconsecutive cells. -/
theorem countable_clocked_cell_interval_minima_all (f : ℝ → ℝ) (hf : Continuous f)
    (ψ : ℝ ≃o ℝ) (ε : ℝ) (hε : 0 < ε)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y) :
    {θ : ℝ | ∃ i j : ℤ, i + 1 < j ∧
      let a := ψ (ε * ((i : ℝ) - 1 + θ))
      let b := ψ (ε * ((i : ℝ) + θ))
      let c := ψ (ε * ((j : ℝ) - 1 + θ))
      let d := ψ (ε * ((j : ℝ) + θ))
      sInf (f '' Icc a b) = sInf (f '' Icc b c) ∨
      sInf (f '' Icc b c) = sInf (f '' Icc c d)}.Countable := by
  classical
  have hc := countable_iUnion fun (i : ℤ) => countable_iUnion fun (j : ℤ) =>
    countable_iUnion fun (hij : i + 1 < j) =>
      countable_clocked_cell_interval_minima f hf ψ ε hε i j hij hdist
  apply hc.mono
  intro θ hθ
  obtain ⟨i, j, hij, h⟩ := hθ
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hij, h⟩⟩⟩

end LatticeProb
