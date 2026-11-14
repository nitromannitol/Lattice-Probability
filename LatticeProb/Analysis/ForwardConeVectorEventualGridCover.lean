import LatticeProb.Analysis.ForwardConeVectorWeakGridCover
import LatticeProb.Analysis.UniformExcursionHorizon

/-!
# Eventual grid barriers for reflected forward cone vectors

Separated forward cone vectors have a common positive horizon for their
reflected grid barriers.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- A separated reflected forward cone vector admits grid barriers at all
sufficiently fine meshes, provided the displayed modulus bounds hold. -/
theorem exists_horizon_eventually_forwardConeVector_reflected_grid_barriers
    {X Y : ℝ → ℝ} (hX : Continuous X) (hY : Continuous Y)
    {d : ℝ} (hd : 0 < d) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hmesh : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0))
    (e : ℕ → ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ a s : ℝ,
      (∃ t > s, X t < X s ∨ Y t < Y s) →
      (a, s) ∈ forwardConeVectors X Y →
      0 < -a → -s < 1 → d < -s - -a →
      ∀ᶠ n in atTop,
        (∀ x ∈ Icc (-a - 1 / (N n : ℝ) - (-s - ((-a - s) / 2)))
            (-s + 1 / (N n : ℝ)),
          ∀ y ∈ Icc (-a - 1 / (N n : ℝ) - (-s - ((-a - s) / 2)))
            (-s + 1 / (N n : ℝ)),
              |x - y| ≤ 1 / (N n : ℝ) → |X (-x) - X (-y)| ≤ e n) →
        (∀ x ∈ Icc (-a - 1 / (N n : ℝ) - (-s - ((-a - s) / 2)))
            (-s + 1 / (N n : ℝ)),
          ∀ y ∈ Icc (-a - 1 / (N n : ℝ) - (-s - ((-a - s) / 2)))
            (-s + 1 / (N n : ℝ)),
              |x - y| ≤ 1 / (N n : ℝ) → |Y (-x) - Y (-y)| ≤ e n) →
        ∃ i j : Fin (N n),
          let t₀ : ℝ := (i.val : ℝ) / N n
          let t₁ : ℝ := (j.val : ℝ) / N n
          0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
          |t₀ - -a| ≤ 1 / (N n : ℝ) ∧ |t₁ - -s| ≤ 1 / (N n : ℝ) ∧
          (((∀ u ∈ Icc 0 H, X (-t₀) - 2 * e n ≤ X (-(t₀ + u))) ∧
            (∀ u ∈ Icc 0 H, X (-t₁) - 2 * e n ≤ X (-(t₁ - u)) ∧
              Y (-t₁) - 2 * e n ≤ Y (-(t₁ - u))) ∧
            |X (-t₁) - X (-t₀)| ≤ 2 * e n ∧
            ∀ x ∈ Icc t₀ t₁, X (-t₁) - 2 * e n ≤ X (-x)) ∨
          ((∀ u ∈ Icc 0 H, Y (-t₀) - 2 * e n ≤ Y (-(t₀ + u))) ∧
            (∀ u ∈ Icc 0 H, Y (-t₁) - 2 * e n ≤ Y (-(t₁ - u)) ∧
              X (-t₁) - 2 * e n ≤ X (-(t₁ - u))) ∧
            |Y (-t₁) - Y (-t₀)| ≤ 2 * e n ∧
            ∀ x ∈ Icc t₀ t₁, Y (-t₁) - 2 * e n ≤ Y (-x))) := by
  obtain ⟨H, hH, hhorizon⟩ :=
    exists_uniform_excursion_horizon_eventually hd (half_pos hd) hmesh
  refine ⟨H, hH, ?_⟩
  intro a s hdrop hvec ha hs hsep
  have hslack : 0 < -s - -a - d := by linarith
  filter_upwards [hhorizon, hmesh.eventually (eventually_lt_nhds ha),
    hmesh.eventually (eventually_lt_nhds hslack)] with n hn hna hnsep
  intro hmodX hmodY
  have hmid : d / 2 < -s - ((-a - s) / 2) := by linarith
  obtain ⟨hf, hb⟩ := hn (-a) ((-a - s) / 2) (-s) hsep hmid
  exact forwardConeVector_reflected_exists_grid_barriers (hN n) hX hY hdrop hvec
    ha (by linarith) (by linarith) hs hd.le hH.le hna (by linarith)
    hf.le hb hmodX hmodY

end LatticeProb
