import LatticeProb.Analysis.ConeVectorWeakGridCover
import LatticeProb.Analysis.UniformExcursionHorizon

/-!
# Eventual grid barriers for cone vectors

A fixed separated positive-gap class admits a common horizon. The grid
threshold for an individual vector may depend on that vector.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- A common horizon works on a separated positive-gap class; every individual
backward cone vector in the class has grid barriers at all sufficiently fine
meshes whenever the indicated path modulus bounds hold. -/
theorem exists_horizon_eventually_backwardConeVector_grid_barriers
    {X Y : ℝ → ℝ} (hX : Continuous X) (hY : Continuous Y)
    {d q : ℝ} (hd : 0 < d) (hq : 0 < q)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hmesh : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0))
    (e : ℕ → ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ a s : ℝ,
      (∃ r < s, X r < X s) → (∃ r < s, Y r < Y s) →
      (a, s) ∈ backwardConeVectors X Y →
      0 < a → s < 1 → d < s - a →
      q < s - coneFirstExitBackward X Y s →
      ∀ᶠ n in atTop,
        (∀ x ∈ Icc (a - 1 / (N n : ℝ) - (s - coneFirstExitBackward X Y s))
            (s + 1 / (N n : ℝ)),
          ∀ y ∈ Icc (a - 1 / (N n : ℝ) - (s - coneFirstExitBackward X Y s))
            (s + 1 / (N n : ℝ)),
              |x - y| ≤ 1 / (N n : ℝ) → |X x - X y| ≤ e n) →
        (∀ x ∈ Icc (a - 1 / (N n : ℝ) - (s - coneFirstExitBackward X Y s))
            (s + 1 / (N n : ℝ)),
          ∀ y ∈ Icc (a - 1 / (N n : ℝ) - (s - coneFirstExitBackward X Y s))
            (s + 1 / (N n : ℝ)),
              |x - y| ≤ 1 / (N n : ℝ) → |Y x - Y y| ≤ e n) →
        ∃ i j : Fin (N n),
          let t₀ : ℝ := (i.val : ℝ) / N n
          let t₁ : ℝ := (j.val : ℝ) / N n
          0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
          |t₀ - a| ≤ 1 / (N n : ℝ) ∧ |t₁ - s| ≤ 1 / (N n : ℝ) ∧
          (((∀ u ∈ Icc 0 H, X t₀ - 2 * e n ≤ X (t₀ + u)) ∧
            (∀ u ∈ Icc 0 H, X t₁ - 2 * e n ≤ X (t₁ - u) ∧
              Y t₁ - 2 * e n ≤ Y (t₁ - u)) ∧
            |X t₁ - X t₀| ≤ 2 * e n ∧
            ∀ x ∈ Icc t₀ t₁, X t₁ - 2 * e n ≤ X x) ∨
          ((∀ u ∈ Icc 0 H, Y t₀ - 2 * e n ≤ Y (t₀ + u)) ∧
            (∀ u ∈ Icc 0 H, Y t₁ - 2 * e n ≤ Y (t₁ - u) ∧
              X t₁ - 2 * e n ≤ X (t₁ - u)) ∧
            |Y t₁ - Y t₀| ≤ 2 * e n ∧
            ∀ x ∈ Icc t₀ t₁, Y t₁ - 2 * e n ≤ Y x)) := by
  obtain ⟨H, hH, hhorizon⟩ := exists_uniform_excursion_horizon_eventually hd hq hmesh
  refine ⟨H, hH, ?_⟩
  intro a s hx hy hvec ha hs hsep hgap
  have hslack : 0 < s - a - d := by linarith
  filter_upwards [hhorizon, hmesh.eventually (eventually_lt_nhds ha),
    hmesh.eventually (eventually_lt_nhds hslack)] with n hn hna hnsep
  intro hmodX hmodY
  obtain ⟨hf, hb⟩ := hn a (coneFirstExitBackward X Y s) s hsep hgap
  exact backwardConeVector_exists_grid_barriers (hN n) hX hY hx hy hvec ha hs
    hd.le hH.le hna (by linarith) hf.le hb hmodX hmodY

end LatticeProb
