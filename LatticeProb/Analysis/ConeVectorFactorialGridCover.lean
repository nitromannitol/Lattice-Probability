import LatticeProb.Analysis.ConeVectorEventualGridCover
import LatticeProb.Analysis.FactorialMesh

/-!
# Factorial grid barriers for cone vectors

A fixed compact-interval modulus gives eventual factorial-grid barriers for
each separated backward cone vector with a positive exit gap.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- A common compact-interval modulus yields eventual sixth-power factorial
grid barriers, with a common horizon and a vector-dependent grid threshold. -/
theorem exists_horizon_eventually_factorial_backwardConeVector_grid_barriers
    {X Y : ℝ → ℝ} (hX : Continuous X) (hY : Continuous Y)
    {d q : ℝ} (hd : 0 < d) (hq : 0 < q) (e : ℕ → ℝ)
    (hmod : ∀ᶠ n in atTop,
      ∀ x ∈ Icc (-2 : ℝ) 2, ∀ y ∈ Icc (-2 : ℝ) 2,
        |x - y| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) →
        |X x - X y| ≤ e n ∧ |Y x - Y y| ≤ e n) :
    ∃ H : ℝ, 0 < H ∧ ∀ a s : ℝ,
      (∃ r < s, X r < X s) → (∃ r < s, Y r < Y s) →
      (a, s) ∈ backwardConeVectors X Y →
      0 < a → s < 1 → d < s - a →
      q < s - coneFirstExitBackward X Y s →
      ∀ᶠ n in atTop,
        ∃ i j : Fin (n.factorial ^ 6),
          let t₀ : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
          let t₁ : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
          0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
          |t₀ - a| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
          |t₁ - s| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
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
  have hmesh : Tendsto (fun n : ℕ => 1 / ((n.factorial ^ 6 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_pow] using tendsto_one_div_factorial_pow 6 (by norm_num)
  obtain ⟨H, hH, hcover⟩ := exists_horizon_eventually_backwardConeVector_grid_barriers
    hX hY hd hq (fun n => n.factorial ^ 6)
    (fun n => pow_pos (Nat.factorial_pos n) _) hmesh e
  refine ⟨H, hH, ?_⟩
  intro a s hx hy hv ha hs hsep hgap
  have hab : a < coneFirstExitBackward X Y s := by
    simpa only [← hv.1] using hv.2.1
  have hbs : coneFirstExitBackward X Y s < s := hv.2.2.1
  filter_upwards [hcover a s hx hy hv ha hs hsep hgap, hmod,
    hmesh.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with n hc hm hn
  have hsub : Icc (a - 1 / ((n.factorial ^ 6 : ℕ) : ℝ) -
      (s - coneFirstExitBackward X Y s)) (s + 1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ⊆
      Icc (-2 : ℝ) 2 := by
    intro x hx'
    constructor <;> linarith [hx'.1, hx'.2]
  apply hc
  · intro x hx' y hy' hxy
    exact (hm x (hsub hx') y (hsub hy') hxy).1
  · intro x hx' y hy' hxy
    exact (hm x (hsub hx') y (hsub hy') hxy).2

end LatticeProb
