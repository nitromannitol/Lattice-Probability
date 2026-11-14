import Mathlib

/-!
# Ordered anchors on a finite grid

Two separated points in the unit interval admit ordered lower grid
approximations, with quantitative separation and horizon margins.
-/

set_option autoImplicit false

namespace LatticeProb

/-- Lower grid approximations of two points preserve prescribed separation
and forward and backward horizon bounds when the mesh is sufficiently small. -/
theorem exists_ordered_grid_anchors
    {N : ℕ} (hN : 0 < N) {a s b d H : ℝ}
    (ha : 0 < a) (hs : s < 1) (hd : 0 ≤ d)
    (hmesh : 1 / (N : ℝ) < a)
    (hsep : d + 1 / (N : ℝ) < s - a)
    (hforward : a + H ≤ s)
    (hbackward : b + H + 1 / (N : ℝ) < s) :
    ∃ i j : Fin N,
      let t₀ : ℝ := (i.val : ℝ) / N
      let t₁ : ℝ := (j.val : ℝ) / N
      0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
      |t₀ - a| ≤ 1 / (N : ℝ) ∧ |t₁ - s| ≤ 1 / (N : ℝ) ∧
      t₀ + H ≤ s ∧ b ≤ t₁ - H := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmeshpos : 0 < 1 / (N : ℝ) := by positivity
  have has : a < s := by linarith
  have hsa : 0 ≤ (N : ℝ) * a := mul_nonneg hNr.le ha.le
  have hss : 0 ≤ (N : ℝ) * s := mul_nonneg hNr.le (le_of_lt (lt_trans ha has))
  let i := ⌊(N : ℝ) * a⌋₊
  let j := ⌊(N : ℝ) * s⌋₊
  have hia : ((i : ℝ) / N) ≤ a := by
    apply (div_le_iff₀ hNr).2
    simpa only [i, mul_comm] using Nat.floor_le hsa
  have haj : a - 1 / (N : ℝ) < (i : ℝ) / N := by
    have h := Nat.lt_floor_add_one ((N : ℝ) * a)
    dsimp [i] at h ⊢
    apply (lt_div_iff₀ hNr).2
    have hmul : (1 / (N : ℝ)) * N = 1 := by field_simp
    nlinarith
  have hjs : ((j : ℝ) / N) ≤ s := by
    apply (div_le_iff₀ hNr).2
    simpa only [j, mul_comm] using Nat.floor_le hss
  have hsj : s - 1 / (N : ℝ) < (j : ℝ) / N := by
    have h := Nat.lt_floor_add_one ((N : ℝ) * s)
    dsimp [j] at h ⊢
    apply (lt_div_iff₀ hNr).2
    have hmul : (1 / (N : ℝ)) * N = 1 := by field_simp
    nlinarith
  have hiN : i < N := by
    apply (Nat.floor_lt hsa).2
    nlinarith
  have hjN : j < N := by
    apply (Nat.floor_lt hss).2
    nlinarith
  refine ⟨⟨i, hiN⟩, ⟨j, hjN⟩, ?_⟩
  dsimp only
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_, by linarith, by linarith⟩
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

end LatticeProb
