import Mathlib

/-!
# Second differences on the integers

The one-dimensional lemma behind the slab stabilizers of A. Fey, L. Levine and Y. Peres,
*Growth rates and explosions in sandpiles*, J. Stat. Phys. 138 (2010), 143–159, Lemma 3.3:
a function `f : ℤ → ℤ` supported in `[-a, b]` with `∑ f(y) = ∑ y f(y) = 0` is the second
difference of `g(x) = ∑_{-a ≤ y ≤ b} max (x - y) 0 · f(y)`, which is supported in
`[1 - a, b - 1]`; if `f` has no sign pattern `(-, +, -)`, then `g ≥ 0`
(`exists_secondDiff_eq`).

The sign statement goes through a minimum principle (`nonneg_of_secondDiff`): a function that
vanishes outside a bounded interval is nonnegative as soon as its second difference is
nonpositive wherever it is negative. At a point where `g(x) < 0`, the two expressions
`g(x) = ∑ max (x - y) 0 f(y) = ∑ max (y - x) 0 f(y)` give negative values of `f` on both sides
of `x`, so `f(x) ≤ 0` when the pattern `(-, +, -)` is excluded.
-/

namespace LatticeProb.Sandpile.FLP

/-- **Minimum principle for second differences.** If `g : ℤ → ℤ` vanishes outside `[-c, c]`
and its second difference is nonpositive at every point where `g` is negative, then `g ≥ 0`. -/
theorem nonneg_of_secondDiff {g f : ℤ → ℤ} (c : ℤ)
    (hΔ : ∀ x, g (x + 1) - 2 * g x + g (x - 1) = f x)
    (hsupp : ∀ x, x < -c ∨ c < x → g x = 0) (hneg : ∀ x, g x < 0 → f x ≤ 0) (x : ℤ) :
    0 ≤ g x := by
  by_contra hx
  push Not at hx
  have hxI : x ∈ Finset.Icc (-c) c := by
    rw [Finset.mem_Icc]
    by_contra hnot
    exact absurd (hsupp x (by omega)) hx.ne
  have hvle : ∀ z, (Finset.Icc (-c) c).inf' ⟨x, hxI⟩ g ≤ g z := by
    intro z
    by_cases hz : z ∈ Finset.Icc (-c) c
    · exact Finset.inf'_le g hz
    · rw [Finset.mem_Icc] at hz
      rw [hsupp z (by omega)]
      exact (Finset.inf'_le g hxI).trans hx.le
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_mem_eq_inf' ⟨x, hxI⟩ g
  have hvx := hvle x
  generalize (Finset.Icc (-c) c).inf' ⟨x, hxI⟩ g = v at hx₀ hvx hvle
  have hstep : ∀ k : ℕ, g (x₀ - k) = v := by
    intro k
    induction k with
    | zero => simpa using hx₀.symm
    | succ k ih =>
      have hf := hneg (x₀ - k) (by omega)
      have h1 := hΔ (x₀ - k)
      have h2 := hvle (x₀ - k + 1)
      have h3 := hvle (x₀ - k - 1)
      have h4 : x₀ - ((k + 1 : ℕ) : ℤ) = x₀ - k - 1 := by push_cast; ring
      rw [h4]
      omega
  have hfar := hstep (x₀ + c + 1).toNat
  have hzero := hsupp (x₀ - ((x₀ + c + 1).toNat : ℤ)) (Or.inl (by omega))
  omega

/-- The second difference of `x ↦ max (x - y) 0` is the indicator of `x = y`. -/
theorem max_sub_secondDiff (x y : ℤ) :
    max (x + 1 - y) 0 - 2 * max (x - y) 0 + max (x - 1 - y) 0 = if x = y then 1 else 0 := by
  simp only [max_def]
  split_ifs <;> omega

/-- **The one-dimensional lemma** (Fey–Levine–Peres, Lemma 3.3). A function `f : ℤ → ℤ`
supported in `[-a, b]` with total mass zero and centre of mass zero is the second difference of a
function `g` supported in `[1 - a, b - 1]`; if there are no `x₁ < x₂ < x₃` with `f(x₁) < 0`,
`f(x₂) > 0` and `f(x₃) < 0`, then `g ≥ 0`. -/
theorem exists_secondDiff_eq (f : ℤ → ℤ) (a b : ℤ) (_hab : -a ≤ b)
    (hf : ∀ x, x < -a ∨ b < x → f x = 0)
    (h0 : ∑ y ∈ Finset.Icc (-a) b, f y = 0) (h1 : ∑ y ∈ Finset.Icc (-a) b, y * f y = 0) :
    ∃ g : ℤ → ℤ, (∀ x, g (x + 1) - 2 * g x + g (x - 1) = f x) ∧
      (∀ x, x < 1 - a ∨ b - 1 < x → g x = 0) ∧
      ((¬ ∃ x₁ x₂ x₃, x₁ < x₂ ∧ x₂ < x₃ ∧ f x₁ < 0 ∧ 0 < f x₂ ∧ f x₃ < 0) → ∀ x, 0 ≤ g x) := by
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℤ, ∀ x, g x = ∑ y ∈ Finset.Icc (-a) b, max (x - y) 0 * f y :=
    ⟨_, fun _ => rfl⟩
  have hswap : ∀ x, g x = ∑ y ∈ Finset.Icc (-a) b, max (y - x) 0 * f y := by
    intro x
    have hlin : ∑ y ∈ Finset.Icc (-a) b, (x - y) * f y = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h0, h1, mul_zero, sub_zero]
    rw [hg, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hlin]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← sub_mul]
    congr 1
    simp only [max_def]
    split_ifs <;> omega
  have hΔ : ∀ x, g (x + 1) - 2 * g x + g (x - 1) = f x := by
    intro x
    have hterm : ∀ y ∈ Finset.Icc (-a) b,
        max (x + 1 - y) 0 * f y - 2 * (max (x - y) 0 * f y) + max (x - 1 - y) 0 * f y =
          if x = y then f y else 0 := by
      intro y _
      rw [show max (x + 1 - y) 0 * f y - 2 * (max (x - y) 0 * f y) + max (x - 1 - y) 0 * f y =
          (max (x + 1 - y) 0 - 2 * max (x - y) 0 + max (x - 1 - y) 0) * f y by ring,
        max_sub_secondDiff]
      split_ifs <;> simp
    rw [hg, hg, hg, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with hx
    · rfl
    · rw [Finset.mem_Icc] at hx
      exact (hf x (by omega)).symm
  have hsupp : ∀ x, x < 1 - a ∨ b - 1 < x → g x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · rw [hg]
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [Finset.mem_Icc] at hy
      rw [max_eq_right (by omega), zero_mul]
    · rw [hswap]
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [Finset.mem_Icc] at hy
      rw [max_eq_right (by omega), zero_mul]
  refine ⟨g, hΔ, hsupp, fun hpat x => ?_⟩
  have hma := le_max_left a b
  have hmb := le_max_right a b
  refine nonneg_of_secondDiff (max a b) hΔ (fun z hz => hsupp z (by omega)) (fun z hz => ?_) x
  by_contra hfz
  push Not at hfz
  apply hpat
  have hl : ∑ y ∈ Finset.Icc (-a) b, max (z - y) 0 * f y < ∑ y ∈ Finset.Icc (-a) b, (0 : ℤ) := by
    rw [Finset.sum_const_zero, ← hg]
    exact hz
  have hr : ∑ y ∈ Finset.Icc (-a) b, max (y - z) 0 * f y < ∑ y ∈ Finset.Icc (-a) b, (0 : ℤ) := by
    rw [Finset.sum_const_zero, ← hswap]
    exact hz
  obtain ⟨y₁, -, h₁⟩ := Finset.exists_lt_of_sum_lt hl
  obtain ⟨y₃, -, h₃⟩ := Finset.exists_lt_of_sum_lt hr
  rcases mul_neg_iff.mp h₁ with ⟨hm₁, hf₁⟩ | ⟨hm₁, -⟩
  · rcases mul_neg_iff.mp h₃ with ⟨hm₃, hf₃⟩ | ⟨hm₃, -⟩
    · have hy₁ := lt_max_iff.mp hm₁
      have hy₃ := lt_max_iff.mp hm₃
      exact ⟨y₁, z, y₃, by omega, by omega, hf₁, hfz, hf₃⟩
    · exact absurd hm₃ (not_lt.mpr (le_max_right _ _))
  · exact absurd hm₁ (not_lt.mpr (le_max_right _ _))

end LatticeProb.Sandpile.FLP
