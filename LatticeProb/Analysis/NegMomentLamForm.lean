import Mathlib
import LatticeProb.Analysis.NegMomentRecursion

/-!
# Polynomial decay of a Laplace-transform envelope from a one-step self-improving recursion

Let `l : (0, ∞) → [0, 1]` be nonincreasing with `l ≤ ρ < 1` on `[λ₀, ∞)`. Suppose that for every
`x > 0` and `u ≥ u₀`
`l (x e^u) ≤ max (β (x e^u)) (K₀ exp(-s (u-u₀)²) + l(x)^N)`, with `N ≥ 2`, `K₀ ≥ 0`, `s > 0`, and
`β (x) ≤ C₁ x⁻¹`. Then `l (x) ≤ C x^{-a}` for all `x > 0`, for some `C, a > 0`.

The proof applies `LatticeProb.exists_superexp_decay_of_recursion` along the geometric-Gaussian
sequence `λ_j = λ₀ exp(j(j-1)/2 + j u₀)`, `λ_{j+1} = λ_j e^{j + u₀}`, and then interpolates between
consecutive terms using monotonicity.

* `LatticeProb.exists_rpow_decay_of_recursion`: the conclusion.
-/

open Filter Topology

namespace LatticeProb

private lemma nat_le_sq (j : ℕ) : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
  exact_mod_cast Nat.le_self_pow (two_ne_zero) j

/-- A nonincreasing envelope `l` of Laplace transforms which improves from `l(x)` to `l(x e^u)` in
one step, up to a polynomially small error `β`, decays polynomially. -/
theorem exists_rpow_decay_of_recursion {N : ℕ} (hN : 2 ≤ N) {ρ lam0 u0 K0 s C1 : ℝ} (hρ : ρ < 1)
    (hlam0 : 0 < lam0) (hu0 : 0 ≤ u0) (hK0 : 0 ≤ K0) (hs : 0 < s) (hC1 : 0 ≤ C1)
    {l β : ℝ → ℝ} (hl0 : ∀ x, 0 < x → 0 ≤ l x) (hl1 : ∀ x, 0 < x → l x ≤ 1)
    (hanti : ∀ x y, 0 < x → x ≤ y → l y ≤ l x) (hρl : ∀ x, lam0 ≤ x → l x ≤ ρ)
    (hβ : ∀ x, 0 < x → β x ≤ C1 * x⁻¹)
    (hrec : ∀ x, 0 < x → ∀ u, u0 ≤ u →
      l (x * Real.exp u) ≤ max (β (x * Real.exp u)) (K0 * Real.exp (-(s * (u - u0) ^ 2)) + l x ^ N)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ x, 0 < x → l x ≤ C * x ^ (-a) := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ, ∀ j : ℕ,
      L j = lam0 * Real.exp ((j : ℝ) * ((j : ℝ) - 1) / 2 + (j : ℝ) * u0) := ⟨_, fun _ => rfl⟩
  have hLpos : ∀ j, 0 < L j := fun j => by rw [hL]; positivity
  have hexp0 : ∀ j : ℕ, 0 ≤ (j : ℝ) * ((j : ℝ) - 1) / 2 + (j : ℝ) * u0 := by
    intro j
    have := nat_le_sq j
    have h2 : 0 ≤ (j : ℝ) * u0 := mul_nonneg (Nat.cast_nonneg j) hu0
    nlinarith
  have hL0 : ∀ j, lam0 ≤ L j := by
    intro j
    rw [hL]
    have : (1 : ℝ) ≤ Real.exp ((j : ℝ) * ((j : ℝ) - 1) / 2 + (j : ℝ) * u0) :=
      Real.one_le_exp (hexp0 j)
    nlinarith
  have hLs : ∀ j : ℕ, L (j + 1) = L j * Real.exp ((j : ℝ) + u0) := by
    intro j
    rw [hL, hL, mul_assoc, ← Real.exp_add]
    congr 2
    push_cast
    ring
  -- the sequence `u j = l (L j)` and its recursion
  set c : ℝ := min (1 / 2) s with hcdef
  have hc : 0 < c := lt_min (by norm_num) hs
  set K : ℝ := C1 * lam0⁻¹ + K0 + 1 with hKdef
  have hK : 0 < K := by positivity
  have hrec' : ∀ j : ℕ, l (L (j + 1)) ≤
      (C1 * (L (j + 1))⁻¹ + K0 * Real.exp (-(s * (j : ℝ) ^ 2))) + l (L j) ^ N := by
    intro j
    have h1 := hrec (L j) (hLpos j) ((j : ℝ) + u0) (by linarith [Nat.cast_nonneg (α := ℝ) j])
    rw [← hLs j] at h1
    have h2 : (j : ℝ) + u0 - u0 = (j : ℝ) := by ring
    rw [h2] at h1
    have hpos : 0 ≤ K0 * Real.exp (-(s * (j : ℝ) ^ 2)) + l (L j) ^ N := by
      have := hl0 (L j) (hLpos j)
      positivity
    have hβj := hβ (L (j + 1)) (hLpos (j + 1))
    have hCpos : 0 ≤ C1 * (L (j + 1))⁻¹ := by
      have := hLpos (j + 1)
      positivity
    refine h1.trans (max_le ?_ ?_) <;> linarith
  have hE : ∀ j : ℕ, (C1 * (L (j + 1))⁻¹ + K0 * Real.exp (-(s * (j : ℝ) ^ 2))) ≤
      K * Real.exp (-(c * (j : ℝ) ^ 2)) := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hinv : (L (j + 1))⁻¹ = lam0⁻¹ * Real.exp (-(((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
        + ((j + 1 : ℕ) : ℝ) * u0)) := by
      rw [hL, mul_inv, Real.exp_neg]
    have hg : c * (j : ℝ) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
        + ((j + 1 : ℕ) : ℝ) * u0 := by
      push_cast
      have hc2 : c ≤ 1 / 2 := min_le_left _ _
      nlinarith [mul_nonneg hj0 hu0, sq_nonneg (j : ℝ), mul_le_mul_of_nonneg_right hc2
        (sq_nonneg (j : ℝ))]
    have e1 : Real.exp (-(((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
        + ((j + 1 : ℕ) : ℝ) * u0)) ≤ Real.exp (-(c * (j : ℝ) ^ 2)) :=
      Real.exp_le_exp.2 (by linarith)
    have e2 : Real.exp (-(s * (j : ℝ) ^ 2)) ≤ Real.exp (-(c * (j : ℝ) ^ 2)) :=
      Real.exp_le_exp.2 (by
        have : c ≤ s := min_le_right _ _
        nlinarith [sq_nonneg (j : ℝ)])
    have t1 : C1 * (L (j + 1))⁻¹ ≤ C1 * lam0⁻¹ * Real.exp (-(c * (j : ℝ) ^ 2)) := by
      rw [hinv, ← mul_assoc, mul_assoc C1]
      calc C1 * (lam0⁻¹ * Real.exp _) ≤ C1 * (lam0⁻¹ * Real.exp (-(c * (j : ℝ) ^ 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 (by positivity)) hC1
        _ = C1 * lam0⁻¹ * Real.exp (-(c * (j : ℝ) ^ 2)) := by ring
    have t2 : K0 * Real.exp (-(s * (j : ℝ) ^ 2)) ≤ K0 * Real.exp (-(c * (j : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left e2 hK0
    have t3 := (Real.exp_pos (-(c * (j : ℝ) ^ 2))).le
    have t4 : 0 ≤ C1 * lam0⁻¹ := by positivity
    nlinarith
  obtain ⟨a, ha, hu⟩ := exists_superexp_decay_of_recursion (N := N) hN (ρ := ρ) (K := K) (c := c)
    hρ hK hc (u := fun j => l (L j))
    (E := fun j => C1 * (L (j + 1))⁻¹ + K0 * Real.exp (-(s * (j : ℝ) ^ 2)))
    (fun j => hl0 _ (hLpos j)) (fun j => hρl _ (hL0 j)) hE hrec'
  -- interpolation
  set a0 : ℝ := a / (1 + u0) with ha0def
  have ha0 : 0 < a0 := by positivity
  have hfa : ∀ j : ℕ, a0 * (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
      + ((j + 1 : ℕ) : ℝ) * u0) ≤ a * (j : ℝ) ^ 2 + 2 * a := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2 + ((j + 1 : ℕ) : ℝ) * u0)
        ≤ (1 + u0) * (j : ℝ) ^ 2 + 2 * (1 + u0) := by
      push_cast
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 + u0) (sq_nonneg ((j : ℝ) - 1 / 2))]
    have h2 : a0 * (1 + u0) = a := by rw [ha0def]; field_simp
    calc _ ≤ a0 * ((1 + u0) * (j : ℝ) ^ 2 + 2 * (1 + u0)) :=
          mul_le_mul_of_nonneg_left h1 ha0.le
      _ = a * (j : ℝ) ^ 2 + 2 * a := by rw [← h2]; ring
  refine ⟨a0, 4 * lam0 ^ a0 * Real.exp (2 * a), ha0, by positivity, fun x hx => ?_⟩
  have hxa : 0 < x ^ a0 := Real.rpow_pos_of_pos hx _
  have hla : 0 < lam0 ^ a0 := Real.rpow_pos_of_pos hlam0 _
  have h4 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  by_cases hxl : x < lam0
  · -- below the starting point, `l ≤ 1`
    have h1 := hl1 x hx
    have h2 : x ^ a0 ≤ lam0 ^ a0 := Real.rpow_le_rpow hx.le hxl.le ha0.le
    rw [Real.rpow_neg hx.le]
    have : 1 ≤ 4 * lam0 ^ a0 * Real.exp (2 * a) * (x ^ a0)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hxa]
      nlinarith
    linarith
  · have hxl' : lam0 ≤ x := not_lt.1 hxl
    have hex : ∃ j : ℕ, x < L (j + 1) := by
      obtain ⟨j, hj⟩ := exists_nat_gt (x / lam0)
      refine ⟨j, ?_⟩
      rw [hL]
      have h1 := nat_le_sq j
      have h2 : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
          + ((j + 1 : ℕ) : ℝ) * u0 := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hu0, Nat.cast_nonneg (α := ℝ) j]
      have h3 := Real.add_one_le_exp (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
          + ((j + 1 : ℕ) : ℝ) * u0)
      have h5 : x / lam0 < Real.exp (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
          + ((j + 1 : ℕ) : ℝ) * u0) := by linarith
      rwa [div_lt_iff₀ hlam0, mul_comm] at h5
    classical
    set j := Nat.find hex with hjdef
    have hj1 : x < L (j + 1) := Nat.find_spec hex
    have hj2 : L j ≤ x := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, hL]; simpa using hxl'
      · obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have := Nat.find_min hex (show i < j by omega)
        rw [hi]
        exact not_lt.1 this
    have hl_le : l x ≤ 4 * Real.exp (-(a * (j : ℝ) ^ 2)) :=
      (hanti (L j) x (hLpos j) hj2).trans (hu j)
    have hxa' : x ^ a0 ≤ lam0 ^ a0 * Real.exp (a * (j : ℝ) ^ 2 + 2 * a) := by
      calc x ^ a0 ≤ (L (j + 1)) ^ a0 := Real.rpow_le_rpow hx.le hj1.le ha0.le
        _ = lam0 ^ a0 * Real.exp (a0 * (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) / 2
            + ((j + 1 : ℕ) : ℝ) * u0)) := by
          rw [hL, Real.mul_rpow hlam0.le (Real.exp_pos _).le, ← Real.exp_mul, mul_comm _ a0]
        _ ≤ lam0 ^ a0 * Real.exp (a * (j : ℝ) ^ 2 + 2 * a) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hfa j)) hla.le
    rw [Real.rpow_neg hx.le, ← div_eq_mul_inv]
    refine hl_le.trans ?_
    rw [le_div_iff₀ hxa]
    calc 4 * Real.exp (-(a * (j : ℝ) ^ 2)) * x ^ a0
        ≤ 4 * Real.exp (-(a * (j : ℝ) ^ 2)) * (lam0 ^ a0 * Real.exp (a * (j : ℝ) ^ 2 + 2 * a)) :=
          mul_le_mul_of_nonneg_left hxa' (by positivity)
      _ = 4 * lam0 ^ a0 * Real.exp (2 * a) := by
          rw [Real.exp_add]
          have : Real.exp (-(a * (j : ℝ) ^ 2)) * Real.exp (a * (j : ℝ) ^ 2) = 1 := by
            rw [← Real.exp_add]; simp
          calc _ = 4 * lam0 ^ a0 * Real.exp (2 * a) *
                (Real.exp (-(a * (j : ℝ) ^ 2)) * Real.exp (a * (j : ℝ) ^ 2)) := by ring
            _ = _ := by rw [this, mul_one]

end LatticeProb
