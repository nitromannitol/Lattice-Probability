import Mathlib
import LatticeProb.Network.ConductanceThomsonBound

/-!
# Lower bound for the energy of a unit flow out of a set, from a clamped Poisson potential

Let `c : V → V → ℝ` be symmetric nonnegative conductances on a finite vertex set `S`, let `A ⊆ B ⊆ S`, and let `u`
vanish off `B` and solve the Poisson problem `∑_{b ∈ S} c(a,b) (u(a) − u(b)) = 𝟙{a = x}` on `B`, with the pole `x`
in `A` (for the walk killed on exiting `B`, `u` is the normalized Green function with pole `x`). If `u ≥ a₀ ≥ 0` on `A`,
then every unit flow `θ` from the set `A` out to the complement of `B` (antisymmetric, carried by the edges,
divergence-free on `B ∖ A`, total flux `1` out of `A`) has energy `½ ∑ θ(a,b)² / c(a,b) ≥ a₀`.

The proof tests the flow against the clamped potential `f = min (u, a₀)`, which equals `a₀` on `A` and vanishes off
`B`: summation by parts gives `½ ∑ c (df)² ≤ ½ ∑ c du df = f(x) = a₀` (the clamp is monotone and `1`-Lipschitz) and
`∑ θ df = 2 a₀`, and the inequality `θ d ≤ θ² / (2c) + c d² / 2` finishes. In terms of effective resistance, this is the
lower bound `R(A ↔ Bᶜ) ≥ min_A u` with no error term.

## Main statement

* `LatticeProb.le_flowEnergy_of_clamped_poisson`
-/

namespace LatticeProb

open Finset

variable {V : Type*}

/-- A clamp is monotone and `1`-Lipschitz: `(min p a − min q a)² ≤ (p − q)(min p a − min q a)`. -/
theorem sq_min_sub_min_le (p q a : ℝ) :
    (min p a - min q a) ^ 2 ≤ (p - q) * (min p a - min q a) := by
  rcases le_total p a with hp | hp <;> rcases le_total q a with hq | hq
  · simp only [min_eq_left hp, min_eq_left hq]; nlinarith
  · simp only [min_eq_left hp, min_eq_right hq]; nlinarith
  · simp only [min_eq_right hp, min_eq_left hq]; nlinarith
  · simp only [min_eq_right hp, min_eq_right hq]; nlinarith

/-- The weighted inequality of arithmetic and geometric means `θ d ≤ θ² / (2 c) + c d² / 2` for `c ≥ 0`, `θ = 0` if `c = 0`. -/
theorem mul_le_div_add_mul_sq {c θ d : ℝ} (hc : 0 ≤ c) (hθ : c = 0 → θ = 0) :
    θ * d ≤ θ ^ 2 / (2 * c) + c * d ^ 2 / 2 := by
  rcases hc.eq_or_lt with h | h
  · have := hθ h.symm
    subst this
    subst h
    simp
  · have h2 : θ ^ 2 / (2 * c) - θ * d + c * d ^ 2 / 2 = (θ - c * d) ^ 2 / (2 * c) := by
      field_simp
      ring
    have h3 : 0 ≤ (θ - c * d) ^ 2 / (2 * c) := by positivity
    linarith

/-- **The energy of a unit flow from `A` to the complement of `B` is at least the minimum of the Poisson
potential on `A`.** -/
theorem le_flowEnergy_of_clamped_poisson [DecidableEq V] {S B A : Finset V} (hBS : B ⊆ S) (hAB : A ⊆ B)
    {c : V → V → ℝ} (hc : ∀ a b, c a b = c b a) (hc0 : ∀ a b, 0 ≤ c a b)
    {u : V → ℝ} (hu : ∀ a, a ∉ B → u a = 0) {x : V} (hx : x ∈ A)
    (hlap : ∀ a ∈ B, ∑ b ∈ S, c a b * (u a - u b) = if a = x then 1 else 0)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (hA : ∀ y ∈ A, a₀ ≤ u y)
    {θ : V → V → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, c a b = 0 → θ a b = 0)
    (hdiv : ∀ v ∈ B, v ∉ A → ∑ b ∈ S, θ v b = 0) (hflux : ∑ v ∈ A, ∑ b ∈ S, θ v b = 1) :
    a₀ ≤ (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / c a b := by
  set f : V → ℝ := fun v => min (u v) a₀ with hf
  have hf0 : ∀ a, a ∉ B → f a = 0 := fun a ha => by
    simp only [hf, hu a ha]; exact min_eq_left ha₀
  have hfA : ∀ y ∈ A, f y = a₀ := fun y hy => min_eq_right (hA y hy)
  have hxB : x ∈ B := hAB hx
  have hxS : x ∈ S := hBS hxB
  -- the antisymmetric kernel `c (u a - u b)`
  have hw : ∀ a b, c a b * (u a - u b) = -(c b a * (u b - u a)) := fun a b => by
    rw [hc a b]; ring
  -- Step 1: `∑ c du df = 2 a₀`
  have hS1 : ∑ a ∈ S, ∑ b ∈ S, f a * (c a b * (u a - u b)) = a₀ := by
    have h1 : ∀ a ∈ S, ∑ b ∈ S, f a * (c a b * (u a - u b)) = if a = x then a₀ else 0 := by
      intro a _
      rw [← Finset.mul_sum]
      by_cases haB : a ∈ B
      · rw [hlap a haB]
        by_cases hax : a = x
        · subst hax; simp [hfA a hx]
        · simp [hax]
      · have hax : a ≠ x := fun h => haB (h ▸ hxB)
        simp [hf0 a haB, hax]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' S x (fun _ => a₀)]
    simp [hxS]
  have hS1' := sum_mul_antisymm_eq_half S f (fun a b => c a b * (u a - u b)) hw
  rw [hS1] at hS1'
  -- Step 2: the energy of `f`
  have hEf : ∑ a ∈ S, ∑ b ∈ S, c a b * (f a - f b) ^ 2 ≤ 2 * a₀ := by
    calc ∑ a ∈ S, ∑ b ∈ S, c a b * (f a - f b) ^ 2
        ≤ ∑ a ∈ S, ∑ b ∈ S, c a b * (u a - u b) * (f a - f b) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          have := sq_min_sub_min_le (u a) (u b) a₀
          have h := mul_le_mul_of_nonneg_left this (hc0 a b)
          simp only [hf]
          nlinarith [h]
      _ = 2 * a₀ := by linarith
  -- Step 3: the flux `∑ θ df = 2 a₀`
  have hθf := sum_mul_antisymm_eq_half S f θ hθ
  have hdivf : ∑ a ∈ S, ∑ b ∈ S, f a * θ a b = a₀ := by
    have h1 : ∀ a ∈ S, ∑ b ∈ S, f a * θ a b = if a ∈ A then a₀ * ∑ b ∈ S, θ a b else 0 := by
      intro a _
      rw [← Finset.mul_sum]
      by_cases haA : a ∈ A
      · simp [haA, hfA a haA]
      · by_cases haB : a ∈ B
        · simp [haA, hdiv a haB haA]
        · simp [haA, hf0 a haB]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have hfil : S.filter (· ∈ A) = A := by
      ext v; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hBS (hAB h), h⟩⟩
    rw [hfil, ← Finset.mul_sum, hflux, mul_one]
  rw [hdivf] at hθf
  -- Step 4: pointwise AM-GM
  have hamgm : 2 * a₀ ≤ ∑ a ∈ S, ∑ b ∈ S, (θ a b ^ 2 / (2 * c a b) + c a b * (f a - f b) ^ 2 / 2) := by
    calc 2 * a₀ = ∑ a ∈ S, ∑ b ∈ S, θ a b * (f a - f b) := by linarith
      _ ≤ _ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          mul_le_div_add_mul_sq (hc0 a b) (hθc a b)
  have hsplit : ∑ a ∈ S, ∑ b ∈ S, (θ a b ^ 2 / (2 * c a b) + c a b * (f a - f b) ^ 2 / 2) =
      (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / c a b +
        (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, c a b * (f a - f b) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
    refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
      (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    · rcases (hc0 a b).eq_or_lt with h | h
      · rw [← h]; simp
      · field_simp
    · ring
  rw [hsplit] at hamgm
  linarith

end LatticeProb
