import Mathlib

/-!
# Thomson's bound for the Green function with conductances

Let `c : V → V → ℝ` be symmetric nonnegative conductances (for a random walk on a multigraph, the edge
multiplicities), let `A ⊆ S` be finite sets of vertices such that every neighbour of a vertex of `A` lies in `S`,
and let `u` vanish off `A` and solve the Poisson problem
`∑_{b ∈ S} c(a,b) (u(a) − u(b)) = D·𝟙{a = x}` for `a ∈ A`. For the walk killed on exiting `A`, `u` is `D/deg(x)`
times the Green function `G_A(·, x)`. Then for every unit flow `θ` from `x` out of `A`
(antisymmetric, carried by the edges, with divergence `𝟙{a = x}` on `A`),
`u(x) ≤ D · ½ ∑_{a,b ∈ S} θ(a,b)² / c(a,b)`.

This is Thomson's principle in the form of an upper bound for the effective resistance: summation by parts gives
`D·u(x) = ½ ∑ c (du)²` and `u(x) = ½ ∑ θ du`, and the Cauchy–Schwarz inequality concludes.

## Main statements

* `LatticeProb.sum_mul_antisymm_eq_half`: summation by parts against an antisymmetric kernel.
* `LatticeProb.le_mul_flowEnergy_of_poisson`: the bound above.
-/

namespace LatticeProb

open Finset

variable {V : Type*}

/-- **Summation by parts.** For an antisymmetric kernel `w`,
`∑_{a,b ∈ S} u(a) w(a,b) = ½ ∑_{a,b ∈ S} w(a,b) (u(a) − u(b))`. -/
theorem sum_mul_antisymm_eq_half (S : Finset V) (u : V → ℝ) (w : V → V → ℝ)
    (hw : ∀ a b, w a b = -w b a) :
    ∑ a ∈ S, ∑ b ∈ S, u a * w a b = (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, w a b * (u a - u b) := by
  have h1 : ∑ a ∈ S, ∑ b ∈ S, u a * w a b = -∑ a ∈ S, ∑ b ∈ S, u b * w a b := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hw b a]
    ring
  have h2 : ∑ a ∈ S, ∑ b ∈ S, w a b * (u a - u b) =
      ∑ a ∈ S, ∑ b ∈ S, u a * w a b - ∑ a ∈ S, ∑ b ∈ S, u b * w a b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h2]
  linarith

/-- **Thomson's bound for the Poisson problem with conductances.** Let `c` be symmetric nonnegative conductances,
`A ⊆ S` finite with every `c`-neighbour of `A` in `S`, and `u` vanishing off `A` with
`∑_{b ∈ S} c(a,b) (u(a) − u(b)) = D·𝟙{a = x}` on `A`, `D ≥ 0`. If `θ` is antisymmetric, vanishes where `c` does, and
has divergence `∑_{b ∈ S} θ(a,b) = 𝟙{a = x}` at every `a ∈ A`, then
`u(x) ≤ D · ½ ∑_{a,b ∈ S} θ(a,b)² / c(a,b)`. -/
theorem le_mul_flowEnergy_of_poisson [DecidableEq V] {S A : Finset V} (hAS : A ⊆ S)
    {c : V → V → ℝ} (hc : ∀ a b, c a b = c b a) (hc0 : ∀ a b, 0 ≤ c a b)
    {u : V → ℝ} (hu : ∀ a, a ∉ A → u a = 0) {x : V} (hx : x ∈ A) {D : ℝ} (hD : 0 ≤ D)
    (hlap : ∀ a ∈ A, ∑ b ∈ S, c a b * (u a - u b) = if a = x then D else 0)
    {θ : V → V → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, c a b = 0 → θ a b = 0)
    (hdiv : ∀ a ∈ A, ∑ b ∈ S, θ a b = if a = x then 1 else 0) :
    u x ≤ D * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / c a b) := by
  have hAtoS : ∀ f : V → ℝ, ∑ a ∈ A, u a * f a = ∑ a ∈ S, u a * f a := fun f =>
    Finset.sum_subset hAS fun a _ ha => by rw [hu a ha, zero_mul]
  -- `D u(x)` is the Dirichlet energy of `u`
  have hDu : D * u x = (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, c a b * (u a - u b) ^ 2 := by
    have e1 : ∑ a ∈ A, u a * (∑ b ∈ S, c a b * (u a - u b)) = u x * D := by
      rw [Finset.sum_congr rfl fun a ha => by rw [hlap a ha]]
      simp [mul_ite, hx]
    rw [hAtoS] at e1
    simp_rw [Finset.mul_sum] at e1
    have k := sum_mul_antisymm_eq_half S u (fun a b => c a b * (u a - u b))
      (fun a b => by rw [hc a b]; ring)
    rw [k] at e1
    have hsq : ∀ a b, c a b * (u a - u b) * (u a - u b) = c a b * (u a - u b) ^ 2 := fun a b => by ring
    simp_rw [hsq] at e1
    linarith
  -- `u(x)` is the pairing of the flow with the gradient of `u`
  have hux : u x = (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b * (u a - u b) := by
    have e2 : ∑ a ∈ A, u a * (∑ b ∈ S, θ a b) = u x := by
      rw [Finset.sum_congr rfl fun a ha => by rw [hdiv a ha]]
      simp [mul_ite, hx]
    rw [hAtoS] at e2
    simp_rw [Finset.mul_sum] at e2
    rw [sum_mul_antisymm_eq_half S u θ hθ] at e2
    linarith
  -- Cauchy–Schwarz
  have hcs : (∑ a ∈ S, ∑ b ∈ S, θ a b * (u a - u b)) ^ 2 ≤
      (∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / c a b) * ∑ a ∈ S, ∑ b ∈ S, c a b * (u a - u b) ^ 2 := by
    let f : V × V → ℝ := fun p => θ p.1 p.2 / Real.sqrt (c p.1 p.2)
    let g : V × V → ℝ := fun p => Real.sqrt (c p.1 p.2) * (u p.1 - u p.2)
    have hfg : ∀ a b, θ a b * (u a - u b) = f (a, b) * g (a, b) := by
      intro a b
      by_cases h0 : c a b = 0
      · simp [f, g, hθc a b h0]
      · have hs : Real.sqrt (c a b) ≠ 0 :=
          Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (hc0 a b) (Ne.symm h0))
        simp only [f, g]
        field_simp
    have hf2 : ∀ a b, θ a b ^ 2 / c a b = f (a, b) ^ 2 := by
      intro a b
      simp only [f, div_pow, Real.sq_sqrt (hc0 a b)]
    have hg2 : ∀ a b, c a b * (u a - u b) ^ 2 = g (a, b) ^ 2 := by
      intro a b
      simp only [g, mul_pow, Real.sq_sqrt (hc0 a b)]
    simp_rw [hfg, hf2, hg2]
    rw [← Finset.sum_product' (f := fun a b => f (a, b) * g (a, b)),
      ← Finset.sum_product' (f := fun a b => f (a, b) ^ 2),
      ← Finset.sum_product' (f := fun a b => g (a, b) ^ 2)]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ f g
  have hE : 0 ≤ ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / c a b :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => div_nonneg (sq_nonneg _) (hc0 a b)
  by_cases hpos : 0 < u x
  · have hsq : u x * u x ≤ (D * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / c a b)) * u x := by
      have h4 : u x ^ 2 ≤ (1 / 4) * ((∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / c a b) *
          ∑ a ∈ S, ∑ b ∈ S, c a b * (u a - u b) ^ 2) := by
        rw [hux]
        nlinarith [hcs]
      nlinarith [h4, hDu]
    exact le_of_mul_le_mul_right hsq hpos
  · exact (le_of_not_gt hpos).trans (mul_nonneg hD (mul_nonneg (by norm_num) hE))

end LatticeProb
