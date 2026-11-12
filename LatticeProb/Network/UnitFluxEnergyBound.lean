import LatticeProb.Network.ConductanceThomsonBound

/-!
# Energy of separating functions from a potential with unit flux

Let `c : V → V → ℝ` be symmetric nonnegative conductances, `F ⊆ B ⊆ S` finite sets of vertices, and `g` a potential
vanishing off `B`, harmonic on `B \ F` (`∑_{b ∈ S} c(a,b) (g(a) − g(b)) = 0`), whose current
`c(a,b) (g(a) − g(b))` has total flux `1` out of `F`. If across every edge leaving `F` the potential decreases and
its value on the `F`-side is at most `K`, then every function `h` with `h = 1` on `F` and `h = 0` off `B` has energy
`½ ∑_{a,b ∈ S} c(a,b) (h(a) − h(b))² ≥ 1 / K`.

In the language of electrical networks: the effective resistance between `F` and the complement of `B` is at most
`K`. For the Green function `g = g_B(x, ·)` of the walk killed on exiting `B` and the super-level set
`F = {g > t}` this is the upper bound `R(F ↔ Bᶜ) ≤ t + δ` in the comparison of the Green function with effective
resistances of Berestycki and Gwynne (*Random walks on mated-CRT planar maps and Liouville Brownian motion*,
Lemma 3.4), where `δ` bounds the increments of `g` across edges.

The proof is Thomson's argument restricted to the edges not inside `F`: with `w = c dg` on those edges, summation
by parts gives `∑ w dh = 2` (unit flux, harmonicity) and `∑ w dg ≤ 2K`, and `2 dg dh ≤ dg²/K + K dh²`.

## Main statements

* `LatticeProb.one_le_mul_energy_of_unitFlux`: `1 ≤ K · ½ ∑_{a,b ∈ S} c(a,b) (h(a) − h(b))²`.
-/

namespace LatticeProb

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Energy lower bound from a potential with unit flux.** Let `c` be symmetric nonnegative conductances,
`F ⊆ B ⊆ S` finite, `g` vanishing off `B`, harmonic on `B \ F`, with unit flux of `c dg` out of `F`, and such that
across every edge `a ∼ b` with `a ∈ F`, `b ∉ F` one has `g(b) ≤ g(a) ≤ K`, `K > 0`. Then every `h` with `h = 1` on
`F` and `h = 0` off `B` satisfies `1 ≤ K · ½ ∑_{a,b ∈ S} c(a,b) (h(a) − h(b))²`. -/
theorem one_le_mul_energy_of_unitFlux {S B F : Finset V} (hFB : F ⊆ B) (hBS : B ⊆ S)
    {c : V → V → ℝ} (hc : ∀ a b, c a b = c b a) (hc0 : ∀ a b, 0 ≤ c a b)
    {g : V → ℝ} (hg : ∀ a, a ∉ B → g a = 0)
    (hharm : ∀ a ∈ B, a ∉ F → ∑ b ∈ S, c a b * (g a - g b) = 0)
    (hflux : ∑ a ∈ F, ∑ b ∈ S, (if b ∈ F then 0 else c a b * (g a - g b)) = 1)
    {K : ℝ} (hK : 0 < K)
    (hFK : ∀ a ∈ F, ∀ b ∈ S, b ∉ F → c a b ≠ 0 → g b ≤ g a ∧ g a ≤ K)
    {h : V → ℝ} (h1 : ∀ a ∈ F, h a = 1) (h0 : ∀ a, a ∉ B → h a = 0) :
    1 ≤ K * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, c a b * (h a - h b) ^ 2) := by
  set w : V → V → ℝ := fun a b => if a ∈ F ∧ b ∈ F then 0 else c a b * (g a - g b) with hwdef
  have hw : ∀ a b, w a b = -w b a := by
    intro a b
    simp only [hwdef]
    rw [hc b a]
    by_cases ha : a ∈ F <;> by_cases hb : b ∈ F <;> simp [ha, hb] <;> ring
  have hrowF : ∀ a ∈ F, ∑ b ∈ S, w a b = ∑ b ∈ S, (if b ∈ F then 0 else c a b * (g a - g b)) := by
    intro a ha
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ F <;> simp [hwdef, ha, hb]
  have hrow : ∀ u : V → ℝ, (∀ a, a ∉ B → u a = 0) →
      ∀ a ∈ S, a ∉ F → u a * ∑ b ∈ S, w a b = 0 := by
    intro u hu a _ haF
    by_cases haB : a ∈ B
    · have hsum : ∑ b ∈ S, w a b = ∑ b ∈ S, c a b * (g a - g b) :=
        Finset.sum_congr rfl fun b _ => by simp [hwdef, haF]
      rw [hsum, hharm a haB haF, mul_zero]
    · rw [hu a haB, zero_mul]
  have hFS : F ⊆ S := hFB.trans hBS
  -- the flux of `w` against `h` is `2`
  have hI1 : ∑ a ∈ S, ∑ b ∈ S, w a b * (h a - h b) = 2 := by
    have hhalf := sum_mul_antisymm_eq_half S h w hw
    have hsplit : ∑ a ∈ S, ∑ b ∈ S, h a * w a b = 1 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_subset hFS (fun a ha haF => hrow h h0 a ha haF)]
      rw [Finset.sum_congr rfl fun a ha => by rw [h1 a ha, one_mul, hrowF a ha]]
      exact hflux
    linarith
  -- the energy of `w` is at most `2K`
  have hI2 : ∑ a ∈ S, ∑ b ∈ S, w a b * (g a - g b) ≤ 2 * K := by
    have hhalf := sum_mul_antisymm_eq_half S g w hw
    have hsplit : ∑ a ∈ S, ∑ b ∈ S, g a * w a b =
        ∑ a ∈ F, g a * ∑ b ∈ S, (if b ∈ F then 0 else c a b * (g a - g b)) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_subset hFS (fun a ha haF => hrow g hg a ha haF)]
      exact Finset.sum_congr rfl fun a ha => by rw [hrowF a ha]
    have hle : ∑ a ∈ F, g a * ∑ b ∈ S, (if b ∈ F then 0 else c a b * (g a - g b)) ≤
        ∑ a ∈ F, K * ∑ b ∈ S, (if b ∈ F then 0 else c a b * (g a - g b)) := by
      refine Finset.sum_le_sum fun a ha => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun b hb => ?_
      by_cases hbF : b ∈ F
      · simp [hbF]
      · by_cases hcab : c a b = 0
        · simp [hbF, hcab]
        · obtain ⟨hgb, hgK⟩ := hFK a ha b hb hbF hcab
          simp only [hbF, ↓reduceIte]
          exact mul_le_mul_of_nonneg_right hgK (mul_nonneg (hc0 a b) (by linarith))
    have hK1 : ∑ a ∈ F, K * ∑ b ∈ S, (if b ∈ F then 0 else c a b * (g a - g b)) = K := by
      rw [← Finset.mul_sum, hflux, mul_one]
    linarith
  -- pointwise `2 w dh ≤ w dg / K + K c dh²`
  have hpt : ∀ a b, 2 * (w a b * (h a - h b)) ≤
      w a b * (g a - g b) / K + K * (c a b * (h a - h b) ^ 2) := by
    intro a b
    have hKc : 0 ≤ K * (c a b * (h a - h b) ^ 2) :=
      mul_nonneg hK.le (mul_nonneg (hc0 a b) (sq_nonneg _))
    by_cases hab : a ∈ F ∧ b ∈ F
    · simp only [hwdef, hab, and_self, ↓reduceIte, zero_mul, mul_zero, zero_div, zero_add]
      exact hKc
    · simp only [hwdef, hab, ↓reduceIte]
      have hsq : 0 ≤ c a b * ((g a - g b) - K * (h a - h b)) ^ 2 / K :=
        div_nonneg (mul_nonneg (hc0 a b) (sq_nonneg _)) hK.le
      have hid : c a b * (g a - g b) * (g a - g b) / K + K * (c a b * (h a - h b) ^ 2) -
          2 * (c a b * (g a - g b) * (h a - h b)) =
          c a b * ((g a - g b) - K * (h a - h b)) ^ 2 / K := by
        field_simp
        ring
      linarith
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ S) =>
    Finset.sum_le_sum fun b (_ : b ∈ S) => hpt a b
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  have hdiv : (∑ a ∈ S, ∑ b ∈ S, w a b * (g a - g b)) / K ≤ 2 := by
    rw [div_le_iff₀ hK]
    linarith
  rw [hI1] at hsum
  linarith

end LatticeProb
