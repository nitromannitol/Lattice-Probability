/-
The discrete Caccioppoli inequality for a harmonic function on a finite
weighted graph, and the first step of Moser iteration it feeds: a mean-value
bound at one harmonic vertex (`moser_mean_value`), summed over a finite set
of vertices of uniformly bounded total conductance (`moser_estimate`), and
specialized to a uniform bound on the neighbours (`moser_l2_step`). This is
the classical De Giorgi-Nash-Moser first step of discrete elliptic
regularity.

Moved from Unique-Continuation-Planar, `UCPlanar/Support/Poly/Caccioppoli.lean`.
The source file's own import `UCPlanar.Support.Poly.Basic` is unused by
anything in this file (verified directly: every identifier used here resolves
to Mathlib or to `LatticeProb.Network`), so it is dropped; `formOn_eq_neg_two_mul`
is already `LatticeProb.Network.formOn_eq_neg_two_mul` (`Network/Basic.lean`),
not in `Network/Variational.lean` as the source file's import suggests.
-/
import LatticeProb.Network.Basic

open scoped BigOperators Classical

namespace LatticeProb.Network

/-- The pointwise inequality behind the Caccioppoli estimate: for reals
`a, b, u, v`, expanding `((a-b)u)^2` against the cross term `2(a-b)(au^2-bv^2)`
leaves a remainder controlled by `(u-v)^2`. -/
theorem caccioppoli_pointwise (a b u v : ℝ) :
    (a - b) ^ 2 * u ^ 2
      ≤ 2 * (a - b) * (a * u ^ 2 - b * v ^ 2) + 4 * (a ^ 2 + b ^ 2) * (u - v) ^ 2 := by
  nlinarith [sq_nonneg ((a - b) * v + (a + b) * (u - v)), sq_nonneg (2 * a - b),
    sq_nonneg a, sq_nonneg b, sq_nonneg (u - v)]

variable {V : Type*} {G : SimpleGraph V}

/-- **The discrete Caccioppoli inequality.**  For `f` harmonic on `S` and a
cutoff `η` supported in `B ⊆ S` with all of `B`'s neighbours in `S`, the
`η`-weighted Dirichlet energy of `f` is controlled by the Dirichlet energy of
`η` itself, weighted by `f`. -/
theorem caccioppoli [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c)
    (S B : Finset V) (f η : V → ℝ)
    (hf : ∀ x ∈ S, netLaplacian G c f x = 0)
    (hη : ∀ x, x ∉ B → η x = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
  have hg : ∀ x, x ∉ B → f x * η x ^ 2 = 0 := fun x hx => by rw [hη x hx]; ring
  have hform := formOn_eq_neg_two_mul hc S B f
    (fun x => f x * η x ^ 2) hg hBS hnb
  have hharm : ∑ x ∈ B, f x * η x ^ 2 * netLaplacian G c f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hf x (hBS hx)]
    ring
  rw [hharm, mul_zero] at hform
  have hpt : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x,
      c x y * (f x - f y) ^ 2 * η x ^ 2
        ≤ 2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
          + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) := by
    intro x _ y _
    have hc0 := hc.nonneg x y
    nlinarith [caccioppoli_pointwise (f x) (f y) (η x) (η y),
      mul_nonneg hc0 (sq_nonneg (f x - f y)), mul_nonneg hc0 (sq_nonneg (η x - η y))]
  calc ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
            + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = 2 * formOn G c S f (fun x => f x * η x ^ 2)
          + 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        have h1 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)))
            = 2 * formOn G c S f (fun x => f x * η x ^ 2) := by
          simp only [formOn, Finset.mul_sum]
        have h2 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2))
            = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
          simp only [Finset.mul_sum]
        rw [show (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
                + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)))
            = (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)))
              + ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                  4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) from by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
        rw [h1, h2]
    _ = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        rw [hform]; ring

/-- **The first Moser-iteration step, at a single vertex.**  At a harmonic
vertex of positive total conductance, its squared value is at most the
conductance-weighted mean square of its neighbours (Cauchy-Schwarz applied to
the mean-value property). -/
theorem moser_mean_value [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c)
    (f : V → ℝ) (x₀ : V)
    (hx₀ : weight G c x₀ ≠ 0)
    (hf : netLaplacian G c f x₀ = 0) :
    f x₀ ^ 2 ≤ (∑ y ∈ G.neighborFinset x₀, c x₀ y * f y ^ 2)
      / weight G c x₀ := by
  rw [harmonic_iff_mean f hx₀] at hf
  rw [hf]
  set W := weight G c x₀ with hWdef
  have hW : 0 < W :=
    lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hc.nonneg x₀ y) (Ne.symm hx₀)
  have hcs : (∑ y ∈ G.neighborFinset x₀, c x₀ y * f y) ^ 2
      ≤ W * ∑ y ∈ G.neighborFinset x₀, c x₀ y * f y ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (G.neighborFinset x₀)
      (fun y => Real.sqrt (c x₀ y)) (fun y => Real.sqrt (c x₀ y) * f y)
    rw [hWdef, weight]
    have e1 : (∑ y ∈ G.neighborFinset x₀, Real.sqrt (c x₀ y) * (Real.sqrt (c x₀ y) * f y))
        = ∑ y ∈ G.neighborFinset x₀, c x₀ y * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← mul_assoc, ← sq, Real.sq_sqrt (hc.nonneg x₀ y)]
    have e2 : (∑ y ∈ G.neighborFinset x₀, Real.sqrt (c x₀ y) ^ 2)
        = ∑ y ∈ G.neighborFinset x₀, c x₀ y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Real.sq_sqrt (hc.nonneg x₀ y)]
    have e3 : (∑ y ∈ G.neighborFinset x₀, (Real.sqrt (c x₀ y) * f y) ^ 2)
        = ∑ y ∈ G.neighborFinset x₀, c x₀ y * f y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_pow, Real.sq_sqrt (hc.nonneg x₀ y)]
    rw [e1, e2, e3] at h
    exact h
  rw [div_pow, div_le_div_iff₀ (by positivity) hW]
  nlinarith [hcs]

/-- **The first Moser-iteration step, summed over a finite set.**  For `f`
harmonic on `B` with total conductance at every vertex of `B` at least `w`,
the sum of `f²` over `B` is at most `1/w` times the conductance-weighted sum
of the neighbours' squares. -/
theorem moser_estimate [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c)
    (B : Finset V) (f : V → ℝ) (w : ℝ) (hw : 0 < w)
    (hf : ∀ x ∈ B, netLaplacian G c f x = 0)
    (hweight : ∀ x ∈ B, w ≤ weight G c x) :
    ∑ x ∈ B, f x ^ 2
      ≤ (1 / w) * ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 := by
  have h : ∀ x ∈ B, f x ^ 2
      ≤ (∑ y ∈ G.neighborFinset x, c x y * f y ^ 2) / weight G c x :=
    fun x hx => moser_mean_value hc f x
      (ne_of_gt (lt_of_lt_of_le hw (hweight x hx))) (hf x hx)
  calc ∑ x ∈ B, f x ^ 2
      ≤ ∑ x ∈ B, (∑ y ∈ G.neighborFinset x, c x y * f y ^ 2)
          / weight G c x := Finset.sum_le_sum h
    _ ≤ ∑ x ∈ B, (1 / w) * ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hnum : 0 ≤ ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 :=
          Finset.sum_nonneg fun y _ => mul_nonneg (hc.nonneg x y) (sq_nonneg _)
        rw [div_le_iff₀ (lt_of_lt_of_le hw (hweight x hx))]
        rw [one_div_mul_eq_div]
        rw [div_mul_eq_mul_div, le_div_iff₀ hw]
        nlinarith [hweight x hx, hnum]
    _ = (1 / w) * ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 := by
        rw [Finset.mul_sum]

/-- **The first Moser-iteration step, against a uniform sup bound.**  For `f`
harmonic on `B` with total conductance at every vertex of `B` at least `w`,
each vertex's edges summing to conductance at most `K`, and `f` bounded by
`Ssup` everywhere, every vertex of `B` satisfies `f² ≤ (K/w) Ssup²`. -/
theorem moser_l2_step [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c)
    (B : Finset V) (f : V → ℝ) (K w Ssup : ℝ) (hw : 0 < w) (hK : 0 ≤ K)
    (hf : ∀ x ∈ B, netLaplacian G c f x = 0)
    (hweight : ∀ x ∈ B, w ≤ weight G c x)
    (hcond : ∀ x ∈ B, ∑ y ∈ G.neighborFinset x, c x y ≤ K)
    (hfsup : ∀ y, f y ^ 2 ≤ Ssup ^ 2) :
    ∀ x ∈ B, f x ^ 2 ≤ (K / w) * Ssup ^ 2 := by
  intro x hx
  have hW : 0 < weight G c x := lt_of_lt_of_le hw (hweight x hx)
  have hmv := moser_mean_value hc f x (ne_of_gt hW) (hf x hx)
  have hnum : ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2
      ≤ (∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy => by
      have hy2 := hfsup y
      nlinarith [hc.nonneg x y, hy2, sq_nonneg (f y), sq_nonneg Ssup]
  have hS : 0 ≤ Ssup ^ 2 := sq_nonneg Ssup
  calc f x ^ 2
      ≤ (∑ y ∈ G.neighborFinset x, c x y * f y ^ 2) / weight G c x := hmv
    _ ≤ ((∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2)
          / weight G c x := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hW)
    _ ≤ (K * Ssup ^ 2) / w := by
        rw [div_le_div_iff₀ hW hw]
        have h1 := hcond x hx
        have hKS : 0 ≤ K * Ssup ^ 2 := mul_nonneg hK hS
        have hstep1 : (∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2 ≤ K * Ssup ^ 2 :=
          mul_le_mul_of_nonneg_right h1 hS
        have hstep2 : (∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2 * w
            ≤ K * Ssup ^ 2 * w := mul_le_mul_of_nonneg_right hstep1 (le_of_lt hw)
        have hstep3 : K * Ssup ^ 2 * w ≤ K * Ssup ^ 2 * weight G c x :=
          mul_le_mul_of_nonneg_left (hweight x hx) hKS
        linarith
    _ = (K / w) * Ssup ^ 2 := by ring

end LatticeProb.Network
