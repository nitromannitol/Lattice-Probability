import LatticeProb.Analysis.NearFatCellCount
import LatticeProb.Analysis.FatCellInverseSquareSum
import LatticeProb.Network.ConductanceThomsonBound

/-!
# Energy of a flow through fat planar cells

Let `H a`, `a ∈ S`, be pairwise a.e.-disjoint bounded measurable planar cells inside
`closedBall u R`, each containing an open disc (an inball) of radius `κ · diam (H a)`, with
diameters in `[m, M]`. Let `w` be nonnegative conductances with weighted degrees
`∑ b, w a b ≤ Δ`, and let `θ` be a flow with `1 ≤ w a b` wherever `θ a b ≠ 0`, `|θ| ≤ 1`, and
`|θ a b| ≤ diam (H a) / dist (u, H a)` for the cells far from `u`
(those with `diam (H a) < dist (u, H a)`). Then the energy of `θ` satisfies
`∑ a ∑ b θ(a,b)² / w(a,b) ≤ Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)`.

The cells near `u` are counted by inball packing (`LatticeProb.card_le_logb_of_infDist_le_diam`);
the far cells are summed by comparison with `∫ |w - u|⁻²`
(`LatticeProb.sum_sq_div_sq_infDist_le`). Combined with the Thomson-type bound
`LatticeProb.le_mul_flowEnergy_of_poisson`, this bounds the value at the source of the solution
of a Poisson equation, i.e. the diagonal Green function of the network killed outside `A`.

## Main results

* `LatticeProb.sum_sq_div_le_sq_mul_sum`: the energy of one row of the flow.
* `LatticeProb.sum_sum_sq_div_le_of_fatCells`: the energy bound above.
* `LatticeProb.le_of_poisson_of_fatCells`: the resulting bound on the solution of the Poisson
  equation at its source.
-/

open MeasureTheory Metric Set Function

namespace LatticeProb

/-- One row of the energy: if `|θ b| ≤ β` on `S` and `1 ≤ w b` wherever `θ b ≠ 0`, then
`∑ b θ(b)² / w(b) ≤ β² ∑ b w(b)`. -/
theorem sum_sq_div_le_sq_mul_sum {ι : Type*} {S : Finset ι} {θ w : ι → ℝ} {β : ℝ}
    (hw0 : ∀ b ∈ S, 0 ≤ w b) (hw : ∀ b ∈ S, θ b ≠ 0 → 1 ≤ w b)
    (hθ : ∀ b ∈ S, |θ b| ≤ β) :
    ∑ b ∈ S, θ b ^ 2 / w b ≤ β ^ 2 * ∑ b ∈ S, w b := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  by_cases h0 : θ b = 0
  · calc θ b ^ 2 / w b = 0 := by rw [h0]; simp
      _ ≤ β ^ 2 * w b := mul_nonneg (sq_nonneg β) (hw0 b hb)
  · have h1 := hw b hb h0
    have hsq : θ b ^ 2 ≤ β ^ 2 := by
      have hθb := hθ b hb
      have hβ : 0 ≤ β := (abs_nonneg _).trans hθb
      calc θ b ^ 2 = |θ b| ^ 2 := (sq_abs _).symm
        _ ≤ β ^ 2 := by gcongr
    calc θ b ^ 2 / w b ≤ θ b ^ 2 := div_le_self (sq_nonneg _) h1
      _ ≤ β ^ 2 := hsq
      _ = β ^ 2 * 1 := (mul_one _).symm
      _ ≤ β ^ 2 * w b := by gcongr

/-- **Energy of a flow through fat planar cells.** For pairwise a.e.-disjoint bounded measurable
cells `H a ⊆ closedBall u R` with inballs `ball (c a) (κ · diam (H a)) ⊆ H a` and diameters in
`[m, M]`, conductances `w ≥ 0` with weighted degrees at most `Δ` and `w ≥ 1` on the support of
`θ`, a flow `θ` with `|θ| ≤ 1` and `|θ a b| ≤ diam (H a) / dist (u, H a)` for the cells far from
`u` has energy at most `Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)`. -/
theorem sum_sum_sq_div_le_of_fatCells {ι : Type*} {S : Finset ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {u : ℂ} {κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m) (hmM : m ≤ M)
    (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hd : (S : Set ι).Pairwise (AEDisjoint volume on H))
    (hHm : ∀ a ∈ S, MeasurableSet (H a)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, m ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    {θ w : ι → ι → ℝ} (hw0 : ∀ a b, 0 ≤ w a b) (hw : ∀ a b, θ a b ≠ 0 → 1 ≤ w a b)
    (hdeg : ∀ a ∈ S, ∑ b ∈ S, w a b ≤ Δ)
    (hθ1 : ∀ a ∈ S, ∀ b ∈ S, |θ a b| ≤ 1)
    (hθ : ∀ a ∈ S, diam (H a) < infDist u (H a) → ∀ b ∈ S,
      |θ a b| ≤ diam (H a) / infDist u (H a)) :
    ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / w a b ≤
      Δ * ((Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) + 8 * Real.log (R / m) / κ ^ 2) := by
  classical
  set β : ι → ℝ := fun a =>
    if diam (H a) < infDist u (H a) then diam (H a) / infDist u (H a) else 1 with hβ
  have hrow : ∀ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / w a b ≤ Δ * β a ^ 2 := by
    intro a ha
    refine (sum_sq_div_le_sq_mul_sum (β := β a) (fun b _ => hw0 a b) (fun b _ => hw a b)
      ?_).trans ?_
    · intro b hb'
      by_cases hf : diam (H a) < infDist u (H a)
      · simp only [hβ, hf, ↓reduceIte]; exact hθ a ha hf b hb'
      · simp only [hβ, hf, ↓reduceIte]; exact hθ1 a ha b hb'
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hdeg a ha) (sq_nonneg _)
  -- far cells: comparison with `∫ |w - u|⁻²`
  have hfar : ∑ a ∈ S with diam (H a) < infDist u (H a), β a ^ 2 ≤
      8 * Real.log (R / m) / κ ^ 2 := by
    have hT : ∀ a ∈ S.filter (fun a => diam (H a) < infDist u (H a)),
        a ∈ S ∧ diam (H a) < infDist u (H a) := fun a ha => Finset.mem_filter.1 ha
    have hpos : ∀ a ∈ S.filter (fun a => diam (H a) < infDist u (H a)),
        0 < infDist u (H a) := fun a ha =>
      (hm.trans_le (hlo a (hT a ha).1)).trans (hT a ha).2
    have hsum := sum_sq_div_sq_infDist_le (s := S.filter (fun a => diam (H a) < infDist u (H a)))
      (H := H) (c := c) (ρ := fun a => κ * diam (H a)) (u := u) hm hmR
      (hd.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))
      (fun a ha => hHm a (hT a ha).1) (fun a ha => hb a (hT a ha).1)
      (fun a _ => mul_nonneg hκ.le diam_nonneg) (fun a ha => hball a (hT a ha).1) hpos
      (fun a ha => (hT a ha).2.le) (fun a ha => hsub a (hT a ha).1) (fun a ha => by
        refine Disjoint.aedisjoint (Set.disjoint_left.2 fun z hz hzb => ?_)
        have h1 : infDist u (H a) ≤ dist u z := infDist_le_dist_of_mem hz
        have h2 : m < infDist u (H a) := (hlo a (hT a ha).1).trans_lt (hT a ha).2
        rw [mem_ball, dist_comm] at hzb
        linarith)
    have heq : ∑ a ∈ S with diam (H a) < infDist u (H a), β a ^ 2 =
        (∑ a ∈ S with diam (H a) < infDist u (H a),
          (κ * diam (H a)) ^ 2 / infDist u (H a) ^ 2) / κ ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hI := (hpos a ha).ne'
      have hκ0 := hκ.ne'
      simp only [hβ, (hT a ha).2, ↓reduceIte]
      field_simp
    rw [heq]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 hsum
  -- near cells: inball packing
  have hnear : ∑ a ∈ S with ¬diam (H a) < infDist u (H a), β a ^ 2 ≤
      (Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) := by
    have hN : ∀ a ∈ S.filter (fun a => ¬diam (H a) < infDist u (H a)),
        a ∈ S ∧ ¬diam (H a) < infDist u (H a) := fun a ha => Finset.mem_filter.1 ha
    have h1 : ∑ a ∈ S with ¬diam (H a) < infDist u (H a), β a ^ 2 =
        ((S.filter fun a => ¬diam (H a) < infDist u (H a)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      simp only [hβ, (hN a ha).2, ↓reduceIte]
      norm_num
    rw [h1]
    exact card_le_logb_of_infDist_le_diam hκ hm hmM
      (pairwiseDisjoint_ball_of_aedisjoint
        (hd.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))
        fun a ha => hball a (hN a ha).1)
      (fun a ha => hball a (hN a ha).1) (fun a ha => hb a (hN a ha).1)
      (fun a ha => hlo a (hN a ha).1) (fun a ha => hhi a (hN a ha).1)
      (fun a ha => not_lt.1 (hN a ha).2)
  calc ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / w a b ≤ ∑ a ∈ S, Δ * β a ^ 2 := Finset.sum_le_sum hrow
    _ = Δ * (∑ a ∈ S with diam (H a) < infDist u (H a), β a ^ 2 +
          ∑ a ∈ S with ¬diam (H a) < infDist u (H a), β a ^ 2) := by
      rw [Finset.sum_filter_add_sum_filter_not, Finset.mul_sum]
    _ ≤ Δ * (8 * Real.log (R / m) / κ ^ 2 + (Real.logb 2 (M / m) + 1) * (16 / κ ^ 2)) := by
      gcongr
    _ = Δ * ((Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) + 8 * Real.log (R / m) / κ ^ 2) := by
      rw [add_comm (8 * Real.log (R / m) / κ ^ 2)]

/-- **Poisson equation through fat planar cells.** If `f` vanishes off `A ⊆ S`, solves
`∑ b w(a,b) (f a - f b) = D 𝟙[a = x]` on `A`, and `θ` is a unit flow from `x` out of `A` through
cells as in `LatticeProb.sum_sum_sq_div_le_of_fatCells` (conductances `w ≥ 1` where nonzero),
then `f x ≤ D · (1/2) · Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)`. For `f` the
Green function of the network killed outside `A` and `D` the weighted degree of `x`, this is a
bound on the diagonal Green function by the geometry of the cells. -/
theorem le_of_poisson_of_fatCells {V : Type*} [DecidableEq V] {S A : Finset V} (hAS : A ⊆ S)
    {w : V → V → ℝ} (hws : ∀ a b, w a b = w b a) (hw0 : ∀ a b, 0 ≤ w a b)
    (hw1 : ∀ a b, w a b ≠ 0 → 1 ≤ w a b)
    {f : V → ℝ} (hf : ∀ a, a ∉ A → f a = 0) {x : V} (hx : x ∈ A) {D : ℝ} (hD : 0 ≤ D)
    (hlap : ∀ a ∈ A, ∑ b ∈ S, w a b * (f a - f b) = if a = x then D else 0)
    {θ : V → V → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθw : ∀ a b, w a b = 0 → θ a b = 0)
    (hdiv : ∀ a ∈ A, ∑ b ∈ S, θ a b = if a = x then 1 else 0)
    {H : V → Set ℂ} {c : V → ℂ} {u : ℂ} {κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hmM : m ≤ M) (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hd : (S : Set V).Pairwise (AEDisjoint volume on H))
    (hHm : ∀ a ∈ S, MeasurableSet (H a)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, m ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    (hdeg : ∀ a ∈ S, ∑ b ∈ S, w a b ≤ Δ)
    (hθ1 : ∀ a ∈ S, ∀ b ∈ S, |θ a b| ≤ 1)
    (hθf : ∀ a ∈ S, diam (H a) < infDist u (H a) → ∀ b ∈ S,
      |θ a b| ≤ diam (H a) / infDist u (H a)) :
    f x ≤ D * ((1 / 2) * (Δ * ((Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) +
      8 * Real.log (R / m) / κ ^ 2))) := by
  refine (le_mul_flowEnergy_of_poisson hAS hws hw0 hf hx hD hlap hθ hθw hdiv).trans ?_
  have hE := sum_sum_sq_div_le_of_fatCells hκ hm hmM hmR hΔ hd hHm hb hball hlo hhi hsub hw0
    (fun a b h => hw1 a b fun h0 => h (hθw a b h0)) hdeg hθ1 hθf
  gcongr

end LatticeProb
