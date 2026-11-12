import LatticeProb.Analysis.FatCellFlowEnergy

/-!
# Energy of a flow through planar cells with pairwise disjoint inballs

The bounds `LatticeProb.sum_sum_sq_div_le_of_fatCells` and `LatticeProb.le_of_poisson_of_fatCells`
with their hypotheses that the cells be measurable and pairwise almost disjoint for Lebesgue
measure replaced by the weaker one that the inballs `ball (c a) (κ · diam (H a))` be pairwise
disjoint. This is the form available for the cells `η([ε (k - 1), ε k])` of a space-filling curve
`η` parametrized by the area of a measure which charges every nonempty open set but may be
singular with respect to Lebesgue measure: two distinct such cells share no nonempty open set,
while Lebesgue-null intersections are not a consequence of the parametrization.

The far cells are compared with `∫ |w - u|⁻²` over their inballs instead of over the cells.

## Main results

* `LatticeProb.ofReal_sq_div_sq_infDist_le_lintegral_ball`: one far cell, integral over its inball.
* `LatticeProb.sum_sq_div_sq_infDist_le_of_inballs`: inverse-square sum over far cells.
* `LatticeProb.sum_sum_sq_div_le_of_fatInballs`: the energy bound.
* `LatticeProb.le_of_poisson_of_fatInballs`: the bound on a Poisson solution at its source.
-/

open MeasureTheory Metric Set Real Function
open scoped ENNReal

namespace LatticeProb

/-- If a bounded set `H` contains the disc `ball c r` and `0 < dist(u, H)` with
`diam H ≤ dist(u, H)`, then `r² / dist(u, H)² ≤ (4 / π) ∫_{ball c r} |w - u|⁻² dw`. -/
theorem ofReal_sq_div_sq_infDist_le_lintegral_ball {H : Set ℂ} {c u : ℂ} {r : ℝ}
    (hb : Bornology.IsBounded H) (hr : 0 ≤ r) (hball : ball c r ⊆ H)
    (hpos : 0 < infDist u H) (hdiam : diam H ≤ infDist u H) :
    ENNReal.ofReal (r ^ 2 / infDist u H ^ 2)
      ≤ ENNReal.ofReal (4 / π) * ∫⁻ w in ball c r, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
  have hlow : ∀ w ∈ ball c r,
      ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) ≤ ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
    intro w hw'
    have hw := hball hw'
    apply ENNReal.ofReal_le_ofReal
    have h1 := norm_sub_le_two_mul_infDist hb hw hdiam
    have hne : 0 < ‖w - u‖ := by
      have := infDist_le_dist_of_mem (x := u) hw
      rw [dist_comm, dist_eq_norm] at this
      linarith
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  have hmeas : Measurable fun w : ℂ => ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by fun_prop
  have hpi : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal π := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hd0 : infDist u H ≠ 0 := hpos.ne'
  calc ENNReal.ofReal (r ^ 2 / infDist u H ^ 2)
      = ENNReal.ofReal (4 / π) *
          (ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) * (ENNReal.ofReal r ^ 2 * NNReal.pi)) := by
        rw [hpi, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = ENNReal.ofReal (4 / π) *
          (ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) * volume (ball c r)) := by
        rw [Complex.volume_ball c r]
    _ = ENNReal.ofReal (4 / π) *
          ∫⁻ _w in ball c r, ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (4 / π) * ∫⁻ w in ball c r, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) :=
        mul_le_mul' le_rfl (setLIntegral_mono hmeas hlow)

/-- **Inverse-square sum over far cells with disjoint inballs.** Let `H_i` (`i ∈ s`) be bounded
sets in `closedBall u R`, disjoint from `ball u r₀`, containing pairwise disjoint discs
`B_{ρ_i}(c_i)`, each far from `u` compared with its size (`0 < dist(u, H_i)`,
`diam H_i ≤ dist(u, H_i)`). Then `∑ ρ_i² / dist(u, H_i)² ≤ 8 log(R / r₀)`. -/
theorem sum_sq_div_sq_infDist_le_of_inballs {ι : Type*} {s : Finset ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {ρ : ι → ℝ} {u : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (c i) (ρ i))
    (hb : ∀ i ∈ s, Bornology.IsBounded (H i))
    (hρ : ∀ i ∈ s, 0 ≤ ρ i) (hball : ∀ i ∈ s, ball (c i) (ρ i) ⊆ H i)
    (hpos : ∀ i ∈ s, 0 < infDist u (H i)) (hdiam : ∀ i ∈ s, diam (H i) ≤ infDist u (H i))
    (hsub : ∀ i ∈ s, H i ⊆ closedBall u R)
    (hout : ∀ i ∈ s, Disjoint (H i) (ball u r)) :
    ∑ i ∈ s, ρ i ^ 2 / infDist u (H i) ^ 2 ≤ 8 * Real.log (R / r) := by
  have hlog : 0 ≤ Real.log (R / r) := Real.log_nonneg ((one_le_div hr).2 hrR)
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  calc ∑ i ∈ s, ENNReal.ofReal (ρ i ^ 2 / infDist u (H i) ^ 2)
      ≤ ∑ i ∈ s, ENNReal.ofReal (4 / π) *
          ∫⁻ w in ball (c i) (ρ i), ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
        gcongr with i hi
        exact ofReal_sq_div_sq_infDist_le_lintegral_ball (hb i hi) (hρ i hi) (hball i hi)
          (hpos i hi) (hdiam i hi)
    _ = ENNReal.ofReal (4 / π) *
          ∫⁻ w in ⋃ i ∈ s, ball (c i) (ρ i), ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun i _ => measurableSet_ball)]
    _ ≤ ENNReal.ofReal (4 / π) * ENNReal.ofReal (2 * π * Real.log (R / r)) := by
        gcongr
        refine lintegral_inv_sq_norm_sub_le_of_subset_annulus u hr hrR ?_
        intro w hw
        simp only [mem_iUnion] at hw
        obtain ⟨i, hi, hwi⟩ := hw
        exact ⟨hsub i hi (hball i hi hwi), Set.disjoint_left.1 (hout i hi) (hball i hi hwi)⟩
    _ = ENNReal.ofReal (8 * Real.log (R / r)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- **Energy of a flow through planar cells with disjoint inballs.** For bounded cells
`H a ⊆ closedBall u R` with pairwise disjoint inballs `ball (c a) (κ · diam (H a)) ⊆ H a`, diameters in
`[m, M]`, conductances `w ≥ 0` with weighted degrees at most `Δ` and `w ≥ 1` on the support of
`θ`, a flow `θ` with `|θ| ≤ 1` and `|θ a b| ≤ diam (H a) / dist (u, H a)` for the cells far from
`u` has energy at most `Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)`. -/
theorem sum_sum_sq_div_le_of_fatInballs {ι : Type*} {S : Finset ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {u : ℂ} {κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m) (hmM : m ≤ M)
    (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hdisj : (S : Set ι).PairwiseDisjoint fun a => ball (c a) (κ * diam (H a)))
    (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
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
    have hsum := sum_sq_div_sq_infDist_le_of_inballs (s := S.filter (fun a => diam (H a) < infDist u (H a)))
      (H := H) (c := c) (ρ := fun a => κ * diam (H a)) (u := u) hm hmR
      (hdisj.subset (Finset.coe_subset.2 (Finset.filter_subset _ _)))
      (fun a ha => hb a (hT a ha).1)
      (fun a _ => mul_nonneg hκ.le diam_nonneg) (fun a ha => hball a (hT a ha).1) hpos
      (fun a ha => (hT a ha).2.le) (fun a ha => hsub a (hT a ha).1) (fun a ha => by
        refine Set.disjoint_left.2 fun z hz hzb => ?_
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
      (hdisj.subset (Finset.coe_subset.2 (Finset.filter_subset _ _)))
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

/-- **Poisson equation through planar cells with disjoint inballs.** If `f` vanishes off `A ⊆ S`, solves
`∑ b w(a,b) (f a - f b) = D 𝟙[a = x]` on `A`, and `θ` is a unit flow from `x` out of `A` through
cells as in `LatticeProb.sum_sum_sq_div_le_of_fatInballs` (conductances `w ≥ 1` where nonzero),
then `f x ≤ D · (1/2) · Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)`. For `f` the
Green function of the network killed outside `A` and `D` the weighted degree of `x`, this is a
bound on the diagonal Green function by the geometry of the cells. -/
theorem le_of_poisson_of_fatInballs {V : Type*} [DecidableEq V] {S A : Finset V} (hAS : A ⊆ S)
    {w : V → V → ℝ} (hws : ∀ a b, w a b = w b a) (hw0 : ∀ a b, 0 ≤ w a b)
    (hw1 : ∀ a b, w a b ≠ 0 → 1 ≤ w a b)
    {f : V → ℝ} (hf : ∀ a, a ∉ A → f a = 0) {x : V} (hx : x ∈ A) {D : ℝ} (hD : 0 ≤ D)
    (hlap : ∀ a ∈ A, ∑ b ∈ S, w a b * (f a - f b) = if a = x then D else 0)
    {θ : V → V → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθw : ∀ a b, w a b = 0 → θ a b = 0)
    (hdiv : ∀ a ∈ A, ∑ b ∈ S, θ a b = if a = x then 1 else 0)
    {H : V → Set ℂ} {c : V → ℂ} {u : ℂ} {κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hmM : m ≤ M) (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hdisj : (S : Set V).PairwiseDisjoint fun a => ball (c a) (κ * diam (H a)))
    (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
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
  have hE := sum_sum_sq_div_le_of_fatInballs hκ hm hmM hmR hΔ hdisj hb hball hlo hhi hsub hw0
    (fun a b h => hw1 a b fun h0 => h (hθw a b h0)) hdeg hθ1 hθf
  gcongr

end LatticeProb
