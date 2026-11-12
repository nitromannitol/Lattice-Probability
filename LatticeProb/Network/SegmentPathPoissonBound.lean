import LatticeProb.Network.SegmentPathFlow
import LatticeProb.Analysis.FatCellFlowEnergy
import LatticeProb.Analysis.FatInballFlowEnergy

/-!
# Green function bounds by paths through the cells met by a random segment

Combining the expected crossing flow of `segmentPathFlow` with the energy bound for flows
through fat planar cells (`sum_sum_sq_div_le_of_fatCells`) and Thomson's principle in Poisson
form (`le_of_poisson_of_fatCells`):

* `sum_sum_sq_div_segmentPathFlow_le`: the energy of the expected flow of self-avoiding paths
  along edges of conductance at least one, through the cells met by a uniformly random segment
  from `u`, is at most `Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)`;
* `le_of_poisson_of_segmentPaths`: hence the solution `f` of `∑_b w(a,b)(f a - f b) = D·1{a = x}`
  on `A`, vanishing off `A`, satisfies `f x ≤ D · ½ · Δ · (…)`, provided in every direction the
  chosen path runs from `x` out of `A`;
* `sum_sum_sq_div_segmentPathFlow_le_of_inballs`, `le_of_poisson_of_segmentPaths_of_inballs`:
  the same bounds when the cells are only assumed to have pairwise disjoint inballs
  `ball (c a) (κ · diam (H a))` (no Lebesgue almost-disjointness or measurability of the cells).

For `f` the Green function of the network killed outside `A`, this is the method of random paths
for the upper bound of the diagonal Green function (Berestycki-Gwynne, upper bound for effective
resistances). The existence of the paths is a hypothesis.
-/

namespace LatticeProb

open Complex Function Metric MeasureTheory Set

variable {ι : Type*} [DecidableEq ι]

/-- **Energy of the segment-path flow through fat cells.** -/
theorem sum_sum_sq_div_segmentPathFlow_le {S Y : Finset ι} {H : ι → Set ℂ} {c : ι → ℂ} {u : ℂ}
    {ρ κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m) (hmM : m ≤ M) (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hd : (S : Set ι).Pairwise (AEDisjoint volume on H))
    (hHc : ∀ y ∈ Y, IsClosed (H y))
    (hHm : ∀ a ∈ S, MeasurableSet (H a)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, m ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    {w : ι → ι → ℝ} (hws : ∀ a b, w a b = w b a) (hw0 : ∀ a b, 0 ≤ w a b)
    (hw1 : ∀ a b, w a b ≠ 0 → 1 ≤ w a b) (hdeg : ∀ a ∈ S, ∑ b ∈ S, w a b ≤ Δ)
    {F : Finset ι → List ι} (hF : ∀ T : Finset ι, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ θ, (segmentPath u ρ H Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => w a b ≠ 0) :
    ∑ a ∈ S, ∑ b ∈ S, segmentPathFlow u ρ H Y F a b ^ 2 / w a b ≤
      Δ * ((Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) + 8 * Real.log (R / m) / κ ^ 2) := by
  have hR' : ∀ a b, w a b ≠ 0 → w b a ≠ 0 := fun a b h => by rwa [hws]
  refine sum_sum_sq_div_le_of_fatCells hκ hm hmM hmR hΔ hd hHm hb hball hlo hhi hsub hw0
    (fun a b h => hw1 a b fun h0 =>
      h (segmentPathFlow_eq_zero_of_not_rel hR' hchain (not_not.2 h0)))
    hdeg (fun a _ b _ => abs_segmentPathFlow_le_one hHc hnd a b) ?_
  intro a ha hfar b _
  exact abs_segmentPathFlow_le_diam_div_infDist hHc hnd
    (fun θ a h => mem_segmentDirections_of_mem_segmentPath hF h) (hb a ha)
    (diam_nonneg.trans_lt hfar) b

/-- **Bound on a Poisson solution at its source by random segment paths.** If in every
direction the path chosen through the cells met by the segment from `u` is self-avoiding, uses
edges of positive conductance, starts at `x`, stays in `S` and ends outside `A`, then the
solution of the Poisson equation with source `D · 1{x}` on `A` is at most
`D · ½ · Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)` at `x`. -/
theorem le_of_poisson_of_segmentPaths {S A Y : Finset ι} (hAS : A ⊆ S)
    {w : ι → ι → ℝ} (hws : ∀ a b, w a b = w b a) (hw0 : ∀ a b, 0 ≤ w a b)
    (hw1 : ∀ a b, w a b ≠ 0 → 1 ≤ w a b)
    {f : ι → ℝ} (hf : ∀ a, a ∉ A → f a = 0) {x : ι} (hx : x ∈ A) {D : ℝ} (hD : 0 ≤ D)
    (hlap : ∀ a ∈ A, ∑ b ∈ S, w a b * (f a - f b) = if a = x then D else 0)
    {H : ι → Set ℂ} {c : ι → ℂ} {u : ℂ} {ρ κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hmM : m ≤ M) (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hd : (S : Set ι).Pairwise (AEDisjoint volume on H))
    (hHc : ∀ y ∈ Y, IsClosed (H y))
    (hHm : ∀ a ∈ S, MeasurableSet (H a)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, m ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    (hdeg : ∀ a ∈ S, ∑ b ∈ S, w a b ≤ Δ)
    {F : Finset ι → List ι} (hF : ∀ T : Finset ι, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ θ, (segmentPath u ρ H Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => w a b ≠ 0)
    (hpath : ∀ θ, ∃ p, segmentPath u ρ H Y F θ = x :: p ∧ (∀ v ∈ x :: p, v ∈ S) ∧
      (x :: p).getLast (List.cons_ne_nil x p) ∉ A) :
    f x ≤ D * ((1 / 2) * (Δ * ((Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) +
      8 * Real.log (R / m) / κ ^ 2))) := by
  have hR' : ∀ a b, w a b ≠ 0 → w b a ≠ 0 := fun a b h => by rwa [hws]
  refine (le_mul_flowEnergy_of_poisson hAS hws hw0 hf hx hD hlap
    (segmentPathFlow_antisymm (z := u) (ρ := ρ) (H := H) (Y := Y) (F := F))
    (fun a b h0 => segmentPathFlow_eq_zero_of_not_rel hR' hchain (not_not.2 h0))
    (sum_segmentPathFlow_eq_ite_of_path hHc hpath)).trans ?_
  have hE := sum_sum_sq_div_segmentPathFlow_le (c := c) hκ hm hmM hmR hΔ hd hHc hHm hb hball
    hlo hhi hsub hws hw0 hw1 hdeg hF hnd hchain
  gcongr

/-- **Energy of the segment-path flow through cells with disjoint inballs.** The bound of
`sum_sum_sq_div_segmentPathFlow_le` with the almost-disjointness and measurability of the cells
replaced by pairwise disjointness of the inballs `ball (c a) (κ · diam (H a))`. -/
theorem sum_sum_sq_div_segmentPathFlow_le_of_inballs {S Y : Finset ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {u : ℂ} {ρ κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m) (hmM : m ≤ M)
    (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hdisj : (S : Set ι).PairwiseDisjoint fun a => ball (c a) (κ * diam (H a)))
    (hHc : ∀ y ∈ Y, IsClosed (H y)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, m ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    {w : ι → ι → ℝ} (hws : ∀ a b, w a b = w b a) (hw0 : ∀ a b, 0 ≤ w a b)
    (hw1 : ∀ a b, w a b ≠ 0 → 1 ≤ w a b) (hdeg : ∀ a ∈ S, ∑ b ∈ S, w a b ≤ Δ)
    {F : Finset ι → List ι} (hF : ∀ T : Finset ι, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ θ, (segmentPath u ρ H Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => w a b ≠ 0) :
    ∑ a ∈ S, ∑ b ∈ S, segmentPathFlow u ρ H Y F a b ^ 2 / w a b ≤
      Δ * ((Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) + 8 * Real.log (R / m) / κ ^ 2) := by
  have hR' : ∀ a b, w a b ≠ 0 → w b a ≠ 0 := fun a b h => by rwa [hws]
  refine sum_sum_sq_div_le_of_fatInballs hκ hm hmM hmR hΔ hdisj hb hball hlo hhi hsub hw0
    (fun a b h => hw1 a b fun h0 =>
      h (segmentPathFlow_eq_zero_of_not_rel hR' hchain (not_not.2 h0)))
    hdeg (fun a _ b _ => abs_segmentPathFlow_le_one hHc hnd a b) ?_
  intro a ha hfar b _
  exact abs_segmentPathFlow_le_diam_div_infDist hHc hnd
    (fun θ a h => mem_segmentDirections_of_mem_segmentPath hF h) (hb a ha)
    (diam_nonneg.trans_lt hfar) b

/-- **Bound on a Poisson solution at its source by random segment paths, disjoint inballs.**
The bound of `le_of_poisson_of_segmentPaths` with the almost-disjointness and measurability of
the cells replaced by pairwise disjointness of the inballs `ball (c a) (κ · diam (H a))`. -/
theorem le_of_poisson_of_segmentPaths_of_inballs {S A Y : Finset ι} (hAS : A ⊆ S)
    {w : ι → ι → ℝ} (hws : ∀ a b, w a b = w b a) (hw0 : ∀ a b, 0 ≤ w a b)
    (hw1 : ∀ a b, w a b ≠ 0 → 1 ≤ w a b)
    {f : ι → ℝ} (hf : ∀ a, a ∉ A → f a = 0) {x : ι} (hx : x ∈ A) {D : ℝ} (hD : 0 ≤ D)
    (hlap : ∀ a ∈ A, ∑ b ∈ S, w a b * (f a - f b) = if a = x then D else 0)
    {H : ι → Set ℂ} {c : ι → ℂ} {u : ℂ} {ρ κ m M R Δ : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hmM : m ≤ M) (hmR : m ≤ R) (hΔ : 0 ≤ Δ)
    (hdisj : (S : Set ι).PairwiseDisjoint fun a => ball (c a) (κ * diam (H a)))
    (hHc : ∀ y ∈ Y, IsClosed (H y)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, m ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    (hdeg : ∀ a ∈ S, ∑ b ∈ S, w a b ≤ Δ)
    {F : Finset ι → List ι} (hF : ∀ T : Finset ι, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ θ, (segmentPath u ρ H Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath u ρ H Y F θ).IsChain fun a b => w a b ≠ 0)
    (hpath : ∀ θ, ∃ p, segmentPath u ρ H Y F θ = x :: p ∧ (∀ v ∈ x :: p, v ∈ S) ∧
      (x :: p).getLast (List.cons_ne_nil x p) ∉ A) :
    f x ≤ D * ((1 / 2) * (Δ * ((Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) +
      8 * Real.log (R / m) / κ ^ 2))) := by
  have hR' : ∀ a b, w a b ≠ 0 → w b a ≠ 0 := fun a b h => by rwa [hws]
  refine (le_mul_flowEnergy_of_poisson hAS hws hw0 hf hx hD hlap
    (segmentPathFlow_antisymm (z := u) (ρ := ρ) (H := H) (Y := Y) (F := F))
    (fun a b h0 => segmentPathFlow_eq_zero_of_not_rel hR' hchain (not_not.2 h0))
    (sum_segmentPathFlow_eq_ite_of_path hHc hpath)).trans ?_
  have hE := sum_sum_sq_div_segmentPathFlow_le_of_inballs (c := c) hκ hm hmM hmR hΔ hdisj hHc
    hb hball hlo hhi hsub hws hw0 hw1 hdeg hF hnd hchain
  gcongr

end LatticeProb
