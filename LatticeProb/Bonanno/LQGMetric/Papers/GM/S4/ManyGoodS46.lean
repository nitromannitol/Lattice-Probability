/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodS46 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGood
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond2

/-!
# GM.S4.6: the geodesic `P` enters a ball `B_{λ₂r}(z)` with `(z,r) ∈ 𝒵_k` and `E_r(z)`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Proposition 4.12,
l. 2229–2234: "By condition 5 … each point of `∂B_{2λ₄ε𝕣}(𝓑^•_{t_k})` is contained in a
Euclidean ball `B_{λ₂r}(z)` for some `(z,r) ∈ 𝒵_k` for which `E_r(z)` occurs. … the union of
these Euclidean balls disconnects `∂𝓑^•_{t_k}` from `𝕨`. Therefore, `P` must enter
`B_{λ₂r}(z)` for some `(z,r) ∈ 𝒵_k` such that `E_r(z)` occurs." (GM_B: GM.S4.6.)

Own elementary write-up of GM's unstated step: `u ↦ dist(P(u), K)` is continuous, `0` at
`P(0) = 𝕫 ∈ K` and large at `P(L) = 𝕨`, so `P` hits the level set `{dist(·, K) = d₀}`; a grid
point `z ∈ (λ₁ε^{1+ν}𝕣/4)ℤ²` within `λ₁ε^{1+ν}𝕣/2` of that point (`gm_exists_gridPt_near`) has a
good radius `r` by condition 5, and `λ₁ε^{1+ν}𝕣/2 < λ₂ r`.

Reading (proposed DEVIATIONS entry): GM cover the level set at `d₀ = 2λ₄ε𝕣`, but the grid point
`z` near it can then have `dist(z, ∂𝓑^•_{t_k}) > 2λ₄ε𝕣`, outside the range (4.10) of `𝒵_k`; we
use any level `d₀` with `[d₀ − 2σ, d₀ + 2σ] ⊆ [λ₄ε𝕣, 2λ₄ε𝕣]` (`σ = λ₁ε^{1+ν}𝕣/4`; e.g.
`d₀ = (3/2)λ₄ε𝕣` for small `ε`).

* `gm_infDist_frontier_eq` — for `K` closed and `z ∉ K`, `dist(z, ∂K) = dist(z, K)`.
* `gm_S4_6_det` — the deterministic statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- for `K` closed and `z ∉ K`, `dist(z, ∂K) = dist(z, K)` -/
theorem gm_infDist_frontier_eq {K : Set ℂ} (hK : IsClosed K) (hne : K.Nonempty) {z : ℂ}
    (hz : z ∉ K) : infDist z (frontier K) = infDist z K := by
  -- every `q ∈ K` has a point of `∂K` on `[z, q]`
  have hseg : ∀ q ∈ K, ∃ p ∈ frontier K, dist z p ≤ dist z q := by
    intro q hq
    obtain ⟨p, hpseg, hpfr⟩ := jb_inter_frontier_nonempty hK (convex_segment z q).isPreconnected
      (left_mem_segment ℝ z q) hz (right_mem_segment ℝ z q) hq
    have hsub : segment ℝ z q ⊆ closedBall z (dist z q) :=
      (convex_closedBall z _).segment_subset (mem_closedBall_self dist_nonneg)
        (by rw [mem_closedBall, dist_comm])
    have := hsub hpseg
    rw [mem_closedBall, dist_comm] at this
    exact ⟨p, hpfr, this⟩
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨p₀, hp₀, -⟩ := hseg q₀ hq₀
  have hfne : (frontier K).Nonempty := ⟨p₀, hp₀⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset hK.frontier_subset hfne)
  refine (le_infDist ⟨q₀, hq₀⟩).2 fun q hq => ?_
  obtain ⟨p, hp, hpq⟩ := hseg q hq
  exact (infDist_le_dist_of_mem hp).trans hpq

/-- **GM.S4.6** (l. 2229–2234), deterministic form: `K = 𝓑^•_{t_k}`, `P` a curve from a point of
`K` to a point at distance `> d₀` from `K`, `σ = λ₁ε^{1+ν}𝕣/4` the grid mesh, `Good z r` the
event `E_r(z)` with the covering property of condition 5 near `K`. -/
theorem gm_S4_6_det {K : Set ℂ} (hK : IsClosed K) {P : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hPc : ContinuousOn P (Icc 0 L)) (hP0 : P 0 ∈ K) {d₀ σ lam1 lam2 lam4 ε ν 𝕣 : ℝ}
    (hσ : 0 < σ) (hσdef : σ = lam1 * ε ^ (1 + ν) * 𝕣 / 4)
    (hlow : lam4 * ε * 𝕣 ≤ d₀ - 2 * σ) (hup : d₀ + 2 * σ ≤ 2 * lam4 * ε * 𝕣)
    (hPL : d₀ < infDist (P L) K) {Rads : Set ℝ} (Good : ℂ → ℝ → Prop)
    (hcov : ∀ z ∈ gridPts σ, infDist z K ≤ 2 * lam4 * ε * 𝕣 → ∃ r ∈ Rads, Good z r)
    (hRad : ∀ r ∈ Rads, 2 * σ < lam2 * r) :
    ∃ z r, (z, r) ∈ candSet K lam1 lam4 ε ν 𝕣 Rads ∧ Good z r ∧
      ∃ u ∈ Icc 0 L, P u ∈ ball z (lam2 * r) := by
  have hKne : K.Nonempty := ⟨_, hP0⟩
  -- `P` hits the level set `{dist(·, K) = d₀}`
  have hd0 : 0 ≤ d₀ := by nlinarith [hσ]
  have hfc : ContinuousOn (fun u => infDist (P u) K) (Icc 0 L) :=
    (continuous_infDist_pt K).comp_continuousOn hPc
  have hiv := intermediate_value_Icc hL hfc
  have hmem : d₀ ∈ Icc (infDist (P 0) K) (infDist (P L) K) :=
    ⟨by rw [infDist_zero_of_mem hP0]; exact hd0, hPL.le⟩
  obtain ⟨u, hu, hud⟩ := hiv hmem
  simp only at hud
  -- a grid point near `P u`
  obtain ⟨z, hz, hzu⟩ := gm_exists_gridPt_near hσ (P u)
  have hdz : |infDist z K - infDist (P u) K| ≤ ‖P u - z‖ := by
    have := infDist_le_infDist_add_dist (x := z) (y := P u) (s := K)
    have := infDist_le_infDist_add_dist (x := P u) (y := z) (s := K)
    rw [abs_le]
    rw [dist_eq_norm] at *
    constructor <;> linarith [norm_sub_rev (P u) z]
  rw [hud] at hdz
  have hz1 : lam4 * ε * 𝕣 ≤ infDist z K := by
    have := (abs_le.1 hdz).1; linarith
  have hz2 : infDist z K ≤ 2 * lam4 * ε * 𝕣 := by
    have := (abs_le.1 hdz).2; linarith
  have hzK : z ∉ K := fun h => by
    rw [infDist_zero_of_mem h] at hz1
    have : 0 < lam4 * ε * 𝕣 := by nlinarith [hσ]
    linarith
  obtain ⟨r, hr, hgood⟩ := hcov z hz hz2
  refine ⟨z, r, ⟨by rw [hσdef] at hz; exact hz, hzK, hr, ?_⟩, hgood, u, hu, ?_⟩
  · rw [gm_infDist_frontier_eq hK hKne hzK]; exact ⟨hz1, hz2⟩
  · rw [mem_ball, dist_eq_norm]
    exact hzu.trans (hRad r hr)

end LQGMetric.GM
