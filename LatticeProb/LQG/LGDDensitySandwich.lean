import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiB1
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDScale

/-!
# Liouville graph distance of a measure compared with a reference measure on balls

The Liouville graph distance `D_δ(μ)(u, v)` (`LQGMetric.lgdDZZ`) is the least number of open
Euclidean balls with rational centres, each of `μ`-mass at most `δ²`, whose union contains a path
from `u` to `v`. This file compares `D_δ(μ)` with the walled distances of a reference measure `ν`
when `μ` and `ν` are comparable only on the balls inside two closed sets (walls), as happens for an
LQG measure that coincides with `e^{γ Y} ν` on an open set, with `Y` continuous there.

* `LatticeProb.LQG.exists_heavy_of_pos_thickening`: if `μ` charges every rational ball inside the
  `4r`-thickening of a compact set `C`, and `K` contains the `4r`-neighbourhood of `C`, then for
  small `δ` every rational ball of `μ`-mass at most `δ²` meeting `C` lies in `K`. The proof is that
  of `LQGMetric.DZZ.exists_heavy_of_pos` (Ding-Zeitouni-Zhang, arXiv:1807.00422, the heavy-ball
  step of the proof of Proposition 5.1), whose positivity hypothesis on the unit square is replaced
  by positivity on the balls inside the thickening, the only balls the argument uses.
* `LatticeProb.LQG.lgd_sandwich_of_ball_le`: if `ν ≤ e^b μ` on the balls inside the closed set `K`,
  `μ ≤ e^a ν` on the balls inside the closed set `K'`, and the balls of `μ`-mass at most `δ²`
  meeting `closure U` lie in `K`, then for `u ∈ U`, `v ∉ U`,
  `min_{x ∈ ∂U} D^K_{δ e^{b/2}}(ν)(u, x) ≤ D_δ(μ)(u, v) ≤ D^{K'}_{δ e^{−a/2}}(ν)(u, v)`.
* `LatticeProb.LQG.le_mul_of_restrict_eq_withDensity`: if `μ = e^{γ Y} ρ` on `V` and `|Y| ≤ A` on
  `K ⊆ V`, then `e^{−γA} ρ(s) ≤ μ(s) ≤ e^{γA} ρ(s)` for measurable `s ⊆ K`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric

open DZZ

/-- **Heavy balls** (the heavy-ball step of Ding-Zeitouni-Zhang, proof of Proposition 5.1; the
argument of `LQGMetric.DZZ.exists_heavy_of_pos`): if `C` is compact, every point of `C` is at
distance at least `4r` from `Kᶜ`, and `μ` charges every rational ball inside the `4r`-thickening of
`C`, then there is `δ₀ > 0` such that for `δ < δ₀` every rational ball of `μ`-mass at most `δ²`
meeting `C` lies in `K`. -/
theorem _root_.LatticeProb.LQG.exists_heavy_of_pos_thickening {μ : Measure ℂ} {C K : Set ℂ}
    (hC : IsCompact C) {r : ℝ} (hr : 0 < r) (hCK : ∀ p ∈ C, ∀ z ∉ K, 4 * r ≤ dist p z)
    (hpos : ∀ (g : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt g) q ⊆ thickening (4 * r) C →
      0 < μ (ball (ratPt g) q)) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ (c : ℚ × ℚ) (ρ : ℝ),
      (ball (ratPt c) ρ ∩ C).Nonempty → μ (ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) →
        ball (ratPt c) ρ ⊆ K := by
  classical
  obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn hr
  have hq0' : (0 : ℝ) < q := hq0
  have hq0'' : (0 : ℚ) < q := by exact_mod_cast hq0
  obtain ⟨G, hG⟩ := exists_finite_ratNet (hC.cthickening (r := 2 * r)) hr
  -- the fixed balls `B(g, q)`, `g ∈ G` near `C`
  set G' : Finset (ℚ × ℚ) := G.filter fun g => ball (ratPt g) q ⊆ thickening (4 * r) C
  set m : ℝ≥0∞ := min (G'.inf fun g => μ (ball (ratPt g) q)) 1 with hm
  have hm0 : 0 < m := by
    refine lt_min ((Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun g hg => ?_) one_pos
    exact hpos g q hq0'' (Finset.mem_filter.1 hg).2
  have hm1 : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hm1
  refine ⟨Real.sqrt m.toReal, Real.sqrt_pos.2 hmr, fun δ hδ hδ₀ c ρ hne hμ => ?_⟩
  by_contra hsub
  obtain ⟨z, hzB, hzK⟩ := not_subset.1 hsub
  obtain ⟨p, hpB, hpC⟩ := hne
  -- the ball is large
  have hρ : 2 * r < ρ := by
    have h1 := hCK p hpC z hzK
    have h2 : dist p z < 2 * ρ := by
      have := dist_triangle p (ratPt c) z
      rw [mem_ball] at hpB hzB
      rw [dist_comm (ratPt c) z] at this
      linarith
    linarith
  obtain ⟨y, hyp, hyB⟩ := exists_ball_sub_ball_near hr hρ hpB
  have hyC : y ∈ cthickening (2 * r) C :=
    mem_cthickening_of_dist_le y p _ _ hpC hyp
  obtain ⟨g, hgG, hgy⟩ := hG y hyC
  have hsub1 : ball (ratPt g) q ⊆ ball (ratPt c) ρ := by
    refine (ball_subset_ball' ?_).trans hyB
    rw [dist_comm]; linarith
  have hsub2 : ball (ratPt g) q ⊆ thickening (4 * r) C := by
    intro x hx
    rw [mem_ball] at hx
    refine mem_thickening_iff.2 ⟨p, hpC, ?_⟩
    have := dist_triangle4 x (ratPt g) y p
    rw [dist_comm (ratPt g) y] at this
    linarith
  have hgG' : g ∈ G' := by rw [Finset.mem_filter]; exact ⟨hgG, hsub2⟩
  have h1 : m ≤ μ (ball (ratPt g) q) := (min_le_left _ _).trans (Finset.inf_le hgG')
  have h2 : ENNReal.ofReal (δ ^ 2) < m := by
    rw [← ENNReal.ofReal_toReal hm1]
    refine (ENNReal.ofReal_lt_ofReal_iff hmr).2 ?_
    have := Real.sq_sqrt hmr.le
    nlinarith [Real.sqrt_nonneg m.toReal]
  exact absurd (h1.trans ((measure_mono hsub1).trans hμ)) (not_le.2 h2)

/-- **Liouville graph distance sandwich against a reference measure.** If `ν ≤ e^b μ` on the
rational balls inside the closed set `K`, `μ ≤ e^a ν` on the rational balls inside the closed set
`K'`, and every rational ball of `μ`-mass at most `δ²` meeting `closure U` lies in `K`, then for
`u ∈ U` and `v ∉ U`,
`min_{x ∈ ∂U} D^K_{δ e^{b/2}}(ν)(u, x) ≤ D_δ(μ)(u, v) ≤ D^{K'}_{δ e^{−a/2}}(ν)(u, v)`,
where `D^K(ν) = D(ν + ∞ · Leb|_{Kᶜ})` only uses balls inside `K`. -/
theorem _root_.LatticeProb.LQG.lgd_sandwich_of_ball_le {μ ν : Measure ℂ} {a b δ : ℝ}
    {U K K' : Set ℂ} (hU : IsOpen U) (hK : IsClosed K) (hK' : IsClosed K')
    (hlow : ∀ (x : ℚ × ℚ) (r : ℝ), ball (ratPt x) r ⊆ K →
      ν (ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp b) * μ (ball (ratPt x) r))
    (hup : ∀ (x : ℚ × ℚ) (r : ℝ), ball (ratPt x) r ⊆ K' →
      μ (ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp a) * ν (ball (ratPt x) r))
    {u v : ℂ} (hu : u ∈ U) (hv : v ∉ U)
    (hheavy : ∀ (c : ℚ × ℚ) (ρ : ℝ), (ball (ratPt c) ρ ∩ closure U).Nonempty →
      μ (ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) → ball (ratPt c) ρ ⊆ K) :
    lgdMinSet (dzzWall K ν) (δ * Real.exp (b / 2)) {u} (frontier U) ≤ lgdDZZ μ δ u v ∧
      lgdDZZ μ δ u v ≤ lgdDZZ (dzzWall K' ν) (δ * Real.exp (-a / 2)) u v := by
  refine ⟨lgd_sandwich_dzzWall_lower_K hU hK hlow hu hv hheavy, ?_⟩
  have hexp : ENNReal.ofReal (Real.exp a) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos a)).ne'
  exact (lgdDZZ_mono_measure (le_dzzWall K' μ) δ u v).trans
    (lgdDZZ_le_of_ball_le (dzzWall_ball_le hK' hexp hup) δ u v)

/-- **Mass comparison through a bounded density.** If `μ = e^{γ Y} ρ` on `V` (as restrictions),
`γ ≥ 0` and `|Y| ≤ A` on `K ⊆ V`, then every measurable `s ⊆ K` satisfies
`μ(s) ≤ e^{γA} ρ(s)` and `ρ(s) ≤ e^{γA} μ(s)`. -/
theorem _root_.LatticeProb.LQG.le_mul_of_restrict_eq_withDensity {μ ρ : Measure ℂ}
    {V K : Set ℂ} {Y : ℂ → ℝ} {γ A : ℝ} (hγ : 0 ≤ γ)
    (hμ : μ.restrict V =
      (ρ.restrict V).withDensity fun z => ENNReal.ofReal (Real.exp (γ * Y z)))
    (hKV : K ⊆ V) (hY : ∀ z ∈ K, |Y z| ≤ A) {s : Set ℂ} (hs : MeasurableSet s) (hsK : s ⊆ K) :
    μ s ≤ ENNReal.ofReal (Real.exp (γ * A)) * ρ s ∧
      ρ s ≤ ENNReal.ofReal (Real.exp (γ * A)) * μ s := by
  have hsV : s ⊆ V := hsK.trans hKV
  have hμs : μ s = ∫⁻ z in s, ENNReal.ofReal (Real.exp (γ * Y z)) ∂ρ := by
    rw [show μ s = μ.restrict V s by rw [Measure.restrict_apply hs, inter_eq_left.2 hsV], hμ,
      withDensity_apply _ hs,
      Measure.restrict_restrict hs, inter_eq_left.2 hsV]
  have hYs : ∀ z ∈ s, -A ≤ Y z ∧ Y z ≤ A := fun z hz => abs_le.1 (hY z (hsK hz))
  refine ⟨?_, ?_⟩
  · rw [hμs, ← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall fun z hz => ?_))
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (hYs z hz).2 hγ))
  · have hc : ENNReal.ofReal (Real.exp (γ * A)) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [hμs, ← lintegral_const_mul' _ _ hc, ← setLIntegral_one]
    refine lintegral_mono_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall fun z hz => ?_))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
    nlinarith [(hYs z hz).1]

end LQGMetric
