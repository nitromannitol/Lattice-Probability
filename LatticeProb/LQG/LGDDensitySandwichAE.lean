import LatticeProb.LQG.LGDDensitySandwich
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W2

/-!
# Almost sure Liouville graph distance sandwich for a measure with a continuous LQG density

Let `μ` be a measure that coincides, on an open set `V`, with `e^{γ Y} ρ` for a continuous function
`Y`, and let `ν` be a reference measure comparable with `ρ` on the balls inside two compact sets
`K, K' ⊆ V`. Since `Y` is bounded on `K ∪ K'`, the measures `μ` and `ν` are then comparable on the
balls inside `K` and inside `K'`, so the Liouville graph distance `D_δ(μ)` is squeezed between the
walled distances of `ν` at the scales `δ e^{b/2}` and `δ e^{−a/2}`, for constants `a, b` that depend
on the bound of `Y` (Ding-Zeitouni-Zhang, arXiv:1807.00422, proof of Proposition 5.1, where the
same comparison is made for the LQG measure of the zero-boundary field of the unit square).

* `LatticeProb.LQG.lgd_sandwich_of_restrict_eq_withDensity`: the deterministic statement.
* `LatticeProb.LQG.ae_lgd_sandwich_of_restrict_eq_withDensity`: its almost sure form for the
  white-noise field of the unit square, with `ρ` its `γ`-LQG measure and `ν` its Wick-normalized
  measure (`LQGMetric.DZZ.dzzMuIn`), the constants `a, b` now random.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric

open DZZ WhiteNoise QuantumZipper

/-- **Liouville graph distance sandwich through a continuous density.** If `μ = e^{γ Y} ρ` on the
open set `V` with `Y` continuous, `ν ≤ e^{b₀} ρ` on the rational balls inside the compact set
`K ⊆ V`, `ρ ≤ e^{a₀} ν` on those inside the compact set `K' ⊆ V`, `ρ` charges the rational balls
inside `K`, and `K` contains the `4r`-neighbourhood of `closure U` (`U` open with compact closure),
then there are `a, b` and `δ₀ > 0` such that for `δ < δ₀`, `u ∈ U` and `v ∉ U`,
`min_{x ∈ ∂U} D^K_{δ e^{b/2}}(ν)(u, x) ≤ D_δ(μ)(u, v) ≤ D^{K'}_{δ e^{−a/2}}(ν)(u, v)`. -/
theorem _root_.LatticeProb.LQG.lgd_sandwich_of_restrict_eq_withDensity {μ ρ ν : Measure ℂ}
    {V U K K' : Set ℂ} {Y : ℂ → ℝ} {γ a₀ b₀ : ℝ} (hγ : 0 ≤ γ)
    (hμ : μ.restrict V =
      (ρ.restrict V).withDensity fun z => ENNReal.ofReal (Real.exp (γ * Y z)))
    (hY : Continuous Y) (hU : IsOpen U) (hC : IsCompact (closure U)) (hK : IsCompact K)
    (hKV : K ⊆ V) (hK' : IsCompact K') (hK'V : K' ⊆ V) {r : ℝ} (hr : 0 < r)
    (hCK : ∀ p ∈ closure U, ∀ z ∉ K, 4 * r ≤ dist p z)
    (hlow : ∀ (x : ℚ × ℚ) (s : ℝ), ball (ratPt x) s ⊆ K →
      ν (ball (ratPt x) s) ≤ ENNReal.ofReal (Real.exp b₀) * ρ (ball (ratPt x) s))
    (hup : ∀ (x : ℚ × ℚ) (s : ℝ), ball (ratPt x) s ⊆ K' →
      ρ (ball (ratPt x) s) ≤ ENNReal.ofReal (Real.exp a₀) * ν (ball (ratPt x) s))
    (hpos : ∀ (g : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt g) q ⊆ K →
      0 < ρ (ball (ratPt g) q)) :
    ∃ a b δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ u ∈ U, ∀ v ∉ U,
      lgdMinSet (dzzWall K ν) (δ * Real.exp (b / 2)) {u} (frontier U) ≤ lgdDZZ μ δ u v ∧
        lgdDZZ μ δ u v ≤ lgdDZZ (dzzWall K' ν) (δ * Real.exp (-a / 2)) u v := by
  obtain ⟨A, hA⟩ := (hK.union hK').exists_bound_of_continuousOn hY.continuousOn
  have hYA : ∀ z ∈ K ∪ K', |Y z| ≤ A := fun z hz => by
    simpa [Real.norm_eq_abs] using hA z hz
  have hcmp : ∀ {s : Set ℂ}, MeasurableSet s → s ⊆ K ∪ K' →
      μ s ≤ ENNReal.ofReal (Real.exp (γ * A)) * ρ s ∧
        ρ s ≤ ENNReal.ofReal (Real.exp (γ * A)) * μ s := fun hs hsK =>
    LatticeProb.LQG.le_mul_of_restrict_eq_withDensity hγ hμ (union_subset hKV hK'V) hYA hs hsK
  have hexp : ∀ c d : ℝ, ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (Real.exp d) =
      ENNReal.ofReal (Real.exp (c + d)) := fun c d => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, ← Real.exp_add]
  have hthick : thickening (4 * r) (closure U) ⊆ K := by
    intro z hz
    obtain ⟨p, hp, hpz⟩ := mem_thickening_iff.1 hz
    by_contra hzK
    exact absurd (hCK p hp z hzK) (not_le.2 (by rw [dist_comm]; exact hpz))
  have hposμ : ∀ (g : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt g) q ⊆ thickening (4 * r) (closure U) →
      0 < μ (ball (ratPt g) q) := by
    intro g q hq hsub
    have hsK : ball (ratPt g) (q : ℝ) ⊆ K := hsub.trans hthick
    have h1 := (hcmp measurableSet_ball (hsK.trans subset_union_left)).2
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at h1
    exact (hpos g q hq hsK).ne' (le_antisymm h1 bot_le)
  obtain ⟨δ₀, hδ₀, hheavy⟩ :=
    LatticeProb.LQG.exists_heavy_of_pos_thickening hC hr hCK hposμ
  refine ⟨γ * A + a₀, b₀ + γ * A, δ₀, hδ₀, fun δ hδ hδδ₀ u hu v hv => ?_⟩
  refine LatticeProb.LQG.lgd_sandwich_of_ball_le hU hK.isClosed hK'.isClosed (fun x s hsub => ?_)
    (fun x s hsub => ?_) hu hv (hheavy δ hδ hδδ₀)
  · calc ν (ball (ratPt x) s) ≤ ENNReal.ofReal (Real.exp b₀) * ρ (ball (ratPt x) s) :=
          hlow x s hsub
      _ ≤ ENNReal.ofReal (Real.exp b₀) *
            (ENNReal.ofReal (Real.exp (γ * A)) * μ (ball (ratPt x) s)) :=
          by gcongr; exact (hcmp measurableSet_ball (hsub.trans subset_union_left)).2
      _ = ENNReal.ofReal (Real.exp (b₀ + γ * A)) * μ (ball (ratPt x) s) := by
          rw [← mul_assoc, hexp]
  · calc μ (ball (ratPt x) s) ≤ ENNReal.ofReal (Real.exp (γ * A)) * ρ (ball (ratPt x) s) :=
          (hcmp measurableSet_ball (hsub.trans subset_union_right)).1
      _ ≤ ENNReal.ofReal (Real.exp (γ * A)) *
            (ENNReal.ofReal (Real.exp a₀) * ν (ball (ratPt x) s)) :=
          by gcongr; exact hup x s hsub
      _ = ENNReal.ofReal (Real.exp (γ * A + a₀)) * ν (ball (ratPt x) s) := by
          rw [← mul_assoc, hexp]

/-- **Almost sure Liouville graph distance sandwich for the white-noise field of the unit square.**
Let `W` be a white noise, `0 < γ < 2`, and let `μ` be a random measure that almost surely coincides
on the open set `V ⊆ (0,1)²` with `e^{γ Y} M_γ`, where `M_γ` is the `γ`-LQG measure of the
white-noise field of the unit square and `Y(·, ω)` is continuous. For `U` open with compact closure
and compact `K, K' ⊆ V` with `K` containing the `4r`-neighbourhood of `closure U`, almost surely
there are `a, b` and `δ₀ > 0` such that for `δ < δ₀`, `u ∈ U` and `v ∉ U`,
`min_{x ∈ ∂U} D^K_{δ e^{b/2}}(ν)(u, x) ≤ D_δ(μ)(u, v) ≤ D^{K'}_{δ e^{−a/2}}(ν)(u, v)`,
`ν` the Wick-normalized measure `LQGMetric.DZZ.dzzMuIn`. -/
theorem _root_.LatticeProb.LQG.ae_lgd_sandwich_of_restrict_eq_withDensity {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {Y : ℂ → Ω → ℝ}
    (hY : ∀ ω, Continuous fun z => Y z ω) {V : Set ℂ} (hVsq : V ⊆ openSquare)
    (hμ : ∀ᵐ ω ∂P, (μ ω).restrict V =
      ((qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare).restrict V).withDensity
        fun z => ENNReal.ofReal (Real.exp (γ * Y z ω)))
    {U K K' : Set ℂ} (hU : IsOpen U) (hC : IsCompact (closure U)) (hK : IsCompact K)
    (hKV : K ⊆ V) (hK' : IsCompact K') (hK'V : K' ⊆ V) {r : ℝ} (hr : 0 < r)
    (hCK : ∀ p ∈ closure U, ∀ z ∉ K, 4 * r ≤ dist p z) :
    ∀ᵐ ω ∂P, ∃ a b δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ u ∈ U, ∀ v ∉ U,
      lgdMinSet (dzzWall K (dzzMuIn γ W ω)) (δ * Real.exp (b / 2)) {u} (frontier U) ≤
          lgdDZZ (μ ω) δ u v ∧
        lgdDZZ (μ ω) δ u v ≤ lgdDZZ (dzzWall K' (dzzMuIn γ W ω)) (δ * Real.exp (-a / 2)) u v := by
  obtain ⟨b₀, hb⟩ := wickArea_le_of_compact γ hK (hKV.trans hVsq)
  filter_upwards [hμ, ae_qArea_wn_ball_pos hW hγ hγ2] with ω hμω hpos
  rw [show dzzMuIn γ W ω = dzzWall dzzV (wickQArea γ W ω) from rfl,
    dzzWall_dzzWall_of_subset ((hKV.trans hVsq).trans openSquare_subset_dzzV),
    dzzWall_dzzWall_of_subset ((hK'V.trans hVsq).trans openSquare_subset_dzzV)]
  exact LatticeProb.LQG.lgd_sandwich_of_restrict_eq_withDensity (b₀ := b₀)
    (a₀ := γ ^ 2 / 2 * Real.log 3) hγ.le hμω (hY ω) hU hC hK hKV hK' hK'V hr hCK
    (fun x s hsub => hb _ _ measurableSet_ball hsub)
    (fun x s _ => le_wickQArea γ W ω measurableSet_ball)
    (fun g q hq hsub => hpos g q hq (hsub.trans (hKV.trans hVsq)))

end LQGMetric
