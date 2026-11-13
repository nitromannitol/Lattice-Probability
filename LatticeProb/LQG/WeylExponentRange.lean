import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

/-!
# A Weyl exponent with the LFPP exponent of `γ ∈ (0, 2)` is of the form `γ' / d_γ'`

For `γ ∈ (0, 2)` let `Q_γ = 2/γ + γ/2`, `d_γ` the dimension of `γ`-LQG and `ξ_γ = γ / d_γ`.
Let `ξ ↦ Q(ξ)` be the LFPP distance exponent (Ding-Gwynne, *Uniqueness of the critical and
supercritical Liouville quantum gravity metrics*, arXiv:2110.00177, Section 1). Suppose that

* `ξ ↦ Q(ξ)` is nonincreasing on `(0, ∞)`;
* `Q(ξ_γ') = Q_γ'` for every `γ' ∈ (0, 2)` (Ding-Gwynne, *The fractal dimension of Liouville quantum
  gravity: universality, monotonicity, and bounds*, arXiv:1807.01072, Theorem 1.5);
* `γ ↦ d_γ` is continuous on `(0, 2)` (ibid., Theorem 1.2).

If `ξ > 0` and `Q(ξ) = Q_γ` for some `γ ∈ (0, 2)`, then `ξ = ξ_γ'` for some `γ' ∈ (0, 2)`
(`exists_xiGamma_eq_of_lfppExponent_eq`). Indeed, either `ξ ≤ ξ_t` for some `t ∈ (0, 2)`, and then the
intermediate value theorem on `[ε, t]` applies since `ξ_ε ≤ ε < ξ` for small `ε` (`d_γ ≥ 1`); or
`ξ_t < ξ` for every `t ∈ (0, 2)`, and then `Q_γ = Q(ξ) ≤ Q(ξ_t) = Q_t` for every `t`, which fails at
`t = (γ + 2)/2` since `Q` is strictly decreasing on `(0, 2)` (`Q_lt_Q`).

The real-variable step is `exists_eq_of_antitoneOn_comp_eq_Q`, for an arbitrary continuous `f` in
place of `γ ↦ ξ_γ`.
-/

open Set

noncomputable section

namespace LatticeProb.LQG

/-- `Q = 2/γ + γ/2` is strictly decreasing on `(0, 2)`. -/
theorem Q_lt_Q {γ γ' : ℝ} (hγ : 0 < γ) (hγγ' : γ < γ') (hγ2' : γ' < 2) :
    LQGMetric.Q γ' < LQGMetric.Q γ := by
  have hγ' : 0 < γ' := hγ.trans hγγ'
  have e : LQGMetric.Q γ - LQGMetric.Q γ' = (γ' - γ) * (4 - γ * γ') / (2 * γ * γ') := by
    unfold LQGMetric.Q
    field_simp
    ring
  have hprod : 0 < 4 - γ * γ' := by nlinarith
  have hpos : 0 < (γ' - γ) * (4 - γ * γ') / (2 * γ * γ') :=
    div_pos (mul_pos (by linarith) hprod) (by positivity)
  linarith

/-- Let `f` be continuous and positive on `(0, 2)` with `f t ≤ t`, and let `q` be nonincreasing on
`(0, ∞)` with `q (f t) = Q_t` for `t ∈ (0, 2)`. If `q ξ = Q_γ` for some `ξ > 0` and `γ ∈ (0, 2)`, then
`ξ = f t` for some `t ∈ (0, 2)`. -/
theorem exists_eq_of_antitoneOn_comp_eq_Q {f q : ℝ → ℝ} (hcont : ContinuousOn f (Ioo 0 2))
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 2, 0 < f t) (hle : ∀ t ∈ Ioo (0 : ℝ) 2, f t ≤ t)
    (hanti : AntitoneOn q (Ioi 0)) (hq : ∀ t ∈ Ioo (0 : ℝ) 2, q (f t) = LQGMetric.Q t)
    {ξ γ : ℝ} (hξ : 0 < ξ) (hγ : γ ∈ Ioo (0 : ℝ) 2) (hqξ : q ξ = LQGMetric.Q γ) :
    ∃ t ∈ Ioo (0 : ℝ) 2, f t = ξ := by
  by_cases hA : ∃ t₀ ∈ Ioo (0 : ℝ) 2, ξ ≤ f t₀
  · obtain ⟨t₀, ht₀, hξt₀⟩ := hA
    have hε0 : 0 < min (ξ / 2) (t₀ / 2) := lt_min (by linarith) (by linarith [ht₀.1])
    have hεt : min (ξ / 2) (t₀ / 2) ≤ t₀ := (min_le_right _ _).trans (by linarith [ht₀.1])
    have hεξ : min (ξ / 2) (t₀ / 2) < ξ := (min_le_left _ _).trans_lt (by linarith)
    have hsub : Icc (min (ξ / 2) (t₀ / 2)) t₀ ⊆ Ioo (0 : ℝ) 2 :=
      fun s hs => ⟨hε0.trans_le hs.1, hs.2.trans_lt ht₀.2⟩
    have hfε : f (min (ξ / 2) (t₀ / 2)) < ξ :=
      (hle _ (hsub ⟨le_rfl, hεt⟩)).trans_lt hεξ
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hεt (hcont.mono hsub) ⟨hfε.le, hξt₀⟩
    exact ⟨t, hsub ht, hft⟩
  · push Not at hA
    exfalso
    have htmem : (γ + 2) / 2 ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
    have h1 : q ξ ≤ q (f ((γ + 2) / 2)) :=
      hanti (mem_Ioi.2 (hpos _ htmem)) (mem_Ioi.2 hξ) (hA _ htmem).le
    have h2 : LQGMetric.Q ((γ + 2) / 2) < LQGMetric.Q γ :=
      Q_lt_Q hγ.1 (by linarith [hγ.2]) htmem.2
    rw [hq _ htmem, hqξ] at h1
    linarith

/-- `ξ_γ = γ / d_γ ≤ γ` for `γ ∈ (0, 2)`, since `d_γ ≥ 1`. -/
theorem xiGamma_le_self {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : LQGMetric.xiGamma γ ≤ γ := by
  have hd := LQGMetric.DG.one_le_dGamma LQGMetric.DG.chiLeTwo hγ hγ2
  unfold LQGMetric.xiGamma
  exact div_le_self hγ.le hd

/-- If `γ ↦ d_γ` is continuous on `(0, 2)`, so is `γ ↦ ξ_γ = γ / d_γ`. -/
theorem continuousOn_xiGamma (hd : ContinuousOn LQGMetric.dGamma (Ioo 0 2)) :
    ContinuousOn LQGMetric.xiGamma (Ioo 0 2) := by
  show ContinuousOn (fun γ => γ / LQGMetric.dGamma γ) (Ioo 0 2)
  exact continuousOn_id.div hd (fun γ _ => (LQGMetric.DG.dGamma_pos γ).ne')

/-- Let `q` be nonincreasing on `(0, ∞)` with `q (γ' / d_γ') = Q_γ'` for every `γ' ∈ (0, 2)`, and let
`γ ↦ d_γ` be continuous on `(0, 2)`. If `ξ > 0` and `q ξ = Q_γ` for some `γ ∈ (0, 2)`, then
`ξ = γ' / d_γ'` for some `γ' ∈ (0, 2)`. -/
theorem exists_xiGamma_eq_of_lfppExponent_eq (hd : ContinuousOn LQGMetric.dGamma (Ioo 0 2))
    {q : ℝ → ℝ} (hanti : AntitoneOn q (Ioi 0))
    (hq : ∀ t ∈ Ioo (0 : ℝ) 2, q (LQGMetric.xiGamma t) = LQGMetric.Q t)
    {ξ γ : ℝ} (hξ : 0 < ξ) (hγ : 0 < γ) (hγ2 : γ < 2) (hqξ : q ξ = LQGMetric.Q γ) :
    ∃ t ∈ Ioo (0 : ℝ) 2, LQGMetric.xiGamma t = ξ :=
  exists_eq_of_antitoneOn_comp_eq_Q (continuousOn_xiGamma hd)
    (fun _ ht => LQGMetric.DG.xiGamma_pos ht.1) (fun _ ht => xiGamma_le_self ht.1 ht.2) hanti hq hξ
    ⟨hγ, hγ2⟩ hqξ

end LatticeProb.LQG
