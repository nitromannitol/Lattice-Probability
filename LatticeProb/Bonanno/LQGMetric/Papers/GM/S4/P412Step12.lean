/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412Step12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422E
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanPunct
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.LiftGeod

/-!
# GM Lemma 4.15, Steps 1–2 (deterministic parts)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.15 (`lem-stab-endpt`), l. 2120–2170.

* **Step 1** (l. 2125–2131) applies CONF Theorem 3.9 at `τ = s_k` with the radius
  `s_k + N^{-β_C}𝔠e^{ξh}` and compares with `t_k`; this needs the monotonicity
  `X_{s,t'} ⊆ X_{s,t}` for `s ≤ t ≤ t'` (a leftmost geodesic to `∂𝓑^•_{t'}` restricted to `[0,t]`
  is a leftmost geodesic to `∂𝓑^•_t`, CONF l. 554). `p412_hitSetDD_mono` proves it for the
  leftmost geodesics of decision D44 (= D-D1, `CONF.DD.IsLeftmostGeod`), via
  `CONF.DD.isLeftmost_restr` (S-left-restr). For the one-sided-limit reading still in
  `Blueprint.IsSideGeod` (which D44 supersedes) the restriction property is not available.
* **Step 2** (l. 2133–2160): `R_k ≤ 7ε^{κ/2}𝕣` from condition 6 of `ℰ_𝕣` (`p412_confRK_le`) and
  `σ_k ≤ t_k + (7ε^{κ/2})^χ 𝔠_𝕣e^{ξh_𝕣(0)}` from the Hölder upper bound, condition 3
  (`p412_enbhd_subset`, `p412_confSigma_le`, `p412_step2`). The scale `ε^κ` of GM is a dyadic
  `δ = 2^{-m}` here, since condition 6 is imposed only at dyadic scales (reading, proposed
  DEVIATIONS entry in the P2-M2J2 report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-! ## Step 1: monotonicity of the confluence-point sets -/

/-- CONF's `X_{t,s}` (`Blueprint.hitSet`) with the leftmost geodesics of decision D44
(`CONF.DD.IsLeftmostGeod`) -/
def hitSetDD (D : ContMetric) (z : ℂ) (t s : ℝ) : Set ℂ :=
  {x | x ∈ frontier (filledBall D z t) ∧
    ∃ y P, CONF.DD.IsLeftmostGeod D z s y P ∧ ∃ u ∈ Icc 0 s, P u = x}

/-- `hitSetDD` is the set counted by `Blueprint.CONFThm3_9At` (D76) -/
theorem hitSetDD_eq_hitSetLM (D : ContMetric) (z : ℂ) (t s : ℝ) :
    hitSetDD D z t s = Blueprint.hitSetLM D z t s := rfl

/-- **GM L4.15 Step 1, monotonicity** (GM l. 2129–2131 with CONF l. 554): for `0 < s ≤ t ≤ t'`,
every point of `∂𝓑^•_s` hit by a leftmost geodesic to `∂𝓑^•_{t'}` is hit by a leftmost geodesic
to `∂𝓑^•_t`. -/
theorem p412_hitSetDD_mono {D : ContMetric} {z : ℂ} {s t t' : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (htt' : t ≤ t') (hbd : Bornology.IsBounded (ballM D z s)) :
    hitSetDD D z s t' ⊆ hitSetDD D z s t := by
  rintro x ⟨hx, y, P, hl, u, hu, rfl⟩
  have hPu : D.1 (z, P u) = u := CONF.DD.cl_geodL_dist hl.2.1 hu
  have hxs : D.1 (z, P u) = s := jp_frontier_subset_sphere hbd hx
  have hus : u = s := hPu.symm.trans hxs
  rcases htt'.lt_or_eq with hlt | heq
  · exact ⟨hx, P t, P, CONF.DD.isLeftmost_restr hl (hs.trans_le hst) hlt, u,
      ⟨hu.1, hus ▸ hst⟩, rfl⟩
  · subst heq; exact ⟨hx, y, P, hl, u, hu, rfl⟩

/-! ## Step 2: the bounds for `R_k` and `σ_k` -/

section Step2
variable {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω}
  {h : Ω → DistC} {R : RegPar} {𝕣 a : ℝ} {ω : Ω}

/-- **GM l. 2142–2143**: on condition 6 of `ℰ_𝕣`, `R^δ_𝕣(K) ≤ 7δ^{1/2}𝕣` for a dyadic
`δ = 2^{-m} ≤ a` and `K` with `B_{δ𝕣}(K) ⊆ B_{4ℓ𝕣}(𝕣V)`. -/
theorem p412_confRK_le (hω : ω ∈ regC6 D P h R 𝕣 a) (h𝕣 : 0 < 𝕣) {m : ℕ}
    (hm : (2 : ℝ)⁻¹ ^ m ≤ a) {K : Set ℂ}
    (hK : thickening ((2 : ℝ)⁻¹ ^ m * 𝕣) K ⊆ regRegion R 𝕣) :
    confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m) K ω ≤
      ENNReal.ofReal (7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) * 𝕣) := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsq : δ ≤ δ ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hsup : (⨆ z ∈ gridPts (δ * 𝕣 / 4) ∩ thickening (δ * 𝕣) K,
      confRho R.ξ R.c D P h R.p (δ * 𝕣) z (confN R.p δ) ω) ≤
      ENNReal.ofReal (δ ^ (1 / 2 : ℝ) * 𝕣) :=
    iSup₂_le fun z hz => hω m hm z ⟨hz.1, hK hz.2⟩
  have hpos : 0 ≤ δ ^ (1 / 2 : ℝ) * 𝕣 := by positivity
  calc confRK R.ξ R.c D P h R.p 𝕣 δ K ω
      ≤ 6 * ENNReal.ofReal (δ ^ (1 / 2 : ℝ) * 𝕣) + ENNReal.ofReal (δ * 𝕣) := by
        unfold confRK; gcongr
    _ = ENNReal.ofReal (6 * (δ ^ (1 / 2 : ℝ) * 𝕣) + δ * 𝕣) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (7 * δ ^ (1 / 2 : ℝ) * 𝕣) := by
        apply ENNReal.ofReal_le_ofReal; nlinarith

end Step2

/-- **GM l. 2143–2144** (deterministic): if the `D`-distance from `∂𝓑^•_t` to points within
Euclidean distance `ρ` outside `𝓑^•_t` is at most `(ρ/𝕣)^χ S`, then
`B_ρ(𝓑^•_t) ⊆ 𝓑^•_{s'}` for every `s' > t + (ρ/𝕣)^χ S`. -/
theorem p412_enbhd_subset {D : ContMetric} {𝕫 : ℂ} {t ρ s' S χ 𝕣 : ℝ}
    (hbd : Bornology.IsBounded (ballM D 𝕫 t)) (hS : 0 ≤ (ρ / 𝕣) ^ χ * S)
    (hHol : ∀ u ∈ frontier (filledBall D 𝕫 t), ∀ x, x ∉ filledBall D 𝕫 t → ‖u - x‖ < ρ →
      D.1 (u, x) ≤ (ρ / 𝕣) ^ χ * S)
    (hs' : t + (ρ / 𝕣) ^ χ * S < s') :
    enbhd (ENNReal.ofReal ρ) (filledBall D 𝕫 t) ⊆ filledBall D 𝕫 s' := by
  intro x hx
  by_cases hxK : x ∈ filledBall D 𝕫 t
  · exact gm_filledBall_mono D 𝕫 (by linarith) hxK
  obtain ⟨y, hyK, hxy⟩ := infEDist_lt_iff.1 (show infEDist x (filledBall D 𝕫 t) < _ from hx)
  rw [edist_lt_ofReal] at hxy
  obtain ⟨u, huS, hu⟩ := jb_inter_frontier_nonempty (jb_isClosed_filledBall hbd)
    (convex_segment x y).isPreconnected (left_mem_segment ℝ x y) hxK (right_mem_segment ℝ x y) hyK
  have hux : ‖u - x‖ < ρ := by
    have := segment_subset_closedBall_left x y huS
    rw [mem_closedBall, dist_eq_norm] at this
    exact this.trans_lt hxy
  have hDu : D.1 (𝕫, u) = t := jp_frontier_subset_sphere hbd hu
  have h1 := hHol u hu x hxK hux
  have h2 := D.2.triangle 𝕫 u x
  exact Or.inl (subset_closure (show D.1 (𝕫, x) < s' by linarith))

/-- `σ^δ_{t,𝕣} ≤ s'` as soon as `t < s'` and `B_{R^δ_𝕣(𝓑^•_t)}(𝓑^•_t) ⊆ 𝓑^•_{s'}`
(definition (3.17) of CONF, `confSigma`) -/
theorem p412_confSigma_le {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric}
    {P : Measure Ω} {h : Ω → DistC} {R : RegPar} {z₀ : ℂ} {𝕣 δ t s' : ℝ} {ω : Ω}
    (hlt : t < s') (hsub : enbhd (confRK R.ξ R.c D P h R.p 𝕣 δ (filledBall (D (h ω)) z₀ t) ω)
      (filledBall (D (h ω)) z₀ t) ⊆ filledBall (D (h ω)) z₀ s') :
    confSigma R.ξ R.c D P h R.p z₀ 𝕣 δ t ω ≤ ENNReal.ofReal s' :=
  iInf_le_of_le s' (iInf_le_of_le hlt (iInf_le_of_le hsub le_rfl))

/-- **GM l. 2143–2144 on `ℰ_𝕣`** (condition 3, Hölder upper bound): for `𝕫 ∈ 𝕣V`,
`𝓑^•_t ⊆ B_{2ℓ𝕣}(𝕫)` and `0 < ρ ≤ a𝕣` (`a ≤ ℓ`), `B_ρ(𝓑^•_t) ⊆ 𝓑^•_{s'}` for every
`s' > t + (ρ/𝕣)^χ 𝔠_𝕣e^{ξh_𝕣(0)}`. -/
theorem p412_enbhd_regC3 {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} {ω : Ω} (h3 : ω ∈ regC3 D h R 𝕣 a) (h𝕣 : 0 < 𝕣) (haℓ : a ≤ R.ℓ) (hχ : 0 < R.χ)
    (hS : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.V) {t : ℝ}
    (hbd : Bornology.IsBounded (ballM (D (h ω)) 𝕫 t))
    (hK : filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 (2 * (R.ℓ * 𝕣))) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρa : ρ ≤ a * 𝕣) {s' : ℝ}
    (hs' : t + (ρ / 𝕣) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0 < s') :
    enbhd (ENNReal.ofReal ρ) (filledBall (D (h ω)) 𝕫 t) ⊆ filledBall (D (h ω)) 𝕫 s' := by
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0
  set K := filledBall (D (h ω)) 𝕫 t
  have hreg : ∀ x, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    mem_thickening_iff.2 ⟨𝕫, h𝕫, hx⟩
  refine p412_enbhd_subset (χ := R.χ) (S := S) (𝕣 := 𝕣) hbd (by positivity) ?_ hs'
  intro u hu x hxK hux
  have huK : u ∈ K := (jb_isClosed_filledBall hbd).frontier_subset hu
  have hu𝕫 := mem_ball.1 (hK huK)
  have hρℓ : ρ ≤ R.ℓ * 𝕣 := hρa.trans (mul_le_mul_of_nonneg_right haℓ h𝕣.le)
  have hxr : x ∈ regRegion R 𝕣 := hreg x (by
    have : dist x u < ρ := by rw [dist_eq_norm, ← norm_neg, neg_sub]; exact hux
    linarith [dist_triangle x u 𝕫])
  have hur : u ∈ regRegion R 𝕣 := hreg u (by linarith)
  have hne : u ≠ x := fun e => hxK (e ▸ huK)
  have h1 := (gm_D_le_internal (D (h ω)) _ _ _).trans
    (gm_regC3_upper h3 h𝕣 hS hur hxr (hux.le.trans hρa) hne)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hS.le)
  exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hux.le h𝕣.le) hχ.le

/-- **GM L4.15 Step 2** (l. 2139–2147), on `ℰ_𝕣` (conditions 3 and 6): for a dyadic scale
`δ = 2^{-m} ≤ a` with `7δ^{1/2} ≤ a`, a centre `𝕫 ∈ 𝕣V` and a radius `t` with
`𝓑^•_t ⊆ B_{2ℓ𝕣}(𝕫)`, one has `R_k := R^δ_𝕣(𝓑^•_t) ≤ 7δ^{1/2}𝕣` and
`σ^δ_{t,𝕣} ≤ s'` for every `s' > t + (7δ^{1/2})^χ 𝔠_𝕣e^{ξh_𝕣(0)}`. -/
theorem p412_step2 {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω}
    {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} {R : RegPar} {𝕣 a : ℝ} {ω : Ω}
    (hω : ω ∈ regEvent D P h H R 𝕣 a) (h𝕣 : 0 < 𝕣) (haℓ : a ≤ R.ℓ) (hχ : 0 < R.χ)
    (hS : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {m : ℕ} (hm : (2 : ℝ)⁻¹ ^ m ≤ a)
    (hm7 : 7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) ≤ a) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.V) {t : ℝ}
    (hbd : Bornology.IsBounded (ballM (D (h ω)) 𝕫 t))
    (hK : filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 (2 * (R.ℓ * 𝕣))) :
    confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m) (filledBall (D (h ω)) 𝕫 t) ω ≤
        ENNReal.ofReal (7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) * 𝕣) ∧
      ∀ s' : ℝ, t + (7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ)) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0 < s' →
        confSigma R.ξ R.c D P h R.p 𝕫 𝕣 ((2 : ℝ)⁻¹ ^ m) t ω ≤ ENNReal.ofReal s' := by
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩, h6⟩, _⟩ := hω
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0
  set K := filledBall (D (h ω)) 𝕫 t
  set ρ : ℝ := 7 * δ ^ (1 / 2 : ℝ) * 𝕣 with hρ
  have hδ0 : 0 < δ := by positivity
  have ha0 : 0 < a := hδ0.trans_le hm
  have hℓ0 : 0 < R.ℓ := ha0.trans_le haℓ
  have hℓ𝕣 : 0 < R.ℓ * 𝕣 := mul_pos hℓ0 h𝕣
  have hρa : ρ ≤ a * 𝕣 := by rw [hρ]; exact mul_le_mul_of_nonneg_right hm7 h𝕣.le
  have hreg : ∀ x, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    mem_thickening_iff.2 ⟨𝕫, h𝕫, hx⟩
  have hRK := p412_confRK_le (ω := ω) h6 h𝕣 hm (K := K) (by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have hy' := mem_ball.1 (hK hy)
    refine hreg x ?_
    have : (2 : ℝ)⁻¹ ^ m * 𝕣 ≤ R.ℓ * 𝕣 := mul_le_mul_of_nonneg_right (hm.trans haℓ) h𝕣.le
    linarith [dist_triangle x y 𝕫])
  refine ⟨hRK, fun s' hs' => p412_confSigma_le (by
      have : 0 ≤ (7 * δ ^ (1 / 2 : ℝ)) ^ R.χ * S := by positivity
      linarith) ?_⟩
  have hρ𝕣 : ρ / 𝕣 = 7 * δ ^ (1 / 2 : ℝ) := by rw [hρ]; field_simp
  have H2 : enbhd (ENNReal.ofReal ρ) K ⊆ filledBall (D (h ω)) 𝕫 s' :=
    p412_enbhd_regC3 h3 h𝕣 haℓ hχ hS h𝕫 hbd hK (by positivity) hρa (by rw [hρ𝕣]; exact hs')
  exact fun x hx => H2 (lt_of_lt_of_le hx hRK)

end LQGMetric.GM
