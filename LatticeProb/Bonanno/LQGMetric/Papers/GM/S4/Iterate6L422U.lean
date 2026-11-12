/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6L422U at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422F

/-!
# GM Lemma 4.22 with a uniform threshold `ε₁` (P2-M2K6)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.22 (l. 2527–2565), as in
`gm_L4_22` (ManyGoodL422F.lean), whose proof chooses `ε₁` from the numbers
`β, χ, χ', a, λ₄, λ₅, ℓ, ξ` only (GM's constants depend only on the parameters, D75).

* `gmEpsOK`: the numeric smallness conditions on `ε` used in `gm_L4_22` and in the ball lemma
  `gm_regEvent_ball_subset` (Iterate3Ball.lean);
* `gm_epsOK_exists`: they hold for all `ε ∈ (0, ε₁)`, `ε₁` depending on these numbers only;
* `gm_L4_22P`: the pointwise form of `gm_L4_22` (same proof) for every `ε` with `gmEpsOK`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the numeric smallness conditions on `ε` of GM Lemmas 4.19/4.22 (proofs of `gm_L4_22` and
`gm_regEvent_ball_subset`): the gaps (4.40), `ε^β ≤ a/c₂` and the linear bounds -/
def gmEpsOK (β χ χ' a l3 l4 ℓ ξ ε : ℝ) : Prop :=
  (((⌈16 * Real.pi * l3⌉₊ : ℕ) : ℝ) + 1) / (a / 2) ^ χ' * ε ^ χ < ε ^ β - ε ^ (2 * β) ∧
  (((⌈16 * Real.pi * l3⌉₊ : ℕ) : ℝ) + (4 * l3 + l4) ^ χ) / (a / 2) ^ χ' * ε ^ χ <
    ε ^ β - ε ^ (2 * β) ∧
  ε ^ β ≤ a / ((ℓ / a + 1) * Real.exp (ξ / a)) ∧
  ε ∈ Ioo 0 (min (min 1 (a / (2 * l3))) (ℓ / (4 * l3 + 1))) ∧
  ε ∈ Ioo 0 (min (min 1 (a / (4 * l3 + l4))) (ℓ / (4 * l3 + l4)))

theorem gm_epsOK_eventually {β χ χ' a l3 l4 ℓ ξ : ℝ} (ha0 : 0 < a) (haℓ : a ≤ ℓ) (hβ : 0 < β)
    (hβχ : β < χ) (hlam : 1 < l3) (hlam5 : 0 ≤ l4) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), gmEpsOK β χ χ' a l3 l4 ℓ ξ ε := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le ha0 haℓ
  have hl3 : 0 < l3 := by linarith
  have hM : 0 < 4 * l3 + l4 := by linarith
  have ha2 : 0 < (a / 2) ^ χ' := by positivity
  have hM' : 0 < (4 * l3 + l4) ^ χ := by positivity
  have g1 := gm_small_gap hβ hβχ
    (show 0 < (((⌈16 * Real.pi * l3⌉₊ : ℕ) : ℝ) + 1) / (a / 2) ^ χ' by positivity)
  have g2 := gm_small_gap hβ hβχ
    (show 0 < (((⌈16 * Real.pi * l3⌉₊ : ℕ) : ℝ) + (4 * l3 + l4) ^ χ) / (a / 2) ^ χ' by positivity)
  have hβev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ β ≤ a / ((ℓ / a + 1) * Real.exp (ξ / a)) := by
    have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    rw [Real.zero_rpow hβ.ne'] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))
  have l1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min (min 1 (a / (2 * l3))) (ℓ / (4 * l3 + 1))) :=
    Ioo_mem_nhdsGT (lt_min (lt_min one_pos (by positivity)) (by positivity))
  have l2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min (min 1 (a / (4 * l3 + l4))) (ℓ / (4 * l3 + l4))) :=
    Ioo_mem_nhdsGT (lt_min (lt_min one_pos (by positivity)) (by positivity))
  filter_upwards [g1, g2, hβev, l1, l2] with ε e1 e2 e3 e4 e5
  exact ⟨e1, e2, e3, e4, e5⟩

/-- the threshold `ε₁` of GM Lemmas 4.19/4.22 depends only on the numbers -/
theorem gm_epsOK_exists {β χ χ' a l3 l4 ℓ ξ : ℝ} (ha0 : 0 < a) (haℓ : a ≤ ℓ) (hβ : 0 < β)
    (hβχ : β < χ) (hlam : 1 < l3) (hlam5 : 0 ≤ l4) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁, gmEpsOK β χ χ' a l3 l4 ℓ ξ ε := by
  obtain ⟨ε₁, hε₁, h⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (gm_epsOK_eventually (χ' := χ') (ξ := ξ) ha0 haℓ hβ hβχ hlam hlam5)
  exact ⟨ε₁, hε₁, fun ε hε => h hε⟩

theorem gm_epsOK_pos {β χ χ' a l3 l4 ℓ ξ ε : ℝ} (h : gmEpsOK β χ χ' a l3 l4 ℓ ξ ε) : 0 < ε :=
  h.2.2.2.1.1

/-- **GM Lemma 4.22** on `ℰ_𝕣`, pointwise in `ε` (the proof of `gm_L4_22`, with the numeric
smallness of `ε` as the hypothesis `gmEpsOK`) -/
theorem gm_L4_22P {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω}
    {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} (R : RegPar) {𝕣 a β : ℝ}
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 < R.χ) (hχ' : 0 < R.χ')
    (hβ : 0 < β) (hβχ : β < R.χ) (hlam : 1 < R.lam 3) (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣)
    (hξ : 0 ≤ R.ξ) {ε : ℝ} (hεP : gmEpsOK β R.χ R.χ' a (R.lam 3) (R.lam 4) R.ℓ R.ξ ε) :
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ∀ z : ℂ,
      R.lam 3 * (ε * 𝕣) ≤ infDist z (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) →
      infDist z (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ≤ 2 * R.lam 3 * (ε * 𝕣) →
      filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) ⊆ ball 𝕫 (3 * (R.ℓ * 𝕣)) ∧
      s4T D h 𝕫 R.ℓ 𝕣 ε β k ω + ⌈16 * Real.pi * R.lam 3⌉₊ *
          ((ε / 4) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0) < s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω ∧
      2 * R.lam 3 * (ε * 𝕣) < ‖𝕫 - z‖ ∧
      ∀ u ∈ sphere z (2 * R.lam 3 * (ε * 𝕣)),
        (D (h ω)).internal (filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) \
            closedBall z (ε * 𝕣)) 𝕫 u ≤
          ENNReal.ofReal (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω + ⌈16 * Real.pi * R.lam 3⌉₊ *
            ((ε / 4) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0)) := by
  unfold gmEpsOK at hεP
  obtain ⟨hgap0, -, hεβ, hεlin, -⟩ := hεP
  have hε := hεlin
  set lam := R.lam 3 with hlamdef
  set N := ⌈16 * Real.pi * lam⌉₊ with hNdef
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  have hc2 : 0 < regC2const R a := by unfold regC2const; positivity
  have ha2 : 0 < (a / 2) ^ R.χ' := by positivity
  replace hεβ : ε ^ β ≤ a / regC2const R a := hεβ
  intro ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z hz1 hz2
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hεlin.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hεa : ε < a / (2 * lam) := lt_of_lt_of_le hεlin.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hεℓ : ε < R.ℓ / (4 * lam + 1) := lt_of_lt_of_le hεlin.2 (min_le_right _ _)
  have hlam0 : 0 < lam := by linarith
  have hεa' : 2 * lam * ε < a := by rw [lt_div_iff₀ (by positivity)] at hεa; linarith
  have hεℓ' : (4 * lam + 1) * ε < R.ℓ := by rw [lt_div_iff₀ (by positivity)] at hεℓ; linarith
  obtain ⟨_, h2, h3, _, _, _, _⟩ := gm_regEvent_mem.1 hω
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  set e := ε * 𝕣 with hedef
  have he : 0 < e := mul_pos hε0 h𝕣
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hreg : ∀ x : ℂ, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫V, hx⟩
  have h𝕫R : 𝕫 ∈ regRegion R 𝕣 := hreg 𝕫 (by rw [dist_self]; positivity)
  -- the unit `τ = τ_{ℓ𝕣}(𝕫) ≥ (a/2)^{χ'} S`
  set τ := tauR D h 𝕫 (R.ℓ * 𝕣) ω with hτdef
  have hτ : (a / 2) ^ R.χ' * S ≤ τ := by
    have har : 0 < a * 𝕣 := mul_pos ha0 h𝕣
    have hal : a * 𝕣 ≤ R.ℓ * 𝕣 := mul_le_mul_of_nonneg_right haℓ h𝕣.le
    refine gm_tauR_ge_of_sphere hL (by positivity : 0 < a * 𝕣 / 2) (by linarith) fun w hw => ?_
    have hw' : ‖𝕫 - w‖ = a * 𝕣 / 2 := by rw [← dist_eq_norm, dist_comm]; exact mem_sphere.1 hw
    have := gm_regC3_lower h3 h𝕣 hS h𝕫R (hreg w (by rw [mem_sphere.1 hw]; linarith))
      (by rw [hw']; linarith)
    rwa [hw', show a * 𝕣 / 2 / 𝕣 = a / 2 by field_simp] at this
  have hτ0 : 0 < τ := lt_of_lt_of_le (mul_pos ha2 hS) hτ
  -- times
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  set s' := s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω with hs'def
  have hεβ0 : 0 ≤ ε ^ β := (Real.rpow_pos_of_pos hε0 _).le
  have hτt : τ ≤ t := by
    have := gm_s4S_le_s4T (D := D) (h := h) (𝕫 := 𝕫) (ℓ := R.ℓ) (𝕣 := 𝕣) (β := β) hε0 k ω
    have h1 : τ ≤ s4S D h 𝕫 R.ℓ 𝕣 ε β k ω := by
      simp only [s4S, s4Unit]; rw [← hτdef, mul_add, mul_one]
      have := mul_nonneg hτ0.le (mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hεβ0)
      linarith
    linarith
  have ht0 : 0 < t := lt_of_lt_of_le hτ0 hτt
  have hts' : t ≤ s' := gm_s4T_le_s4S_succ hε0 hε1.le hβ.le k ω
  have hs'2 : s' ≤ tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω := by
    refine gm_S4_3 hω hc hξ h𝕣 hℓ ha0 ha1 hχ.le hUV h𝕫 hH0 hH𝕫 ?_
    have hx1 : 1 ≤ a / regC2const R a * ε ^ (-β) := by
      rw [Real.rpow_neg hε0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hε0 _)]
      linarith
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ a / regC2const R a * ε ^ (-β) := by
      have h1 : k + 1 ≤ ⌊a / regC2const R a * ε ^ (-β)⌋₊ := by
        have := Nat.one_le_floor_iff _ |>.2 hx1
        unfold p4K at hk; omega
      exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
    calc ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a * ε ^ (-β) * ε ^ β :=
          mul_le_mul_of_nonneg_right hk1 hεβ0
      _ = a / regC2const R a := by
          rw [Real.rpow_neg hε0.le, mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hε0 _).ne',
            mul_one]
  have h2𝕫 := h2 𝕫 h𝕫R
  have hs'3 : s' < tauR D h 𝕫 (3 * (R.ℓ * 𝕣)) ω := by
    have hpos : 0 < a * max (R.c 𝕣 * Real.exp (R.ξ * H 𝕣 𝕫 ω))
        (R.c (R.ℓ * 𝕣) * Real.exp (R.ξ * H (R.ℓ * 𝕣) 𝕫 ω)) :=
      mul_pos ha0 (lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (le_max_left _ _))
    have := h2𝕫.2.trans (min_le_right _ _)
    linarith
  -- `K = 𝓑^•_t ⊆ B_{3ℓ𝕣}(𝕫)` and `B_{a𝕣}(𝕫) ⊆ K`
  have hKball : filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 (3 * (R.ℓ * 𝕣)) :=
    gm_filledBall_subset_ball_of_lt_tauR ht0 (lt_of_le_of_lt hts' hs'3)
  have hballK : ball 𝕫 (a * 𝕣) ⊆ filledBall (D (h ω)) 𝕫 t :=
    h2𝕫.1.trans (gm_filledBall_mono _ _ hτt)
  have hfar : 2 * lam * e < ‖𝕫 - z‖ := by
    by_contra hle
    push_neg at hle
    have hlt : 2 * lam * e < a * 𝕣 := by
      rw [hedef, ← mul_assoc]; exact mul_lt_mul_of_pos_right hεa' h𝕣
    have hzK : z ∈ filledBall (D (h ω)) 𝕫 t := hballK (by
      rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith)
    rw [infDist_zero_of_mem hzK] at hz1
    exact absurd hz1 (not_le.2 (by positivity))
  -- `z` is close to `K`
  have hKne : (filledBall (D (h ω)) 𝕫 t).Nonempty := ⟨𝕫, hballK (mem_ball_self (by positivity))⟩
  have hKc : IsCompact (filledBall (D (h ω)) 𝕫 t) :=
    Metric.isCompact_of_isClosed_isBounded (gm_filledBall_isClosed _ _ _)
      (isBounded_ball.subset hKball)
  obtain ⟨y, hyK, hyz'⟩ := hKc.exists_infDist_eq_dist hKne z
  have hyz : dist z y ≤ 2 * lam * e := hyz' ▸ hz2
  have hy𝕫 : dist y 𝕫 < 3 * (R.ℓ * 𝕣) := hKball hyK
  -- Hölder upper bound on the circle
  have hHol : ∀ u ∈ sphere z (2 * lam * e), ∀ v : ℂ, u ≠ v → ‖u - v‖ ≤ e / 2 →
      (D (h ω)).internal (ball u (2 * ‖u - v‖)) u v ≤
        ENNReal.ofReal ((‖u - v‖ / 𝕣) ^ R.χ * S) := by
    intro u' hu' v huv hd
    have hu'z : dist u' z = 2 * lam * e := mem_sphere.1 hu'
    have hkey : (4 * lam + 1) * e < R.ℓ * 𝕣 := by
      rw [hedef]; have := mul_lt_mul_of_pos_right hεℓ' h𝕣; linarith
    have hu'𝕫 : dist u' 𝕫 < 4 * (R.ℓ * 𝕣) - e / 2 := by
      have := dist_triangle4 u' z y 𝕫
      linarith
    refine gm_regC3_upper h3 h𝕣 hS (hreg u' (by linarith [he])) (hreg v ?_) ?_ huv
    · have := dist_triangle v u' 𝕫
      rw [dist_eq_norm v u', norm_sub_rev] at this
      linarith
    · have hεl : ε < lam * ε := lt_mul_of_one_lt_left hε0 hlam
      have : e / 2 ≤ a * 𝕣 := by
        rw [hedef]
        have : ε * 𝕣 ≤ a * 𝕣 := mul_le_mul_of_nonneg_right (by linarith) h𝕣.le
        linarith
      linarith
  -- the gap (4.40)
  have hgap : t + ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ * ((e / 4 / 𝕣) ^ R.χ * S) +
      (e / 2 / 𝕣) ^ R.χ * S < s' := by
    have hN : ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ = N := by
      rw [hNdef]; congr 1; field_simp; ring
    rw [hN, show e / 4 / 𝕣 = ε / 4 by rw [hedef]; field_simp,
      show e / 2 / 𝕣 = ε / 2 by rw [hedef]; field_simp]
    have h4 : (ε / 4) ^ R.χ ≤ ε ^ R.χ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hχ.le
    have h2' : (ε / 2) ^ R.χ ≤ ε ^ R.χ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hχ.le
    have hs't : s' - t = τ * (ε ^ β - ε ^ (2 * β)) := by
      simp only [hs'def, htdef, s4T, s4S, s4Unit]; rw [← hτdef]; push_cast; ring
    have hgap0' : ((N : ℝ) + 1) * ε ^ R.χ < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) := by
      have := hgap0
      rw [div_mul_eq_mul_div, div_lt_iff₀ ha2] at this
      linarith
    have hdiff0 : 0 ≤ ε ^ β - ε ^ (2 * β) := by
      have : ε ^ (2 * β) ≤ ε ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
      linarith
    have : ((N : ℝ) + 1) * ε ^ R.χ * S < τ * (ε ^ β - ε ^ (2 * β)) := by
      calc ((N : ℝ) + 1) * ε ^ R.χ * S < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) * S :=
            mul_lt_mul_of_pos_right hgap0' hS
        _ = (a / 2) ^ R.χ' * S * (ε ^ β - ε ^ (2 * β)) := by ring
        _ ≤ τ * (ε ^ β - ε ^ (2 * β)) := mul_le_mul_of_nonneg_right hτ hdiff0
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have k1 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hN0 hS.le)
    have k2 := mul_le_mul_of_nonneg_right h2' hS.le
    linarith
  have hN : ⌈8 * Real.pi * (2 * lam * e) / e⌉₊ = N := by
    rw [hNdef]; congr 1; field_simp; ring
  have he4 : e / 4 / 𝕣 = ε / 4 := by rw [hedef]; field_simp
  refine ⟨gm_filledBall_subset_ball_of_lt_tauR (lt_of_lt_of_le ht0 hts') hs'3, ?_, hfar, ?_⟩
  · have := hgap
    rw [hN, he4] at this
    have : 0 ≤ (e / 2 / 𝕣) ^ R.χ * S := by positivity
    linarith
  · intro u hu
    have hmain := gm_L4_22_det (D (h ω)) hlam he h𝕣 hχ hS.le ht0 hL (hbd t) hgeod hz1
      ⟨y, hyK, hyz⟩ hfar hHol hgap u hu
    rw [hN, he4] at hmain
    exact hmain


end LQGMetric.GM
