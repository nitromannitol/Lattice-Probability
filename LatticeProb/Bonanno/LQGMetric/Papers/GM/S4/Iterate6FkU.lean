/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6FkU at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6L422U
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3L420

/-!
# `ℰ_𝕣 ⊂ F_k` with a uniform threshold `ε₁` (P2-M2K6)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.19 (l. 2318–2327, 2593),
Lemma 4.22 (l. 2527–2565). Same proofs as `gm_regEvent_ball_subset` (Iterate3Ball.lean),
`gm_regEvent_subset_gmF0C` (Iterate3F.lean), `gm_regEvent_subset_gmGeo` (Iterate3Geo.lean) and
`gm_regEvent_subset_gmFk` (Iterate3L420.lean), pointwise in `ε` under the numeric hypothesis
`gmEpsOK` (Iterate6L422U.lean); `gm_regEvent_subset_gmFkU` then chooses `ε₁` from the numbers
`β, χ, χ', a, λ₄, λ₅, ℓ, ξ` only, before `Ω, P, h, H, R, 𝕣` (D75: GM's constants depend only on
the parameters).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω}
  {h : Ω → DistC}

/-- **B1** pointwise in `ε` (proof of `gm_regEvent_ball_subset`) -/
theorem gm_regEvent_ball_subsetP {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric}
    {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} (R : RegPar) {𝕣 a β : ℝ}
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 < R.χ) (hχ' : 0 < R.χ')
    (hβ : 0 < β) (hβχ : β < R.χ) (hlam : 1 < R.lam 3) (hlam5 : 0 ≤ R.lam 4)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) (hξ : 0 ≤ R.ξ)
    {ε : ℝ} (hεP : gmEpsOK β R.χ R.χ' a (R.lam 3) (R.lam 4) R.ℓ R.ξ ε) :
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ∀ z : ℂ,
      R.lam 3 * (ε * 𝕣) ≤ infDist z (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) →
      infDist z (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ≤ 2 * R.lam 3 * (ε * 𝕣) →
      ball z ((2 * R.lam 3 + R.lam 4) * (ε * 𝕣)) ⊆
        ballM (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) := by
  have hεP' := hεP
  unfold gmEpsOK at hεP'
  obtain ⟨-, hgap0, -, -, hεlin⟩ := hεP'
  have hε := hεlin
  set lam := R.lam 3 with hlamdef
  set N := ⌈16 * Real.pi * lam⌉₊ with hNdef
  set M := 4 * lam + R.lam 4 with hMdef
  have hlam0 : 0 < lam := by linarith
  have hM : 0 < M := by rw [hMdef]; linarith
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  have ha2 : 0 < (a / 2) ^ R.χ' := by positivity
  intro ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z hz1 hz2
  obtain ⟨hK3, hgap22, -, hcirc⟩ := gm_L4_22P (D := D) (P := P) (h := h) (H := H) R h𝕣 ha0 ha1
    haℓ hχ hχ' hβ hβχ hlam hUV hc hξ hεP ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z hz1 hz2
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hεlin.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hεa : M * ε ≤ a := by
    have := lt_of_lt_of_le hεlin.2 ((min_le_left _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ hM] at this; linarith
  have hεℓ : M * ε < R.ℓ := by
    have := lt_of_lt_of_le hεlin.2 (min_le_right _ _)
    rw [lt_div_iff₀ hM] at this; linarith
  obtain ⟨_, -, h3, _, _, _, _⟩ := gm_regEvent_mem.1 hω
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  set e := ε * 𝕣 with hedef
  have he : 0 < e := mul_pos hε0 h𝕣
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hreg : ∀ x : ℂ, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫V, hx⟩
  have h𝕫R : 𝕫 ∈ regRegion R 𝕣 := hreg 𝕫 (by rw [dist_self]; positivity)
  -- the unit `τ = τ_{ℓ𝕣}(𝕫) ≥ (a/2)^{χ'} S` (as in `gm_L4_22`)
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
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  set s' := s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω with hs'def
  have hs't : s' - t = τ * (ε ^ β - ε ^ (2 * β)) := by
    simp only [hs'def, htdef, s4T, s4S, s4Unit]; rw [← hτdef]; push_cast; ring
  have hεβ0 : 0 ≤ ε ^ β := (Real.rpow_pos_of_pos hε0 _).le
  have ht0 : 0 ≤ t := by
    simp only [htdef, s4T, s4S, s4Unit]; rw [← hτdef]; positivity
  -- the gap
  set θ' := t + N * ((ε / 4) ^ R.χ * S) with hθ'def
  have hgap : θ' + (M * ε) ^ R.χ * S < s' := by
    have h4 : (ε / 4) ^ R.χ ≤ ε ^ R.χ := Real.rpow_le_rpow (by positivity) (by linarith) hχ.le
    have hMe : (M * ε) ^ R.χ = M ^ R.χ * ε ^ R.χ := Real.mul_rpow hM.le hε0.le
    have hgap0' : ((N : ℝ) + M ^ R.χ) * ε ^ R.χ < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) := by
      have := hgap0
      rw [div_mul_eq_mul_div, div_lt_iff₀ ha2] at this
      linarith
    have hdiff0 : 0 ≤ ε ^ β - ε ^ (2 * β) := by
      have : ε ^ (2 * β) ≤ ε ^ β := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
      linarith
    have : ((N : ℝ) + M ^ R.χ) * ε ^ R.χ * S < τ * (ε ^ β - ε ^ (2 * β)) := by
      calc ((N : ℝ) + M ^ R.χ) * ε ^ R.χ * S
          < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) * S := mul_lt_mul_of_pos_right hgap0' hS
        _ = (a / 2) ^ R.χ' * S * (ε ^ β - ε ^ (2 * β)) := by ring
        _ ≤ τ * (ε ^ β - ε ^ (2 * β)) := mul_le_mul_of_nonneg_right hτ hdiff0
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have k1 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hN0 hS.le)
    rw [hMe]
    nlinarith
  -- a point `u` of the circle `∂B_{2λ₄ε𝕣}(z)`
  have hρ : 0 ≤ 2 * lam * e := by positivity
  set u := gmSph z (2 * lam * e) 0 with hudef
  have hu : u ∈ sphere z (2 * lam * e) := gm_gmSph_mem_sphere z hρ 0
  have hθ'0 : 0 ≤ θ' := by rw [hθ'def]; positivity
  have hu𝕫 : (D (h ω)).1 (𝕫, u) ≤ θ' := by
    have := (gm_D_le_internal (D (h ω)) _ 𝕫 u).trans (hcirc u hu)
    rwa [ENNReal.ofReal_le_ofReal_iff hθ'0] at this
  have huB : dist u 𝕫 < 3 * (R.ℓ * 𝕣) := by
    have hmem : u ∈ filledBall (D (h ω)) 𝕫 s' :=
      subset_closure.trans subset_union_left
        (show (D (h ω)).1 (𝕫, u) < s' by
          have : 0 ≤ (M * ε) ^ R.χ * S := by positivity
          linarith)
    exact hK3 hmem
  intro w hw
  show (D (h ω)).1 (𝕫, w) < s'
  have huw : ‖u - w‖ < M * e := by
    have h1 : ‖u - z‖ = 2 * lam * e := by rw [← dist_eq_norm]; exact mem_sphere.1 hu
    have h2 : ‖z - w‖ < (2 * lam + R.lam 4) * e := by
      rw [← dist_eq_norm, dist_comm]; exact hw
    calc ‖u - w‖ = ‖(u - z) + (z - w)‖ := by ring_nf
      _ ≤ ‖u - z‖ + ‖z - w‖ := norm_add_le _ _
      _ < M * e := by rw [h1, hMdef]; linarith
  by_cases huw0 : u = w
  · rw [← huw0]
    have : 0 ≤ (M * ε) ^ R.χ * S := by positivity
    linarith
  have hMe' : M * e = M * ε * 𝕣 := by rw [hedef]; ring
  have hwR : w ∈ regRegion R 𝕣 := hreg w (by
    have := dist_triangle w u 𝕫
    rw [dist_eq_norm w u, norm_sub_rev] at this
    have : M * e < R.ℓ * 𝕣 := by rw [hMe']; exact mul_lt_mul_of_pos_right hεℓ h𝕣
    linarith)
  have hHol := gm_regC3_upper h3 h𝕣 hS (hreg u (by have := mul_pos hℓ h𝕣; linarith)) hwR
    (by rw [hMe'] at huw; exact huw.le.trans (mul_le_mul_of_nonneg_right hεa h𝕣.le)) huw0
  have hDuw : (D (h ω)).1 (u, w) ≤ (M * ε) ^ R.χ * S := by
    have h1 := (gm_D_le_internal (D (h ω)) _ u w).trans hHol
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) ?_ hχ.le)
      hS.le)
    rw [div_le_iff₀ h𝕣, ← hMe']; exact huw.le
  have htri := (D (h ω)).2.triangle 𝕫 u w
  linarith


/-- **`ℰ_𝕣 ⊂ gmF0C k`** pointwise in `ε` (proof of `gm_regEvent_subset_gmF0C`) -/
theorem gm_regEvent_subset_gmF0CP {H : ℝ → ℂ → Ω → ℝ} (R : RegPar) {𝕣 a β : ℝ}
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 < R.χ) (hχ' : 0 < R.χ')
    (hβ : 0 < β) (hβχ : β < R.χ) (hlam : 1 < R.lam 3) (hlam5 : 0 ≤ R.lam 4)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) (hξ : 0 ≤ R.ξ)
    {ε : ℝ} (hεP : gmEpsOK β R.χ R.χ' a (R.lam 3) (R.lam 4) R.ℓ R.ξ ε) :
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ω ∈ gmF0C D h R 𝕫 𝕣 ε β k := by
  have hε0 := gm_epsOK_pos hεP
  intro ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk
  refine mem_iInter₂.2 fun ab n => ?_
  by_cases hG : ω ∈ gmG0 D h 𝕫 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε)
      (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (R.rr 𝕣 ε n) 0
  · refine Or.inr ?_
    set z := gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab
    set K := filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)
    obtain ⟨-, hzK, -, hI⟩ := hG.1
    have hKc : IsClosed K := gm_filledBall_isClosed _ _ _
    have htk : 0 < s4T D h 𝕫 R.ℓ 𝕣 ε β k ω := by
      rw [gm_s4T_eq]
      have hτ := gm_tauD_pos (D (h ω)) 𝕫 (mul_pos (lt_of_lt_of_le ha0 haℓ) h𝕣)
      have : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε0.le β)
      have : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
      positivity
    have hKne : K.Nonempty := ⟨𝕫, subset_closure.trans subset_union_left
      (show (D (h ω)).1 (𝕫, 𝕫) < _ by rw [(D (h ω)).2.self_eq_zero 𝕫]; exact htk)⟩
    rw [gm_infDist_frontier_eq' hKc hKne hzK] at hI
    have hI1 : R.lam 3 * (ε * 𝕣) ≤ infDist z K := by rw [← mul_assoc]; exact hI.1
    have hI2 : infDist z K ≤ 2 * R.lam 3 * (ε * 𝕣) := by
      have := hI.2; rw [mul_assoc (2 * R.lam 3)] at this; exact this
    exact (gm_regEvent_ball_subsetP (D := D) (P := P) (h := h) (H := H) R h𝕣 ha0
      ha1 haℓ hχ hχ' hβ hβχ hlam hlam5 hUV hc hξ hεP ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z hI1 hI2).trans
      (subset_closure.trans subset_union_left)
  · exact Or.inl hG


/-- **`ℰ_𝕣 ⊆ gmGeo k`** pointwise in `ε` (proof of `gm_regEvent_subset_gmGeo`) -/
theorem gm_regEvent_subset_gmGeoP {H : ℝ → ℂ → Ω → ℝ} (R : RegPar) {𝕣 a β : ℝ}
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 < R.χ) (hχ' : 0 < R.χ')
    (hβ : 0 < β) (hβχ : β < R.χ) (hlam : 1 < R.lam 3) (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣)
    (hξ : 0 ≤ R.ξ)
    {ε : ℝ} (hεP : gmEpsOK β R.χ R.χ' a (R.lam 3) (R.lam 4) R.ℓ R.ξ ε) :
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ω ∈ gmGeo D h R 𝕫 𝕣 ε β k := by
  have hε0 := gm_epsOK_pos hεP
  intro ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk
  refine mem_iInter₂.2 fun ab n => ?_
  by_cases hG : ω ∈ gmG0 D h 𝕫 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε)
      (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (R.rr 𝕣 ε n) 0
  · refine Or.inr ?_
    set z := gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab
    set K := filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)
    obtain ⟨-, hzK, -, hI⟩ := hG.1
    have hKc : IsClosed K := gm_filledBall_isClosed _ _ _
    have htk : 0 < s4T D h 𝕫 R.ℓ 𝕣 ε β k ω := by
      rw [gm_s4T_eq]
      have hτ := gm_tauD_pos (D (h ω)) 𝕫 (mul_pos (lt_of_lt_of_le ha0 haℓ) h𝕣)
      have : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε0.le β)
      have : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
      positivity
    have hKne : K.Nonempty := ⟨𝕫, subset_closure.trans subset_union_left
      (show (D (h ω)).1 (𝕫, 𝕫) < _ by rw [(D (h ω)).2.self_eq_zero 𝕫]; exact htk)⟩
    rw [gm_infDist_frontier_eq' hKc hKne hzK] at hI
    have hI1 : R.lam 3 * (ε * 𝕣) ≤ infDist z K := by rw [← mul_assoc]; exact hI.1
    have hI2 : infDist z K ≤ 2 * R.lam 3 * (ε * 𝕣) := by
      have := hI.2; rw [mul_assoc (2 * R.lam 3)] at this; exact this
    obtain ⟨-, hgap, -, hcirc⟩ := gm_L4_22P (D := D) (P := P) (h := h) (H := H) R h𝕣 ha0
      ha1 haℓ hχ hχ' hβ hβχ hlam hUV hc hξ hεP ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z hI1 hI2
    set θ' := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω + ⌈16 * Real.pi * R.lam 3⌉₊ *
      ((ε / 4) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0)
    obtain ⟨θ, hθ1, hθ2⟩ := exists_rat_btwn hgap
    refine ⟨θ, ?_, fun m => ?_⟩
    · rw [gm_s4S_eq] at hθ2; exact_mod_cast hθ2
    have hρ : 0 ≤ 2 * R.lam 3 * (ε * 𝕣) := by
      have := hε0; have := h𝕣; positivity
    refine (gm_internal_anti (D (h ω)) (sdiff_subset_compl _ _) _ _).trans
      ((hcirc _ (gm_gmSph_mem_sphere z hρ m)).trans ?_)
    exact ENNReal.ofReal_le_ofReal hθ1.le
  · exact Or.inl hG


/-- **`ℰ_𝕣 ⊂ F_k`** pointwise in `ε` (proof of `gm_regEvent_subset_gmFk`) -/
theorem gm_regEvent_subset_gmFkP {H : ℝ → ℂ → Ω → ℝ} (R : RegPar) {𝕣 a β : ℝ}
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 < R.χ) (hχ' : 0 < R.χ')
    (hβ : 0 < β) (hβχ : β < R.χ) (hlam : 1 < R.lam 3) (hlam5 : 0 ≤ R.lam 4)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) (hξ : 0 ≤ R.ξ)
    {ε : ℝ} (hεP : gmEpsOK β R.χ R.χ' a (R.lam 3) (R.lam 4) R.ℓ R.ξ ε) :
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, ∀ 𝕨 : ℂ, 3 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
    H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    ∀ k ≤ p4K R a ε β, ω ∈ gmFk D h R 𝕫 𝕨 𝕣 ε β k := by
  intro ω hω 𝕫 h𝕫 𝕨 h𝕨 hH0 hH𝕫 hL hbd hgeod k hk
  have hε0 := gm_epsOK_pos hεP
  have hεβ : ε ^ β ≤ a / regC2const R a := hεP.2.2.1
  refine ⟨⟨gm_regEvent_subset_gmF0CP (D := D) (P := P) (h := h) (H := H) R h𝕣 ha0 ha1 haℓ hχ
      hχ' hβ hβχ hlam hlam5 hUV hc hξ hεP ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk,
    gm_regEvent_subset_gmGeoP (D := D) (P := P) (h := h) (H := H) R h𝕣 ha0 ha1 haℓ hχ hχ' hβ hβχ
      hlam hUV hc hξ hεP ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk⟩, ?_⟩
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  have hc2 : 0 < regC2const R a := by unfold regC2const; positivity
  have hεβ0 : 0 ≤ ε ^ β := (Real.rpow_pos_of_pos hε0 _).le
  have hx1 : 1 ≤ a / regC2const R a * ε ^ (-β) := by
    rw [Real.rpow_neg hε0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hε0 _)]
    linarith
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ a / regC2const R a * ε ^ (-β) := by
    have h1 : k + 1 ≤ ⌊a / regC2const R a * ε ^ (-β)⌋₊ := by
      have := Nat.one_le_floor_iff _ |>.2 hx1
      unfold p4K at hk; omega
    exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
  have hk2 : ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a :=
    calc ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a * ε ^ (-β) * ε ^ β :=
          mul_le_mul_of_nonneg_right hk1 hεβ0
      _ = a / regC2const R a := by
          rw [Real.rpow_neg hε0.le, mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hε0 _).ne',
            mul_one]
  have hsub := gm_filledBall_s_subset_ball R h𝕣 ha0 ha1 haℓ hχ.le hUV hc hξ hε0 hω h𝕫 hH0 hH𝕫
    hk2
  intro h𝕨B
  have := hsub h𝕨B
  rw [mem_ball, dist_eq_norm, norm_sub_rev] at this
  linarith

/-- **`ℰ_𝕣 ⊂ F_k`, uniform threshold** (GM Lemma 4.19, l. 2318–2327): `ε₁` depends only on
`a, β, χ, χ', ℓ, ξ, λ₄, λ₅`, not on `Ω, P, h, H, R, 𝕣` -/
theorem gm_regEvent_subset_gmFkU {a β χ χ' ℓ ξ : ℝ} {lam : Fin 5 → ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) (haℓ : a ≤ ℓ) (hχ : 0 < χ) (hχ' : 0 < χ') (hβ : 0 < β) (hβχ : β < χ)
    (hlam : 1 < lam 3) (hlam5 : 0 ≤ lam 4) (hξ : 0 ≤ ξ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ {Ω : Type} [MeasurableSpace Ω]
      {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
      (R : RegPar), R.χ = χ → R.χ' = χ' → R.lam = lam → R.ℓ = ℓ → R.ξ = ξ → R.U ⊆ R.V →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ ω ∈ regEvent D P h H R 𝕣 a,
      ∀ 𝕫 ∈ rScale 𝕣 R.U, ∀ 𝕨 : ℂ, 3 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
      H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
      (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
      (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
      ∀ k ≤ p4K R a ε β, ω ∈ gmFk D h R 𝕫 𝕨 𝕣 ε β k := by
  obtain ⟨ε₁, hε₁, hok⟩ := gm_epsOK_exists (χ' := χ') (ξ := ξ) ha0 haℓ hβ hβχ hlam hlam5
  refine ⟨ε₁, hε₁, fun ε hε Ω _ D P h H R hRχ hRχ' hRlam hRℓ hRξ hUV 𝕣 h𝕣 hc => ?_⟩
  subst hRχ hRχ' hRlam hRℓ hRξ
  exact gm_regEvent_subset_gmFkP (D := D) (P := P) (h := h) (H := H) R h𝕣 ha0 ha1 haℓ hχ hχ' hβ
    hβχ hlam hlam5 hUV hc hξ (hok ε hε)

end LQGMetric.GM
