/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412U3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412U2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fCore

/-!
# The deterministic core of GM Prop 4.12 with a uniform threshold (P2-M2J2i, part 3)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3 (l. 2155–2199) and the
proof of Prop 4.12 (l. 2212–2276). Primed copies (`…U`, same proofs, `∃ ε₁` before `R`, the space
and `𝕣`; see P412U1.lean) of `p412f_core` (P412fCore) and `p412_eq439`
(P412Sigma).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {ξN : ℝ} {cN : ℝ → ℝ} {pN : CONFParams} {χN χ'N μN νN : ℝ} {lamN : Fin 5 → ℝ} {ℓN : ℝ}
  {UN VN : Set ℂ}

theorem p412f_coreU
    {a β κ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hl0 : 0 < lamN 0) (hl01 : lamN 0 < lamN 1)
    (hl12 : lamN 1 ≤ lamN 2) (hl23 : lamN 2 ≤ lamN 3) (hlam : 1 < lamN 3)
    (hν : 0 ≤ νN) (hUV : UN ⊆ VN) (hξ : 0 ≤ ξN) (hχχ : χN ≤ χ'N)
    (hκ : 0 < κ) (hβκ : β < κ * χN / 2)
    (he1 : κ * (χ'N / χN) < χN / χ'N) (he2 : κ * (χ'N / χN) < 1) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₁ →
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, ∀ 𝕨 : ℂ, 4 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
    H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    (∀ k < ⌊R.μ * Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹⌋₊,
      R.rr 𝕣 ((2 : ℝ)⁻¹ ^ n) k ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣) ((2 : ℝ)⁻¹ ^ n * 𝕣)) →
    IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) →
    ∀ k ≤ p4K R a ((2 : ℝ)⁻¹ ^ n) β,
    (⋃ x ∈ confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
        (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω),
        arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x =
      frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω))) →
    ∀ (E : Set ℂ) (zf : ℂ → ℂ),
    (∀ x₀ ∈ confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
        (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω),
      closure (arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x₀) ∩
        closure (frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) \
          arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x₀) ⊆ E) →
    (∀ e ∈ E, p412eGoodZ (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) e
      (zf e) (((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣)) →
    (∀ e ∈ E, Disjoint (range (sel 𝕫 𝕨 (h ω)))
      (ball (zf e) (17 * (((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣)) \
        filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω))) →
    (zkE D sel h R 𝕫 𝕨 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω).Nonempty := by
  have hℓ : 0 < ℓN := lt_of_lt_of_le ha0 haℓ
  obtain ⟨ε₁, hε₁, HC⟩ := p412e_core_noHitU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1
    haℓ hχ hχ' hβ hβχ hl0 hl01 hl12 hl23 hlam hUV  hξ hχχ he1 he2
  obtain ⟨ε₂, hε₂, HT⟩ := p412f_timesU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1 haℓ
    hχ hχχ hβ hκ hβκ hUV  hξ
  obtain ⟨ε₃, hε₃, HS⟩ := p412f_small (lam := lamN 3) (χ' := χ'N) ha0 hκ hℓ
    (show 0 < χ'N / χN by positivity) hχ
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro R hRN Ω _ D P h H sel 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace HC := HC R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  replace HT := HT R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  try simp only [regC2N_eq] at *
  intro n hn ω hω 𝕫 h𝕫 𝕨 h𝕫𝕨 hH0 hH𝕫 hL hbd hgeod hrr hsel k hk hcov E zf hE hz hG
  set ε := (2 : ℝ)⁻¹ ^ n with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1' : ε < ε₁ := hn.trans_le (min_le_left _ _)
  have hε2' : ε < ε₂ := hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε3' : ε < ε₃ := hn.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hεa, h17a, h4l, hε'1, hε'a, hε'χ⟩ := HS ε ⟨hε0, hε3'⟩
  have hε1 : ε < 1 := hεa.trans_lt ha1
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  set s' := s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω with hs'def
  set K := filledBall (D (h ω)) 𝕫 t with hKdef
  set F := filledBall (D (h ω)) 𝕫 s' with hFdef
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  obtain ⟨hA, hB, ht0, hKb, hFb, -⟩ := HT ε ⟨hε0, hε2'⟩ ω hω 𝕫 h𝕫 hH0 hH𝕫 hL k hk
  obtain ⟨_, _, h3, _⟩ := gm_regEvent_mem.1 hω
  have hℓ𝕣 : 0 < R.ℓ * 𝕣 := mul_pos hℓ h𝕣
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hreg : ∀ x : ℂ, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    mem_thickening_iff.2 ⟨𝕫, h𝕫V, hx⟩
  have hεκ0 : 0 < ε ^ κ := Real.rpow_pos_of_pos hε0 _
  have hts' : t < s' := by
    have : 0 < (17 * ε ^ κ) ^ R.χ * S := by positivity
    linarith
  -- the geodesic `P` in unit-speed form
  have h𝕨F : 𝕨 ∉ F := fun hw => by
    have := mem_ball.1 (hFb hw)
    rw [dist_eq_norm, ← norm_neg, neg_sub] at this
    linarith
  have hne : 𝕫 ≠ 𝕨 := fun he => by
    rw [he, sub_self, norm_zero] at h𝕫𝕨; linarith
  set Pc := geodL (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) with hPcdef
  set L := (D (h ω)).1 (𝕫, 𝕨) with hLdef
  have hPg : IsGeodesicL (D (h ω)) Pc L 𝕫 𝕨 := gm_geodL_isGeodesicL hsel hne
  have hs'L : s' ≤ L := by
    by_contra hlt
    exact h𝕨F (Or.inl (subset_closure (show (D (h ω)).1 (𝕫, 𝕨) < s' from not_le.1 hlt)))
  have htL : t < L := hts'.trans_le hs'L
  have h𝕨K : 𝕨 ∉ K := fun hw => h𝕨F (gm_filledBall_mono _ _ hts'.le hw)
  have hPL : Pc L = 𝕨 := hPg.2.2.1
  -- the arc `I_k ∋ P(t_k)`
  have hPt : Pc t ∈ frontier K := gm_geod_mem_frontier hPg ht0 htL h𝕨K
  rw [← hcov] at hPt
  obtain ⟨x₀, hx₀, hPI⟩ := mem_iUnion₂.1 hPt
  -- `d₀ = (3/2)λ₄ε𝕣`
  have hνε : ε ^ (1 + R.ν) ≤ ε := by
    have := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (show (1 : ℝ) ≤ 1 + R.ν by linarith)
    rwa [Real.rpow_one] at this
  have hlam03 : R.lam 0 ≤ R.lam 3 := (hl01.le.trans hl12).trans hl23
  have hl0ε : R.lam 0 * ε ^ (1 + R.ν) * 𝕣 ≤ R.lam 3 * ε * 𝕣 := by
    have := mul_le_mul hlam03 hνε (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right this h𝕣.le
  have hKne : K.Nonempty :=
    ⟨𝕫, Or.inl (subset_closure (show (D (h ω)).1 (𝕫, 𝕫) < t by
      rw [(D (h ω)).2.self_eq_zero]; exact ht0))⟩
  have hdist : 2 * (R.ℓ * 𝕣) ≤ infDist (Pc L) K := by
    rw [hPL]
    refine (le_infDist hKne).2 fun y hy => ?_
    have h1 := mem_ball.1 (hKb hy)
    have h2 : ‖𝕫 - 𝕨‖ ≤ dist 𝕨 y + dist y 𝕫 := by
      rw [← dist_eq_norm, dist_comm]; exact dist_triangle _ _ _
    linarith
  have hlamε : 4 * R.lam 3 * ε * 𝕣 < 2 * (R.ℓ * 𝕣) := by
    have := mul_lt_mul_of_pos_right h4l h𝕣
    linarith
  have hl3 : (0 : ℝ) < R.lam 3 := by linarith
  have hlε0 : 0 < R.lam 3 * ε * 𝕣 := by positivity
  -- regions
  have hKreg4 : cthickening (4 * R.lam 3 * ε * 𝕣) K ⊆ regRegion R 𝕣 :=
    p412f_cth_reg h𝕫V hKb hℓ𝕣 (by linarith) hlamε
  set ε' := (ε ^ κ / 2) ^ (R.χ' / R.χ) with hε'def
  have hε'0 : 0 < ε' := by positivity
  have hε'ℓ : ε' * 𝕣 ≤ R.ℓ * 𝕣 := mul_le_mul_of_nonneg_right (hε'a.trans haℓ) h𝕣.le
  have hKreg' : cthickening (ε' * 𝕣) K ⊆ regRegion R 𝕣 :=
    p412f_cth_reg h𝕫V hKb hℓ𝕣 (by positivity) (by linarith)
  have hε'pow : ε' ^ R.χ = (ε ^ κ / 2) ^ R.χ' := by
    rw [hε'def, ← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hχ.ne']
  have hreg' : ∀ u ∈ Icc t L, u ≤ t + S * ε' ^ R.χ → Pc u ∈ regRegion R 𝕣 := by
    intro u hu hut
    rw [hε'pow] at hut
    have hu' : u ∈ Icc 0 L := ⟨ht0.le.trans hu.1, hu.2⟩
    have hd := gm_geodL_dist hPg hu'
    have hmem : Pc u ∈ F := Or.inl (subset_closure (show (D (h ω)).1 (𝕫, Pc u) < s' by
      rw [hd]; linarith))
    exact hreg _ ((mem_ball.1 (hFb hmem)).trans (by linarith))
  -- `F = 𝓑^•_{s_{k+1}}`
  have hFc : IsClosed F := jb_isClosed_filledBall (hbd s')
  have hFbd : Bornology.IsBounded F := (jb_isCompact_filledBall (hbd s')).isBounded
  have hFconn : IsConnected Fᶜ := ⟨⟨𝕨, h𝕨F⟩, jb_isPreconnected_compl (hbd s')⟩
  have he2' := p412f_eps2 (κ := κ) (𝕣 := 𝕣) hε0 hχ hχ'
  have hρa : 17 * (ε ^ κ * 𝕣) ≤ a * 𝕣 := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h17a h𝕣.le
  have hen := p412_enbhd_regC3 h3 h𝕣 haℓ hχ hS h𝕫V (hbd t) hKb (by positivity) hρa
    (s' := s') (by
      rw [show 17 * (ε ^ κ * 𝕣) / 𝕣 = 17 * ε ^ κ by field_simp]; exact hA)
  have hKF : cthickening (16 * (2 * ε' ^ (R.χ / R.χ') * 𝕣)) K ⊆ F := by
    rw [he2']
    intro x hx
    refine hen ((mem_cthickening_iff.1 hx).trans_lt ?_)
    have : 0 < ε ^ κ * 𝕣 := by positivity
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  -- the no-hit condition from `G_e`
  have hnohit : ∀ e ∈ E, ∀ u ∈ Ioc t L,
      Pc u ∉ ball (zf e) (17 * (2 * ε' ^ (R.χ / R.χ') * 𝕣)) := by
    intro e he u hu hb
    rw [he2'] at hb
    exact disjoint_left.1 (hG e he) (mem_range_self _)
      ⟨hb, gm_S4_7_not_mem hPg ht0.le h𝕨K hu⟩
  have hz' : ∀ e ∈ E, p412eGoodZ K e (zf e) (2 * ε' ^ (R.χ / R.χ') * 𝕣) := by
    rw [he2']; exact hz
  have Hout := HC n hε1' hεa ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod hrr k hk hKreg4 Pc L 𝕨 hPg h𝕨K
    htL (3 / 2 * R.lam 3 * ε * 𝕣) (by rw [← hεdef]; linarith)
    (by rw [← hεdef]; linarith) (by rw [← hεdef, ← htdef, ← hKdef]; linarith) x₀ hx₀ hPI
    hε'1 hε'a hε'χ hKreg' hreg' F hFc hFbd hFconn hKF L htL
    le_rfl (by rw [hPL]; exact h𝕨F) E zf (hE x₀ hx₀) hz' hnohit
  obtain ⟨z, r, hcand, hEr, hst, u, hu, hPu⟩ := Hout
  have hL0 : 0 < L := ht0.trans htL
  refine p412b_zkE_nonempty ⟨z, r, hcand, hEr, hst, u / L,
    ⟨div_nonneg hu.1 hL0.le, (div_le_one hL0).2 hu.2⟩, ?_⟩
  exact hPu


theorem p412_eq439U
    {a β κ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN)
    (hβ : 0 < β) (hκ : 0 < κ) (hβκ : β < κ * χN / 2) (hUV : UN ⊆ VN)
    (hξ : 0 ≤ ξN) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    ∀ k ≤ p4K R a ε β, ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ κ →
      confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ω ≤
        ENNReal.ofReal (7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) * 𝕣) ∧
      confSigma R.ξ R.c D P h R.p 𝕫 𝕣 ((2 : ℝ)⁻¹ ^ m) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ω ≤
        ENNReal.ofReal (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) ∧
      enbhd (ENNReal.ofReal (16 * (2 : ℝ)⁻¹ ^ m * 𝕣))
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ⊆
        filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) := by
  have hℓ : 0 < ℓN := lt_of_lt_of_le ha0 haℓ
  have hc2 : 0 < regC2N ℓN ξN a := by unfold regC2N; positivity
  have ha2 : 0 < (a / 2) ^ χ'N := by positivity
  have hgapev := gm_small_gap hβ hβκ (show 0 < (7 : ℝ) ^ χN / (a / 2) ^ χ'N by positivity)
  have hβev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ β ≤ a / regC2N ℓN ξN a := by
    have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    rw [Real.zero_rpow hβ.ne'] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))
  have hκev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ κ ≤ min ((a / 7) ^ 2) ((7 / 16) ^ 2) := by
    have := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto
    rw [Real.zero_rpow hκ.ne'] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))
  have hlin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨ε₁, hε₁, hε₁'⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 (((hgapev.and hβev).and hκev).and hlin)
  refine ⟨ε₁, hε₁, ?_⟩
  intro R hRN Ω _ D P h H 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  try simp only [regC2N_eq] at *
  intro ε hε ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd k hk m hm
  obtain ⟨⟨⟨hgap0, hεβ⟩, hεκ⟩, hε01⟩ := hε₁' hε
  have hε0 : 0 < ε := hε01.1
  have hε1 : ε < 1 := hε01.2
  obtain ⟨_, h2, h3, _, _, _, _⟩ := gm_regEvent_mem.1 hω
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
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
  -- the times
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
  have hs't : s' - t = τ * (ε ^ β - ε ^ (2 * β)) := by
    simp only [hs'def, htdef, s4T, s4S, s4Unit]; rw [← hτdef]; push_cast; ring
  have hκχ0 : 0 < ε ^ (κ * R.χ / 2) := Real.rpow_pos_of_pos hε0 _
  have hdiff : (7 : ℝ) ^ R.χ / (a / 2) ^ R.χ' * ε ^ (κ * R.χ / 2) < ε ^ β - ε ^ (2 * β) :=
    hgap0
  have hdiff0 : 0 < ε ^ β - ε ^ (2 * β) :=
    lt_of_le_of_lt (by positivity) hdiff
  have hts' : t < s' := by nlinarith [mul_pos hτ0 hdiff0]
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
  have hK : filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 (2 * (R.ℓ * 𝕣)) :=
    gm_filledBall_subset_ball_of_lt_tauR ht0 (lt_of_lt_of_le hts' hs'2)
  -- the scale `δ = 2^{-m} ≤ ε^κ`
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  have hδ0 : 0 < δ := by positivity
  set e : ℝ := ε ^ κ with hedef
  have he0 : 0 < e := Real.rpow_pos_of_pos hε0 _
  have hsqrt : δ ^ (1 / 2 : ℝ) = Real.sqrt δ := (Real.sqrt_eq_rpow δ).symm
  have hsδe : Real.sqrt δ ≤ Real.sqrt e := Real.sqrt_le_sqrt hm
  have hsa : Real.sqrt e ≤ a / 7 := by
    calc Real.sqrt e ≤ Real.sqrt ((a / 7) ^ 2) := Real.sqrt_le_sqrt (hεκ.trans (min_le_left _ _))
      _ = a / 7 := Real.sqrt_sq (by positivity)
  have hs716 : Real.sqrt e ≤ 7 / 16 := by
    calc Real.sqrt e ≤ Real.sqrt ((7 / 16 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (hεκ.trans (min_le_right _ _))
      _ = 7 / 16 := Real.sqrt_sq (by norm_num)
  have hsδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hδsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ0.le
  have hm7 : 7 * δ ^ (1 / 2 : ℝ) ≤ a := by rw [hsqrt]; linarith
  have hδa : δ ≤ a := by nlinarith
  have h16 : 16 * δ ≤ 7 * δ ^ (1 / 2 : ℝ) := by rw [hsqrt]; nlinarith
  -- the gap `(7δ^{1/2})^χ S < s_{k+1} − t_k`
  have hpow : (7 * δ ^ (1 / 2 : ℝ)) ^ R.χ ≤ (7 : ℝ) ^ R.χ * ε ^ (κ * R.χ / 2) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : δ ^ (1 / 2 : ℝ) ≤ e ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hδ0.le hm (by norm_num)
    calc (δ ^ (1 / 2 : ℝ)) ^ R.χ ≤ (e ^ (1 / 2 : ℝ)) ^ R.χ :=
          Real.rpow_le_rpow (by positivity) h1 hχ.le
      _ = ε ^ (κ * R.χ / 2) := by
          rw [hedef, ← Real.rpow_mul hε0.le, ← Real.rpow_mul hε0.le]; congr 1; ring
  have hgap : t + (7 * δ ^ (1 / 2 : ℝ)) ^ R.χ * S < s' := by
    have h1 : (7 : ℝ) ^ R.χ * ε ^ (κ * R.χ / 2) < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) := by
      have := mul_lt_mul_of_pos_left hdiff ha2
      rwa [← mul_assoc, mul_div_cancel₀ _ ha2.ne'] at this
    have h2' : (7 * δ ^ (1 / 2 : ℝ)) ^ R.χ * S <
        (a / 2) ^ R.χ' * S * (ε ^ β - ε ^ (2 * β)) := by
      calc (7 * δ ^ (1 / 2 : ℝ)) ^ R.χ * S ≤ (7 : ℝ) ^ R.χ * ε ^ (κ * R.χ / 2) * S :=
            mul_le_mul_of_nonneg_right hpow hS.le
        _ < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) * S := mul_lt_mul_of_pos_right h1 hS
        _ = _ := by ring
    have h3' := mul_le_mul_of_nonneg_right hτ hdiff0.le
    linarith
  obtain ⟨hRK, hσ⟩ := p412_step2 (m := m) hω h𝕣 haℓ hχ hS hδa hm7 h𝕫V (hbd t) hK
  refine ⟨hRK, hσ s' hgap, ?_⟩
  -- `B_{16δ𝕣}(𝓑^•_{t_k}) ⊆ 𝓑^•_{s_{k+1}}`
  have hρa : 16 * δ * 𝕣 ≤ a * 𝕣 := mul_le_mul_of_nonneg_right (h16.trans hm7) h𝕣.le
  refine p412_enbhd_regC3 h3 h𝕣 haℓ hχ hS h𝕫V (hbd t) hK (by positivity) hρa ?_
  have h16r : 16 * δ * 𝕣 / 𝕣 = 16 * δ := by field_simp
  rw [h16r]
  have : (16 * δ) ^ R.χ * S ≤ (7 * δ ^ (1 / 2 : ℝ)) ^ R.χ * S :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) h16 hχ.le) hS.le
  linarith

end LQGMetric.GM
