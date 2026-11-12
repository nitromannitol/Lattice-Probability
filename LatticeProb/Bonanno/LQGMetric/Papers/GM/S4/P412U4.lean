/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412U4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412U3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jAsm

/-!
# `P412jGoodU`: the good-`k` step of GM Prop 4.12 with a uniform threshold (P2-M2J2i, part 4)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3–4 (l. 2155–2199) and
the proof of Prop 4.12 (l. 2212–2276). Primed copies (`…U`, same proofs, `∃ ε₁` before `R`, the
space and `𝕣`; see P412U1.lean) of `p412f_propA` (P412fPropA), `p412f_good_near` (P412fGood) and
`p412i_good_k` (P412iGood), and **`p412j_goodU : P412jGoodU`** (P412jAsm.lean).
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

theorem p412f_propAU
    {a β κ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN)
    (hχχ : χN ≤ χ'N) (hβ : 0 < β) (hκ : 0 < κ) (hβκ : β < κ * χN / 4) (hUV : UN ⊆ VN)
    (hξ : 0 ≤ ξN) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ (A : ℝ) (m : ℕ), A * ε ^ κ ≤ (2 : ℝ)⁻¹ ^ m →
    (2 : ℝ)⁻¹ ^ m ≤ 36 * ε ^ κ → ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, ∀ 𝕨 : ℂ, 4 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
    H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) → ∀ k ≤ p4K R a ε β, ∀ x : ℂ,
    (confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
        (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ω ≤
        Metric.ediam (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) →
      ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
        y ∉ enbhd (confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ω)
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) →
        IsGeodesicL (D (h ω)) Q L 𝕫 y → ∀ u ∈ Icc 0 L,
          Q u ∉ ball x ((2 : ℝ)⁻¹ ^ m * 𝕣) \ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) →
    Disjoint (range (sel 𝕫 𝕨 (h ω)))
      (ball x (A * (ε ^ κ * 𝕣)) \ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) := by
  have hℓ : 0 < ℓN := lt_of_lt_of_le ha0 haℓ
  obtain ⟨ε₁, hε₁, H439⟩ := p412_eq439U (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1 haℓ
    hχ hβ (κ := κ / 2) (by positivity) (by linarith) hUV  hξ
  obtain ⟨ε₂, hε₂, HT⟩ := p412f_timesU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1 haℓ
    hχ hχχ hβ hκ (by nlinarith) hUV  hξ
  have t0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have tκ : Tendsto (fun ε : ℝ => ε ^ (κ / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    t0.rpow_const_nhds_zero (by positivity)
  have t34 : Tendsto (fun ε : ℝ => 36 * ε ^ (κ / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tκ.const_mul 36
  have t7 : Tendsto (fun ε : ℝ => 7 * (ε ^ (κ / 2)) ^ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tκ.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 7
  obtain ⟨ε₃, hε₃, HS⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    ((t34.eventually (Iic_mem_nhds one_pos)).and (t7.eventually (gt_mem_nhds hℓ)))
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro R hRN Ω _ D P h H sel 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace H439 := H439 R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  replace HT := HT R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  try simp only [regC2N_eq] at *
  intro ε hε A m hm17 hm34 ω hω 𝕫 h𝕫 𝕨 h𝕫𝕨 hH0 hH𝕫 hL hbd hsel k hk x hA
  have hε0 : 0 < ε := hε.1
  obtain ⟨h34, h7⟩ := HS ⟨hε0, hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  set K := filledBall (D (h ω)) 𝕫 t with hKdef
  have hδ0 : 0 < δ := by positivity
  have he2 : ε ^ κ = ε ^ (κ / 2) * ε ^ (κ / 2) := by
    rw [← Real.rpow_add hε0]; ring_nf
  have he0 : 0 < ε ^ (κ / 2) := Real.rpow_pos_of_pos hε0 _
  have hδκ : δ ≤ ε ^ (κ / 2) := by
    have := mul_le_mul_of_nonneg_right h34 he0.le
    rw [he2] at hm34; nlinarith
  obtain ⟨hRK, -, -⟩ := H439 ε ⟨hε0, hε.2.trans_le (min_le_left _ _)⟩ ω hω 𝕫 h𝕫 hH0 hH𝕫 hL
    hbd k hk m hδκ
  obtain ⟨-, -, ht0, hKb, -, -⟩ := HT ε ⟨hε0, hε.2.trans_le ((min_le_right _ _).trans
    (min_le_left _ _))⟩ ω hω 𝕫 h𝕫 hH0 hH𝕫 hL k hk
  have h7δ : 7 * δ ^ (1 / 2 : ℝ) * 𝕣 ≤ R.ℓ * 𝕣 := by
    refine mul_le_mul_of_nonneg_right ?_ h𝕣.le
    have := Real.rpow_le_rpow hδ0.le hδκ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  -- `diam 𝓑^•_{t_k} ≥ ℓ𝕣` (`t_k > τ_{ℓ𝕣}`)
  obtain ⟨_, _, h3, _⟩ := gm_regEvent_mem.1 hω
  have hτ := p412b_tau_ge h3 h𝕣 ha0 haℓ hUV hc h𝕫 hL
  have hτ0 : 0 < tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
    lt_of_lt_of_le (mul_pos (by positivity) (mul_pos hc (Real.exp_pos _))) hτ
  have htτ : tauR D h 𝕫 (R.ℓ * 𝕣) ω < t := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε0.le β)
    have h2 : 0 < ε ^ (2 * β) * tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
      mul_pos (Real.rpow_pos_of_pos hε0 _) hτ0
    simp only [htdef, s4T, s4S, s4Unit]
    nlinarith
  obtain ⟨q, -, hqt, hq⟩ := (gm_tauR_lt_iff D h 𝕫 (R.ℓ * 𝕣) ω t).1 htτ
  obtain ⟨w, hwq, hwb⟩ := not_subset.1 hq
  have hwK : w ∈ K := gm_filledBall_mono _ _ hqt.le hwq
  have h𝕫K : 𝕫 ∈ K := Or.inl (subset_closure (show (D (h ω)).1 (𝕫, 𝕫) < t by
    rw [(D (h ω)).2.self_eq_zero]; exact ht0))
  have hdiam : ENNReal.ofReal (R.ℓ * 𝕣) ≤ Metric.ediam K := by
    refine le_trans ?_ (edist_le_ediam_of_mem hwK h𝕫K)
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (not_lt.1 hwb)
  have hRKd := hRK.trans ((ENNReal.ofReal_le_ofReal h7δ).trans hdiam)
  -- `𝕨` is far from `𝓑^•_{t_k}`
  have h𝕨 : 𝕨 ∉ enbhd (confRK R.ξ R.c D P h R.p 𝕣 δ K ω) K := by
    intro hmem
    refine not_le.2 (lt_of_lt_of_le hmem hRK) ?_
    refine Metric.le_infEDist.2 fun y hy => ?_
    have h1 := mem_ball.1 (hKb hy)
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : ‖𝕫 - 𝕨‖ ≤ dist 𝕨 y + dist y 𝕫 := by
      rw [← dist_eq_norm, dist_comm]; exact dist_triangle _ _ _
    have := mul_pos hℓ h𝕣
    have h7' : 7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) * 𝕣 ≤ R.ℓ * 𝕣 := h7δ
    linarith
  -- the path
  have hne : 𝕫 ≠ 𝕨 := fun he => by
    rw [he, sub_self, norm_zero] at h𝕫𝕨; nlinarith
  have hPg := gm_geodL_isGeodesicL hsel hne
  have hL0 : 0 < (D (h ω)).1 (𝕫, 𝕨) :=
    lt_of_le_of_ne (gm_D_nonneg _ _ _) (fun h0 => hne ((D (h ω)).2.eq_of_eq_zero _ _ h0.symm))
  have hAω := hA hRKd 𝕨 _ _ h𝕨 hPg
  rw [disjoint_left]
  rintro _ ⟨ζ, rfl⟩ ⟨hb, hK⟩
  have hζ : geodL (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ((ζ : ℝ) * (D (h ω)).1 (𝕫, 𝕨)) =
      sel 𝕫 𝕨 (h ω) ζ := by
    simp only [geodL, mul_div_cancel_right₀ _ hL0.ne', projIcc_val]
  refine hAω ((ζ : ℝ) * (D (h ω)).1 (𝕫, 𝕨))
    ⟨mul_nonneg ζ.2.1 hL0.le, mul_le_of_le_one_left hL0.le ζ.2.2⟩ ?_
  rw [hζ]
  refine ⟨mem_ball.2 ((mem_ball.1 hb).trans_le ?_), hK⟩
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hm17 h𝕣.le


theorem p412f_good_nearU
    {a β κ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hl0 : 0 < lamN 0) (hl01 : lamN 0 < lamN 1)
    (hl12 : lamN 1 ≤ lamN 2) (hl23 : lamN 2 ≤ lamN 3) (hlam : 1 < lamN 3)
    (hν : 0 ≤ νN) (hUV : UN ⊆ VN) (hξ : 0 ≤ ξN) (hχχ : χN ≤ χ'N)
    (hκ : 0 < κ) (hβκ : β < κ * χN / 4)
    (he1 : κ * (χ'N / χN) < χN / χ'N) (he2 : κ * (χ'N / χN) < 1) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₁ →
    ∀ m : ℕ, 18 * ((2 : ℝ)⁻¹ ^ n) ^ κ ≤ (2 : ℝ)⁻¹ ^ m → (2 : ℝ)⁻¹ ^ m ≤ 36 * ((2 : ℝ)⁻¹ ^ n) ^ κ →
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
    ∀ Z : Set ℂ,
    (∀ e ∈ p412fEndSet (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
        (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω), ∃ x ∈ Z, ∃ z : ℂ,
      p412eGoodZ (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) e z
        (((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣) ∧ dist z x ≤ ((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣) →
    (∀ x ∈ Z,
      confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ω ≤
          Metric.ediam (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
        ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
          y ∉ enbhd (confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
            (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ω)
            (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
          IsGeodesicL (D (h ω)) Q L 𝕫 y → ∀ u ∈ Icc 0 L,
            Q u ∉ ball x ((2 : ℝ)⁻¹ ^ m * 𝕣) \
              filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
    (zkE D sel h R 𝕫 𝕨 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω).Nonempty := by
  obtain ⟨ε₁, hε₁, HC⟩ := p412f_coreU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)

    ha0 ha1 haℓ hχ hχ' hβ hβχ hl0 hl01 hl12 hl23 hlam hν hUV  hξ hχχ hκ (by nlinarith)
    he1 he2
  obtain ⟨ε₂, hε₂, HA⟩ := p412f_propAU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)

    ha0 ha1 haℓ hχ hχχ hβ hκ hβκ hUV  hξ
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro R hRN Ω _ D P h H sel 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace HC := HC R (regNum_self R) (D := D) (P := P) (h := h) (H := H) (sel := sel) h𝕣 hc
  replace HA := HA R (regNum_self R) (D := D) (P := P) (h := h) (H := H) (sel := sel) h𝕣 hc
  try simp only [regC2N_eq] at *
  intro n hn m hm18 hm36 ω hω 𝕫 h𝕫 𝕨 h𝕫𝕨 hH0 hH𝕫 hL hbd hgeod hrr hsel k hk hcov Z hZ hZA
  classical
  have hε0 : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  set K := filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) with hK
  set e₀ : ℝ := ((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣 with he₀
  set Pz : ℂ → ℂ × ℂ → Prop := fun e xz => xz.1 ∈ Z ∧ p412eGoodZ K e xz.2 e₀ ∧
    dist xz.2 xz.1 ≤ e₀ with hPz
  set xz : ℂ → ℂ × ℂ := fun e => if he : ∃ p, Pz e p then he.choose else (0, 0) with hxz
  have hxz' : ∀ e ∈ p412fEndSet (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
      (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω), Pz e (xz e) := by
    intro e he
    have hex : ∃ p, Pz e p := by
      obtain ⟨x, hx, z, hz, hd⟩ := hZ e he
      exact ⟨(x, z), hx, hz, hd⟩
    simp only [hxz, hex, ↓reduceDIte]
    exact hex.choose_spec
  refine HC n (hn.trans_le (min_le_left _ _)) ω hω 𝕫 h𝕫 𝕨 h𝕫𝕨 hH0 hH𝕫 hL hbd hgeod hrr hsel
    k hk hcov _ (fun e => (xz e).2) (fun x₀ hx₀ => p412f_endpts_subset_endSet hx₀)
    (fun e he => (hxz' e he).2.1) (fun e he => ?_)
  have hD := HA _ ⟨hε0, hn.trans_le (min_le_right _ _)⟩ 18 m hm18 hm36 ω hω 𝕫 h𝕫 𝕨 h𝕫𝕨 hH0
    hH𝕫 hL hbd hsel k hk (xz e).1 (hZA _ (hxz' e he).1)
  refine hD.mono_right (diff_subset_diff_left (ball_subset_ball' ?_))
  have := (hxz' e he).2.2
  linarith


theorem p412i_good_kU
    {a β κ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hl0 : 0 < lamN 0) (hl01 : lamN 0 < lamN 1)
    (hl12 : lamN 1 ≤ lamN 2) (hl23 : lamN 2 ≤ lamN 3) (hlam : 1 < lamN 3)
    (hν : 0 ≤ νN) (hUV : UN ⊆ VN) (hξ : 0 ≤ ξN) (hχχ : χN ≤ χ'N)
    (hκ : 0 < κ) (hβκ : β < κ * χN / 4)
    (he1 : κ * (χ'N / χN) < χN / χ'N) (he2 : κ * (χ'N / χN) < 1) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₁ →
    ∀ m : ℕ, 18 * ((2 : ℝ)⁻¹ ^ n) ^ κ ≤ (2 : ℝ)⁻¹ ^ m → (2 : ℝ)⁻¹ ^ m ≤ 36 * ((2 : ℝ)⁻¹ ^ n) ^ κ →
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
    ∀ (N L : ℕ) (x : ℕ → Ω → ℂ) (G : ℕ → Set Ω),
    (∀ e ∈ p412fEndSet (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
        (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω), ∃ j < N, ∃ z : ℂ,
      p412eGoodZ (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) e z
        (((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣) ∧ dist z (x j ω) ≤ ((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣) →
    (∀ j, ω ∈ G j → confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ω ≤
          Metric.ediam (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
        ∀ (y : ℂ) (Q : ℝ → ℂ) (Lq : ℝ),
          y ∉ enbhd (confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
            (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ω)
            (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
          IsGeodesicL (D (h ω)) Q Lq 𝕫 y → ∀ u ∈ Icc 0 Lq,
            Q u ∉ ball (x j ω) ((2 : ℝ)⁻¹ ^ m * 𝕣) \
              filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
    ω ∈ (⋂ j ∈ Finset.range N, G j) ∪
          {ω | ENNReal.ofReal (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β (k + 1) ω) <
            confSigma R.ξ R.c D P h R.p 𝕫 𝕣 ((2 : ℝ)⁻¹ ^ m)
              (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) ω} ∪
          {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (h ω)) 𝕫
            (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
            (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)).encard} →
    (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
        (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)).encard ≤ L →
    (zkE D sel h R 𝕫 𝕨 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω).Nonempty := by
  obtain ⟨ε₁, hε₁, HG⟩ := p412f_good_nearU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)

    ha0 ha1 haℓ hχ hχ' hβ hβχ hl0 hl01 hl12 hl23 hlam hν hUV  hξ hχχ hκ hβκ he1 he2
  obtain ⟨ε₂, hε₂, H39⟩ := p412_eq439U (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1 haℓ hχ
    hβ (half_pos hκ) (by linarith) hUV  hξ
  obtain ⟨ε₃, hε₃, hsm⟩ := p412i_small_pow hκ
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro R hRN Ω _ D P h H sel 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace HG := HG R (regNum_self R) (D := D) (P := P) (h := h) (H := H) (sel := sel) h𝕣 hc
  replace H39 := H39 R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  try simp only [regC2N_eq] at *
  intro n hn m hm18 hm36 ω hω 𝕫 h𝕫 𝕨 h𝕫𝕨 hH0 hH𝕫 hL hbd hgeod hrr hsel k hk hcov N L x G
    hZ hGA hAk hconf
  have hn1 : (2 : ℝ)⁻¹ ^ n < ε₁ := lt_of_lt_of_le hn (min_le_left _ _)
  have hn2 : (2 : ℝ)⁻¹ ^ n < ε₂ := lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_left _ _))
  have hn3 : (2 : ℝ)⁻¹ ^ n < ε₃ :=
    lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_right _ _))
  have hpos : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  have hmκ : (2 : ℝ)⁻¹ ^ m ≤ ((2 : ℝ)⁻¹ ^ n) ^ (κ / 2) :=
    hm36.trans (hsm _ ⟨hpos, hn3⟩)
  have hσ := (H39 _ ⟨hpos, hn2⟩ ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd k hk m hmκ).2.1
  have hG : ∀ j < N, ω ∈ G j := by
    rcases hAk with (hI | hσ') | hC
    · intro j hj
      exact mem_iInter₂.1 hI j (Finset.mem_range.2 hj)
    · exact absurd hσ (not_le.2 hσ')
    · exact absurd hconf (not_le.2 hC)
  refine HG n hn1 m hm18 hm36 ω hω 𝕫 h𝕫 𝕨 h𝕫𝕨 hH0 hH𝕫 hL hbd hgeod hrr hsel k hk hcov
    ((fun j => x j ω) '' Iio N) (fun e he => ?_) ?_
  · obtain ⟨j, hj, z, hz, hd⟩ := hZ e he
    exact ⟨x j ω, ⟨j, hj, rfl⟩, z, hz, hd⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact hGA j (hG j hj)

/-- **`P412jGoodU`** (`p412i_good_k` with `ε₁` chosen before `E, rr`, the space and `𝕣`), from
`p412i_good_kU` -/
theorem p412j_goodU : P412jGoodU := by
  intro R₀ a β κ ha0 ha1 haℓ hχ hχ' hβ hβχ hl0 hl01 hl12 hl23 hlam hν hUV hξ hχχ hκ hβκ he1 he2
  obtain ⟨ε₁, hε₁, HG⟩ := p412i_good_kU (ξN := R₀.ξ) (cN := R₀.c) (pN := R₀.p) (χN := R₀.χ)
    (χ'N := R₀.χ') (μN := R₀.μ) (νN := R₀.ν) (lamN := R₀.lam) (ℓN := R₀.ℓ) (UN := R₀.U)
    (VN := R₀.V) ha0 ha1 haℓ hχ hχ' hβ hβχ hl0 hl01 hl12 hl23 hlam hν hUV hξ hχχ hκ hβκ he1 he2
  refine ⟨ε₁, hε₁, fun E rr R hR => ?_⟩
  intro Ω _ D P h H sel 𝕣 h𝕣 hc
  subst hR
  exact HG { R₀ with E := E, rr := rr } (regNum_self _) h𝕣 hc

end LQGMetric.GM
