/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6Pair at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6Reg
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6Rate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ConditionalL48

/-!
# `T4_2PairOne` at a fixed scale with all rates discharged (P2-M2K6)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.8 (l. 1756–1780), the proof
of Lemma 4.7 / Lemma 4.21 (l. 1890–1940, 2361–2398), Proposition 4.17 (l. 2404–2433) and the end
of the proof of Theorem 4.2 (l. 2437–2441).

`gm_T42_pairU`: `gm_T42_reg` with `M₈ = 2/ζ + 1`, the bound (4.19) from `gm_L4_8_uncondU` with
`δ = max(C₈, 1) ε^p`, `p = 4M₈ + 4ν + 8 + 2β + 2M`, the rate condition from `gm_T42_rateU`, and
`(K + 1)√δ ≤ (b + 1)√C₈' ε^M` (`K ≤ (a/c₂)ε^{-β}`): on `ℰ_𝕣 ∩ G_𝕫`, the pair has no witness with
probability at most `δ₁ + C ε^M`, `δ₁` the bound of Proposition 4.12. `C` and the threshold `ε₀`
depend only on the numbers and the metric (`γ, D, c'`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric Topology
open LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

open scoped Classical in
/-- **`T4_2PairOne` at a fixed scale, rates discharged** (GM l. 1756–1780, 2361–2441) -/
theorem gm_T42_pairU (hDF43 : DFGPSProp4_3F) (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c')
    {a β θ ν ζ χ χ' ℓ ξ Λ μ B : ℝ} {lam : Fin 5 → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (haℓ : a ≤ ℓ) (hℓ1 : ℓ < 1) (hχ : 0 < χ) (hχ' : 0 < χ') (hβ : 0 < β) (hβχ : β < χ)
    (hlam0 : 0 < lam 0) (hlam : 1 < lam 3)
    (hlam5 : 0 ≤ lam 4) (hξ : 0 ≤ ξ) (hθ : 0 < θ) (hθβ : θ < β) (hζ : 0 < ζ)
    (hβν : 4 * ν + ζ < β) (hν : 0 ≤ ν) (hΛ : 1 ≤ Λ) (hμ : 0 ≤ μ) (M : ℝ) (hM : 0 < M) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] [P.IsComplete]
      {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
      (hh : IsWholePlaneGFF h P)
      (R : RegPar), R.ν = ν → R.χ = χ → R.χ' = χ' → R.lam = lam → R.ℓ = ℓ →
      R.ξ = ξ → R.μ = μ → R.U ⊆ R.V → ∀ {𝕫 𝕨 : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨)
      (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
      (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
      {𝕣 δ₁ : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → 𝕫 ∈ rScale 𝕣 R.U → ‖𝕫‖ ≤ B * 𝕣 →
      4 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
      0 < R.lam 0 → R.lam 0 ≤ 2 → 1 < R.lam 3 → 0 ≤ R.lam 1 → R.lam 1 ≤ 1 → 0 ≤ R.lam 2 →
      R.lam 2 ≤ 1 → 0 ≤ R.lam 4 →
      (∀ r ∈ p4Rads R 𝕣 ε, ε ^ (1 + R.ν) * 𝕣 ≤ r ∧ r ≤ ε * 𝕣) →
      ∀ (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) {ψ₀ : TestC}, ∫ x, ψ₀ x = 1 →
      (∀ ω, h ω ψ₀ = 0) →
      tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball (0 : ℂ) (‖𝕫‖ +
        (4 * R.lam 3 * ε) ^ (-(2 / ζ + 1)) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣 + ε * 𝕣))ᶜ →
      (∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma
        (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
        (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' R.E r z)) →
      (∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔
        MeasurableSpace.comap (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω))
          (Metric.ball z (R.lam 3 * r))) inferInstance) (h ⁻¹' Ef r z 𝕫 𝕨)) →
      (∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, 𝕫 ∉ Metric.ball z (R.lam 3 * r) →
        𝕨 ∉ Metric.ball z (R.lam 3 * r) →
        (fun ω => Λ⁻¹ * (P[(h ⁻¹' R.E r z ∩
            {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
            (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ]) ω) ≤ᵐ[P]
          P[(h ⁻¹' Ef r z 𝕫 𝕨 ∩
            {ω | (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}).indicator
            (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z (R.lam 2 * r))ᶜ]) →
      P.real (p412Bad D sel P h H R 𝕫 𝕨 𝕣 a ε β θ) ≤ δ₁ →
      P.real ((regEvent D P h H R 𝕣 a ∩ gmGoodPt D h H 𝕣 𝕫) ∩
          {ω | ¬ t42Wit sel h Ef R.lam R.rr R.μ 𝕣 ε 𝕫 𝕨 ω}) ≤
        δ₁ + C * ε ^ M := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le ha0 haℓ
  have hl3 : 0 < lam 3 := by linarith
  have hM₈0 : (0 : ℝ) < 2 / ζ + 1 := by positivity
  have hM₈ : 2 / ζ < 2 / ζ + 1 := by linarith
  have hp0 : (0 : ℝ) < 4 * (2 / ζ + 1) + 4 * ν + 8 + 2 * β + 2 * M := by positivity
  obtain ⟨C₈, ε₈, hε₈, H48⟩ := gm_L4_8_uncondU hDF43 hγ hγ2 hD hM₈0 (lam1 := lam 0)
    (lam4 := lam 3) (ν := ν) (by linarith) _ hp0
  have hC₈' : 0 ≤ max C₈ 1 := le_trans zero_le_one (le_max_right _ _)
  obtain ⟨εr, hεr, HR⟩ := gm_T42_rateU (Λ := Λ) (ν := ν) (ζ := ζ) (μ := μ) (B := B)
    (p := 4 * (2 / ζ + 1) + 4 * ν + 8 + 2 * β + 2 * M) hΛ hν hζ hM₈0 hM₈ hlam0 hl3 hμ hC₈'
    (by linarith)
  obtain ⟨εg, hεg, HG⟩ := gm_T42_reg (lam := lam) (χ := χ) (χ' := χ') (ℓ := ℓ) (ξ := ξ) ha0 ha1
    haℓ hχ hχ' hβ hβχ hlam hlam5 hξ hθ hθβ hζ hβν M
  have hb0 : 0 < a / ((ℓ / a + 1) * Real.exp (ξ / a)) := by positivity
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (4 * lam 3 * ε) ^ (2 / ζ + 1) ≤ 1 / 3 ∧ ε ∈ Ioo 0 1 := by
    have t : Tendsto (fun ε : ℝ => (4 * lam 3 * ε) ^ (2 / ζ + 1)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => 4 * lam 3 * ε) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => 4 * lam 3 * ε) (𝓝 0) (𝓝 (4 * lam 3 * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 := (Real.continuousAt_rpow_const 0 (2 / ζ + 1) (Or.inr hM₈0.le)).tendsto
      rw [Real.zero_rpow hM₈0.ne'] at h2
      exact h2.comp h1
    exact (t.eventually (Iic_mem_nhds (by norm_num))).and (Ioo_mem_nhdsGT one_pos)
  obtain ⟨εe, hεe, HE⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  refine ⟨(a / ((ℓ / a + 1) * Real.exp (ξ / a)) + 1) * Real.sqrt (max C₈ 1) + 2,
    min (min ε₈ εr) (min εg εe), by positivity,
    lt_min (lt_min hε₈ hεr) (lt_min hεg hεe), ?_⟩
  intro ε hε Ω _ P _ _ h H hh R hRν hRχ hRχ' hRlam hRℓ hRξ hRμ hUV 𝕫 𝕨 h𝕫𝕨 sel hη 𝕣 δ₁ h𝕣 hc
    h𝕫 h𝕫B h4ℓ hl0 hl02 hl3' hl1 hl11 hl2 hl21 hl4 hRadsI Ef ψ₀ hψ₀ h0 hψ hE2 hEf2 h4 h412
  subst hRν hRlam
  have hε0 : 0 < ε := hε.1
  have hε8 : ε ∈ Ioo 0 ε₈ := ⟨hε0, hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hεr' : ε ∈ Ioo 0 εr := ⟨hε0, hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hεg' : ε ∈ Ioo 0 εg := ⟨hε0, hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  obtain ⟨hεM, hε01⟩ := HE ⟨hε0, hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  -- the radii as a `Finset`
  set Rads : Finset ℝ := (Finset.range ⌊R.μ * Real.logb 8 ε⁻¹⌋₊).image (R.rr 𝕣 ε) with hRadsdef
  have hRads : (Rads : Set ℝ) = p4Rads R 𝕣 ε := by
    rw [hRadsdef, Finset.coe_image, Finset.coe_range, p4Rads]
  set δ := max C₈ 1 * ε ^ (4 * (2 / ζ + 1) + 4 * R.ν + 8 + 2 * β + 2 * M) with hδdef
  have hεp : 0 < ε ^ (4 * (2 / ζ + 1) + 4 * R.ν + 8 + 2 * β + 2 * M) := Real.rpow_pos_of_pos hε0 _
  have hδ0 : 0 < δ := mul_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) hεp
  have hL48 := H48 P h hh 𝕫 𝕨 ε hε8 𝕣 h𝕣
  replace hL48 := hL48.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left C₈ 1) hεp.le))
  obtain ⟨hrate, hrate1⟩ := HR ε hεr' R rfl rfl rfl hRμ 𝕣 h𝕣 𝕫 h𝕫B
    Rads hRads δ hδ0.le le_rfl
  have hM8c : 3 * R.ℓ ≤ (4 * R.lam 3 * ε) ^ (-(2 / ζ + 1)) := by
    rw [hRℓ, Real.rpow_neg (by positivity)]
    have hx0 : 0 < (4 * R.lam 3 * ε) ^ (2 / ζ + 1) := Real.rpow_pos_of_pos (by positivity) _
    rw [le_inv_comm₀ (by positivity) hx0]
    calc (4 * R.lam 3 * ε) ^ (2 / ζ + 1) ≤ 1 / 3 := hεM
      _ ≤ (3 * ℓ)⁻¹ := by
        rw [one_div]; exact inv_anti₀ (by positivity) (by linarith)
  have key := HG ε hεg' h38 hC24 hC27 hC14 hγ hγ2 hD hh R rfl hRχ hRχ' rfl hRℓ hRξ hUV h𝕫𝕨
    sel hη (𝕣 := 𝕣) (M₈ := 2 / ζ + 1) (δ := δ) (δ₁ := δ₁) h𝕣 hc h𝕫 h4ℓ hM8c hδ0 hl0 hl02 hl3'
    hl1 hl11 hl2 hl21 hl4 hRadsI Ef (Λ := Λ) (by linarith) hψ₀ h0 hψ hE2 hEf2 h4 Rads hRads hL48
    h412 hrate hrate1
  refine key.trans ?_
  -- `(K + 1)√δ + 2ε^M ≤ ((b + 1)√C₈' + 2) ε^M`
  set b := a / ((ℓ / a + 1) * Real.exp (ξ / a)) with hbdef
  have hc2 : regC2const R a = (ℓ / a + 1) * Real.exp (ξ / a) := by
    rw [regC2const, hRℓ, hRξ]
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have hεβ1 : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε01.2.le
    (by linarith)
  have hK : ((p4K R a ε β : ℕ) : ℝ) + 1 ≤ (b + 1) * ε ^ (-β) := by
    have h1 : ((p4K R a ε β : ℕ) : ℝ) ≤ b * ε ^ (-β) := by
      have hx : 0 ≤ a / regC2const R a * ε ^ (-β) := by rw [hc2]; positivity
      have : ((p4K R a ε β : ℕ) : ℝ) ≤ (⌊a / regC2const R a * ε ^ (-β)⌋₊ : ℝ) := by
        exact_mod_cast Nat.sub_le _ _
      rw [hc2] at this hx
      exact this.trans (Nat.floor_le hx)
    calc ((p4K R a ε β : ℕ) : ℝ) + 1 ≤ b * ε ^ (-β) + ε ^ (-β) := by linarith
      _ = (b + 1) * ε ^ (-β) := by ring
  have hsq : Real.sqrt δ = Real.sqrt (max C₈ 1) *
      ε ^ ((4 * (2 / ζ + 1) + 4 * R.ν + 8 + 2 * β + 2 * M) / 2) := by
    rw [hδdef, Real.sqrt_mul hC₈', Real.sqrt_eq_rpow (ε ^ _), ← Real.rpow_mul hε0.le]
    congr 2; ring
  have hexp : ε ^ (-β) * ε ^ ((4 * (2 / ζ + 1) + 4 * R.ν + 8 + 2 * β + 2 * M) / 2) ≤ ε ^ M := by
    rw [← Real.rpow_add hε0]
    refine Real.rpow_le_rpow_of_exponent_ge hε0 hε01.2.le ?_
    have : 0 ≤ 2 / ζ + 1 := hM₈0.le
    linarith
  have hsC : 0 ≤ Real.sqrt (max C₈ 1) := Real.sqrt_nonneg _
  have hb1 : 0 ≤ b + 1 := by positivity
  have hsδ : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  calc δ₁ + (((p4K R a ε β : ℕ) : ℝ) + 1) * Real.sqrt δ + 2 * ε ^ M
      ≤ δ₁ + (b + 1) * ε ^ (-β) * Real.sqrt δ + 2 * ε ^ M := by
        have := mul_le_mul_of_nonneg_right hK hsδ; linarith
    _ = δ₁ + (b + 1) * Real.sqrt (max C₈ 1) *
          (ε ^ (-β) * ε ^ ((4 * (2 / ζ + 1) + 4 * R.ν + 8 + 2 * β + 2 * M) / 2)) + 2 * ε ^ M := by
        rw [hsq]; ring
    _ ≤ δ₁ + (b + 1) * Real.sqrt (max C₈ 1) * ε ^ M + 2 * ε ^ M := by
        have := mul_le_mul_of_nonneg_left hexp (mul_nonneg hb1 hsC); linarith
    _ = δ₁ + ((b + 1) * Real.sqrt (max C₈ 1) + 2) * ε ^ M := by ring

end LQGMetric.GM
