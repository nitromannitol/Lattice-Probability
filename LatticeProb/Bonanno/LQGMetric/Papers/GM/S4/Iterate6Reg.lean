/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6Reg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6FkU
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6L47S
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4RegWG

/-!
# `T4_2PairOne` at a fixed scale on the regularity event (P2-M2K6)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.19 (l. 2318–2327), the
proof of Proposition 4.17 (l. 2404–2433) and the end of the proof of Thm 4.2 (l. 2437–2441).

`gm_T42_reg`: `gm_T42_fixedS` (slack `sl = 𝕣`, Iterate6L47S.lean) with `Reg := ℰ_𝕣 ∩ G_𝕫`
(`G_𝕫`, `gmGoodPt`: the a.s. properties
`H = h_·(·)` at `(𝕣, 0)`, `(𝕣, 𝕫)`, length metric, bounded balls, geodesics from `𝕫`),
`K := p4K` (GM (4.35)), `L := 3ℓ𝕣`: the hypotheses `Reg ⊆ F_k` (`gm_regEvent_subset_gmFkU`),
the `W ∩ G` conditions and `𝓑^•_{t_k} ⊆ B_L(𝕫)` (`gm_regEvent_WG`), `1 ≤ K`, `bε^{-β} ≤ K + 2`
(`b = a/c₂`) and `L + 3λ₄ε𝕣 < |𝕫 − 𝕨|` (from `|𝕫 − 𝕨| ≥ 4ℓ𝕣`) are discharged, and the P4.12
bound is taken on GM's event `p412Bad` itself. The threshold `ε₀` depends only on the numbers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric Topology
open LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

/-- the a.s. properties at `𝕫` used on `ℰ_𝕣` (GM Lemmas 4.19, 4.22) -/
def gmGoodPt {Ω : Type} (D : DistC → ContMetric) (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ) (𝕣 : ℝ)
    (𝕫 : ℂ) : Set Ω :=
  {ω | H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 ∧ H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 ∧ (D (h ω)).IsLength ∧
    (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) ∧
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y)}

open scoped Classical in
/-- **`T4_2PairOne` at a fixed scale on `ℰ_𝕣`** (GM l. 2318–2327, 2361–2441) -/
theorem gm_T42_reg {a β θ ν ζ χ χ' ℓ ξ : ℝ} {lam : Fin 5 → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (haℓ : a ≤ ℓ) (hχ : 0 < χ) (hχ' : 0 < χ') (hβ : 0 < β) (hβχ : β < χ) (hlam : 1 < lam 3)
    (hlam5 : 0 ≤ lam 4) (hξ : 0 ≤ ξ) (hθ : 0 < θ) (hθβ : θ < β) (hζ : 0 < ζ)
    (hβν : 4 * ν + ζ < β) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
    ∀ (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7) (hC14 : CONFThm1_4)
      {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
      (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] [P.IsComplete] {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
      (hh : IsWholePlaneGFF h P)
      (R : RegPar), R.ν = ν → R.χ = χ → R.χ' = χ' → R.lam = lam → R.ℓ = ℓ →
      R.ξ = ξ → R.U ⊆ R.V → ∀ {𝕫 𝕨 : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨)
      (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
      (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
      {𝕣 M₈ δ δ₁ : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → 𝕫 ∈ rScale 𝕣 R.U →
      4 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ → 3 * R.ℓ ≤ (4 * R.lam 3 * ε) ^ (-M₈) → 0 < δ →
      0 < R.lam 0 → R.lam 0 ≤ 2 → 1 < R.lam 3 → 0 ≤ R.lam 1 → R.lam 1 ≤ 1 → 0 ≤ R.lam 2 →
      R.lam 2 ≤ 1 → 0 ≤ R.lam 4 →
      (∀ r ∈ p4Rads R 𝕣 ε, ε ^ (1 + R.ν) * 𝕣 ≤ r ∧ r ≤ ε * 𝕣) →
      ∀ (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) {Λ : ℝ}, 0 < Λ → ∀ {ψ₀ : TestC}, ∫ x, ψ₀ x = 1 →
      (∀ ω, h ω ψ₀ = 0) →
      tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball (0 : ℂ) (‖𝕫‖ +
        (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣 + ε * 𝕣))ᶜ →
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
      ∀ (Rads : Finset ℝ), (Rads : Set ℝ) = p4Rads R 𝕣 ε →
      P {ω | ∀ t : ℝ, 0 < t →
        filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 ((4 * R.lam 3 * ε) ^ (-M₈) * 𝕣) →
        𝕨 ∉ filledBall (D (h ω)) 𝕫 t → ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) G L 𝕫 𝕨 →
        ∀ σ : ℝ, 0 < σ → σ ≤ R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 →
        ∀ Rads : Finset ℝ, (∀ r ∈ Rads, 2 * σ ≤ r ∧ r ≤ ε * 𝕣) →
        ∀ S : Finset (ℂ × ℝ), (∀ p ∈ S, p ∈ candSet (filledBall (D (h ω)) 𝕫 t) (R.lam 0)
            (R.lam 3) ε R.ν 𝕣 (Rads : Set ℝ) ∧ (G '' Icc 0 L ∩ ball p.1 p.2).Nonempty) →
        (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤
          Rads.card * ENNReal.ofReal ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2)}ᶜ ≤
        ENNReal.ofReal δ →
      P.real (p412Bad D sel P h H R 𝕫 𝕨 𝕣 a ε β θ) ≤ δ₁ →
      ε ^ (2 * ν + ζ / 2) ≤
        (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹ / 2 -
        ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣)).ncard
          : ℝ) * Real.sqrt δ /
        (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1) →
      (Λ * (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1))⁻¹ / 2 -
        ((gmCandSet R 𝕣 ε (‖𝕫‖ + (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 + 2 * R.lam 3 * ε * 𝕣 + 𝕣)).ncard
          : ℝ) * Real.sqrt δ /
        (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M₈) * 𝕣 ^ 2) /
          (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 + 1) ≤ 1 →
      P.real ((regEvent D P h H R 𝕣 a ∩ gmGoodPt D h H 𝕣 𝕫) ∩
          {ω | ¬ t42Wit sel h Ef R.lam R.rr R.μ 𝕣 ε 𝕫 𝕨 ω}) ≤
        δ₁ + (p4K R a ε β + 1) * Real.sqrt δ + 2 * ε ^ M := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le ha0 haℓ
  have hb0 : 0 < a / ((ℓ / a + 1) * Real.exp (ξ / a)) := by positivity
  obtain ⟨ε₀, hε₀, HF⟩ := gm_T42_fixedS hb0 hθ hθβ hζ hβν M
  obtain ⟨ε₁, hε₁, HU⟩ := gm_regEvent_subset_gmFkU (χ := χ) (χ' := χ') (lam := lam) ha0 ha1
    haℓ hχ hχ' hβ hβχ hlam hlam5 hξ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε ^ β ≤ a / ((ℓ / a + 1) * Real.exp (ξ / a)) / 2 ∧ ε ∈ Ioo 0 (min 1 (ℓ / (3 * lam 3))) := by
    have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    rw [Real.zero_rpow hβ.ne'] at this
    exact ((this.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))).and
      (Ioo_mem_nhdsGT (lt_min one_pos (by have : 0 < lam 3 := by linarith
                                          positivity)))
  obtain ⟨ε₂, hε₂, H2⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  refine ⟨min (min ε₀ ε₁) ε₂, lt_min (lt_min hε₀ hε₁) hε₂, ?_⟩
  intro ε hε h38 hC24 hC27 hC14 γ D c' hγ hγ2 hD Ω _ P _ _ h H hh R hRν hRχ hRχ' hRlam hRℓ hRξ
    hUV 𝕫 𝕨 h𝕫𝕨 sel hη 𝕣 M₈ δ δ₁ h𝕣 hc h𝕫 h4ℓ hM8 hδ hl0 hl02 hl3 hl1 hl11 hl2 hl21 hl4 hRadsI
    Ef Λ hΛ ψ₀ hψ₀ h0 hψ hE2 hEf2 h4 Rads hRads hL48 h412 hrate hrate1
  have hε0 : 0 < ε := hε.1
  have hεA : ε ∈ Ioo 0 ε₀ := ⟨hε0, hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hεB : ε ∈ Ioo 0 ε₁ := ⟨hε0, hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩
  obtain ⟨hεβ2, hεlin⟩ := H2 ⟨hε0, hε.2.trans_le (min_le_right _ _)⟩
  have HUε := HU ε hεB (D := D) (P := P) (h := h) (H := H) R hRχ hRχ' hRlam hRℓ hRξ hUV 𝕣 h𝕣 hc
  subst hRχ hRχ' hRlam hRℓ hRξ
  have hℓ𝕣 : 0 < R.ℓ * 𝕣 := mul_pos hℓ0 h𝕣
  set Reg := regEvent D P h H R 𝕣 a ∩ gmGoodPt D h H 𝕣 𝕫 with hReg
  set K := p4K R a ε β with hKdef
  have hc2 : regC2const R a = (R.ℓ / a + 1) * Real.exp (R.ξ / a) := rfl
  obtain ⟨b, hbdef⟩ : ∃ b, b = a / regC2const R a := ⟨_, rfl⟩
  have hKeq : K = ⌊b * ε ^ (-β)⌋₊ - 1 := by rw [hKdef, hbdef]; rfl
  have hb : 0 < b := by rw [hbdef, hc2]; exact hb0
  have hεβ0 : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have hx2 : 2 ≤ b * ε ^ (-β) := by
    rw [Real.rpow_neg hε0.le, ← div_eq_mul_inv, le_div_iff₀ hεβ0]
    rw [hbdef, hc2]; linarith
  have hfl : 2 ≤ ⌊b * ε ^ (-β)⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
  have hK1 : 1 ≤ K := by rw [hKeq]; omega
  have hbK : b * ε ^ (-β) ≤ (K : ℝ) + 2 := by
    have h1 : ((K : ℕ) : ℝ) + 1 = (⌊b * ε ^ (-β)⌋₊ : ℝ) := by
      rw [hKeq]; push_cast [show 1 ≤ ⌊b * ε ^ (-β)⌋₊ by omega]; ring
    have := Nat.lt_floor_add_one (b * ε ^ (-β))
    linarith
  -- `(k+1)ε^β ≤ a/c₂` for `k ≤ K`
  have hkK : ∀ k ≤ K, ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ b := by
    intro k hk
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ b * ε ^ (-β) := by
      have : k + 1 ≤ ⌊b * ε ^ (-β)⌋₊ := by rw [hKeq] at hk; omega
      exact (Nat.cast_le.2 this).trans (Nat.floor_le (by positivity))
    calc ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ b * ε ^ (-β) * ε ^ β :=
          mul_le_mul_of_nonneg_right hk1 hεβ0.le
      _ = b := by rw [Real.rpow_neg hε0.le, mul_assoc, inv_mul_cancel₀ hεβ0.ne', mul_one]
  have hε1 : ε ≤ 1 := hεlin.2.le.trans (min_le_left _ _)
  have h3l : 3 * R.lam 3 * ε * 𝕣 < R.ℓ * 𝕣 := by
    have h1 := lt_of_lt_of_le hεlin.2 (min_le_right _ _)
    rw [lt_div_iff₀ (by linarith)] at h1
    have := mul_lt_mul_of_pos_right h1 h𝕣
    linarith
  have hd0 : 0 ≤ 3 * R.lam 3 * ε * 𝕣 := by
    have : 0 < R.lam 3 := by linarith
    positivity
  have hρ' : 3 * (R.ℓ * 𝕣) ≤ (4 * R.lam 3 * ε) ^ (-M₈) * 𝕣 := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hM8 h𝕣.le
  have hWG := fun (ρ' d : ℝ) (hρ : 3 * (R.ℓ * 𝕣) ≤ ρ') (hd : 0 ≤ d)
      (h𝕨 : 3 * (R.ℓ * 𝕣) + d ≤ ‖𝕫 - 𝕨‖) (ω : Ω) (hω : ω ∈ Reg) (k : ℕ) (hk : k ≤ K) =>
    gm_regEvent_WG (D := D) (P := P) (h := h) (H := H) R (ε := ε) (β := β) h𝕣 ha0 ha1 haℓ hχ.le
      hUV hc hξ hε0 hε1 hβ.le hω.1 h𝕫 hω.2.1 hω.2.2.1 (by rw [← hbdef]; exact hkK k hk) hρ hd h𝕨
  have key := HF ε hεA h38 hC24 hC27 hC14 hγ hγ2 hD hh R hRν h𝕫𝕨 sel hη (𝕣 := 𝕣) (M₈ := M₈)
    (δ := δ) (δ₁ := δ₁) (L := 3 * (R.ℓ * 𝕣)) (sl := 𝕣) (K := K) h𝕣 hℓ𝕣 h𝕣 hδ hl0 hl02 hl3 hl1
    hl11 hl2 hl21 hl4
    hRadsI Ef hΛ hψ₀ h0 hψ hE2 hEf2 h4 Rads hRads hL48 Reg hK1 ?_ ?_ ?_ ?_ ?_ ?_ hrate hrate1
  · exact key
  · rw [hbdef, hc2] at hbK; exact hbK
  · intro k hk
    refine ae_of_all _ fun ω hω => ?_
    obtain ⟨hH0, hH𝕫, hL, hbd, hgeod⟩ := hω.2
    exact HUε ω hω.1 𝕫 h𝕫 𝕨 (by linarith) hH0 hH𝕫 hL hbd hgeod k hk
  · intro k hk
    refine ae_of_all _ fun ω hω => ?_
    exact hWG _ _ hρ' hd0 (by linarith) ω hω k hk
  · intro ω hω k hk
    exact (hWG _ 0 le_rfl le_rfl (by linarith) ω hω k hk).2.1
  · linarith
  · refine le_trans (measureReal_mono ?_) h412
    intro ω hω
    exact ⟨hω.1.1, hω.2⟩

end LQGMetric.GM
