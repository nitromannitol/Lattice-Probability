/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412S at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jAsm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6Main
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412U4
import LatticeProb.Bonanno.LQGMetric.Field.HarmLocD
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412kBridge

/-!
# GM Proposition 4.12 at the CONF §3 parameters (D104, P2-M2J2i)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`: GM fix the CONF §3 constants
`c, δ, A, η` once (l. 1096–1168) and use Prop 4.12 (`prop-stab`, l. 2022–2024) only for them; the
proof of Theorem 4.2 (l. 1611–1613, 2437–2446).

* `GMP4_12S`: Prop 4.12 for *some* valid CONF parameters satisfying CONF Lemma 3.5 (D104);
* `gm_P4_12S_of`: `GMP4_12S` from `CONFSection3` (CONF L3.6, Thm 3.9 at its parameters) and the
  other inputs of `gm_P4_12_of` (`p412j_P4_12At`), with `P412jHarmLoc` (`HarmLoc.p412jHarmLoc`)
  `P412jGoodU` (`p412j_goodU`, P412U4.lean), CONF Lemma 2.4 (`CONF.confLem2_4`) and the D76
  bridge (`p412k_bridge`) discharged;
* `gm_T4_2PairOneS`, `gm_T4_2S`: copies of `gm_T4_2PairOne`, `gm_T4_2` (Iterate6Main.lean) taking
  the parameters `cp` from `GMP4_12S` instead of from `CONFLem3_5`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric Topology
open LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

/-- **GM Proposition 4.12 at the CONF §3 parameters** (D104): for every weak LQG metric there are
valid CONF parameters satisfying CONF Lemma 3.5 for which Prop 4.12 holds for all Hölder exponents
`0 < χ < ξ(Q−2)`, `χ' > ξ(Q+2)` and constant-invariant geodesic selectors -/
def GMP4_12S : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∃ cp : CONFParams, cp.Valid ∧ CONFLem3_5At γ D c cp ∧
  ∀ χ χ' : ℝ, 0 < χ → χ < xiGamma γ * (Q γ - 2) → xiGamma γ * (Q γ + 2) < χ' →
  ∀ sel : ℂ → ℂ → DistC → C(unitInterval, ℂ),
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  GMP4_12At γ D c cp χ χ' sel

open scoped Classical in
/-- **`T4_2PairOne`** from `GMP4_12S` (copy of `gm_T4_2PairOne`, the parameters `cp` taken from
`GMP4_12S`; GM proof of Thm 4.2, l. 1611–1613, 2437–2446) -/
theorem gm_T4_2PairOneS (h31a : LMLem3_1a) (h24e : GMS2_4e) (h318 : DFGPSProp3_18)
    (h320 : DFGPSLem3_20) (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) (hDF43 : DFGPSProp4_3F) (hMQ : MQThm1_2Weak)
    (hP412 : GMP4_12S) : T4_2PairOne := by
  intro γ D c hγ hγ2 hD sel hsel
  obtain ⟨cp, hcpV, hcp, HP⟩ := hP412 hγ hγ2 hD
  have hξ : 0 < xiGamma γ := DG.xiGamma_pos hγ
  have hQ2 := gm_Q_sub_two_pos hγ hγ2
  have hQ : 0 < Q γ := Q_pos hγ
  have hχ : 0 < xiGamma γ * (Q γ - 2) / 2 := by positivity
  have hχQ : xiGamma γ * (Q γ - 2) / 2 < xiGamma γ * (Q γ - 2) := by
    have : 0 < xiGamma γ * (Q γ - 2) := by positivity
    linarith
  have hχ'Q : xiGamma γ * (Q γ + 2) < xiGamma γ * (Q γ + 2) + 1 := by linarith
  have hχ'1 : 1 < xiGamma γ * (Q γ + 2) + 1 := by
    have : 0 < xiGamma γ * (Q γ + 2) := by positivity
    linarith
  obtain ⟨β, θ, hβ, hθ, hβχ', H412⟩ := HP _ _ hχ hχQ hχ'Q sel hsel
  have hβχ : β < xiGamma γ * (Q γ - 2) / 2 := hβχ'.trans (div_lt_self hχ hχ'1)
  refine ⟨β / 8, ⟨by linarith [hβ.1], by linarith [hβ.2]⟩, ?_⟩
  intro μ ν hμ hμν hνs lam hl0 hl01 hl12 hl21 hl3 hl34
  have hν0 : 0 < ν := hμ.trans hμν
  have hl3' : 0 < lam 3 := by linarith
  obtain ⟨𝕡, h𝕡, H11⟩ := gm_L4_11A h31a h24e h318 h320 hμ hν0 hl0 hl01 hl12
    (hl21.trans hl3.le) hl34
  refine ⟨𝕡, h𝕡, ?_⟩
  intro ℓ U hℓ hUo hUb ε₀ Λ η M hε₀ hη hM
  by_cases hΛ : 1 ≤ Λ
  swap
  · refine ⟨0, 1, le_rfl, one_pos, ?_⟩
    intro R Rad E Ef rr hR hGeo
    exact absurd hGeo.2.1.le hΛ
  have hpp : max (1 - η) (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (by norm_num) (le_max_right _ _), max_lt (by linarith) (by norm_num)⟩
  have hℓ4 : ℓ / 4 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hℓ.1], by linarith [hℓ.2]⟩
  obtain ⟨V, hVo, hVb, hVc, hUV, HV⟩ := H11 hγ hγ2 hD hcp hχ hχQ hχ'Q hUb hℓ4 hpp
  obtain ⟨a₀, ha₀, HA⟩ := HV ε₀ hε₀
  have ha0 : 0 < min a₀ (ℓ / 4) := lt_min ha₀.1 hℓ4.1
  have ha1 : min a₀ (ℓ / 4) < 1 := lt_of_le_of_lt (min_le_left _ _) ha₀.2
  have haℓ : min a₀ (ℓ / 4) ≤ ℓ / 4 := min_le_right _ _
  obtain ⟨B, hB⟩ : ∃ B, ∀ x ∈ U, ‖x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hUb.subset_closedBall 0
    exact ⟨B, fun x hx => by simpa using hB hx⟩
  set R₀ : RegPar := ⟨xiGamma γ, c, cp, xiGamma γ * (Q γ - 2) / 2, xiGamma γ * (Q γ + 2) + 1,
    μ, ν, lam, fun _ _ => univ, fun _ _ _ => 0, ℓ / 4, U, V⟩ with hR₀
  obtain ⟨C₁₂, ε₁₂, hε₁₂, H12⟩ := H412 R₀ rfl rfl rfl rfl rfl hl0 hl01 hl12 (hl21.trans hl3.le)
    hl3 hl34 hμ hμν hℓ4 hUV hVb _ ⟨ha0, ha1⟩ haℓ M hM
  have hθ' : 0 < min θ (β / 2) := lt_min hθ.1 (by linarith [hβ.1])
  have hθβ : min θ (β / 2) < β := lt_of_le_of_lt (min_le_right _ _) (by linarith [hβ.1])
  obtain ⟨Cp, εp, hCp, hεp, HP⟩ := gm_T42_pairU hDF43 h38 hC24 hC27 hC14 hγ hγ2 hD
    (a := min a₀ (ℓ / 4)) (β := β) (θ := min θ (β / 2)) (ν := ν) (ζ := β / 4)
    (χ := xiGamma γ * (Q γ - 2) / 2) (χ' := xiGamma γ * (Q γ + 2) + 1) (ℓ := ℓ / 4)
    (ξ := xiGamma γ) (Λ := Λ) (μ := μ) (B := B) (lam := lam) ha0 ha1 haℓ
    hℓ4.2 hχ (by linarith) hβ.1 hβχ hl0 hl3 (by linarith) hξ.le hθ' hθβ (by linarith [hβ.1])
    (by linarith [hβ.1]) hν0.le hΛ hμ.le M hM
  refine ⟨max C₁₂ 0 + Cp, min (min ε₁₂ εp) (min ε₀ (1 / 2)), by positivity,
    lt_min (lt_min hε₁₂ hεp) (lt_min hε₀ (by norm_num)), ?_⟩
  intro R Rad E Ef rr hR hGeo hRad Ω _ P _ h hh n hn
  obtain ⟨-, -, -, hEfinv, -, Hgeo⟩ := hGeo
  have hε0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hn12 : (2 : ℝ)⁻¹ ^ n < ε₁₂ := hn.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hnp : (2 : ℝ)⁻¹ ^ n < εp := hn.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hnε₀ : (2 : ℝ)⁻¹ ^ n ≤ ε₀ :=
    (hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hn1 : (2 : ℝ)⁻¹ ^ n < 1 :=
    (hn.trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans (by norm_num)
  set ε : ℝ := (2 : ℝ)⁻¹ ^ n with hεdef
  obtain ⟨hrrI, -⟩ := hRad ε ⟨hε0, hnε₀⟩
  -- the modified events and radii (`∀ 𝕣` forms)
  set E' : ℝ → ℂ → Set DistC := fun r z => if r ∈ Rad then E r z else univ with hE'
  set rr' : ℝ → ℝ → ℕ → ℝ := fun 𝕣 e k => if e ≤ ε₀ then 𝕣 / R * rr R e k else e * 𝕣 with hrr'
  have hrr'R : ∀ k, rr' R ε k = rr R ε k := fun k => by
    simp only [hrr', if_pos hnε₀]; field_simp
  have hrr'I : ∀ 𝕣 > 0, ∀ e ∈ Ioo (0 : ℝ) 1, ∀ k < ⌊μ * Real.logb 8 e⁻¹⌋₊,
      rr' 𝕣 e k ∈ Icc (e ^ (1 + ν) * 𝕣) (e * 𝕣) := by
    intro 𝕣 h𝕣 e he k hk
    by_cases hle : e ≤ ε₀
    · obtain ⟨h1, -⟩ := hRad e ⟨he.1, hle⟩
      obtain ⟨⟨hlo, hhi⟩, -⟩ := h1 k hk
      simp only [hrr', if_pos hle]
      have hc : 0 < 𝕣 / R := div_pos h𝕣 hR
      constructor
      · calc e ^ (1 + ν) * 𝕣 = 𝕣 / R * (e ^ (1 + ν) * R) := by field_simp
          _ ≤ 𝕣 / R * rr R e k := mul_le_mul_of_nonneg_left hlo hc.le
      · calc 𝕣 / R * rr R e k ≤ 𝕣 / R * (e * R) := mul_le_mul_of_nonneg_left hhi hc.le
          _ = e * 𝕣 := by field_simp
    · simp only [hrr', if_neg hle]
      refine ⟨mul_le_mul_of_nonneg_right ?_ h𝕣.le, le_rfl⟩
      calc e ^ (1 + ν) ≤ e ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge he.1 he.2.le (by linarith)
        _ = e := Real.rpow_one e
  set R' : RegPar := { R₀ with E := E', rr := rr' } with hR'
  have hp4 : ∀ r ∈ p4Rads R' R ε, r ∈ Rad ∧ r ∈ Icc (ε ^ (1 + ν) * R) (ε * R) := by
    rintro r ⟨k, hk, rfl⟩
    have hk' : k < ⌊μ * Real.logb 8 ε⁻¹⌋₊ := hk
    show rr' R ε k ∈ Rad ∧ rr' R ε k ∈ Icc (ε ^ (1 + ν) * R) (ε * R)
    rw [hrr'R]
    exact ⟨(hrrI k hk').2, (hrrI k hk').1⟩
  have hE'eq : ∀ r ∈ Rad, ∀ z, R'.E r z = E r z := fun r hr z => if_pos hr
  -- completion (D70) and the far normalization
  have hh₁ := gm_isWholePlaneGFF_completion hh
  obtain ⟨ψ₀, hψ₀, hψ⟩ := gm_exists_farTest (B * R + (4 * lam 3 * ε) ^ (-(2 / (β / 4) + 1)) * R +
    2 * lam 3 * ε * R + R + ε * R)
  set h₂ : NullMeasurableSpace Ω P → DistC :=
    fun ω => addConst ((h ∘ gm_ofNull P) ω) (-((h ∘ gm_ofNull P) ω ψ₀)) with hh₂def
  have hh₂ : IsWholePlaneGFF h₂ P.completion :=
    hh₁.addConst ((measurable_evalDist ψ₀).comp hh₁.measurable).neg
  have h0 : ∀ ω, h₂ ω ψ₀ = 0 := fun ω => by
    simp only [hh₂def, GFFInv.addConst_apply, hψ₀, one_mul, add_neg_cancel]
  obtain ⟨H, hH⟩ := DFGPS.exists_isCircleAvgVersion hh₂
  obtain ⟨hgeod2, hE2, hEf2, hEp, h42⟩ := Hgeo P.completion h₂ hh₂
  -- the regularity event (Lemma 4.11)
  have hradii : ∀ 𝕣 > 0, ∀ e ∈ Ioc (0 : ℝ) ε₀, (∀ k < ⌊μ * Real.logb 8 e⁻¹⌋₊,
      R'.rr 𝕣 e k ∈ Icc (e ^ (1 + ν) * 𝕣) (e * 𝕣) ∧ R'.rr 𝕣 e k ∈ (fun _ : ℝ => (univ : Set ℝ)) 𝕣) ∧
      ∀ k, k + 1 < ⌊μ * Real.logb 8 e⁻¹⌋₊ → lam 3 / lam 0 ≤ R'.rr 𝕣 e k / R'.rr 𝕣 e (k + 1) := by
    intro 𝕣 h𝕣 e he
    obtain ⟨h1, h2⟩ := hRad e he
    have hc : 0 < 𝕣 / R := div_pos h𝕣 hR
    have hR'rr : ∀ k, R'.rr 𝕣 e k = 𝕣 / R * rr R e k := fun k => if_pos he.2
    refine ⟨fun k hk => ⟨?_, mem_univ _⟩, fun k hk => ?_⟩
    · obtain ⟨⟨hlo, hhi⟩, -⟩ := h1 k hk
      rw [hR'rr]
      constructor
      · calc e ^ (1 + ν) * 𝕣 = 𝕣 / R * (e ^ (1 + ν) * R) := by field_simp
          _ ≤ 𝕣 / R * rr R e k := mul_le_mul_of_nonneg_left hlo hc.le
      · calc 𝕣 / R * rr R e k ≤ 𝕣 / R * (e * R) := mul_le_mul_of_nonneg_left hhi hc.le
          _ = e * 𝕣 := by field_simp
    · rw [hR'rr, hR'rr, mul_div_mul_left _ _ hc.ne']
      exact h2 k hk
  have hEmeas : ∀ 𝕣 > 0, ∀ z, ∀ r ∈ (fun _ : ℝ => (univ : Set ℝ)) 𝕣,
      AEEventIn P.completion (fieldSigma (fun ω => addConst (h₂ ω)
        (-circleAvg (h₂ ω) (lam 4 * r) z)) (annulus z (lam 0 * r) (lam 3 * r)))
        (h₂ ⁻¹' R'.E r z) := by
    intro 𝕣 _ z r _
    by_cases hr : r ∈ Rad
    · rw [hE'eq r hr]; exact hE2 z r hr
    · have : R'.E r z = univ := if_neg hr
      rw [this, preimage_univ]
      exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩
  have hEprob : ∀ 𝕣 > 0, ∀ z, ∀ r ∈ (fun _ : ℝ => (univ : Set ℝ)) 𝕣,
      ENNReal.ofReal 𝕡 ≤ P.completion (h₂ ⁻¹' R'.E r z) := by
    intro 𝕣 _ z r _
    by_cases hr : r ∈ Rad
    · rw [hE'eq r hr]; exact hEp z r hr
    · have : R'.E r z = univ := if_neg hr
      rw [this, preimage_univ, measure_univ]
      exact ENNReal.ofReal_le_one.2 h𝕡.2.le
  have hRegc := HA (min a₀ (ℓ / 4)) ⟨ha0, min_le_left _ _⟩ P.completion h₂ hh₂ H hH R' rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ => univ) hradii hEmeas hEprob R hR
  set Reg : Set (NullMeasurableSpace Ω P) := regEvent D P.completion h₂ H R' R (min a₀ (ℓ / 4))
    with hRegdef
  refine ⟨Reg, ?_, ?_⟩
  · have e1 : P.real Regᶜ = (P.completion Regᶜ).toReal := rfl
    rw [e1]
    refine (ENNReal.toReal_le_of_le_ofReal ?_ hRegc).trans ?_
    · have := max_lt (show 1 - η < 1 by linarith) (show (1 / 2 : ℝ) < 1 by norm_num)
      linarith
    · linarith [le_max_left (1 - η) (1 / 2 : ℝ)]
  intro 𝕫 𝕨 h𝕫 h𝕨 hℓ𝕫𝕨
  have hℓR : (0 : ℝ) < ℓ * R := mul_pos hℓ.1 hR
  have h𝕫𝕨 : 𝕫 ≠ 𝕨 := fun he => by rw [he, sub_self, norm_zero] at hℓ𝕫𝕨; linarith
  have h𝕫B : ‖𝕫‖ ≤ B * R := by
    obtain ⟨x, hx, rfl⟩ := h𝕫
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have := hB x hx
    nlinarith
  have h4ℓ : 4 * (R'.ℓ * R) ≤ ‖𝕫 - 𝕨‖ := by
    show 4 * (ℓ / 4 * R) ≤ _; linarith
  have hη2 : ∀ᵐ ω ∂P.completion, IsGeod01 (D (h₂ ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h₂ ω)) ∧
      UniqueGeod (D (h₂ ω)) 𝕫 𝕨 :=
    (hgeod2 𝕫 𝕨 h𝕫𝕨).and (gm_S1_2 hMQ hγ hγ2 hD P.completion h₂ hh₂ 𝕫 𝕨)
  have hψ' : tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball (0 : ℂ) (‖𝕫‖ +
      (4 * R'.lam 3 * ε) ^ (-(2 / (β / 4) + 1)) * R + 2 * R'.lam 3 * ε * R + R + ε * R))ᶜ :=
    hψ.trans (compl_subset_compl.2 (ball_subset_ball (by
      show ‖𝕫‖ + (4 * lam 3 * ε) ^ (-(2 / (β / 4) + 1)) * R + 2 * lam 3 * ε * R + R + ε * R ≤ _
      linarith)))
  have hE2' : ∀ (z : ℂ), ∀ r ∈ p4Rads R' R ε, AEEventIn P.completion (fieldSigma
      (fun ω => addConst (h₂ ω) (-circleAvg (h₂ ω) (R'.lam 4 * r) z))
      (annulus z (R'.lam 0 * r) (R'.lam 3 * r))) (h₂ ⁻¹' R'.E r z) := fun z r hr => by
    rw [hE'eq r (hp4 r hr).1]; exact hE2 z r (hp4 r hr).1
  have h4' : ∀ (z : ℂ), ∀ r ∈ p4Rads R' R ε, 𝕫 ∉ Metric.ball z (R'.lam 3 * r) →
      𝕨 ∉ Metric.ball z (R'.lam 3 * r) →
      (fun ω => Λ⁻¹ * (P.completion[(h₂ ⁻¹' R'.E r z ∩
          {ω | (range (sel 𝕫 𝕨 (h₂ ω)) ∩ Metric.ball z (R'.lam 1 * r)).Nonempty}).indicator
          (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h₂ (Metric.ball z (R'.lam 2 * r))ᶜ]) ω)
        ≤ᵐ[P.completion]
        P.completion[(h₂ ⁻¹' Ef r z 𝕫 𝕨 ∩
          {ω | (range (sel 𝕫 𝕨 (h₂ ω)) ∩ Metric.ball z (R'.lam 1 * r)).Nonempty}).indicator
          (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h₂ (Metric.ball z (R'.lam 2 * r))ᶜ] :=
    fun z r hr h1 h2 => by
      rw [hE'eq r (hp4 r hr).1]; exact h42 z r (hp4 r hr).1 𝕫 𝕨 h𝕫𝕨 h1 h2
  have h412' : P.completion.real (p412Bad D sel P.completion h₂ H R' 𝕫 𝕨 R (min a₀ (ℓ / 4)) ε β
      (min θ (β / 2))) ≤ max C₁₂ 0 * ε ^ M := by
    have hb := H12 E' rr' hrr'I P.completion h₂ hh₂ hgeod2 H hH R hR 𝕫 h𝕫 𝕨 h𝕨 h4ℓ n hn12
    have hεM : 0 ≤ ε ^ M := Real.rpow_nonneg hε0.le _
    refine le_trans (measureReal_mono ?_) (ENNReal.toReal_le_of_le_ofReal (by positivity)
      (hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hεM))))
    rintro ω ⟨hω1, hω2⟩
    refine ⟨hω1, ?_⟩
    simp only [mem_setOf_eq] at hω2 ⊢
    refine lt_of_lt_of_le hω2 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    have t1 := Real.rpow_le_rpow_of_exponent_ge hε0 hn1.le (min_le_left θ (β / 2))
    have t2 : ((2 : ℝ)⁻¹ ^ n) ^ θ = ε ^ θ := rfl
    have t3 : ((2 : ℝ)⁻¹ ^ n) ^ min θ (β / 2) = ε ^ min θ (β / 2) := rfl
    linarith
  have key := HP ε ⟨hε0, hnp⟩ hh₂ R' rfl rfl rfl rfl rfl rfl rfl hUV h𝕫𝕨 sel hη2 (𝕣 := R)
    (δ₁ := max C₁₂ 0 * ε ^ M) hR (hD.tightness.1 R hR) h𝕫 h𝕫B h4ℓ hl0 (by linarith) hl3
    (by linarith) (by linarith) (by linarith) hl21 (by linarith) (fun r hr => (hp4 r hr).2) Ef
    hψ₀ h0 hψ' hE2' (fun z r hr => hEf2 z r (hp4 r hr).1 𝕫 𝕨) h4' h412'
  -- transfer back: the a.s. good set, the witness, the completion
  have hG : ∀ᵐ ω ∂P.completion, ω ∈ gmGoodPt D h₂ H R 𝕫 := by
    filter_upwards [hH.ae_eq R hR 0, hH.ae_eq R hR 𝕫, gm_ae_len_bdd_geod h38 hγ hγ2 hD hh₂ 𝕫]
      with ω h1 h2 h3
    exact ⟨h1, h2, h3.1, h3.2.1, h3.2.2⟩
  have hG0 : P.completion (gmGoodPt D h₂ H R 𝕫)ᶜ = 0 := ae_iff.1 hG
  have hwit : ∀ ω, t42Wit sel h₂ Ef R'.lam R'.rr R'.μ R ε 𝕫 𝕨 ω ↔
      t42Wit sel h Ef lam rr μ R ε 𝕫 𝕨 ω := fun ω => by
    rw [hh₂def, gm_t42Wit_addConst hsel hEfinv]
    simp only [t42Wit]
    rw [show R'.rr R ε = rr R ε from funext hrr'R]
    rfl
  set G := gmGoodPt D h₂ H R 𝕫
  set W := {ω | ¬ t42Wit sel h₂ Ef R'.lam R'.rr R'.μ R ε 𝕫 𝕨 ω}
  have hsub : (Reg ∩ W : Set (NullMeasurableSpace Ω P)) ⊆ ((Reg ∩ G) ∩ W) ∪ Gᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G
    · exact Or.inl ⟨⟨hω.1, hg⟩, hω.2⟩
    · exact Or.inr hg
  have heq : P.real (Reg ∩ {ω | ¬ t42Wit sel h Ef lam rr μ R ε 𝕫 𝕨 ω}) =
      P.completion.real (Reg ∩ W) := by
    have : (Reg ∩ {ω | ¬ t42Wit sel h Ef lam rr μ R ε 𝕫 𝕨 ω} : Set Ω) = Reg ∩ W := by
      congr 1; ext ω; exact not_congr (hwit ω).symm
    rw [this]
    rfl
  rw [heq]
  calc P.completion.real (Reg ∩ W) ≤ P.completion.real (((Reg ∩ G) ∩ W) ∪ Gᶜ) :=
        measureReal_mono hsub
    _ ≤ P.completion.real ((Reg ∩ G) ∩ W) + P.completion.real Gᶜ := measureReal_union_le _ _
    _ ≤ (max C₁₂ 0 * ε ^ M + Cp * ε ^ M) + 0 := by
        refine add_le_add key ?_
        rw [Measure.real, hG0, ENNReal.toReal_zero]
    _ = (max C₁₂ 0 + Cp) * ε ^ M := by ring

/-- **GM Theorem 4.2** (`thm-geo-iterate`, l. 1554–1568) from `GMP4_12S` and the Blueprint inputs
(`gm_T4_2_of_pairOne`, D89) -/
theorem gm_T4_2S (h31a : LMLem3_1a) (h24e : GMS2_4e) (h318 : DFGPSProp3_18)
    (h320 : DFGPSLem3_20) (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) (hDF43 : DFGPSProp4_3F) (hMQ : MQThm1_2Weak)
    (hP412 : GMP4_12S) : T4_2 :=
  gm_T4_2_of_pairOne (gm_T4_2PairOneS h31a h24e h318 h320 h38 hC24 hC27 hC14 hDF43 hMQ hP412)

end LQGMetric.GM
