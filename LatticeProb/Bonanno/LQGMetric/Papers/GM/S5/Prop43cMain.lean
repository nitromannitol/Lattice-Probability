/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43cMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43cAsm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bDense

/-!
# GM Proposition 4.3, assembly (task P2-M2N3)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Proposition 4.3 (l. 1582–1593), proof in §5.1 (l. 2722–2836). See `Prop43cAsm.lean` for the
choices of `𝓡`, `E`, `𝔈`, `Λ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM Proposition 4.3** (l. 1582–1593) from GM Propositions 2.2, 3.5, 5.2 and Lemma 5.5 (and
`DFGPSLem3_8` for the law invariance of `𝓡_0`), with the extra hypothesis `ν < 1` (GM: `ν ≤ ν_*`,
`ν_* ∈ (0,1)` from Theorem 4.2). -/
theorem gm_P4_3_core (h22 : P2_2) (h35 : P3_5) (h55 : L5_5) (h52 : P5_2) (h38 : DFGPSLem3_8)
    {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ}
    (hPS : PairSetting γ D D' c) (hRat : RatiosAre D D' cs Cs) (hlt : cs < Cs)
    (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hgeo : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ a b : ℂ, a ≠ b →
        ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω)))
    (hinv : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    (hmeas : ∀ a b : ℂ, Measurable (sel a b))
    (μ ν c₁ c₂ : ℝ) (hμ : 0 < μ) (hμν : μ < ν) (hν1 : ν < 1)
    (hc₁ : cs < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < Cs) :
    ∀ 𝕡 ∈ Ioo (0 : ℝ) 1, ∃ b ρ : ℝ, b ∈ Ioo (0 : ℝ) 1 ∧ ρ ∈ Ioo (0 : ℝ) 1 ∧ ∃ c'' : ℝ, cs < c'' ∧
    ∀ β ∈ Ioo (0 : ℝ) 1, ∃ ε₀ Λ : ℝ, ε₀ ∈ Ioo (0 : ℝ) 1 ∧ 1 < Λ ∧
    ∀ R : ℝ, 0 < R → (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P → ENNReal.ofReal β ≤ P (h ⁻¹' GLow D D' R c'' β)) →
    ∃ (Rad : Set ℝ) (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC),
      GeoIterateHyp D sel (μ / 2) ν ![1 / 4, 2, 3, 4, 5] 𝕡 (ρ⁻¹ * R) ε₀ Λ Rad E Ef ∧
      ∀ (z : ℂ), ∀ r ∈ Rad, ∀ a a' : ℂ, a ∉ Metric.ball z (4 * r) → a' ∉ Metric.ball z (4 * r) →
        ∀ g ∈ Ef r z a a', ∃ s t : unitInterval, s < t ∧
          sel a a' g s ∈ Metric.ball z (3 / 2 * r) ∧ sel a a' g t ∈ Metric.ball z (3 / 2 * r) ∧
          b * r ≤ ‖sel a a' g s - sel a a' g t‖ ∧
          (D' g).1 (sel a a' g s, sel a a' g t) ≤ c₂ * (D g).1 (sel a a' g s, sel a a' g t) := by
  classical
  intro 𝕡 h𝕡
  have hD := hPS.2.2.1
  have hD' := hPS.2.2.2
  obtain ⟨hcs, hcC⟩ := cs_pos_of_ratios h22 hPS hRat
  obtain ⟨α₀, p, hα₀, hp, H35⟩ := h35 hPS hRat hμ hμν hν1
  obtain ⟨α, hα, hα34, hEP⟩ := h55 hPS hcs (hcs.trans hlt) hα₀.2 hp.1 hp.2
  obtain ⟨η, hη⟩ := exists_etaChoice hcs hc₁ hc₁₂ hc₂
  obtain ⟨S, b₀, hb₀, -, -, -, -, -, -, hSR, N, H52⟩ :=
    h52 hPS hRat hcs hlt hα34 hα.2 hp.1 hp.2 hEP hc₁ hc₁₂ hc₂ hη 𝕡 h𝕡
  obtain ⟨c'', hc'', H35'⟩ := H35 α hα c₁ hc₁
  have hρ := hSR.2.2.2.1
  have hρ0 : 0 < S.ρ := hρ.1
  have hΛ₀ : 1 < S.Λ₀ := hSR.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨min b₀ (1 / 2), S.ρ, ⟨lt_min hb₀ (by norm_num), (min_le_right _ _).trans_lt
    (by norm_num)⟩, ⟨hρ0, hρ.2.trans (by norm_num)⟩, c'', hc''.1, ?_⟩
  intro β hβ
  obtain ⟨ε₀', hε₀', H3⟩ := H35' β hβ
  set ε₀ := min ε₀' (1 / 2) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₀' (by norm_num)
  set Λ := ((N : ℝ) + 1) * Real.exp (3 * S.Λ₀) with hΛ
  have hΛ1 : 1 < Λ := by
    have h1 : 1 < Real.exp (3 * S.Λ₀) := by
      have := Real.add_one_le_exp (3 * S.Λ₀); linarith
    have h2 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := N.cast_nonneg (α := ℝ); linarith
    nlinarith
  refine ⟨ε₀, Λ, ⟨hε₀0, (min_le_right _ _).trans_lt (by norm_num)⟩, hΛ1, ?_⟩
  intro R hR hGL
  have hR' : 0 < S.ρ⁻¹ * R := by positivity
  -- the deterministic data of Prop 5.2 at each good radius
  have : Nonempty TestC := ⟨0⟩
  choose! U fb gb hdat using H52
  set gR := goodRadii D D' α c₁ p with hgR
  let Rad : Set ℝ := {r | 0 < r ∧ r ≤ ε₀ * (S.ρ⁻¹ * R) ∧ S.ρ * r ∈ gR}
  let E : ℝ → ℂ → Set DistC := fun r z => constCore (eventAt (eventE D D' S (U r) (fb r) (gb r) r) z)
  let Ef : ℝ → ℂ → ℂ → ℂ → Set DistC := fun r z a b =>
    if hr : S.ρ * r ∈ gR then constCore (frkE D D' sel cs Cs c₂ b₀ (Real.exp (3 * S.Λ₀)) r
      (bumpFamAt S (U r) (fb r) (gb r) r (hdat r hr).1 z : Set TestC) z a b) else ∅
  have hEf : ∀ r (hr : S.ρ * r ∈ gR) z a b, Ef r z a b = constCore (frkE D D' sel cs Cs c₂ b₀
      (Real.exp (3 * S.Λ₀)) r (bumpFamAt S (U r) (fb r) (gb r) r (hdat r hr).1 z : Set TestC)
      z a b) := fun r hr z a b => dif_pos hr
  have l0 : (![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 0 = 1 / 4 := rfl
  have l1 : (![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 1 = 2 := rfl
  have l2 : (![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 2 = 3 := rfl
  have l3 : (![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 3 = 4 := rfl
  have l4 : (![1 / 4, 2, 3, 4, 5] : Fin 5 → ℝ) 4 = 5 := rfl
  refine ⟨Rad, E, Ef, ?_, ?_⟩
  swap
  · -- the conclusion (5.4) ⇒ (4.4)
    intro z r hr a a' _ _ g hg
    rw [hEf r hr.2.2] at hg
    exact frkE_concl hr.1 (constCore_subset _ hg)
  unfold GeoIterateHyp
  simp only [l0, l1, l2, l3, l4]
  refine ⟨fun r hr => ⟨hr.1, hr.2.1⟩, hΛ1, fun r z g c => addConst_mem_constCore_iff _ g c,
    fun r z a b g c => ?_, ?_, ?_⟩
  · -- invariance of `𝔈`
    by_cases hr : S.ρ * r ∈ gR
    · rw [hEf r hr]; exact addConst_mem_constCore_iff _ g c
    · simp only [Ef, dif_neg hr, mem_empty_iff_false]
  · -- (1) density of radii (Prop 3.5 at an auxiliary whole-plane GFF)
    intro ε hε
    obtain ⟨Ω₀, _, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
    have hcount := H3 P₀ h₀ hh₀ R hR (hGL P₀ h₀ hh₀) ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
    obtain ⟨rr, hrr, hgap⟩ := exists_sparse_radii hR' hcount Rad fun k hk h1 h2 => by
      refine ⟨by positivity, ?_, ?_⟩
      · exact mul_le_mul_of_nonneg_right (h2.trans hε.2) hR'.le
      · have e : S.ρ * ((8 : ℝ)⁻¹ ^ k * (S.ρ⁻¹ * R)) = (8 : ℝ)⁻¹ ^ k * R := by
          field_simp
        rw [e]
        refine ⟨by positivity, fun P _ h hh => ?_⟩
        rw [prob_attainedLow_eq h38 hPS α _ c₁ P h hh P₀ h₀ hh₀]
        exact hk
    refine ⟨rr, hrr, fun k hk => ?_⟩
    have := hgap k hk
    have e : (4 : ℝ) / (1 / 4) = 16 := by norm_num
    rw [e]; linarith
  -- the probabilistic conditions
  intro Ω _ P _ h hh
  refine ⟨hgeo P h hh, ?_, ?_, ?_, ?_⟩
  · -- (2) for `E`
    intro z r hr
    obtain ⟨-, -, -, -, H⟩ := hdat r hr.2.2
    obtain ⟨hA, hI, -, -⟩ := H P (fun ω => affineComp 1 z (h ω)) (hh.affineComp one_pos z)
    obtain ⟨F, hF, hEF⟩ := aeEventIn_eventAt _ z r hA
    rw [show (1 / 4 : ℝ) * r = r / 4 by ring]
    exact ⟨F, hF, (ae_constCore_eventAt hI).trans hEF⟩
  · -- (2) for `𝔈` (GM Lemma 5.3)
    intro z r hr a b
    rw [hEf r hr.2.2]
    obtain ⟨hfin, -, hsupp, -⟩ := hdat r hr.2.2
    refine gm_L5_3 hD hD' hinv hmeas hcs hcC (hcs.trans (hc₁.trans hc₁₂)).le hr.1 hRat _ z ?_ a b hh
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 hψ
    refine tsupport_transTest_subset ((hsupp φ (hfin.mem_toFinset.1 hφ)).trans fun y hy => ?_)
    have hy' : r / 4 < ‖y - 0‖ ∧ ‖y - 0‖ < 3 * r := hy
    rw [mem_ball, dist_eq_norm]
    linarith [hy'.2]
  · -- (3)
    intro z r hr
    obtain ⟨-, -, -, -, H⟩ := hdat r hr.2.2
    obtain ⟨-, hI, hp', -⟩ := H P (fun ω => affineComp 1 z (h ω)) (hh.affineComp one_pos z)
    rw [measure_congr (ae_constCore_eventAt hI)]
    exact hp'
  · -- (4) (GM Lemma 5.4)
    intro z r hr a b hab ha hb
    obtain ⟨hfin, hN, hsupp, hB, H⟩ := hdat r hr.2.2
    have hh' := hh.affineComp one_pos z
    obtain ⟨hA, hI, -, hC⟩ := H P (fun ω => affineComp 1 z (h ω)) hh'
    have hEm : NullMeasurableSet ((fun ω => affineComp 1 z (h ω)) ⁻¹'
        eventE D D' S (U r) (fb r) (gb r) r) P := by
      obtain ⟨F, hF, hEF⟩ := hA
      have hle := Bilip.fieldSigma_le ((measurable_addConst_circleAvg (5 * r) 0).comp
        hh'.measurable) (annulus 0 (r / 4) (4 * r))
      exact (hle F hF).nullMeasurableSet.congr hEF.symm
    have hza : a - z ∉ ball (0 : ℂ) (4 * r) := by
      rwa [mem_ball, dist_zero_right, ← dist_eq_norm, ← mem_ball]
    have hzb : b - z ∉ ball (0 : ℂ) (4 * r) := by
      rwa [mem_ball, dist_zero_right, ← dist_eq_norm, ← mem_ball]
    have hN' : hfin.toFinset.card ≤ N := by rwa [← Set.ncard_eq_toFinset_card _ hfin]
    have key := gm_L5_4_P52 hD hD' hinv hmeas hgeo (b₀ := b₀) hr.1 S (U r) (fb r) (gb r) hfin N
      hN' hsupp hB z hab ha hb hh hEm (hC (a - z) (b - z) hza hzb)
    have hind : (h ⁻¹' E r z ∩ {ω | (range (sel a b (h ω)) ∩ ball z (2 * r)).Nonempty}).indicator
        (fun _ => (1 : ℝ)) =ᵐ[P]
        (h ⁻¹' eventAt (eventE D D' S (U r) (fb r) (gb r) r) z ∩
          {ω | (range (sel a b (h ω)) ∩ ball z (2 * r)).Nonempty}).indicator (fun _ => (1 : ℝ)) :=
      indicator_ae_eq_of_ae_eq_set ((ae_constCore_eventAt hI).inter EventuallyEq.rfl)
    have hce := condExp_congr_ae (m := fieldSigmaClosed0 h (ball z (3 * r))ᶜ) hind
    rw [hEf r hr.2.2]
    filter_upwards [key, hce] with ω h1 h2
    simp only at h1 ⊢
    rw [h2]
    exact h1

end LQGMetric.GM
