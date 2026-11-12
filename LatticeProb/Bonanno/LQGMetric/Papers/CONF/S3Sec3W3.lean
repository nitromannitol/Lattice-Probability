/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3Sec3W3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3Sec3W2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M10
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112N3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108Q3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U3

/-!
# CONF Lemma 3.3 (D112 form) and Lemma 3.6 from CONF L2.10 at `confU` (DEC-127 packet J, P2-CONFW)

`l33Gen_fatG_lem2_10_at` is a copy of `l33Gen_fatG_lem2_10` (S3D108Q1, P2-CONF210B) whose only
change is the hypothesis: `CONFLem2_10AtConfU` (CONF L2.10 at the domains `confU r δ z T`,
DEC-127) instead of `CONFLem2_10`, with Step 3 from `confFKGFrozenEUc_of_link_at` (S3Sec3W2).
`conf36_lem3_6AtAE0_at`: CONF L3.6 from it by `conf36_lem3_6AtAE0_of_h38` (S3D114U3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **CONF Lemma 3.3 in the D112 form** (`L33Gen` for `fatG`; C:1176–1244) from CONF Lemma 2.10
at the domains `confU` (DEC-127); proof copied from `l33Gen_fatG_lem2_10` (S3D108Q1). -/
theorem l33Gen_fatG_lem2_10_at {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) (hL : CONFLem2_10AtConfU) {p : CONFParams}
    (hp : p.Valid) (hδ8 : p.δ < 1 / 8) :
    L33Gen γ D c p (fatG p) := by
  have HH : CONFHarmLowZB := confHarmLowZB
  have HL : CONFHarmPartLink := confHarmPartLink
  obtain ⟨hc0, -, hδ0, -, -, -⟩ := hp
  have HF : CONFFKGFrozenEUc γ D c p := confFKGFrozenEUc_of_link_at hL hγ hD hδ0 hc0 HL
  set ξ := xiGamma γ
  set s : ℝ := p.c / 100 * Real.exp (-(ξ * p.A)) with hs_def
  have hs : 0 < s := by positivity
  obtain ⟨𝔭, h𝔭, h𝔭1, H2⟩ := conf33G_step2 hγ hγ2 hD HH hδ0 hδ8.le hs
  refine ⟨𝔭, h𝔭, ?_⟩
  intro Ω _ P _ h hh z r hr T hT ρ w hρ hUw B hB
  set F := confFree p.δ 0 1 T with hF
  have hFr : confFree (p.δ * r) z r T = F := confFree_scale hr z T
  by_cases hne : F.Nonempty
  swap
  · have e : {ω | fatG p (D (h ω)) (scaleFac ξ c (h ω) r z) r z T} = univ := by
      ext ω
      simp only [mem_setOf_eq, mem_univ, iff_true]
      intro k hk
      rw [hFr] at hk
      exact absurd ⟨k, hk⟩ hne
    rw [e, inter_univ]
    calc ENNReal.ofReal 𝔭 * P (B ∩ confEU ξ c D P h p r z T)
        ≤ 1 * P (B ∩ confEU ξ c D P h p r z T) := by
          gcongr; exact ENNReal.ofReal_le_one.2 h𝔭1
      _ = _ := one_mul _
  have hTu : ∀ k ∈ T, k ∈ confSqIdx p.δ 0 (annulus 0 3 4) := fun k hk => by
    rw [← confSqIdx_annulus_scale hr z]; exact hT k hk
  have H : Conf33GStep2At D c p.δ s T 𝔭 := H2 T hTu hne
  set U := confU r p.δ z T with hU_def
  have hUo : IsOpen U := isOpen_confU r p.δ z T
  have hUb : Bornology.IsBounded U := isBounded_confU r p.δ z T
  have hε : 0 < p.δ * r := mul_pos hδ0 hr
  obtain ⟨X, G, hX, hGm, hXG, hXext⟩ := exists_isL33ZBPart_G_ext hh hρ w hUo hUb hUw
  have eU : (affOpens r z (u33G p.δ T) : Set ℂ) = U := affOpens_u33G hr z p.δ T
  have hX' : IsL33ZBPart P h ρ w (affOpens r z (u33G p.δ T)) (affOpens r z (u33G p.δ T)).isOpen X :=
    isL33ZBPart_congr eU.symm hX
  obtain ⟨Y, -, hcl, hPY⟩ := H P h hh ρ w r hr z X hX'
  -- the family `(K_C, W_C)` at scale `r`
  have hFfin : F.Finite := by
    have := finite_confFree (ε := p.δ * 1) (r := 1) (by simpa using hδ0) (0 : ℂ) T
    simpa [hF] using this
  haveI : Finite F := hFfin.to_subtype
  set Cf : F → Set (ℤ × ℤ) := fun k => confComp F k.1 with hCf
  set Wk : F → Opens ℂ := fun k => affOpens r z (w33G p.δ (Cf k)) with hWk
  set Kk : F → Set ℂ := fun k => affFwd r z '' confCtrs p.δ 0 (Cf k) with hKk
  have eW : ∀ k, (Wk k : Set ℂ) = confFatW (p.δ * r) z (Cf k) := fun k =>
    affOpens_w33G hr z p.δ _
  have eK : ∀ k, Kk k = confCtrs (p.δ * r) z (Cf k) := fun k => (confCtrs_scale p.δ r z _).symm
  have hCr : ∀ k : F, Cf k ⊆ confFree (p.δ * r) z r T := fun k => by
    rw [hFr]; exact confComp_subset k.2
  have hWin : ∀ k, (Wk k : Set ℂ) ⊆ innerPart U (p.δ * r / 4) := fun k => by
    rw [eW]; exact confFatW_subset_innerPart hε z (hCr k)
  set V8 : Opens ℂ := ⟨innerPart U (p.δ * r / 8), isOpen_innerPart hUo _⟩ with hV8
  have hWV8 : ∀ k, (Wk k : Set ℂ) ⊆ V8 := fun k x hx =>
    ⟨(hWin k hx).1, by linarith [(hWin k hx).2]⟩
  have hV8U : closure (V8 : Set ℂ) ⊆ U := closure_innerPart_subset hUo (by positivity)
  have hWU : ∀ k, closure (Wk k : Set ℂ) ⊆ U := fun k => (closure_mono (hWV8 k)).trans hV8U
  have hKW : ∀ k, Kk k ⊆ Wk k := fun k => by
    rw [eK, eW]; exact confCtrs_subset_confFatW hε z _
  have hKfin : ∀ k, (Kk k).Finite := fun k =>
    (finite_confCtrs (ε := p.δ) 0 (hFfin.subset (confComp_subset k.2))).image _
  have hWaff : ∀ k, (Wk k : Set ℂ) ⊆ affOpens r z (v33G p.δ T) := fun k x hx => by
    show affMap r z x ∈ (v33G p.δ T : Set ℂ)
    exact confFatW_unit_subset_v33G hδ0 (confComp_subset k.2) hx
  -- CONF Remark 1.2: the zero-boundary metrics on `W_C`
  have hZB := confZBMetricN hD P h hh ρ w U hUo hUb X hX
  choose Fm hFm hFmid using fun k : F => hZB (Wk k) (hWU k)
  set t : ℝ := s * c r with ht_def
  have ht : 0 < t := mul_pos hs (hD.tightness.1 r hr)
  set SG : Set DistC := zbDiamSet Wk Fm Kk t with hSG_def
  have hSG : MeasurableSet SG := by
    have e : SG = ⋂ i, ⋂ u ∈ Kk i, ⋂ v ∈ Kk i,
        (fun x => Fm i (restrictTo (Wk i) x) u v) ⁻¹' Iic (ENNReal.ofReal t) := by
      ext x; simp [SG, zbDiamSet]
    rw [e]
    refine MeasurableSet.iInter fun i => MeasurableSet.biInter (hKfin i).countable fun u _ =>
      MeasurableSet.biInter (hKfin i).countable fun v _ => ?_
    exact measurableSet_Iic.preimage ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp
      ((hFm i).comp (measurable_restrictTo _))))
  obtain ⟨SF, hSF, hEU, HFK⟩ := HF P h hh z r hr T hT ρ w hρ hUw X G hX hGm hXG
    hXext
  have hfkg := HFK Wk hWU Fm hFm hFmid Kk hKW (fun k => (hKfin k).countable) t ht
  -- the cut-off of the harmonic part and the field of Step 1
  obtain ⟨φ, δ', hδ', hcut⟩ := exists_cutoff33G (V := (V8 : Set ℂ)) hUo
    ((hUb.subset hV8U).isCompact_closure.of_isClosed_subset isClosed_closure
      (closure_mono subset_closure |>.trans (by rw [closure_closure])))
    hV8U
  obtain ⟨Y', fn, hYd, hfb, hfV, -, -, hW'⟩ := exists_zbField hD hh hUb hX V8 hV8U
  have hS1 := zb_step1_of hγ hD hh hYd hfb hfV hr z p.A
  have hharm : ∀ᵐ ω ∂P, ∃ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U ∧
      ∀ φ : TestOn (toOpens U hUo),
        restrictTo (toOpens U hUo) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x := by
    obtain ⟨-, -, hh₀, hz, hdec, hXz, hhg, -, -⟩ := hX
    filter_upwards [hhg, hXz] with ω hg hXω
    obtain ⟨g, hg, hgT⟩ := hg
    refine ⟨g, hg, fun φ => ?_⟩
    have e : recField h ρ w ω - X ω = hh₀ ω := by rw [hdec ω, hXω, add_sub_cancel_right]
    rw [e]; exact hgT φ
  have hFmall := ae_all_iff.2 hFmid
  have hlink := HL P h hh ρ w hρ U hUo hUb hUw X G hX hGm hXG
  have hca := CircleAvg.ae_circleAvg_addConst hh z hr
  -- Step 2 transferred to `{X ∈ S_G}`
  have incl1 : {ω | ∀ k ∈ F, internalDiam (D (Y ω))
      (affFwd r z '' confCtrs p.δ 0 (confComp F k))
      (affOpens r z (w33G p.δ (confComp F k))) ≤ ENNReal.ofReal (s * c r)} ≤ᵐ[P] X ⁻¹' SG := by
    filter_upwards [hharm, hcl, hFmall] with ω h1 h2 h3 hYev
    obtain ⟨𝔥, h𝔥, hT𝔥⟩ := h1
    obtain ⟨hfs, hfE⟩ := hcut _ 𝔥 h𝔥 hT𝔥
    intro k u hu v hv
    rw [← h3 k 𝔥 h𝔥 hT𝔥 _ hfs (hfE.mono (hWV8 k)) u (hKW k hu) v (hKW k hv)]
    rw [h2 𝔥 (by rw [eU]; exact h𝔥) (pairing_congr33G eU.symm hT𝔥) (Wk k) (Wk k).isOpen (hWaff k)
      _ (hfE.mono (hWV8 k)) u v]
    have hu2 : u ∈ affFwd r z '' confCtrs p.δ 0 (confComp F k.1) := hu
    have hv2 : v ∈ affFwd r z '' confCtrs p.δ 0 (confComp F k.1) := hv
    refine le_trans ?_ (hYev k.1 k.2)
    unfold internalDiam
    exact le_iSup₂_of_le u hu2 (le_iSup₂_of_le v hv2 le_rfl)
  have hPG : ENNReal.ofReal 𝔭 ≤ P (X ⁻¹' SG) := hPY.trans (measure_mono_ae incl1)
  -- Step 1: `E^U ∩ {X ∈ S_G} ⊆ fatG`
  have incl2 : (confEU ξ c D P h p r z T ∩ X ⁻¹' SG : Set Ω) ≤ᵐ[P]
      {ω | fatG p (D (h ω)) (scaleFac ξ c (h ω) r z) r z T} := by
    filter_upwards [hharm, hFmall, hlink, hS1, hW', hca] with ω h1 h3 h4 h5 h6 h7
    rintro ⟨hE, hXSG⟩
    obtain ⟨𝔥, h𝔥, hT𝔥⟩ := h1
    obtain ⟨hfs, hfE⟩ := hcut _ 𝔥 h𝔥 hT𝔥
    intro k hk
    rw [hFr] at hk ⊢
    set kk : F := ⟨k, hk⟩
    have hrec : circleAvg (recField h ρ w ω) r z = circleAvg (h ω) r z - circleAvg (h ω) ρ w := by
      rw [recField, h7]; ring
    have hWsub : confFatW (p.δ * r) z (Cf kk) ⊆ V8 := by rw [← eW]; exact hWV8 kk
    have hup : ∀ u ∈ confFatW (p.δ * r) z (Cf kk),
        𝔥 u ≤ circleAvg (recField h ρ w ω) r z + p.A := by
      intro u hu
      have hu' := confFatW_subset_innerPart hε z (hCr kk) hu
      have hb := hE.2.2 u hu'
      rw [h4 𝔥 h𝔥 hT𝔥 u hu'.1, abs_le] at hb
      rw [hrec]; linarith [hb.2]
    have key := h5 𝔥 h𝔥 hT𝔥 (confFatW (p.δ * r) z (Cf kk)) isOpen_thickening hWsub hup
      (confCtrs (p.δ * r) z (Cf kk))
    refine key.trans ?_
    have hY'b : internalDiam (D (Y' ω)) (confCtrs (p.δ * r) z (Cf kk))
        (confFatW (p.δ * r) z (Cf kk)) ≤ ENNReal.ofReal t := by
      unfold internalDiam
      refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
      rw [← h6 𝔥 h𝔥 hT𝔥 (confFatW (p.δ * r) z (Cf kk)) isOpen_thickening hWsub _
        (hfE.mono hWsub) u v]
      have hu' : u ∈ Kk kk := by rw [eK]; exact hu
      have hv' : v ∈ Kk kk := by rw [eK]; exact hv
      have e := h3 kk 𝔥 h𝔥 hT𝔥 _ hfs (hfE.mono (hWV8 kk)) u (hKW kk hu') v (hKW kk hv')
      rw [eW] at e
      rw [e]
      exact hXSG kk u hu' v hv'
    calc ENNReal.ofReal (Real.exp (ξ * (p.A + circleAvg (h ω) r z))) *
          internalDiam (D (Y' ω)) (confCtrs (p.δ * r) z (Cf kk)) (confFatW (p.δ * r) z (Cf kk))
        ≤ ENNReal.ofReal (Real.exp (ξ * (p.A + circleAvg (h ω) r z))) * ENNReal.ofReal t := by
          gcongr
      _ = ENNReal.ofReal (p.c / 100 * scaleFac ξ c (h ω) r z) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [scaleFac, ht_def, hs_def, mul_add, Real.exp_add, Real.exp_neg]
          field_simp
  -- Step 3: the conditioning argument
  have hWm := measurable_toSig (recSigma_le hh ρ w Uᶜ)
  have key := condFKG_freeze hWm hX.1 hX.2.1 hSG hSF hfkg (measurableSet_val_preimage hB)
  have eB : toSig (recSigma h ρ w Uᶜ) ⁻¹' (SigOmega.val ⁻¹' B) = B := rfl
  rw [eB] at key
  have h1 : P (B ∩ confEU ξ c D P h p r z T) =
      P (B ∩ {ω | (toSig (recSigma h ρ w Uᶜ) ω, X ω) ∈ SF}) :=
    measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ B) hEU)
  have h2 : P (B ∩ {ω | (toSig (recSigma h ρ w Uᶜ) ω, X ω) ∈ SF} ∩ X ⁻¹' SG) ≤
      P (B ∩ confEU ξ c D P h p r z T ∩
        {ω | fatG p (D (h ω)) (scaleFac ξ c (h ω) r z) r z T}) := by
    refine measure_mono_ae ?_
    filter_upwards [hEU.symm.le, incl2] with ω h₁ h₂
    rintro ⟨⟨hωB, hωF⟩, hωG⟩
    have hωE : ω ∈ confEU ξ c D P h p r z T := h₁ hωF
    exact ⟨⟨hωB, hωE⟩, h₂ ⟨hωE, hωG⟩⟩
  have h3 : ENNReal.ofReal 𝔭 * P (B ∩ {ω | (toSig (recSigma h ρ w Uᶜ) ω, X ω) ∈ SF}) ≤
      P (X ⁻¹' SG) * P (B ∩ {ω | (toSig (recSigma h ρ w Uᶜ) ω, X ω) ∈ SF}) := by
    gcongr
  rw [h1]
  exact (h3.trans key).trans h2

/-- **CONF Lemma 3.6** (`CONFLem3_6AtAE0`) from CONF L2.10 at `confU` and DFGPS Lemma 3.8, for
valid `p` with `δ < 1/8` -/
theorem conf36_lem3_6AtAE0_at (h38 : DFGPSLem3_8) (hL : CONFLem2_10AtConfU) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (hp : p.Valid) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c) : CONFLem3_6AtAE0 γ D c p :=
  conf36_lem3_6AtAE0_of_h38 h38 hγ hγ2 hp hδ8 hD (l33Gen_fatG_lem2_10_at hγ hγ2 hD hL hp hδ8)

end LQGMetric.CONF
