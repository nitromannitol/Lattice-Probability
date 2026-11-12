/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3GeoC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3GeoB

/-!
# GM Lemma 4.20, the `Stab`-piece: `Stab_{k,r}(z) ∩ F_k ∈ 𝓕_{k+1}` a.s. (D81, G2)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.20 (l. 2333–2356; the
`Stab` part l. 2352–2354: "on `F_k`, `Stab_{r,k}(z)` is determined by `𝓕_{k+1}`, since the
`D_h(·,·;ℂ∖cl B_r(z))`-geodesics … are contained in `𝓑^•_{s_{k+1}}`"). Decision
`decisions/DEC-81.md`, packet G2: piece method (`exists_fieldSigma_piece`) with the metric event
`gmStabSetN ∩ gmGeoSet` (universally measurable on `lenSet`, saturated by
`gm_stab_of_internal_eq_geo`), and `Stab =ᵐ gmStabSetN` (`gm_stab_ae_eq_stabSetN`, GM.S4.1).

* `gm_uMeas_of_an`: an analytic set on `lenSet` is universally measurable there;
* `gm_aeEventIn_sigA_of_sat`: a saturated, universally measurable metric event is a.s. in
  `σ(𝓑^•_{τ_R ck}, h|_{𝓑^•_{τ_R ck}})` (the piece method in general form);
* `gm_stabGeo_aeEventIn_sigA`, `gm_stab_piece_aeEventIn`: the `Stab`-piece of Lemma 4.20.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- analytic on `lenSet` ⇒ universally measurable on `lenSet` -/
theorem gm_uMeas_of_an {A : Set ContMetric} (hA : GMAnalyticOn lenSet A) :
    UMeasurableSet (lenSet ∩ A) := by
  obtain ⟨β, m, sb, S, hS, hAS⟩ := hA
  have e : lenSet ∩ A = lenSet ∩ {d | ∃ b, (d, b) ∈ S} := by
    ext d
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨hd, ha⟩ => ⟨hd, (hAS d hd).1 ha⟩, fun ⟨hd, hb⟩ => ⟨hd, (hAS d hd).2 hb⟩⟩
  rw [e]
  exact (UMeasurableSet.of_measurableSet measurableSet_lenSet).inter
    (UMeasurableSet.setOf_exists hS)

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **piece method** (locality, GM l. 1654): a metric event `X`, universally measurable on
`lenSet` and saturated for agreement of internal metrics on open sets `U ⊇ 𝓑^•_{τ_R ck}`, is a.s.
an event of `σ(𝓑^•_{τ_R ck}, h|_{𝓑^•_{τ_R ck}})` -/
theorem gm_aeEventIn_sigA_of_sat (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {R ck : ℝ} (hR : 0 < R)
    (hck : 1 < ck) {X : Set ContMetric} (hX : UMeasurableSet (lenSet ∩ X))
    (hsat : ∀ d₁ ∈ lenSet, ∀ d₂ ∈ lenSet, ∀ U : Set ℂ, IsOpen U → d₁.internal U = d₂.internal U →
      filledBall d₁ 𝕫 (tauD d₁ 𝕫 R * ck) ⊆ U → d₁ ∈ X → d₂ ∈ X) :
    AEEventIn P (localSigma h (fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * ck)))
      {ω | D (h ω) ∈ X} := by
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  refine aeEventIn_localSigma h (fun ω => gm_filledBall_isClosed _ _ _) fun n =>
    aeEventIn_hullSigma_of_pieces h _ (by
      filter_upwards [hlen] with ω hω; exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _) n
      fun s => ?_
  set S' := hullFin n s
  set Hs : Set ContMetric := {d | dyadicHull n (filledBall d 𝕫 (tauD d 𝕫 R * ck)) = S'}
  set Bs : Set DistC := D ⁻¹' (lenSet ∩ (Hs ∩ X)) with hBs
  have e : lenSet ∩ (Hs ∩ X) = (lenSet ∩ Hs) ∩ (lenSet ∩ X) := by
    ext d; simp only [mem_inter_iff]; tauto
  have hnull : NullMeasurableSet Bs (P.map h) := by
    rw [hBs, e]
    exact (((gm_uMeas_of_an (gmE_hullAn 𝕫 R ck n S')).inter hX).preimage
      hD.measurable).nullMeasurableSet _
  obtain ⟨F, hF, hEF⟩ := exists_fieldSigma_piece hD P h (Tight.isGFFPlusCont_of_wp hh) hlen
    isOpen_interior hnull (by
      rintro g₁ g₂ h1 h2 heq ⟨-, hS, hX1⟩
      have l1 := isLength_of_mem_lenSet h1
      have l2 := isLength_of_mem_lenSet h2
      have hKU : filledBall (D g₁) 𝕫 (tauD (D g₁) 𝕫 R * ck) ⊆ interior S' :=
        hS ▸ subset_interior_dyadicHull n _
      obtain ⟨hτ, hball⟩ := gm_tk_congr l1 l2 hck isOpen_interior heq
        (gm_tauD_pos _ 𝕫 hR) hKU
      refine ⟨h2, ?_, hsat _ h1 _ h2 _ isOpen_interior heq hKU hX1⟩
      show dyadicHull n (filledBall (D g₂) 𝕫 (tauD (D g₂) 𝕫 R * ck)) = S'
      rw [hτ, gm_filledBall_congr (hball _ le_rfl)]; exact hS)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hEF, hlen] with ω hω hl hS
  have := Iff.of_eq hω
  simp only [hBs, Hs, mem_preimage, mem_inter_iff, mem_ofPred_eq, hS, hl, true_and] at this
  exact this

/-- **the `Stab`-piece with (4.39), a.s. in `σ(𝓑^•_{t_{k+1}}, h|)`** -/
theorem gm_stabGeo_aeEventIn_sigA (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ e : ℝ} {k : ℕ} {Rads : Set ℝ} {z : ℂ} (hℓ𝕣 : 0 < ℓ * 𝕣)
    (hε : 0 < ε) (ha : 0 < lam4 * ε * 𝕣) (hr : 0 < r) (hre : r ≤ e) (he : 0 < e)
    (hρe : e < ρ) :
    AEEventIn P (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1)))
      (gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩
        {ω | D (h ω) ∈ gmGeoSet 𝕫 (ℓ * 𝕣) (1 + (k + 1) * ε ^ β) z ρ e}) := by
  have hβ : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have hβ2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hk0 : 0 ≤ (k : ℝ) * ε ^ β := by positivity
  have hck : 1 < 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β) := by push_cast; nlinarith
  have hcg : 1 + ((k : ℝ) + 1) * ε ^ β ≤ 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β) := by
    push_cast; linarith
  have hcc : 1 + (k : ℝ) * ε ^ β + ε ^ (2 * β) ≤ 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β) := by
    push_cast; nlinarith
  have hc₁ : 1 + (k : ℝ) * ε ^ β ≤ 1 + (k : ℝ) * ε ^ β + ε ^ (2 * β) := by linarith
  have hcg0 : 0 < 1 + ((k : ℝ) + 1) * ε ^ β := by nlinarith
  have hE := gm_stab_ae_eq_stabSetN (𝕫 := 𝕫) (z := z) (ℓ := ℓ) (β := β) (lam1 := lam1)
    (ν := ν) (r := r) (k := k) (Rads := Rads) h38 hC24 hC27 hC14 hγ hγ2 hD hh hε ha
  have hX := gm_aeEventIn_sigA_of_sat h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hck
    (X := gmStabSetN 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) lam1 lam4 ε ν 𝕣
      Rads z r ∩ gmGeoSet 𝕫 (ℓ * 𝕣) (1 + (k + 1) * ε ^ β) z ρ e)
    (by
      have e2 : lenSet ∩ (gmStabSetN 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β))
          lam1 lam4 ε ν 𝕣 Rads z r ∩ gmGeoSet 𝕫 (ℓ * 𝕣) (1 + (k + 1) * ε ^ β) z ρ e) =
          (lenSet ∩ gmStabSetN 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β))
            lam1 lam4 ε ν 𝕣 Rads z r) ∩
          (lenSet ∩ gmGeoSet 𝕫 (ℓ * 𝕣) (1 + (k + 1) * ε ^ β) z ρ e) := by
        ext d; simp only [mem_inter_iff]; tauto
      rw [e2]
      exact (gm_uMeasurableSet_stabSetN (gm_arcRelAn 𝕫) (gm_avoidRelAn 𝕫 z r) _ _ _ _ _ _ _ _
        _).inter (UMeasurableSet.of_measurableSet (gm_measurableSet_geoSet _ _ _ _ _ _)))
    (fun d₁ h₁ d₂ h₂ U hU heq hKU hd => gm_stab_of_internal_eq_geo h₁ h₂ hU heq hc₁ hcc hcg0 hcg
      hck hℓ𝕣 he hρe hr hre hKU hd)
  have hcT := funext (gm_s4T_eq D h 𝕫 ℓ 𝕣 ε β (k + 1))
  obtain ⟨F, hF, hEF⟩ := hX
  refine ⟨F, ?_, ?_⟩
  · unfold gmSigA; rw [hcT]; exact hF
  · refine (EventuallyEqSet.inter hE EventuallyEq.rfl).trans ?_
    exact hEF

/-- **G2: the `Stab`-piece of GM Lemma 4.20** (l. 2352–2354): for any event `F` of `𝓕_{k+1}`
contained in the geodesic part `gmGeo k` of `F_k`, and `0 < r ≤ ε𝕣`,
`Stab_{r,k}(z) ∩ F` is a.s. an event of `𝓕_{k+1}` -/
theorem gm_stab_piece_aeEventIn (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} {k : ℕ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < R.lam 3 * ε * 𝕣) (hρe : ε * 𝕣 < 2 * R.lam 3 * (ε * 𝕣)) {F : Set Ω}
    (hF : AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) F)
    (hFG : F ⊆ gmGeo D h R 𝕫 𝕣 ε β k) (z : ℂ) {r : ℝ} (hr : 0 < r) (hre : r ≤ ε * 𝕣) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      (gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε) z r ∩ F) := by
  have he : 0 < ε * 𝕣 := hr.trans_le hre
  have e : gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε) z r ∩ F =
      (gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν (p4Rads R 𝕣 ε) z r ∩
        {ω | D (h ω) ∈ gmGeoSet 𝕫 (R.ℓ * 𝕣) (1 + (k + 1) * ε ^ β) z (2 * R.lam 3 * (ε * 𝕣))
          (ε * 𝕣)}) ∩ F := by
    ext ω
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hS, hω⟩
      exact ⟨⟨hS, gm_gmGeo_geoSet (hFG hω) hS.1⟩, hω⟩
    · rintro ⟨⟨hS, -⟩, hω⟩
      exact ⟨hS, hω⟩
  rw [e]
  obtain ⟨G, hG, hEG⟩ := gm_stabGeo_aeEventIn_sigA (k := k) (lam1 := R.lam 0) (ν := R.ν)
    (Rads := p4Rads R 𝕣 ε) (z := z) h38 hC24 hC27 hC14 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε ha hr hre he hρe
  exact gm_aeEventIn_inter ⟨G, (le_sup_left : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _ hG,
    hEG⟩ hF

end LQGMetric.GM
