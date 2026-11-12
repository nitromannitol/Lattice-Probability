/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P6C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P6B
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20Conv
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.ExistenceAsmV
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG

/-!
# DFGPS Thm 1.2, P-4 items 4–5: Axiom V and convergence in probability

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1339–1386: Axiom V from Lemma 2.13 (T:1347–1350); convergence in probability for a GFF plus a
bounded continuous function from Lemma 2.12 (T:1376–1386) and the a.s. convergence in the coupling.

* `exists_subseq_coupling_ae'` — `exists_subseq_coupling_ae` together with the joint-law
  convergence along `ε ∘ φ` (the hypothesis of Lemma 2.13).
* `tendstoInProbLU_of_ae` — a.s. locally uniform convergence of the LFPP of a GFF plus a bounded
  continuous function implies convergence in probability (measurable versions `lfppC`,
  `tendstoInMeasure_of_tendsto_ae` on `C(B̄_R × B̄_R, ℝ)`, as in `L220.tendstoInProbLU_of_det`).
* `tendstoInProbLU_patchT` — the convergence clause of Theorem 1.2 for `patchT`.
* `tightAcrossScales_patchT` — Axiom V for `patchT` (Lemma 2.13 + `tightAcrossScales_of_ref`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP ExistenceAsm

/-- `exists_subseq_coupling_ae` with the joint-law convergence along `ε ∘ φ` -/
theorem exists_subseq_coupling_ae' (h28 : Lem2_8) (h20 : Lem2_20) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (h : Ω → DistC) (Dh : Ω → ContMetric),
      IsNormalizedWPGFF h P ∧ Measurable Dh ∧ (∀ᵐ ω ∂P, (Dh ω).IsLength) ∧
      (∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n p => (aEpsDF (xiGamma γ) (ε (φ n)))⁻¹ * lfppDist (xiGamma γ) (ε (φ n)) (h ω) p)
        (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) ∧
      ∀ F : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous F → (∃ C, ∀ x, |F x| ≤ C) →
        Tendsto (fun n => ∫ ω, F (pairJ ⊤ (h ω), toCMap fun p =>
            (aEpsDF (xiGamma γ) (ε (φ n)))⁻¹ * lfppDist (xiGamma γ) (ε (φ n)) (h ω) p) ∂P)
          atTop (𝓝 (∫ ω, F (pairJ ⊤ (h ω), (Dh ω).1) ∂P)) := by
  obtain ⟨ψ, hψ, Ω, _, P, _, h, Dh, hh, hDm, hconv⟩ := t12Coupling h28 γ hγ hγ2 ε hε hε0
  have hε0' : Tendsto (fun n => ε (ψ n)) atTop (𝓝 0) := hε0.comp hψ.tendsto_atTop
  obtain ⟨-, hT⟩ := h20 γ hγ hγ2 P h Dh (fun n => ε (ψ n)) hh hDm (fun n => hε _) hε0' hconv
  have hgff := isGFFPlusBddCont_of_normalizedWP hh
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_lfppC hgff (Y := fun ω => (Dh ω).1)
    (fun n => hε (ψ n)) hT
  have hconv' : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF (xiGamma γ) (ε ((ψ ∘ ns) n)))⁻¹ *
        lfppDist (xiGamma γ) (ε ((ψ ∘ ns) n)) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R) :=
    hae.mono fun ω hω => hω.1
  have hlen := (ae_isLength_agree h28 hγ hγ2 P h Dh (fun n => ε ((ψ ∘ ns) n)) hgff
    (fun n => hε _) (hε0'.comp hns.tendsto_atTop) hconv').mono fun ω hω => hω.1
  exact ⟨ψ ∘ ns, hψ.comp hns, Ω, inferInstance, P, inferInstance, h, Dh, hh, hDm, hlen, hconv',
    fun F hF hb => (hconv F hF hb).comp hns.tendsto_atTop⟩

/-- a.s. locally uniform convergence ⇒ convergence in probability (`TendstoInProbLU`) -/
theorem tendstoInProbLU_of_ae {ξ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) {εs : ℕ → ℝ}
    (hεs : ∀ k, 0 < εs k) {Y : Ω → ContMetric} (hY : Measurable Y)
    (hae : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) (h ω) p)
      (fun p => (Y ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) :
    TendstoInProbLU P (fun n ω => (aEpsDF ξ (εs n))⁻¹ • lfppDist ξ (εs n) (h ω)) atTop
      (fun ω => (Y ω).1) := by
  intro R hR δ hδ
  let ρ : C(ℂ × ℂ, ℝ) → C(L220.sqR R, ℝ) := fun u => u.restrict (L220.sqR R)
  have hρ : Continuous ρ := ContinuousMap.continuous_restrict _
  have hmeas := fun n => aemeasurable_lfppC hh (ξ := ξ) (hεs n).ne'
  let L : ℕ → Ω → C(ℂ × ℂ, ℝ) := fun n => (hmeas n).mk _
  have hL : ∀ n, Measurable (L n) := fun n => (hmeas n).measurable_mk
  have hLe : ∀ n, (fun ω => lfppC ξ (εs n) (h ω)) =ᵐ[P] L n := fun n => (hmeas n).ae_eq_mk
  have hcont := ae_all_iff.2 fun n =>
    hh.ae_tendstoLocallyUniformly_heatMollify (εs n) (hεs n).ne'
  have hLe' := ae_all_iff.2 hLe
  have hTIM : TendstoInMeasure P (fun n ω => ρ (L n ω)) atTop (fun ω => ρ (Y ω).1) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun n => (hρ.measurable.comp (hL n)).aestronglyMeasurable) ?_
    filter_upwards [hae, hcont, hLe'] with ω hω hc hl
    have hu := (hω R hR).congr (F' := fun n p => L n ω p)
      (Eventually.of_forall fun n p _ => by
        show _ = L n ω p
        rw [← hl n, lfppC_apply_of_continuous (hc n).2 p]
        rfl)
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hu
    exact ContinuousMap.tendsto_iff_tendstoUniformly.2 hu
  have hk := hTIM (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hk (fun _ => zero_le)
    fun n => measure_mono_ae ?_
  filter_upwards [hLe n, hcont] with ω hω hc hmem
  change ENNReal.ofReal δ ≤ _ at hmem ⊢
  refine hmem.trans (iSup₂_le fun p hp => ?_)
  have h1 : ((aEpsDF ξ (εs n))⁻¹ • lfppDist ξ (εs n) (h ω)) p = ρ (L n ω) ⟨p, hp⟩ := by
    show _ = L n ω p
    rw [← hω, lfppC_apply_of_continuous (hc n).2 p]
    simp [lfppDist, smul_eq_mul]
  have h2 : (Y ω).1 p = ρ (Y ω).1 ⟨p, hp⟩ := rfl
  rw [h1, h2, edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal (ContinuousMap.dist_apply_le_dist _)

/-- GFF plus continuous `f₀` = normalized GFF plus `f₀ + const` -/
theorem decomp_of {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {f₀ : Ω → C(ℂ, ℝ)} (hk : IsWholePlaneGFF (fun ω => h ω - ofCont (f₀ ω)) P) :
    ∃ (h₀ : Ω → DistC) (c : Ω → ℝ), IsNormalizedWPGFF h₀ P ∧
      ∀ ω, h ω = addFun (h₀ ω) (f₀ ω + ContinuousMap.const ℂ (c ω)) := by
  set k : Ω → DistC := fun ω => h ω - ofCont (f₀ ω)
  have hcm : Measurable fun ω => circleAvg (k ω) 1 0 :=
    (measurable_circleAvg_left 1 0).comp hk.measurable
  refine ⟨fun ω => addConst (k ω) (-circleAvg (k ω) 1 0), fun ω => circleAvg (k ω) 1 0,
    ⟨hk.addConst hcm.neg, ?_⟩, fun ω => ?_⟩
  · filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hk] with ω hω
    rw [hω]; ring
  · simp only [addConst, addFun_addFun']
    rw [addFun, ofCont_add', ofCont_add']
    simp only [k]
    have : ofCont (ContinuousMap.const ℂ (-circleAvg (h ω - ofCont (f₀ ω)) 1 0)) +
        ofCont (ContinuousMap.const ℂ (circleAvg (h ω - ofCont (f₀ ω)) 1 0)) = 0 := by
      rw [← ofCont_add']
      have e : ContinuousMap.const ℂ (-circleAvg (h ω - ofCont (f₀ ω)) 1 0) +
          ContinuousMap.const ℂ (circleAvg (h ω - ofCont (f₀ ω)) 1 0) = 0 := by
        ext; simp
      rw [e]; ext φ; simp [ofCont]
    rw [add_left_comm _ (ofCont (f₀ ω)), this, add_zero, sub_add_cancel]

/-- **the convergence clause of Theorem 1.2** (T:1376–1386) for `patchT` -/
theorem tendstoInProbLU_patchT (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) :
    TendstoInProbLU P
      (fun n ω => (aEpsDF (xiGamma γ) (εs n))⁻¹ • lfppDist (xiGamma γ) (εs n) (h ω)) atTop
      (fun ω => (patchT (xiGamma γ) εs hεs (h ω)).1) := by
  obtain ⟨hm, f₀, hf₀, hb, hk⟩ := hh
  obtain ⟨h₀, c, hh₀, hdec⟩ := decomp_of hk
  refine tendstoInProbLU_of_ae ⟨hm, f₀, hf₀, hb, hk⟩ hεs (measurable_patchT.comp hm) ?_
  have H12 := h12 γ hγ hγ2 P h₀ (fun ω => patchT (xiGamma γ) εs hεs (h₀ ω)) εs
    (isGFFPlusBddCont_of_normalizedWP hh₀) hεs hε0 (hG P h₀ hh₀).2
  filter_upwards [H12, ae_patchT_isGFFPlusCont HG h12 hγ hγ2 hε0 hG hh₀] with ω h1 hW R hR
  obtain ⟨hD, hW⟩ := hW
  obtain ⟨M, hM⟩ := hb ω
  have hgM : ∀ z, |(f₀ ω + ContinuousMap.const ℂ (c ω)) z| ≤ M + |c ω| := fun z => by
    rw [ContinuousMap.add_apply, ContinuousMap.const_apply]
    exact (abs_add_le _ _).trans (by linarith [hM z])
  have := h1 (fun _ => f₀ ω + ContinuousMap.const ℂ (c ω)) (f₀ ω + ContinuousMap.const ℂ (c ω))
    (M + |c ω|) (fun _ z => hgM z) hgM
    (fun R _ => Metric.tendstoUniformlyOn_iff.2 fun e he =>
      Eventually.of_forall fun n x _ => by simpa using he) R hR
  rw [hdec ω, hW]
  exact this

/-- `D_{h − h_1(0)} = e^{−ξ h_1(0)} D_h` for a whole-plane GFF (Axioms I, III) -/
theorem ae_patchT_normalize (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (patchT (xiGamma γ) εs hεs (addConst (h ω) (-circleAvg (h ω) 1 0))).1 (u, v) =
        Real.exp (-xiGamma γ * circleAvg (h ω) 1 0) * (patchT (xiGamma γ) εs hεs (h ω)).1 (u, v) := by
  have hc : IsGFFPlusCont h P := by
    refine ⟨hh.measurable, fun _ => 0, measurable_const, ?_⟩
    have h0 : ofCont 0 = 0 := by ext φ; simp [ofCont]
    simpa [h0] using hh
  obtain ⟨hl, hw⟩ := ae_length_weyl_isGFFPlusCont HG h12 hγ hγ2 hε0 hG hc
  filter_upwards [hl, hw] with ω h1 h2 u v
  rw [dist_addConst_of_weyl (Dm := patchT (xiGamma γ) εs hεs) h1 h2, mul_neg, neg_mul]

/-- **Axiom V** for `patchT` (T:1347–1350, Lemma 2.13) -/
theorem tightAcrossScales_patchT (h13 : Lem2_13) (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} (hεs : ∀ k, 0 < εs k)
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} {Dh : Ω → ContMetric}
    (hh : IsNormalizedWPGFF h P) (hDm : Measurable Dh) (hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength)
    (hconv : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF (xiGamma γ) (εs n))⁻¹ * lfppDist (xiGamma γ) (εs n) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R))
    (hJ : ∀ F : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous F → (∃ C, ∀ x, |F x| ≤ C) →
        Tendsto (fun n => ∫ ω, F (pairJ ⊤ (h ω), toCMap fun p =>
            (aEpsDF (xiGamma γ) (εs n))⁻¹ * lfppDist (xiGamma γ) (εs n) (h ω) p) ∂P)
          atTop (𝓝 (∫ ω, F (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) :
    ∃ c : ℝ → ℝ, TightAcrossScales (xiGamma γ) (patchT (xiGamma γ) εs hεs) c := by
  obtain ⟨c, Λ, hΛ, hcl, hb, hT⟩ := h13 γ hγ hγ2 εs hεs hε0
  obtain ⟨htight, hclos⟩ := hT P h Dh hh hDm hJ
  have hX : ∀ r, P.map (fun ω => scaledAt0 (xiGamma γ) (patchT (xiGamma γ) εs hεs) c r (h ω)) =
      P.map (fun ω => ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0)) •
        (Dh ω).1.comp (scaleArgs r)) := fun r =>
    Measure.map_congr ((ae_patchT_eq HG hh hεs hε0 hlen hconv).mono fun ω hω => by
      simp only [scaledAt0, hω])
  refine ⟨c, tightAcrossScales_of_ref measurable_patchT (fun r hr => (hcl r hr).1) hΛ hb
    (fun P _ h hh => ae_patchT_normalize HG h12 hγ hγ2 hε0 hG P h hh) P h hh.1 ?_ ?_⟩
  · simp_rw [hX]; exact htight
  · simp_rw [hX]; exact hclos

end LQGMetric.DFGPS.T12
