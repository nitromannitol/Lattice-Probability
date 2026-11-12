/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112L3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2E
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K1

/-!
# D112 packet L1, part 3: CONF Lemma 3.3 for `fatG` (`L33Gen γ D c p (fatG p)`)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.3 (C:1176–1244) in the corrected form
of decision D112 (`decisions/DEC-112.md` §2): Steps 1–3 of CONF's proof for the family
`(K_C, W_C)` of the grid components `C` of the free squares.

* Step 1 (C:1200–1205): condition 3 of `E^U_r(z)` on `W_C ⊆ U_{δr/4}`
  (`confFatW_subset_innerPart`), the link "`harmPart = 𝔥 + h_ρ(w)`" between the Blueprint
  harmonic part and the harmonic part of the Markov decomposition (`CONFHarmPartLink`, open
  input, D110 P3) and `zb_step1_of`.
* Step 2 (C:1217–1234): `conf33G_step2` (S3D112L2), with the open input `CONFHarmLowZB`; the
  event `G^U` is expressed through the zero-boundary metrics `F_C(h̊^U|_{W_C})` of CONF Remark 1.2
  (`confZBMetricN`), so that it is an event of `h̊^U` alone (C:1213).
* Step 3 (C:1236–1243): CONF Proposition 2.8 (FKG for the LQG metric) in the frozen form consumed
  by `condFKG_freeze` (`CONFFKGFrozenEU`, open input: for a.e. realization of `h|_{ℂ∖U}`, the
  section of `E^U_r(z)` and the `D_{h̊}`-diameter event are positively correlated under the law
  of `h̊^U`; both are non-increasing in `D_{h̊}`, C:1238–1242).

The final assembly `l33Gen_fatG` follows `confLem3_3_of_steps` (S3L33M).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **The harmonic part of the Markov decomposition is the Blueprint harmonic part** (CONF
C:1187–1190; D110 P3): `𝔥^U = 𝔥 + h_ρ(w)` on `U`, where `𝔥` is the harmonic part of
`(h − h_ρ(w)) − h̊^U`, for a version `X = (h − h_ρ(w)) − G` of `h̊^U` with `G`
`σ((h − h_ρ(w))|_{ℂ∖U})`-measurable (the version of `exists_isL33ZBPart`). Open input. -/
def CONFHarmPartLink : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → ∀ (U : Set ℂ) (hU : IsOpen U),
    Bornology.IsBounded U → Disjoint U (sphere w ρ) → ∀ X G : Ω → DistC,
    IsL33ZBPart P h ρ w U hU X → Measurable[recSigma h ρ w Uᶜ] G →
    (∀ ω, X ω = recField h ρ w ω - G ω) →
    ∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
      ∀ u ∈ U, harmPart P h U ω u = 𝔥 u + circleAvg (h ω) ρ w

/-- the `D_{h̊}`-diameter event `{x : ∀ i, sup_{u,v ∈ A i} F_i(x|_{V i})(u,v) ≤ t}` -/
def zbDiamSet {ι : Type} (V : ι → Opens ℂ) (Fm : ∀ i, DistOn (V i) → ℂ → ℂ → ℝ≥0∞)
    (A : ι → Set ℂ) (t : ℝ) : Set DistC :=
  {x | ∀ i, ∀ u ∈ A i, ∀ v ∈ A i, Fm i (restrictTo (V i) x) u v ≤ ENNReal.ofReal t}

/-- the cut-off `φ𝔥` of the harmonic part: continuous, supported in `U`, equal to `𝔥` on `V` -/
lemma exists_cutoff33G {U V : Set ℂ} (hU : IsOpen U) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ U) :
    ∃ (φ : C(ℂ, ℝ)) (δ' : ℝ) (hδ' : 0 < δ'), ∀ (T : DistC) (𝔥 : ℂ → ℝ),
      InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ ψ : TestOn (toOpens U hU), restrictTo (toOpens U hU) T ψ = ∫ y, 𝔥 y * ψ y) →
      tsupport ⇑(DFGPS.L217.harmFn φ δ' hδ' T) ⊆ U ∧
        EqOn ⇑(DFGPS.L217.harmFn φ δ' hδ' T) 𝔥 V := by
  obtain ⟨φ, U₁, δ', -, -, hKU₁, hφ1, hδ', hφU⟩ :=
    DFGPS.L217.exists_bump_of_isCompact hVc hU hVU
  refine ⟨φ, δ', hδ', fun T 𝔥 h𝔥 hT => ?_⟩
  have hφU' : ∀ x, φ x ≠ 0 → closedBall x δ' ⊆ (toOpens U hU : Set ℂ) := hφU
  have h𝔥' : InnerProductSpace.HarmonicOnNhd 𝔥 (toOpens U hU : Set ℂ) := h𝔥
  have heq := DFGPS.L217.harmFn_eq_of_harmonic h𝔥' hT hδ' hφU'
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hsub : Function.support ⇑(DFGPS.L217.harmFn φ δ' hδ' T) ⊆ {y | φ y ≠ 0} :=
      fun y hy h0 => hy (by rw [heq y, h0, zero_mul])
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 (closure_mono hsub hx) δ' hδ'
    exact hφU y hy (by rw [mem_closedBall]; exact hxy.le)
  · rw [heq x, hφ1 x (hKU₁ (subset_closure hx)), one_mul]

/-- `exists_isL33ZBPart` (S3L33M) with the outside-measurable part `G` exported -/
theorem exists_isL33ZBPart_G {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ρ : ℝ} (hρ : 0 < ρ)
    (w : ℂ) {U : Set ℂ} (hU : IsOpen U) (hUw : Disjoint U (sphere w ρ)) :
    ∃ X G : Ω → DistC, IsL33ZBPart P h ρ w U hU X ∧ Measurable[recSigma h ρ w Uᶜ] G ∧
      ∀ ω, X ω = recField h ρ w ω - G ω := by
  have hh' := isWholePlaneGFF_recField hh ρ w
  have hn : ∀ᵐ ω ∂P, circleAvg (recField h ρ w ω) ρ w = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh w hρ] with ω hω
    simp only [recField, hω, add_neg_cancel]
  obtain ⟨hh₀, hz, hdec, hharm, ⟨G, hGm, hhG⟩, -, hzb, hvan, hind⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P (recField h ρ w) hh' hρ w hn (toOpens U hU) hUw
  have hle : recSigma h ρ w Uᶜ ≤ mΩ := recSigma_le hh ρ w Uᶜ
  have hGm' : Measurable G := hGm.mono hle le_rfl
  set X : Ω → DistC := fun ω => recField h ρ w ω - G ω with hX_def
  have hXm : Measurable X := by
    refine GFFInv.measurable_distC_iff.2 fun φ => ?_
    exact ((GFFInv.measurable_pair φ).comp hh'.measurable).sub ((GFFInv.measurable_pair φ).comp hGm')
  have hXz : X =ᵐ[P] hz := by
    filter_upwards [hhG] with ω hω
    simp only [hX_def, hdec ω, ← hω, add_sub_cancel_left]
  have hindX : Indep (MeasurableSpace.comap X inferInstance) (recSigma h ρ w Uᶜ) P :=
    MarkovAsm.indep_comap_congr hle hind hXz.symm
  refine ⟨X, G, ⟨hXm, ?_, hh₀, hz, hdec, hXz, hharm, hzb, hvan⟩, hGm, fun ω => rfl⟩
  rw [IndepFun_iff_Indep, comap_toSig]
  exact hindX.symm

lemma pairing_congr33G {U U' : Set ℂ} (e : U = U') {hU : IsOpen U} {hU' : IsOpen U'} {T : DistC}
    {𝔥 : ℂ → ℝ} (H : ∀ φ : TestOn (toOpens U hU), restrictTo (toOpens U hU) T φ = ∫ x, 𝔥 x * φ x) :
    ∀ φ : TestOn (toOpens U' hU'), restrictTo (toOpens U' hU') T φ = ∫ x, 𝔥 x * φ x := by
  subst e; exact H

end LQGMetric.CONF
