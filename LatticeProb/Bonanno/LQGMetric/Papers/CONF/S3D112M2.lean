/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112M2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L3
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAsm
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2D
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer2Fub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Markov version of `h̊^U` is the zero-boundary GFF extended by `0` (CONF L3.3, corrected)

`CONFZBExtOfMarkov` (S3D112L3) is **false as stated**: for any `X G` as there and any
deterministic distribution `m` supported on `∂U` (e.g. `δ_{x₀}`, `x₀ ∈ ∂U`), the pair
`(X + m, G − m)` satisfies all its hypotheses (`IsL33ZBPart` only sees `X|_U`, `X` off `cl U` and
`X`'s independence; `G − m` is still outside-measurable and harmonic on `U`), but `X + m` is not
centred. The law of `X` is pinned only up to such a deterministic mean (CONF C:1187–1190 uses the
canonical decomposition).

Corrected form, proved here: **the** Markov decomposition of LM Lemma 2.1 (the one built from
`MarkovExt.zbExt`, `Field/MarkovAsm.markov_decomp_ae`), transported to the normalization
`h_ρ(w) = 0` as in `DFGPS.markov_normAt`, has a zero-boundary part with the law `IsZBExtField`.

* `markov_normAt_ext` : `DFGPS.markov_normAt` for bounded `V`, with the concrete decomposition and
  the extra clause `IsZBExtField V hz P` (proof: `DFGPS.markov_normAt`'s, with
  `MarkovAsm.markov_decomp_ae`'s construction in place of the abstract `LMLem2_1`);
* `exists_isL33ZBPart_G_ext` : `exists_isL33ZBPart_G` (S3D112L3) plus `IsZBExtField`.

Sources: LM (arXiv:1905.00380) Lemma 2.1; GMSh (arXiv:1807.07511) Lemma 2.2; the scaling
reduction as in `DFGPS.markov_normAt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.CONF

open Blueprint GFFInv DFGPS

variable {r : ℝ} {z : ℂ}

lemma isBounded_preOpens (hr : 0 < r) {V : Opens ℂ} (hVb : Bornology.IsBounded (V : Set ℂ)) :
    Bornology.IsBounded (preOpens r z V : Set ℂ) := by
  obtain ⟨R, hR⟩ := hVb.subset_closedBall (0 : ℂ)
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r⁻¹ * (R + ‖z‖))).subset fun y hy => ?_
  have h1 : r • y + z ∈ (V : Set ℂ) := (mem_preOpens hr.ne' V y).1 hy
  have h2 := hR h1
  rw [mem_closedBall, dist_zero_right] at h2 ⊢
  have h3 : ‖r • y‖ ≤ R + ‖z‖ := by
    calc ‖r • y‖ = ‖(r • y + z) - z‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖r • y + z‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ R + ‖z‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at h3
  rw [le_inv_mul_iff₀ hr]
  exact h3

variable {Ω : Type} [MeasurableSpace Ω]

/-- **`DFGPS.markov_normAt` with the law of `h̊` on `𝒟'(ℂ)`** (bounded `V`): the Markov
decomposition at the normalization `h_r(z) = 0`, with `h̊` the zero-boundary GFF extended by `0` -/
theorem markov_normAt_ext (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (hr : 0 < r) (z : ℂ)
    (hn : ∀ᵐ ω ∂P, circleAvg (h ω) r z = 0) (V : Opens ℂ)
    (hV : Disjoint (V : Set ℂ) (sphere z r)) (hVb : Bornology.IsBounded (V : Set ℂ)) :
    ∃ hh hz : Ω → DistC, (∀ ω, h ω = hh ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧
        ∀ φ : TestOn V, restrictTo V (hh ω) φ = ∫ x, g x * φ x) ∧
      (∃ G : Ω → DistC, @Measurable Ω DistC (fieldSigmaClosed h (V : Set ℂ)ᶜ) _ G ∧
        hh =ᵐ[P] G) ∧
      IndepFun hh hz P ∧
      IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P ∧
      (∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0) ∧
      Indep (MeasurableSpace.comap hz inferInstance) (fieldSigmaClosed h (V : Set ℂ)ᶜ) P ∧
      IsZBExtField V hz P := by
  set g : Ω → DistC := fun ω => affineComp r z (h ω) with hg_def
  have hgN : IsNormalizedWPGFF g P := by
    refine ⟨hh.affineComp hr z, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_affineComp hh hr z, hn] with ω h1 h2
    rw [h1, h2]
  set V' := preOpens r z V
  have hUV : ∀ y : ℂ, y ∈ V' ↔ r • y + z ∈ V := mem_preOpens hr.ne' V
  have hV' := disjoint_preOpens hr hV
  have hVb' : Bornology.IsBounded (V' : Set ℂ) := isBounded_preOpens hr hVb
  obtain ⟨hz', hzm, hzae, hvan⟩ := MarkovVer2.exists_dist_version_zbExt hgN hV'
  have hext : IsZBExtField V' hz' P := isZBExtField_of_zbExt hgN.1 hVb' hzm hzae
  set hh' : Ω → DistC := fun ω => g ω - hz' ω with hh'_def
  have hsum : ∀ ω, g ω = hh' ω + hz' ω := fun ω => (sub_add_cancel _ _).symm
  have hharm := MarkovAsm.ae_harmonic_sub hgN hV' hz' hzae
  obtain ⟨G', hG'm, hG'⟩ := MarkovAsm.exists_germ_dist_version hgN hzae
    (MarkovGermVer.exists_germ_version_harm_of_bdd hgN hV' hVb')
  have hind := MarkovAsm.indepFun_sub_dist hgN hV' hzae
  have hzb := MarkovAsm.isZeroBoundaryGFF_restrict hgN hV' hzm hzae
  have hindep := MarkovAsm.indep_dist_fieldSigmaClosed hgN hV' hzae
  have hmA : Measurable (affInvC r z) := measurable_affineComp _ _
  have hrec : ∀ ω, h ω = affInvC r z (g ω) := fun ω => (affInvC_affineComp hr.ne' (h ω)).symm
  refine ⟨fun ω => affInvC r z (hh' ω), fun ω => affInvC r z (hz' ω), fun ω => ?_, ?_,
    ⟨fun ω => affInvC r z (G' ω), ?_, ?_⟩, hind.comp hmA hmA, ?_, fun ω => ?_, ?_,
    isZBExtField_affineComp (inv_ne_zero hr.ne') hext⟩
  · rw [hrec, hsum, affInvC, GM.affineComp_add]
  · filter_upwards [hharm] with ω hω
    obtain ⟨g', hg'h, hg'p⟩ := hω
    refine ⟨g' ∘ affMap r z, ?_, fun φ => ?_⟩
    · have he : affMap r z = fun x : ℂ => ((r : ℂ)⁻¹) * (x + -z) := by
        funext x; simp only [affMap, Complex.real_smul]; push_cast; ring
      refine harmonicOnNhd_comp_holo V'.isOpen V.isOpen hg'h ?_ fun x hx => ?_
      · rw [he]; fun_prop
      · show affMap r z x ∈ (V' : Set ℂ)
        rw [SetLike.mem_coe, hUV]
        have : r • affMap r z x + z = x := by
          rw [affMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, neg_add_cancel_right]
        rw [this]; exact hx
    · rw [GM.restrictTo_apply_eq_scale hr hUV, affineComp_affInvC hr.ne', hg'p]
      conv_rhs => rw [GFFInv.integral_eq_smul_add _ hr z]
      congr 2
      funext v
      rw [GM.testScalePush_apply]
      have : affMap r z (r • v + z) = v := by
        rw [affMap, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      simp only [Function.comp_apply, this]
  · exact hmA.comp (hG'm.mono (fieldSigmaClosed_affineComp_le hr V h) le_rfl)
  · filter_upwards [hG'] with ω hω
    exact congrArg (affInvC r z) hω
  · have := hzb.affine (r := r⁻¹) (z := -(r⁻¹ • z)) (inv_ne_zero hr.ne')
    convert this using 2 with ω
    exact restrictTo_affInvC hr V (hz' ω)
  · refine DFunLike.ext _ _ fun φ => ?_
    have hUV2 : ∀ y : ℂ, y ∈ toOpens (closure (V' : Set ℂ))ᶜ isClosed_closure.isOpen_compl ↔
        r • y + z ∈ toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl := by
      intro y
      let T : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight z)
      have hT : (V' : Set ℂ) = T ⁻¹' (V : Set ℂ) := by ext y; exact hUV y
      show y ∈ (closure (V' : Set ℂ))ᶜ ↔ T y ∈ (closure (V : Set ℂ))ᶜ
      rw [hT, ← T.preimage_closure]; rfl
    rw [GM.restrictTo_apply_eq_scale hr hUV2, affineComp_affInvC hr.ne', hvan ω]
    simp
  · refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hindep ?_) ?_
    · rw [show (fun ω => affInvC r z (hz' ω)) = affInvC r z ∘ hz' from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hmA.comap_le
    · exact fieldSigmaClosed_le_affineComp hr V h

/-- **Corrected `CONFZBExtOfMarkov`** (CONF C:1187–1190): `exists_isL33ZBPart_G` (S3D112L3) for
bounded `U`, with the Markov version `X = (h − h_ρ(w)) − G` of `h̊^U` the zero-boundary GFF on `U`
extended by `0` (`IsZBExtField`) -/
theorem exists_isL33ZBPart_G_ext {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUw : Disjoint U (sphere w ρ)) :
    ∃ X G : Ω → DistC, IsL33ZBPart P h ρ w U hU X ∧ Measurable[recSigma h ρ w Uᶜ] G ∧
      (∀ ω, X ω = recField h ρ w ω - G ω) ∧ IsZBExtField (toOpens U hU) X P := by
  have hh' := isWholePlaneGFF_recField hh ρ w
  have hn : ∀ᵐ ω ∂P, circleAvg (recField h ρ w ω) ρ w = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh w hρ] with ω hω
    simp only [recField, hω, add_neg_cancel]
  obtain ⟨hh₀, hz, hdec, hharm, ⟨G, hGm, hhG⟩, -, hzb, hvan, hind, hext⟩ :=
    markov_normAt_ext P (recField h ρ w) hh' hρ w hn (toOpens U hU) hUw hUb
  have hle : recSigma h ρ w Uᶜ ≤ ‹MeasurableSpace Ω› := recSigma_le hh ρ w Uᶜ
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
  refine ⟨X, G, ⟨hXm, ?_, hh₀, hz, hdec, hXz, hharm, hzb, hvan⟩, hGm, fun ω => rfl,
    hext.congr hXm fun φ => ?_⟩
  · rw [IndepFun_iff_Indep, comap_toSig]
    exact hindX.symm
  · filter_upwards [hXz] with ω hω
    rw [hω]

end LQGMetric.CONF
