/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4M5 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LM Lemma 3.1, canonical nesting: independence of the increments (task P2-LM34c)

Source: MQ arXiv:1812.03913 `lqg_geodesics.tex`, proof of Prop 4.3 (l. 693–700). For the
canonical decompositions (`exists_lmRep_zbExt`) and `D = nestIncr r G λ` with
`λ_j ≈ κ_j − P_{K_j} κ_j`: the pairings of `D_j` are a.s. the vectors `δ_j` of `L3_4M4`
(`nestIncr_ae`), hence (Gaussian space, orthogonality) `D_{j+1}` is independent of
`σ(D_0, …, D_j)` (`indep_nestIncr_succ`), `D_j` is independent of `Y_j − D_j`
(`indepFun_nestIncr_compl`), and `⟨Y_j − D_j, φ⟩` is integrable and centred for `φ ∈ 𝓓₀`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric.LM

open Blueprint QuantumZipper QuantumZipper.K3 MarkovZB MarkovExt MarkovGauss MarkovNorm

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

variable (hh : IsNormalizedWPGFF h P) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hA : Antitone r)
  {hh0 hz G : ℕ → Ω → DistC} (hrep : ∀ k, IsLMRep P h (r k) (hh0 k) (hz k) (G k))
  (hzae : ∀ k (φ : TestC), (fun ω => hz k ω φ) =ᵐ[P]
    zbExt (isWholePlaneGFF_lmScaled hh.1 (hr k)) (ballO 0 1) φ)
  {lam : ℕ → Ω → ℝ}
  (hlam : ∀ j, lam j =ᵐ[P] ((nKappa hh hr j - nProj hh hr j (nKappa hh hr j) : Lp ℝ 2 P) : Ω → ℝ))

include hrep hzae in
lemma G_ae (k : ℕ) (φ : TestC) : (fun ω => G k ω φ) =ᵐ[P] (nA hh hr k φ : Ω → ℝ) := by
  filter_upwards [(hrep k).2.1, hzae k φ, zbExt_ae (isWholePlaneGFF_lmScaled hh.1 (hr k))
    (ballO 0 1) φ, nPV_ae hh hr k φ, Lp.coeFn_sub (nPV hh hr k φ) (nZ hh hr k φ)]
    with ω h1 h2 h3 h4 h5
  have hdec := (hrep k).1 ω
  rw [show nA hh hr k φ = nPV hh hr k φ - nZ hh hr k φ from rfl, h5, Pi.sub_apply, h4,
    ← h1, show (nZ hh hr k φ : Ω → ℝ) ω = _ from h3.symm, ← h2, hdec]
  simp

include hrep hzae hlam in
lemma nestIncr_ae (j : ℕ) (φ : TestC) :
    (fun ω => nestIncr r G lam j ω φ) =ᵐ[P] (nDelta hh hr j φ : Ω → ℝ) := by
  cases j with
  | zero => exact G_ae hh hr hrep hzae 0 φ
  | succ j =>
    set ρ := r (j + 1) / r j
    set κ' := nKappa hh hr j - nProj hh hr j (nKappa hh hr j)
    rw [nDelta_succ_eq]
    filter_upwards [G_ae hh hr hrep hzae (j + 1) φ, G_ae hh hr hrep hzae j
      (testAffinePull ρ 0 φ), hlam j,
      Lp.coeFn_add (nA hh hr (j + 1) φ - (ρ ^ 2)⁻¹ • nA hh hr j (testAffinePull ρ 0 φ))
        ((∫ x, φ x) • κ'),
      Lp.coeFn_sub (nA hh hr (j + 1) φ) ((ρ ^ 2)⁻¹ • nA hh hr j (testAffinePull ρ 0 φ)),
      Lp.coeFn_smul (ρ ^ 2)⁻¹ (nA hh hr j (testAffinePull ρ 0 φ)),
      Lp.coeFn_smul (∫ x, φ x) κ'] with ω h1 h2 h3 h4 h5 h6 h7
    rw [nestIncr_succ_apply, h4, Pi.add_apply, h5, Pi.sub_apply, h6, h7, Pi.smul_apply,
      Pi.smul_apply, ← h1, ← h2, ← h3, smul_eq_mul, smul_eq_mul]

include hrep hzae hlam in
lemma nestIncr_compl_ae (j : ℕ) (φ : TestC) :
    (fun ω => (lmScaled h (r j) ω - nestIncr r G lam j ω) φ) =ᵐ[P]
      ((nPV hh hr j φ - nDelta hh hr j φ : Lp ℝ 2 P) : Ω → ℝ) := by
  filter_upwards [nestIncr_ae hh hr hrep hzae hlam j φ, nPV_ae hh hr j φ,
    Lp.coeFn_sub (nPV hh hr j φ) (nDelta hh hr j φ)] with ω h1 h2 h3
  rw [h3, Pi.sub_apply, ← h1, h2]
  rfl

include hh hr hrep in
lemma measurable_G (k : ℕ) : Measurable (G k) :=
  (hrep k).2.2.1.mono (MarkovZBIndep.fieldSigmaClosed_le
    (isWholePlaneGFF_lmScaled hh.1 (hr k)) _) le_rfl

/-- `𝓕_j = σ(D_0, …, D_j)` -/
def nestF (D : ℕ → Ω → DistC) (j : ℕ) : MeasurableSpace Ω :=
  ⨆ (i : ℕ) (_ : i ≤ j), MeasurableSpace.comap (D i) inferInstance

lemma nestF_mono (D : ℕ → Ω → DistC) : Monotone (nestF D) := fun _ _ hab =>
  iSup₂_le fun i hi => le_iSup₂ (f := fun (i : ℕ) (_ : i ≤ _) =>
    MeasurableSpace.comap (D i) inferInstance) i (hi.trans hab)

lemma nestF_le {D : ℕ → Ω → DistC} (hD : ∀ j, Measurable (D j)) (j : ℕ) : nestF D j ≤ mΩ :=
  iSup₂_le fun i _ => (hD i).comap_le

lemma measurable_nestF (D : ℕ → Ω → DistC) (j : ℕ) : Measurable[nestF D j] (D j) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun (i : ℕ) (_ : i ≤ j) =>
    MeasurableSpace.comap (D i) inferInstance) j le_rfl)

include hA hrep hzae hlam in
/-- **`D_{j+1}` is independent of `σ(D_0, …, D_j)`** -/
theorem indep_nestIncr_succ (j : ℕ) :
    Indep (MeasurableSpace.comap (nestIncr r G lam (j + 1)) inferInstance)
      (nestF (nestIncr r G lam) j) P := by
  set D := nestIncr r G lam
  set S := {p : ℕ × CoordJ // p.1 ≤ j}
  set g : Ω → S → ℝ := fun ω p => pairJ ⊤ (D p.1.1 ω) p.1.2
  have h0 := indepFun_of_orth hh.1 (fun c : CoordJ => nDelta hh hr (j + 1) (comb ⊤ c))
    (fun p : S => nDelta hh hr p.1.1 (comb ⊤ p.1.2)) (fun c => nDelta_mem hh hr _ _)
    (fun p => nDelta_mem hh hr _ _) fun c p => inner_nDelta_nDelta hh hr hA p.2 _ _
  have h1 : IndepFun (fun ω => pairJ ⊤ (D (j + 1) ω)) g P :=
    h0.congr (MarkovAsm.ae_pairJ_eq (nestIncr_ae hh hr hrep hzae hlam (j + 1))).symm (by
      filter_upwards [ae_all_iff.2 fun p : S => nestIncr_ae hh hr hrep hzae hlam p.1.1
        (comb ⊤ p.1.2)] with ω hω
      funext p
      exact (hω p).symm)
  rw [IndepFun_iff_Indep] at h1
  rw [MarkovAsm.comap_distC_eq]
  refine indep_of_indep_of_le_right h1 (iSup₂_le fun i hi => ?_)
  rw [MarkovAsm.comap_distC_eq]
  have hR : Measurable fun (x : S → ℝ) (c : CoordJ) => x ⟨(i, c), hi⟩ :=
    measurable_pi_iff.2 fun c => measurable_pi_apply _
  have e : (fun ω => pairJ ⊤ (D i ω)) =
      (fun (x : S → ℝ) (c : CoordJ) => x ⟨(i, c), hi⟩) ∘ g := rfl
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hR.comap_le

include hA hrep hzae hlam in
/-- **`D_j` is independent of `Y_j − D_j`** -/
theorem indepFun_nestIncr_compl (j : ℕ) :
    IndepFun (nestIncr r G lam j) (fun ω => lmScaled h (r j) ω - nestIncr r G lam j ω) P := by
  have h0 := (indepFun_of_orth hh.1 (fun φ : TestC => nDelta hh hr j φ)
    (fun ψ : TestC => nPV hh hr j ψ - nDelta hh hr j ψ) (fun φ => nDelta_mem hh hr _ _)
    (fun ψ => sub_mem (nPV_mem hh hr j ψ) (nDelta_mem hh hr _ _))
    fun φ ψ => inner_nDelta_compl hh hr hA j φ ψ).comp MarkovAsm.measurable_coordR
    MarkovAsm.measurable_coordR
  have h1 := h0.congr (MarkovAsm.ae_pairJ_eq (nestIncr_ae hh hr hrep hzae hlam j)).symm
    (MarkovAsm.ae_pairJ_eq (nestIncr_compl_ae hh hr hrep hzae hlam j)).symm
  rw [IndepFun_iff_Indep] at h1 ⊢
  rw [MarkovAsm.comap_distC_eq, MarkovAsm.comap_distC_eq]
  exact h1

include hrep hzae hlam in
/-- `⟨Y_j − D_j, φ⟩` is integrable and centred for `φ ∈ 𝓓₀` -/
theorem integral_nestIncr_compl (j : ℕ) (φ : TestC0) :
    Integrable (fun ω => (lmScaled h (r j) ω - nestIncr r G lam j ω) φ.1) P ∧
      ∫ ω, (lmScaled h (r j) ω - nestIncr r G lam j ω) φ.1 ∂P = 0 := by
  have hae := nestIncr_compl_ae hh hr hrep hzae hlam j φ.1
  have hmem : nPV hh hr j φ.1 - nDelta hh hr j φ.1 ∈ gaussSpace (pairProc h) (memLp_pair hh.1) :=
    sub_mem (nPV_mem hh hr j _) (nDelta_mem hh hr _ _)
  refine ⟨((Lp.memLp _).integrable one_le_two).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae]
  exact (isCGauss_of_mem_gaussSpace (gaussian_pairProc hh.1) (centered_pairProc hh.1)
    (memLp_pair hh.1) hmem).2

end LQGMetric.LM
