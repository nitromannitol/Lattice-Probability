/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovVerCont at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The extension by zero is continuous in probability (task P2-MKH2, leaf (V))

`tendstoInMeasure_zbExt`: if `ψ_k → φ` in `𝓓(ℂ)` then `zbExt ψ_k → zbExt φ` in probability
(`V ∩ ∂𝔻 = ∅`). Proof: `[zbExt χ]` is the orthogonal projection of `[⟨h, χ⟩]` onto the
Cameron–Martin range (`MarkovAdm.inner_pairVec_cmIso_of_disjoint`), so it is an `L²`
contraction (`norm_extVec_sub_le`); `⟨h, ψ_k − φ⟩ → 0` for every `ω` and these are centred
Gaussians, so their variances tend to `0` (LQGDimension `SegLaw.tendsto_variance_of_hasGaussianLaw`).

With it, `exists_dist_version_zbExt_of_adm` reduces leaf (V) to the a.s. admissibility
(finite order on a countable dense family) of the extension, via
`RandomDistVersion.exists_version` (Berestycki–Powell arXiv:2404.16642, `definitionGFF.tex`
l. 842–862) and `MarkovVer.exists_vanishing_version_zbExt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the extension is an `L²` contraction of the pairing -/
lemma norm_extVec_sub_le (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (φ ψ : TestC) :
    ‖extVec hh.1 V ((V : Set ℂ).indicator ψ) - extVec hh.1 V ((V : Set ℂ).indicator φ)‖ ≤
      ‖pairVec hh ψ - pairVec hh φ‖ := by
  let r : TestC → gradClosure (V : Set ℂ) (zeroSpace V) := fun χ =>
    ⟨rieszFun V ((V : Set ℂ).indicator χ), rieszFun_mem V _⟩
  set w := r ψ - r φ
  have ha : extVec hh.1 V ((V : Set ℂ).indicator ψ) - extVec hh.1 V ((V : Set ℂ).indicator φ) =
      cmIso hh.1 V w := by
    rw [show w = r ψ - r φ from rfl, map_sub]; rfl
  have hin : ∀ χ, ⟪pairVec hh χ, cmIso hh.1 V w⟫ = ⟪cmIso hh.1 V (r χ), cmIso hh.1 V w⟫ := by
    intro χ
    rw [MarkovAdm.inner_pairVec_cmIso_of_disjoint hh hV χ w, LinearIsometry.inner_map_map,
      Submodule.coe_inner]
  rw [ha]
  set a := cmIso hh.1 V w
  have key : ⟪pairVec hh ψ - pairVec hh φ, a⟫ = ‖a‖ ^ 2 := by
    rw [inner_sub_left, hin, hin, ← inner_sub_left, ← map_sub, real_inner_self_eq_norm_sq]
  rcases (norm_nonneg a).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have := real_inner_le_norm (pairVec hh ψ - pairVec hh φ) a
    rw [key, sq] at this
    exact le_of_mul_le_mul_right this hpos

/-- **Continuity in probability** of the extension by zero along `𝓓(ℂ)`-convergent sequences. -/
theorem tendstoInMeasure_zbExt (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (φ : TestC) (ψ : ℕ → TestC)
    (hψ : Tendsto ψ atTop (𝓝 φ)) :
    TendstoInMeasure P (fun k => zbExt hh.1 V (ψ k)) atTop (zbExt hh.1 V φ) := by
  set b : ℕ → Lp ℝ 2 P := fun k => pairVec hh (ψ k) - pairVec hh φ
  have hbG : ∀ k, IsCGauss P (b k) := fun k =>
    isCGauss_of_mem_gaussSpace (gaussian_pairProc hh.1) (centered_pairProc hh.1)
      (memLp_pair hh.1) (Submodule.sub_mem _ (pairVec_mem_gaussSpace hh _)
        (pairVec_mem_gaussSpace hh _))
  set Y : ℕ → Ω → ℝ := fun k ω => h ω (ψ k) - h ω φ
  have hbae : ∀ k, (b k : Ω → ℝ) =ᵐ[P] Y k := fun k => by
    filter_upwards [Lp.coeFn_sub (pairVec hh (ψ k)) (pairVec hh φ), pairVec_ae hh (ψ k),
      pairVec_ae hh φ] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hYlim : ∀ ω, Tendsto (fun k => Y k ω) atTop (𝓝 ((0 : Ω → ℝ) ω)) := fun ω => by
    have := (((map_continuous (h ω)).tendsto φ).comp hψ).sub_const (h ω φ)
    rw [sub_self] at this
    exact this
  have h0G : HasGaussianLaw (0 : Ω → ℝ) P :=
    (isCGauss_of_mem_gaussSpace (gaussian_pairProc hh.1) (centered_pairProc hh.1)
      (memLp_pair hh.1) (Submodule.zero_mem _)).1.congr (Lp.coeFn_zero _ _ _)
  have hvar := LQGDimension.SegLaw.tendsto_variance_of_hasGaussianLaw (l := atTop) (Y := Y)
    (Y₀ := 0) (Eventually.of_forall fun k => ⟨(hbG k).1.congr (hbae k),
      by rw [← integral_congr_ae (hbae k)]; exact (hbG k).2⟩) h0G (by simp) hYlim
  rw [variance_zero] at hvar
  have hnorm : ∀ k, ‖b k‖ ^ 2 = Var[Y k; P] := fun k => by
    rw [← variance_congr (hbae k), ← covariance_self (Lp.aestronglyMeasurable _).aemeasurable,
      covariance_eq_inner (b k) (Lp.memLp _) (hbG k).2, Lp.toLp_coeFn,
      real_inner_self_eq_norm_sq]
  have hb : Tendsto (fun k => ‖b k‖) atTop (𝓝 0) := by
    have := hvar.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun k => ?_
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have ha : Tendsto (fun k => extVec hh.1 V ((V : Set ℂ).indicator (ψ k))) atTop
      (𝓝 (extVec hh.1 V ((V : Set ℂ).indicator φ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_extVec_sub_le hh hV φ (ψ k)) hb
  exact (tendstoInMeasure_of_tendsto_Lp ha).congr'
    (Eventually.of_forall fun k => (zbExt_ae hh.1 V (ψ k)).symm) (zbExt_ae hh.1 V φ).symm

/-- **Leaf (V) reduced to a.s. admissibility.** If the countably many values of the extension by
zero on the generating family of `𝓓(ℂ)` are a.s. admissible (additive, consistent, of finite
order on each compact of the exhaustion), the extension has a distribution-valued version
vanishing off `cl V`. -/
theorem exists_dist_version_zbExt_of_adm (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1))
    (hadm : ∀ᵐ ω ∂P, (fun c => zbExt hh.1 V (comb ⊤ c) ω) ∈ rangeSet ⊤) :
    ∃ hz : Ω → DistC, Measurable hz ∧ (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh.1 V φ) ∧
      ∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0 := by
  obtain ⟨hz, hm, hv⟩ := exists_version ⊤ P (zbExt hh.1 V) (measurable_zbExt hh.1 V) hadm
    (tendstoInMeasure_zbExt hh hV)
  exact exists_vanishing_version_zbExt hh.1 hm hv

end MarkovVer
end LQGMetric
