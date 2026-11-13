/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AllOffsetsBasic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryVague

/-!
# M4-B4, part 1: circle values at arbitrary radii and the two-radius lemma at an offset

Blueprint `M4_BLUEPRINT.md`, node M4-B4 (inputs).

* `measurable_evalReg_fc_real`: `(x, t) ↦ evalReg x (fc(t, r))` is jointly measurable.
* `ae_evalReg_fc_eq`: for the free field and a fixed circle, `evalReg (X ω) (fc(w,r))` agrees
  almost surely with the raw coordinate `X ω (fc(w,r))` (at **every** radius `r > 0`).
* `zV X R r t ω = evalReg (Z ω) (fc(t,r))` for the normalized field `Z = zField X R`, its law,
  and the joint integrability of `g(t) · bdryDens γ (Z ω) r t`.
* `integral_abs_bA_sub_lim_le`: for `c ∈ [1,2]`,
  `E|∫ g dν_{c 2^{-k}}(Z) − ∫ g dν(Z)| ≤ C e^{-β k log 2}`, with `C` uniform in `c` and `k`
  (two-radius lemma with the constant profiles `c 2^{-k}`, `2^{-k}`, plus M4-B3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AllOffsets

open BdryExist GaussTK TwoRadius

/-! ## A1. Joint measurability of circle values at a fixed radius -/

theorem measurable_evalReg_fc_real (r : ℝ) :
    Measurable (fun p : FieldSample × ℝ => evalReg p.1 (foldedCircle (p.2 : ℂ) r)) := by
  have key : ∀ k : ℕ, StronglyMeasurable (fun p : FieldSample × ℝ =>
      ∫ w, avgReg p.1 k w ∂foldedCircle (p.2 : ℂ) r) := by
    intro k
    have hc : Measurable (fun s : ℝ × ℝ => circleMap (s.1 : ℂ) r s.2) := by
      have : Continuous (fun s : ℝ × ℝ => circleMap (s.1 : ℂ) r s.2) := by
        simp only [circleMap]; fun_prop
      exact this.measurable
    have hjm : Measurable (fun q : (FieldSample × ℝ) × ℝ =>
        avgReg q.1.1 k (foldH (circleMap (q.1.2 : ℂ) r q.2))) :=
      (measurable_avgReg k).comp (measurable_fst.fst.prodMk
        (measurable_foldH.comp (hc.comp (measurable_fst.snd.prodMk measurable_snd))))
    have e : (fun p : FieldSample × ℝ => ∫ w, avgReg p.1 k w ∂foldedCircle (p.2 : ℂ) r) =
        fun p => (ENNReal.ofReal (2 * π))⁻¹.toReal *
          ∫ θ, avgReg p.1 k (foldH (circleMap (p.2 : ℂ) r θ))
            ∂(volume.restrict (Ico 0 (2 * π))) := by
      funext p
      have hm := RegClosure.measurable_avgReg_slice p.1 k
      rw [foldedCircle, integral_map measurable_foldH.aemeasurable hm.aestronglyMeasurable,
        circleUnif, integral_smul_measure,
        integral_map (f := fun x => avgReg p.1 k (foldH x)) (measurable_circleMap _ _).aemeasurable
          (hm.comp measurable_foldH).aestronglyMeasurable, smul_eq_mul]
    rw [e]
    exact (hjm.stronglyMeasurable.integral_prod_right').const_mul _
  unfold evalReg
  exact (StronglyMeasurable.limUnder key).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## A2. `evalReg` of a fixed circle is the raw coordinate, almost surely -/

open KolmD RegSample CircleFubini in
theorem ae_evalReg_fc_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {w : ℂ}
    (hw : w ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    (fun ω => evalReg (X ω) (foldedCircle w r)) =ᵐ[P] fun ω => X ω (foldedCircle w r) := by
  set V : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => X ω (nuQ q) with hV
  have hVm : ∀ q, AEMeasurable (V q) P := fun q => (hX.measurable_coord _).aemeasurable
  obtain ⟨W, hWc, hWV, hWlim⟩ := exists_continuous_modification_D (d := 4) le_rfl hVm
    fun R => ⟨_, mul_nonneg (pow_nonneg (by positivity) 8) (gaussianAbsMoment_nonneg 16),
      momentBound_nuQ hX R⟩
  have hpt : ∀ ρ : ℝ, 0 < ρ →
      ∀ᵐ ω ∂P, ∫ u, W (pr u ρ 0) ω ∂foldedCircle w r = W (pr w r ρ) ω := by
    intro ρ hρ
    have hYc : ∀ ω, ContinuousOn (fun u => W (pr u ρ 0) ω - W (pr w ρ 0) ω) Hbar := fun ω =>
      (((hWc ω).comp (continuous_pr_fst ρ 0)).sub continuous_const).continuousOn
    have hY : ∀ u ∈ Hbar, (fun ω => W (pr u ρ 0) ω - W (pr w ρ 0) ω) =ᵐ[P]
        fun ω => X ω (foldedCircle u ρ) - X ω (foldedCircle w ρ) := by
      intro u hu
      filter_upwards [hWV (pr u ρ 0), hWV (pr w ρ 0)] with ω h1 h2
      simp only [h1, h2, hV, nuQ_pr_zero hu hρ, nuQ_pr_zero hw hρ]
    have hF := integral_fcAvg_ae_eq_bind_real hX hρ hw hYc hY (foldedCircle w r)
      (isCompact_ballH (‖w‖ + r)) inter_subset_right (foldedCircle_support hr.le le_rfl)
    filter_upwards [hF, hWV (pr w ρ 0), hWV (pr w r ρ)] with ω h1 h2 h3
    have hint : Integrable (fun u => W (pr u ρ 0) ω) (foldedCircle w r) :=
      RegClosure.integrable_fc ((hWc ω).comp (continuous_pr_fst ρ 0)).continuousOn w hr.le
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ,
      one_smul, measure_univ, one_smul] at h1
    simp only [hV] at h2 h3
    rw [nuQ_pr_zero hw hρ] at h2
    rw [h3, nuQ_pr hw hr hρ.le]
    linarith
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∫ u, W (pr u (radius k) 0) ω ∂foldedCircle w r =
      W (pr w r (radius k)) ω := ae_all_iff.2 fun k => hpt _ (radius_pos k)
  filter_upwards [hWlim, hall, hWV (pr w r 0)] with ω hlim hk h0
  have havg : ∀ k : ℕ, ∀ u ∈ Hbar, avgReg (X ω) k u = W (pr u (radius k) 0) ω := by
    intro k u hu
    have h := hlim (pr u (radius k) 0)
    simp only [rndD_pr, hV] at h
    have e : ∀ n, nuQ (pr (dyadicRoundC n u) (radius k) 0) =
        foldedCircle (dyadicRoundC n u) (radius k) := fun n =>
      nuQ_pr_zero (CircleCont.dyadicRoundC_mem_Hbar hu n) (radius_pos k)
    simp only [e] at h
    exact h.limUnder_eq
  have hint : ∀ k : ℕ, ∫ u, avgReg (X ω) k u ∂foldedCircle w r = W (pr w r (radius k)) ω := by
    intro k
    rw [← hk k]
    exact integral_congr_ae ((RegClosure.fc_ae_mem_Hbar w r).mono fun u hu => havg k u hu)
  have hcont : Continuous fun ρ : ℝ => W (pr w r ρ) ω :=
    (hWc ω).comp (continuousOn_pr.comp_continuous (by fun_prop : Continuous
      fun ρ : ℝ => (((w, r) : ℂ × ℝ), ρ)) fun _ => hr)
  have htend : Tendsto (fun k => W (pr w r (radius k)) ω) atTop (𝓝 (W (pr w r 0) ω)) :=
    (hcont.tendsto 0).comp (tendsto_nhdsWithin_iff.1 RegClosure.tendsto_radius_nhdsGT).1
  unfold evalReg
  simp_rw [hint]
  rw [htend.limUnder_eq, h0]
  show X ω (nuQ (pr w r 0)) = _
  rw [nuQ_pr_zero hw hr]

/-! ## A3. The normalized field at an arbitrary radius -/

/-- `Z_r(t) = evalReg (Z ω) (fc(t,r))` for the normalized field `Z = zField X R`. -/
def zV (X : Ω → FieldSample) (R r t : ℝ) (ω : Ω) : ℝ :=
  evalReg (zField X R ω) (foldedCircle (t : ℂ) r)

theorem measurable_zV (hX : IsFreeGFFModConstH X P) (R r : ℝ) :
    Measurable (fun p : ℝ × Ω => zV X R r p.1 p.2) := by
  have h1 : Measurable (fun p : ℝ × Ω => (zField X R p.2, p.1)) :=
    ((measurable_zField hX R).comp measurable_snd).prodMk measurable_fst
  exact Measurable.comp (g := fun q : FieldSample × ℝ => evalReg q.1 (foldedCircle (q.2 : ℂ) r))
    (f := fun p : ℝ × Ω => (zField X R p.2, p.1)) (measurable_evalReg_fc_real r) h1

/-- On a regular sample, `Z_r(t) = X_r(t) − X(fc(0,R))` at every circle. -/
theorem zV_eq_of_regular {R : ℝ} {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    zV X R r t ω = F ((t : ℂ), r) - X ω (foldedCircle 0 R) := by
  have hZ := hF.addConst' (-X ω (foldedCircle 0 R))
  simp only [zV, zField]
  rw [hZ.evalReg_fc_of_mem (ofReal_mem_Hbar t) hr]
  ring

theorem regular_zField {R : ℝ} {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F) :
    IsRegularWith (zField X R ω) (fun q => F q + -X ω (foldedCircle 0 R)) :=
  hF.addConst' _

theorem ae_zV_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (R t : ℝ) {r : ℝ}
    (hr : 0 < r) : zV X R r t =ᵐ[P] fcPairVal X ((t : ℂ), r, 0, R) := by
  filter_upwards [RegSample.ae_isRegularSample hX,
    ae_evalReg_fc_eq hX (ofReal_mem_Hbar t) hr] with ω hreg h
  obtain ⟨F, hF⟩ := hreg
  rw [zV_eq_of_regular hF t hr, ← hF.evalReg_fc_of_mem (ofReal_mem_Hbar t) hr, h]
  rfl

theorem fcPairCov_incr_self_gen {t ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    fcPairCov ((t : ℂ), ρ, (t : ℂ), r) ((t : ℂ), ρ, (t : ℂ), r) = 2 * log r - 2 * log ρ := by
  have hr : 0 < r := hρ.trans_le hρr
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hρ hρ, kernelCov_fc_real_sameCenter hρ hr,
    kernelCov_fc_real_sameCenter hr hρ, kernelCov_fc_real_sameCenter hr hr,
    max_eq_right hρr, max_eq_left hρr]
  simp only [max_self]
  ring

/-! ## A4. Densities, integrals and joint integrability -/

theorem bdryDens_zField (γ R r t : ℝ) (ω : Ω) :
    bdryDens γ (zField X R ω) r t = r ^ (γ ^ 2 / 4) * exp (γ / 2 * zV X R r t ω) := rfl

theorem measurable_bdryDens_zField (hX : IsFreeGFFModConstH X P) (γ R r : ℝ) :
    Measurable (fun p : Ω × ℝ => bdryDens γ (zField X R p.1) r p.2) := by
  have h : Measurable (fun p : Ω × ℝ => zV X R r p.2 p.1) :=
    Measurable.comp (g := fun p : ℝ × Ω => zV X R r p.1 p.2) (f := Prod.swap)
      (measurable_zV hX R r) measurable_swap
  exact measurable_const.mul ((h.const_mul _).exp)

/-- `∫ g dν_r(Z ω)`. -/
def bA (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (r : ℝ) (ω : Ω) : ℝ :=
  ∫ t, g t ∂bdryR γ (zField X R ω) r

/-! ## A5. The two-radius lemma at an offset `c ∈ [1,2]` -/

end AllOffsets
end QuantumZipper
