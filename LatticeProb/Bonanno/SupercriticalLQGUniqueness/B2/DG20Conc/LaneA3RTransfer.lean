/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RSelect
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RFreeze
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RInputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Inputs

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 
def laneA3RStarMap {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams) (W : WNSpace → Ω → ℝ)
    (P : Measure Ω) (K n : ℕ) : Ω → (ℂ → ℝ) × (T20B.nearIdx K → ℂ → ℝ) :=
  fun ω => (fun x => psiMN Q W P K n x ω, fun b x => T20B.blkKn Q W P K n b.1 x ω)

theorem laneFineStar_eq_comap {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ) :
    laneFineStar Q W P K n = MeasurableSpace.comap (laneA3RStarMap Q W P K n) inferInstance := by
  have e : MeasurableSpace.comap (laneA3RStarMap Q W P K n) inferInstance =
      MeasurableSpace.comap (fun ω x => psiMN Q W P K n x ω) inferInstance ⊔
        MeasurableSpace.comap (fun ω (b : T20B.nearIdx K) x => T20B.blkKn Q W P K n b.1 x ω)
          inferInstance :=
    MeasurableSpace.comap_prodMk _ _
  rw [e]
  unfold laneFineStar
  congr 1
  change _ = MeasurableSpace.comap _ (⨆ b : T20B.nearIdx K,
    MeasurableSpace.comap (fun f : T20B.nearIdx K → ℂ → ℝ => f b) inferInstance)
  rw [MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rw [iSup_subtype']
  rfl

theorem laneA3R_add_fields_measurable :
    Measurable fun p : (ℂ → ℝ) × (ℂ → ℝ) => fun x => p.1 x + p.2 x :=
  measurable_pi_iff.mpr fun x =>
    ((measurable_pi_apply x).comp measurable_fst).add ((measurable_pi_apply x).comp measurable_snd)

 
theorem laneA3R_kernel_transfer.{u} (hInd : LaneFineStarIndepCoarse.{u})
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (Q : PsiParams)
    {K n : ℕ} (hKn : K ≤ n) {Z : Ω → ℝ≥0∞} {w : (ℂ → ℝ) → ℝ≥0∞} (hw : Measurable w)
    (hZ : Z =ᵐ[P] fun ω => w (laneA3RField Q W P n ω)) :
    ∀ᵐ ω ∂P, ∫⁻ x, Z x ∂(condExpKernel P (laneFineStar Q W P K n) ω) =
      ∫⁻ x, Z x ∂(J2Inputs.fineKernel Q W P K n ω) := by
  set Fk : Ω → ℂ → ℝ := fun ω x => psiMN Q W P K n x ω with hFk
  set Yc : Ω → ℂ → ℝ := fun ω x => psiMN Q W P 0 K x ω with hYc
  have hFkm : Measurable Fk :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Q) hW hKn).meas
  have hYcm : Measurable Yc :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)).meas
  have hXm : Measurable (laneA3RStarMap Q W P K n) :=
    hFkm.prodMk (measurable_pi_iff.mpr fun b =>
      measurable_pi_iff.mpr (T20B.blkKn_spec hW Q hKn b.1).2.1)
  have hstar : laneFineStar Q W P K n ≤ mΩ := by
    rw [laneFineStar_eq_comap]; exact hXm.comap_le
  have hfine : MeasurableSpace.comap Fk inferInstance ≤ mΩ := hFkm.comap_le
  
  set Z' : Ω → ℝ≥0∞ := fun ω => w (fun x => Fk ω x + Yc ω x) with hZ'
  have hZZ' : Z =ᵐ[P] Z' := by
    filter_upwards [hZ, T20B.psiMN_add_ae hW Q hKn] with ω h1 h2
    rw [h1]
    show w (fun x => psiMN Q W P 0 n x ω) = w (fun x => Fk ω x + Yc ω x)
    congr 1
    funext x
    exact h2 x
  have hstarZ : ∀ᵐ ω ∂P, ∫⁻ x, Z x ∂(condExpKernel P (laneFineStar Q W P K n) ω) =
      ∫⁻ x, Z' x ∂(condExpKernel P (laneFineStar Q W P K n) ω) := by
    filter_upwards [laneC_conditional_lintegral_mono_ae P hstar hZZ'.le,
      laneC_conditional_lintegral_mono_ae P hstar hZZ'.symm.le] with ω h1 h2
    exact le_antisymm h1 h2
  have hfineZ : ∀ᵐ ω ∂P, ∫⁻ x, Z x ∂(J2Inputs.fineKernel Q W P K n ω) =
      ∫⁻ x, Z' x ∂(J2Inputs.fineKernel Q W P K n ω) := by
    filter_upwards [laneC_conditional_lintegral_mono_ae P hfine hZZ'.le,
      laneC_conditional_lintegral_mono_ae P hfine hZZ'.symm.le] with ω h1 h2
    exact le_antisymm h1 h2
  
  have hIndStar : IndepFun (laneA3RStarMap Q W P K n) Yc P := by
    have h := hInd P W hW Q K n hKn
    have h2 : Indep (MeasurableSpace.comap Yc inferInstance) (laneFineStar Q W P K n) P :=
      indep_of_indep_of_le_left h le_sup_right
    rw [laneFineStar_eq_comap] at h2
    exact h2.symm
  have hφs : Measurable fun p : ((ℂ → ℝ) × (T20B.nearIdx K → ℂ → ℝ)) × (ℂ → ℝ) =>
      w (fun x => p.1.1 x + p.2 x) :=
    hw.comp (laneA3R_add_fields_measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hfreezeS := laneA3R_kernel_freeze P hXm hYcm hIndStar hφs
  
  have hIndF : IndepFun Fk Yc P := (T20B.indepFun_psiMN_scales hW Q hKn).symm
  have hφf : Measurable fun p : (ℂ → ℝ) × (ℂ → ℝ) => w (fun x => p.1 x + p.2 x) :=
    hw.comp laneA3R_add_fields_measurable
  have hfreezeF := laneA3R_kernel_freeze P hFkm hYcm hIndF hφf
  filter_upwards [hstarZ, hfineZ, hfreezeS, hfreezeF] with ω h1 h2 h3 h4
  rw [h1, h2]
  rw [laneFineStar_eq_comap]
  have e3 : ∫⁻ x, Z' x ∂(condExpKernel P (MeasurableSpace.comap (laneA3RStarMap Q W P K n)
      inferInstance) ω) = ∫⁻ y, w (fun x => Fk ω x + y x) ∂(P.map Yc) := h3
  have e4 : ∫⁻ x, Z' x ∂(J2Inputs.fineKernel Q W P K n ω) =
      ∫⁻ y, w (fun x => Fk ω x + y x) ∂(P.map Yc) := h4
  rw [e3, e4]

end SupercriticalLQGUniqueness.B2.DG20Conc
