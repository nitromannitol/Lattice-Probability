/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RSelect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RSum
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable
import Mathlib.MeasureTheory.Function.FactorsThrough

 











set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 
def laneA3RField {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams) (W : WNSpace → Ω → ℝ)
    (P : Measure Ω) (n : ℕ) : Ω → ℂ → ℝ :=
  fun ω x => psiMN Q W P 0 n x ω

 
@[instance_reducible] def laneA3RFieldSigma {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams) (W : WNSpace → Ω → ℝ)
    (P : Measure Ω) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (laneA3RField Q W P n) inferInstance

theorem laneA3RFieldSigma_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (n : ℕ) :
    laneA3RFieldSigma Q W P n ≤ mΩ :=
  (measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).meas).comap_le

theorem laneA3R_field_eval_measurable {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω) (n : ℕ) (x : ℂ) :
    Measurable[laneA3RFieldSigma Q W P n] (psiMN Q W P 0 n x) :=
  (measurable_pi_apply x).comp (comap_measurable (laneA3RField Q W P n))

private theorem laneA3R_nearGeodesic_aux {Ω : Type*} [m : MeasurableSpace Ω] (ξ : ℝ)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    {η : ℝ} (hη : 0 < η) :
    ∃ (Qn : ℕ → ℝ → ℂ) (J : Ω → ℕ),
      (∀ k, AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ (Qn k)) ∧
      Measurable J ∧
      ∀ ω, lfppLen ξ (fun x => Y x ω) (Qn (J ω)) <
        (1 + ENNReal.ofReal η) * rectLen ξ (fun x => Y x ω) (rectAB 1 1) := by
  obtain ⟨Qn, hQa, -, -, -, hJ⟩ := exists_nearGeodesic (ξ := ξ) (rectAB 1 1)
    (by norm_num [rectAB]) (by norm_num [rectAB]) hYc hYm (ENNReal.ofReal_pos.2 hη)
  obtain ⟨J, hJm, hJ⟩ := hJ (by simp [rectAB, MarkedRect.crossWidth])
  exact ⟨Qn, J, hQa, hJm, hJ⟩

private theorem laneA3R_crossLen_aux {Ω : Type*} [m : MeasurableSpace Ω] (ξ : ℝ)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) :
    Measurable fun ω => rectLen ξ (fun x => Y x ω) (rectAB 1 1) :=
  measurable_crossLenIn (rectAB 1 1).isCompact_toSet hYc hYm

 
theorem laneA3R_exists_field_selection {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) :
    ∃ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j)) ∧
      ∀ j n K m : ℕ, ∀ b : ℤ × ℤ,
        MeasurableSet[laneA3RFieldSigma Q W P n] (laneCHits γ j n K m b) := by
  have key : ∀ j n : ℕ, ∃ (Qn : ℕ → ℝ → ℂ) (J : Ω → ℕ),
      (∀ k, AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ (Qn k)) ∧
      Measurable[laneA3RFieldSigma Q W P n] J ∧
      ∀ ω, lfppLen ξ (fun x => psiMN Q W P 0 n x ω) (Qn (J ω)) <
        (1 + ENNReal.ofReal (((j : ℝ) + 1)⁻¹)) *
          rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
    intro j n
    have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    exact laneA3R_nearGeodesic_aux (m := laneA3RFieldSigma Q W P n) ξ hψ.cont
      (laneA3R_field_eval_measurable Q W P n) (by positivity)
  choose Qn J hQa hJm hJ using key
  refine ⟨fun j n ω => Qn j n (J j n ω), fun j => ⟨fun n ω => hQa j n _, fun n ω => ?_,
    fun n K b => ?_⟩, fun j n K m b => ?_⟩
  · refine (hJ j n ω).le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
  · exact ((hJm j n).mono (laneA3RFieldSigma_le hW Q n) le_rfl)
      (DiscreteMeasurableSpace.forall_measurableSet {k | b ∈ T20.coarseBlocks K (Qn j n k)})
  · have e : laneCHits (fun j n ω => Qn j n (J j n ω)) j n K m b =
        (J j n) ⁻¹' {k : ℕ | ∃ t ∈ Icc (0 : ℝ) 1, Qn j n k t ∈ laneCHitBall K m b} := by
      ext ω; rfl
    rw [e]
    exact hJm j n (DiscreteMeasurableSpace.forall_measurableSet _)

 
theorem laneA3R_hitWeight_factor {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K : ℕ)
    (hhits : ∀ j m : ℕ, ∀ b : ℤ × ℤ,
      MeasurableSet[laneA3RFieldSigma Q W P n] (laneCHits γ j n K m b)) (b : ℤ × ℤ) :
    ∃ w : (ℂ → ℝ) → ℝ≥0∞, Measurable w ∧
      laneA3HitWeight P W hW Q ξ γ n K b =ᵐ[P] fun ω => w (laneA3RField Q W P n ω) := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hmF := laneA3RFieldSigma_le hW Q n
  have hYm := laneA3R_field_eval_measurable Q W P n
  
  have hF : MeasurableSet[laneA3RFieldSigma Q W P n]
      (laneCEventualHit γ n K (laneBCoarseIndex Q K) b) :=
    @laneCEventualHit_measurableSet Ω (laneA3RFieldSigma Q W P n) γ n K _ b
      (fun j => hhits j _ b)
  have hL : Measurable[laneA3RFieldSigma Q W P n]
      (fun ω => rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1)) :=
    laneA3R_crossLen_aux (m := laneA3RFieldSigma Q W P n) ξ hψ.cont hYm
  have hD := @laneC_measurable_lfppContMetric Ω (laneA3RFieldSigma Q W P n)
    (psiMN Q W P 0 n) hψ.cont hYm ξ
  have hA := @laneC_aemeasurable_aroundDist Ω (laneA3RFieldSigma Q W P n)
    (P.trim hmF) _ _ hD (LaneCInputs.sourceAround K (laneBCoarseIndex Q K) b)
    (LaneCInputs.sourceInner K (laneBCoarseIndex Q K) b)
    (LaneCInputs.sourceOuter K (laneBCoarseIndex Q K) b)
    (laneC_sourceAround_isOpen K _ b)
  have hWae : @AEMeasurable Ω ℝ≥0∞ _ (laneA3RFieldSigma Q W P n)
      (laneA3HitWeight P W hW Q ξ γ n K b) (P.trim hmF) :=
    (hA.div hL.aemeasurable).indicator hF
  obtain ⟨w, hw, hw0⟩ := Measurable.exists_eq_measurable_comp
    (f := laneA3RField Q W P n) (g := hWae.mk _) hWae.measurable_mk
  refine ⟨w, hw, ?_⟩
  have h1 := ae_eq_of_ae_eq_trim hWae.ae_eq_mk
  filter_upwards [h1] with ω hω
  rw [hω, hw0]
  rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
