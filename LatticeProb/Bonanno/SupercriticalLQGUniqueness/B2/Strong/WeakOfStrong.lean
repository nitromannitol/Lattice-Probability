/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Scale

 












set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC ofCont addFun addConst IsGFFPlusCont affineComp circleAvg)

namespace SupercriticalLQGUniqueness.B2.Strong

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

 
theorem ae_acrossDist_lt_top (hS : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (A : EuclideanAnnulus) : ∀ᵐ ω ∂P, acrossDist (D (h ω)) A < ⊤ := by
  obtain ⟨hU, hc₁, hc₂, hk₁, hk₂, hn₁, hn₂, hs₁, hs₂, hd⟩ := boundary_axiomV_data A
  filter_upwards [hS.2.2.2.2.2 P h hh ⊤ hU _ _ hc₁ hc₂ hk₁ hk₂ hn₁ hn₂ hs₁ hs₂ hd] with ω hω
  exact acrossDist_lt_top_of_internalSetDist _ A hω

 

theorem ae_aroundDist_lt_top (hS : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (A : EuclideanAnnulus) : ∀ᵐ ω ∂P, aroundDist (D (h ω)) A < ⊤ := by
  have hk : ∀ k : Fin 4, ∀ᵐ ω ∂P, (D (h ω)).internalSetDist (cfgOpens A k : Set ℂ)
      (Subtype.val ⁻¹' cfgSet₁ A k) (Subtype.val ⁻¹' cfgSet₂ A k) < ∞ := by
    intro k
    obtain ⟨-, hU, hc₁, hc₂, hk₁, hk₂, hn₁, hn₂, hs₁, hs₂, hd⟩ :=
      axiomV_data A.center (annL A) (annΔ A) (annΔ_pos A) k
    exact hS.2.2.2.2.2 P h hh (cfgOpens A k) hU _ _ hc₁ hc₂ hk₁ hk₂ hn₁ hn₂ hs₁ hs₂ hd
  filter_upwards [ae_all_iff.2 hk] with ω hω
  exact aroundDist_lt_top_of_internalSetDist _ A hω

theorem circleAverage_eq {g : DistC} {r : Set.Ioi (0 : ℝ)} {a b : ℝ}
    (ha : IsCircleAverage g r 0 a) (hb : IsCircleAverage g r 0 b) : a = b :=
  tendsto_nhds_unique ha hb

 
theorem tightness_of_strong (hS : IsStrongLQGMetric ξ Q D) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
        (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
        ∀ A : EuclideanAnnulus,
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
              acrossDist (D (h ω)) (A.dilate r r.2)) ∧
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
              aroundDist (D (h ω)) (A.dilate r r.2)) := by
  intro Ω _ P _ h hh a ha A
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  have hh' : IsGFFPlusCont h P := LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh.1
  have hmeas : Measurable h := hh.1.measurable
  have hlaw : ∀ r : Set.Ioi (0 : ℝ), P.map (fun ω => rescaledField (h ω) r) = P.map h :=
    fun r => LQGMetric.CircleAvg.map_affine_sub_circleAvg hold r.2 0
  have hgm : ∀ r : Set.Ioi (0 : ℝ), Measurable fun ω => rescaledField (h ω) r :=
    fun r => (measurable_rescaledField r).comp hmeas
  have hcirc : ∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, a r ω = circleAvg (h ω) r 0 := fun r => by
    filter_upwards [ha r, ae_isCircleAverage_old hh.1 r 0] with ω h₁ h₂
    exact circleAverage_eq h₁ h₂
  constructor
  · refine isTwoSidedTight_of_map_eq P _ (fun u => acrossDist (D u) A)
      ((measurable_acrossDist A).comp hS.1) h hmeas (fun r ω => rescaledField (h ω) r) hgm hlaw
      (fun r => ?_) (ae_acrossDist_lt_top hS P h hh' A)
      (Eventually.of_forall fun ω => acrossDist_pos _ A)
    filter_upwards [ae_annulus_scale hS P h hh' r, hcirc r] with ω hsc hc
    simp only [Function.comp, (hsc A).1, hc]
  · refine isTwoSidedTight_of_map_eq P _ (fun u => aroundDist (D u) A)
      ((Uniqueness.TwoScale.S36.measurable_aroundDist_fixed A).comp hS.1) h hmeas
      (fun r ω => rescaledField (h ω) r) hgm hlaw
      (fun r => ?_) (ae_aroundDist_lt_top hS P h hh' A)
      (Eventually.of_forall fun ω => aroundDist_pos _ A)
    filter_upwards [ae_annulus_scale hS P h hh' r, hcirc r] with ω hsc hc
    simp only [Function.comp, (hsc A).2, hc]

 

theorem isWeakLQGMetric_of_isStrongLQGMetric (hS : IsStrongLQGMetric ξ Q D) :
    IsWeakLQGMetric ξ Q D :=
  ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, translation_of_strong hS, tightness_of_strong hS⟩

end SupercriticalLQGUniqueness.B2.Strong
