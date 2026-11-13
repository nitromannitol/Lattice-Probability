/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.PointP48 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.PointBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalCompletion
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48PrimedIntegral

/-!
# the primed point observable from the local point factor

Source: [18] (4.22) and the proof of Lemma 4.9.

the `Canonical.maskedUStarPrime D hγ ε q ζ z` is the indicator of the event `F′^ε(z)` (window test at every
visit, degree cap, and the two circle-average conditions at radius `ε^{q−4ζ}`) times `u′_*(z)`.
`maskedUStarPrime_eq_ite` separates it as (circle-average condition) × `truePointFactor`.
`l43p_maskedUStarPrime_of_readers` gives, from the GMC readers `H2`, a Borel function `factor` of the
local observation on `W = (B_{4ε^q}(z))_{ε^q}` (its H3 input shape) with
`maskedUStarPrime = 1{circle-average condition} · factor(local observation)` almost surely.

**Remark (the H3).** The circle-average conditions read circles of radius `ε^{q−4ζ}`, which for small `ε`
leave `W = B_{5ε^q}(z)`; so `maskedUStarPrime` itself is not in general an almost-sure function of the local
observation, and H3's `ae_factor` must be stated with the circle-average indicator outside the factor, as here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c MatedCRTHarmonic.MatedCRT

attribute [local instance] Classical.propDecidable

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The circle-average condition of (4.22). -/
def circleCond (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) : Prop :=
  max |GMS4.Canonical.fieldCircleAverage D hγ (Canon.conditioningRadius ε q ζ) z ω|
      |GMS4.Canonical.igCircleAverage hIG₀ U (Canon.conditioningRadius ε q ζ) z ω| ≤
    2 * q * Real.log ε⁻¹

/-- **The primed masked observable factors** as the circle-average condition times the local point factor. -/
theorem maskedUStarPrime_eq_ite
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) :
    GMS4.Canonical.maskedUStarPrime D hγ ε q ζ z ω =
      if circleCond D hγ ε q ζ z ω then truePointFactor (η₀ ω) z ε (ε ^ q) ζ else 0 := by
  unfold GMS4.Canonical.maskedUStarPrime GMS4.Canonical.localEventPrime
    GMS4.Canonical.uStarPrime truePointFactor circleCond
  rw [Set.indicator_apply]
  by_cases hC : max |GMS4.Canonical.fieldCircleAverage D hγ (Canon.conditioningRadius ε q ζ) z ω|
      |GMS4.Canonical.igCircleAverage hIG₀ U (Canon.conditioningRadius ε q ζ) z ω| ≤
        2 * q * Real.log ε⁻¹
  · rw [ite_eq_left hC]
    by_cases hAB : (∀ t : ℝ, η₀ ω t = z → diam (locWindow ε (η₀ ω) t) ≤ ε ^ q) ∧
        (((degreeInPrime ε (η₀ ω) z + degreeOutPrime ε (η₀ ω) z : ℕ∞)) : ℝ≥0∞) ≤
          ENNReal.ofReal (ε ^ (-ζ))
    · rw [ite_eq_left (show ω ∈ {ω | (∀ t : ℝ, η₀ ω t = z →
          diam (locWindow ε (η₀ ω) t) ≤ ε ^ q) ∧
        (((degreeInPrime ε (η₀ ω) z + degreeOutPrime ε (η₀ ω) z : ℕ∞)) : ℝ≥0∞) ≤
          ENNReal.ofReal (ε ^ (-ζ)) ∧
        max |GMS4.Canonical.fieldCircleAverage D hγ (Canon.conditioningRadius ε q ζ) z ω|
          |GMS4.Canonical.igCircleAverage hIG₀ U (Canon.conditioningRadius ε q ζ) z ω| ≤
            2 * q * Real.log ε⁻¹} from ⟨hAB.1, hAB.2, hC⟩), ite_eq_left hAB]
    · rw [ite_eq_right (fun h : ω ∈ {ω | (∀ t : ℝ, η₀ ω t = z →
          diam (locWindow ε (η₀ ω) t) ≤ ε ^ q) ∧
        (((degreeInPrime ε (η₀ ω) z + degreeOutPrime ε (η₀ ω) z : ℕ∞)) : ℝ≥0∞) ≤
          ENNReal.ofReal (ε ^ (-ζ)) ∧
        max |GMS4.Canonical.fieldCircleAverage D hγ (Canon.conditioningRadius ε q ζ) z ω|
          |GMS4.Canonical.igCircleAverage hIG₀ U (Canon.conditioningRadius ε q ζ) z ω| ≤
            2 * q * Real.log ε⁻¹} => hAB ⟨h.1, h.2.1⟩), ite_eq_right hAB]
  · rw [ite_eq_right hC, ite_eq_right (fun h : ω ∈ {ω | (∀ t : ℝ, η₀ ω t = z →
          diam (locWindow ε (η₀ ω) t) ≤ ε ^ q) ∧
        (((degreeInPrime ε (η₀ ω) z + degreeOutPrime ε (η₀ ω) z : ℕ∞)) : ℝ≥0∞) ≤
          ENNReal.ofReal (ε ^ (-ζ)) ∧
        max |GMS4.Canonical.fieldCircleAverage D hγ (Canon.conditioningRadius ε q ζ) z ω|
          |GMS4.Canonical.igCircleAverage hIG₀ U (Canon.conditioningRadius ε q ζ) z ω| ≤
            2 * q * Real.log ε⁻¹} => hC h.2.2)]

/-- **the primed masked observable from its GMC readers**: one Borel function of the H3 local observation,
times the separate circle-average condition. -/
theorem l43p_maskedUStarPrime_of_readers
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (H2 : GMS4.Canonical.ThickGMCReaders D)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (q ζ : ℝ) (z : ℂ) :
    ∃ factor : ((Measure ℂ × LQGMetric.DistOn
        (thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q))) ×
        (LQGMetric.DistOn (thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q)) × ℝ)) → ℝ,
      Measurable factor ∧ ∀ᵐ ω ∂P,
        GMS4.Canonical.maskedUStarPrime D hγ ε q ζ z ω =
          if circleCond D hγ ε q ζ z ω then
            factor (((H2 (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q)
                (Real.rpow_pos_of_pos hε.1 q)).reconstruct
                (LQGMetric.restrictTo
                  (thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q))
                  (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))),
              LQGMetric.restrictTo (thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q))
                (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))),
              (LQGMetric.restrictTo
                (thickOpen (LQGMetric.Blueprint.ballO z (4 * ε ^ q)) (ε ^ q)) (hIG₀ ω), U ω))
          else 0 := by
  set r₀ : ℝ := ε ^ q with hr₀def
  have hr₀ : 0 < r₀ := Real.rpow_pos_of_pos hε.1 q
  set W := thickOpen (LQGMetric.Blueprint.ballO z (4 * r₀)) r₀
  have hWset : (W : Set ℂ) = ball z (5 * r₀) := by
    change thickening r₀ (ball z (4 * r₀)) = _
    rw [_root_.thickening_ball hr₀ (by positivity)]
    congr 1
    ring
  -- the area reader on `B_{9r₀/2}(z)`
  set V₂ := LQGMetric.Blueprint.ballO z (9 / 2 * r₀)
  have hδ₂ : 0 < r₀ / 2 := by positivity
  set A := H2 V₂ (r₀ / 2) hδ₂
  have hthick : thickOpen V₂ (r₀ / 2) ≤ W := by
    intro y hy
    change y ∈ thickening (r₀ / 2) (ball z (9 / 2 * r₀)) at hy
    rw [_root_.thickening_ball hδ₂ (by positivity)] at hy
    change y ∈ (W : Set ℂ)
    rw [hWset]
    refine ball_subset_ball ?_ hy
    linarith
  have hA : ∃ F : LQGMetric.DistOn W → Measure ℂ, Measurable F ∧ ∀ᵐ ω ∂P,
      F (LQGMetric.restrictTo W ((l46tZeroConeCellModel D hγ).field ω)) =
        (CellScaling.lqgArea γ ((l46tZeroConeCellModel D hγ).field ω)).restrict
          (ball z (9 / 2 * r₀)) := by
    refine ⟨fun x => A.reconstruct (LQGMetric.CONF.resUW W (thickOpen V₂ (r₀ / 2)) x),
      A.measurable_reconstruct.comp (LQGMetric.CONF.measurable_resUW _ _), ?_⟩
    filter_upwards [A.ae_reconstruct] with ω hω
    rw [LQGMetric.CONF.resUW_restrictTo hthick]
    exact hω
  have hW : thickening (r₀ / 4) (ball z (9 / 2 * r₀)) ⊆ (W : Set ℂ) := by
    rw [_root_.thickening_ball (by positivity) (by positivity), hWset]
    exact ball_subset_ball (by linarith)
  obtain ⟨f, hf, hfae⟩ := l43p_zeroCone_pointFactor D hγ hε (q := q) ζ z W hW hA
  refine ⟨fun x => f (x.1.2, x.2), hf.comp ((measurable_snd.comp measurable_fst).prodMk
    measurable_snd), ?_⟩
  filter_upwards [hfae] with ω hω
  rw [maskedUStarPrime_eq_ite]
  change (if circleCond D hγ ε q ζ z ω then truePointFactor (η₀ ω) z ε r₀ ζ else 0) =
    if circleCond D hγ ε q ζ z ω then f (LQGMetric.restrictTo W
      ((l46tZeroConeCellModel D hγ).field ω), (LQGMetric.restrictTo W (hIG₀ ω), U ω)) else 0
  rw [hω]

end MatedCRTHarmonic.GMS4cP
