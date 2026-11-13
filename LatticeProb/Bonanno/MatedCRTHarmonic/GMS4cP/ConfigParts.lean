/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.ConfigParts at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.ZeroCone
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2

/-!
# The two halves of the configuration form of Lemma 4.3

Source: the proof of [18] Lemma 4.3 : "`μ_h` is determined by
`h|_V`" (the **area half**: one Borel map of `h|_V` returning `μ_h|_U` almost surely) and Lemma 2.4 (the
**IG half**: one Borel map of `(h^IG|_V, U)` returning the excursion segments into `U`). For the transfer's pair (the
γ-cone translated by `z₀` and the zero cone), both halves are needed for **both** laws with the **same** map.
`l43pZeroConeConfigInput_of_parts` assembles them into `L43PZeroConeConfigInput`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c MatedCRTHarmonic.MatedCRT
open LQGMetric (DistOn restrictTo CONF.resUW CONF.measurable_resUW CONF.resUW_restrictTo)

attribute [local instance] Classical.propDecidable

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The area half of measurable Lemma 4.3** on the transfer's disks: one Borel map of the field on the
observation disk returning the restricted LQG area of both the translated γ-cone and the zero cone. -/
def L43PZeroConeAreaInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ρ : ℝ) (w : ℂ) : Prop :=
  ∃ F : DistOn (l46tObservation ρ w) → Measure ℂ, Measurable F ∧
    (∀ᵐ ω ∂P, F (restrictTo (l46tObservation ρ w)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (MoTInput.cellModelOfCoupling D hγ).field ω)) =
      ((CellScaling.lqgArea γ ((MoTInput.cellModelOfCoupling D hγ).field ω)).map
        (fun x => x + (w + ((1 - ρ) / 2 : ℝ)))).restrict (l46tLocalRegion ρ w)) ∧
    (∀ᵐ ω ∂P, F (restrictTo (l46tObservation ρ w) ((l46tZeroConeCellModel D hγ).field ω)) =
      (CellScaling.lqgArea γ ((l46tZeroConeCellModel D hγ).field ω)).restrict (l46tLocalRegion ρ w))

/-- **The IG half of measurable Lemma 4.3** on the transfer's disks: one Borel map of the IG field on the observation
disk and the IG phase returning the excursion segments into the reconstruction disk of `η_L + z₀` (translated
side) and of `η_L` (zero-cone side). -/
def L43PZeroConeIGInput
    (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (ρ : ℝ) (w : ℂ) : Prop :=
  ∃ G : DistOn (l46tObservation ρ w) × ℝ → (ℚ × ℚ → ℝ → ℂ), Measurable G ∧
    (∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, ratPt q ∈ l46tLocalRegion ρ w →
      G (restrictTo (l46tObservation ρ w)
          (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀ ω), T ω) q =
        excursionSegment (translateC (w + ((1 - ρ) / 2 : ℝ)) (ηL ω)) (l46tLocalRegion ρ w)
          (ratPt q)) ∧
    (∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, ratPt q ∈ l46tLocalRegion ρ w →
      G (restrictTo (l46tObservation ρ w) (hIG₀ ω), T ω) q =
        excursionSegment (ηL ω) (l46tLocalRegion ρ w) (ratPt q))

/-- the transfer's reconstruction disk lies in its observation disk. -/
theorem l46tLocalRegion_le_observation {ρ : ℝ} (hρ : ρ < 1) (w : ℂ) :
    l46tLocalRegion ρ w ≤ l46tObservation ρ w := by
  intro z hz
  exact ball_subset_ball (by linarith) hz

/-- The two halves give the configuration form of measurable Lemma 4.3. -/
theorem l43pZeroConeConfigInput_of_parts
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ : ρ < 1) (w : ℂ)
    (hA : L43PZeroConeAreaInput D hγ ρ w) (hIG : L43PZeroConeIGInput D ρ w) :
    L43PZeroConeConfigInput D hγ ρ w := by
  obtain ⟨F, hF, hFγ, hF₀⟩ := hA
  obtain ⟨G, hG, hGγ, hG₀⟩ := hIG
  have hUV : l46tLocalRegion ρ w ≤ l46tObservation ρ w := l46tLocalRegion_le_observation hρ w
  let R₀ : L46TLocalFieldPhase (l46tObservation ρ w) → LocalConfiguration (l46tLocalRegion ρ w) :=
    fun x => ((F x.1.1, LQGMetric.CONF.resUW (l46tObservation ρ w) (l46tLocalRegion ρ w) x.1.1),
      fun q => if ratPt q ∈ l46tLocalRegion ρ w then G (x.1.2, x.2) q else 0)
  have hR₀ : Measurable R₀ := by
    have h1 : Measurable fun x : L46TLocalFieldPhase (l46tObservation ρ w) =>
        (F x.1.1, LQGMetric.CONF.resUW (l46tObservation ρ w) (l46tLocalRegion ρ w) x.1.1) :=
      (hF.comp (measurable_fst.comp measurable_fst)).prodMk
        ((LQGMetric.CONF.measurable_resUW _ _).comp (measurable_fst.comp measurable_fst))
    have h2 : Measurable fun x : L46TLocalFieldPhase (l46tObservation ρ w) =>
        (fun q => if ratPt q ∈ l46tLocalRegion ρ w then G (x.1.2, x.2) q else 0 :
          ℚ × ℚ → ℝ → ℂ) := by
      refine measurable_pi_iff.mpr fun q => ?_
      by_cases hq : ratPt q ∈ l46tLocalRegion ρ w
      · simp only [hq, ↓reduceIte]
        exact (measurable_pi_apply q).comp
          (hG.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      · simp only [hq, ↓reduceIte]
        exact measurable_const
    exact h1.prodMk h2
  refine ⟨R₀, hR₀, ?_, ?_⟩
  · filter_upwards [hFγ, hGγ] with ω hFω hGω
    simp only [R₀, l46tLocalFieldPhase, GMS4c.localFieldPair, localConfiguration]
    rw [hFω, LQGMetric.CONF.resUW_restrictTo hUV]
    congr 1
    funext q
    by_cases hq : ratPt q ∈ l46tLocalRegion ρ w
    · simp only [hq, ↓reduceIte]
      exact hGω q hq
    · simp [hq]
  · filter_upwards [hF₀, hG₀] with ω hFω hGω
    simp only [R₀, l46tLocalFieldPhase, GMS4c.localFieldPair, localConfiguration]
    rw [hFω, LQGMetric.CONF.resUW_restrictTo hUV]
    congr 1
    funext q
    by_cases hq : ratPt q ∈ l46tLocalRegion ρ w
    · simp only [hq, ↓reduceIte]
      exact hGω q hq
    · simp [hq]

end MatedCRTHarmonic.GMS4cP
