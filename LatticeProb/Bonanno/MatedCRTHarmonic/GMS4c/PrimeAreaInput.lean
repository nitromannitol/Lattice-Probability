/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.PrimeAreaInput at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.TranslatedAreaReader
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.ZeroCone
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.ConfigParts

/-! The Borel area input for the exact primed local reconstruction disk. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
  MatedCRTHarmonic.GMS4cP

/-- The delta-thickening of the reconstruction disk is contained in the
observation disk. -/
theorem prime_thickRegion_le_observation {ρ : ℝ} (hρ : ρ < 1) (w : ℂ) :
    thickOpen (l46tLocalRegion ρ w) ((1 - ρ) / 16) ≤
      l46tObservation ρ w := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := mem_thickening_iff.mp hz
  change x ∈ ball w ((1 - ρ) / 8) at hx
  change z ∈ ball w ((1 - ρ) / 4)
  rw [mem_ball] at hx ⊢
  have ht := dist_triangle z x w
  linarith

/-- The reconstruction disk lies inside the unit disk for the specified
center geometry. -/
theorem prime_localRegion_subset_unit {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    (l46tLocalRegion ρ w : Set ℂ) ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  change z ∈ ball w ((1 - ρ) / 8) at hz
  rw [mem_ball] at hz
  rw [mem_closedBall] at hw
  rw [mem_ball]
  have htri := dist_triangle z w 0
  linarith [hρ.2]

/-- The fixed upward shift by two units puts the local disk in the upper half-plane. -/
theorem prime_localRegion_shifted_upper {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    (Homeomorph.addRight (2 * Complex.I)) '' (l46tLocalRegion ρ w : Set ℂ) ⊆
      QuantumZipper.H := by
  rintro y ⟨x, hx, rfl⟩
  have hnorm : ‖x‖ < 1 := by
    simpa only [mem_ball, dist_zero_right] using prime_localRegion_subset_unit hρ w hw hx
  have him := (Complex.abs_im_le_norm x).trans_lt hnorm
  have hxlo : -1 < x.im := (abs_lt.mp him).1
  change 0 < (x + 2 * Complex.I).im
  norm_num [Complex.add_im, Complex.mul_im] at *
  linarith

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The area half of Lemma 4.3, on the exact disks required by the bundle construction. -/
theorem prime_zeroConeAreaInput_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    L43PZeroConeAreaInput D hγ ρ w := by
  let V : TopologicalSpace.Opens ℂ := l46tLocalRegion ρ w
  let W : TopologicalSpace.Opens ℂ := l46tObservation ρ w
  let δ : ℝ := (1 - ρ) / 16
  let z₀ : ℂ := w + ((1 - ρ) / 2 : ℝ)
  let J : ℂ ≃ₜ ℂ := Homeomorph.addRight (2 * Complex.I)
  have hδ : 0 < δ := by dsimp [δ]; linarith [hρ.2]
  have hVW : thickOpen V δ ≤ W := prime_thickRegion_le_observation hρ.2 w
  have hVb : Bornology.IsBounded (V : Set ℂ) := isBounded_ball
  have hVc : (V : Set ℂ)ᶜ.Nonempty := by
    refine ⟨w + (2 : ℂ), ?_⟩
    change w + (2 : ℂ) ∉ ball w ((1 - ρ) / 8)
    simp only [mem_ball, not_lt]
    norm_num
    linarith [hρ.1]
  have hJb : Bornology.IsBounded (J '' (V : Set ℂ)) :=
    ((hVb.isCompact_closure.image J.continuous).isBounded).subset
      (image_mono subset_closure)
  have hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H :=
    prime_localRegion_shifted_upper hρ w hw
  have hJc : (J '' (V : Set ℂ))ᶜ.Nonempty := by
    refine ⟨0, ?_⟩
    intro hz
    have hh := hJH hz
    exact (lt_irrefl (0 : ℝ)) hh
  obtain ⟨F, hFm, hFγ, hF₀⟩ :=
    exists_borel_translated_bundle_localAreaReader D hγ V hVb hVc hδ z₀ J hJb hJH hJc
  let F' : DistOn W → Measure ℂ :=
    fun x => F (LQGMetric.CONF.resUW W (thickOpen V δ) x)
  have hF' : Measurable F' := hFm.comp (LQGMetric.CONF.measurable_resUW W (thickOpen V δ))
  refine ⟨F', hF', ?_, ?_⟩
  · filter_upwards [hFγ] with ω hω
    change F' (restrictTo W (l46tTranslatedField z₀ (MoTInput.cellModelOfCoupling D hγ).field ω)) = _
    rw [show F' (restrictTo W (l46tTranslatedField z₀ (MoTInput.cellModelOfCoupling D hγ).field ω)) =
      F (restrictTo (thickOpen V δ)
        (l46tTranslatedField z₀ (MoTInput.cellModelOfCoupling D hγ).field ω)) by
          exact congrArg F (LQGMetric.CONF.resUW_restrictTo hVW _)]
    exact hω
  · filter_upwards [hF₀] with ω hω
    change F' (restrictTo W ((l46tZeroConeCellModel D hγ).field ω)) = _
    rw [show F' (restrictTo W ((l46tZeroConeCellModel D hγ).field ω)) =
      F (restrictTo (thickOpen V δ) ((l46tZeroConeCellModel D hγ).field ω)) by
        exact congrArg F (LQGMetric.CONF.resUW_restrictTo hVW _)]
    exact hω

end MatedCRTHarmonic.GMS4c

