import LatticeProb.LQG.InternalMetricAnnulusLocal
import LatticeProb.LQG.InternalMetricSupTailUniform

/-! # Good circles for the internal diameter of an LQG metric

For a γ-LQG metric `𝔇`, a whole-plane GFF `(hC, hcirc)` with a distribution-valued version `H`, a constant `C`, a radius
`r > 0` and a centre `z`, the circle `∂B_r(z)` is *good* when
`sup_{x, y ∈ ∂B_r(z)} 𝔇_h(x, y; A_{r/2, 2r}(z)) ≤ C e^{ξ (h_r(z) + Q log r)}` and the circle average `h_r(z)` of the
GFF agrees with the circle average of the version `H`. This module shows:

* `image_affine_sphere_zero_one`, `image_affine_annulus`: the affine image `w ↦ r w + z` of the unit circle and of
  `A_{1/2, 2}(0)` are `∂B_r(z)` and `A_{r/2, 2r}(z)`;
* `internalMetric_sphere_le_of_mem_scaledInternalSupEvent`: on the diameter event, any two points of `∂B_r(z)` are at
  internal distance at most `C e^{ξ (h_r(z) + Q log r)}` in `A_{r/2, 2r}(z)`;
* `IsLQGMetric.aeAnnulusEvent_goodCircleEvent`: the good-circle event is almost surely local on the annulus
  `A_{r/2, 5r/2}(0)` (the hypothesis of the annulus iteration lemma);
* `IsLQGMetric.exists_le_measure_goodCircleEvent`: for every `p < 1` there is `C > 1`, independent of the realization,
  the radius and the centre, such that the good-circle event has probability at least `p`.
-/

open MeasureTheory Set Metric LatticeProb.Gauss LQGMetric LQGMetric.Blueprint
open scoped ENNReal

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The image of the unit circle under `w ↦ r w + z`, `r > 0`, is the circle `∂B_r(z)`. -/
theorem image_affine_sphere_zero_one {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (fun w : ℂ => (r : ℂ) * w + z) '' sphere (0 : ℂ) 1 = sphere z r := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  ext x
  simp only [mem_image, mem_sphere_iff_norm, sub_zero]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [add_sub_cancel_right, norm_mul, hw, Complex.norm_real, Real.norm_of_nonneg hr.le, mul_one]
  · intro hx
    refine ⟨(r : ℂ)⁻¹ * (x - z), ?_, ?_⟩
    · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, hx, inv_mul_cancel₀ hr.ne']
    · field_simp
      ring

/-- The image of the annulus `A_{1/2, 2}(0)` under `w ↦ r w + z`, `r > 0`, is the annulus `A_{r/2, 2r}(z)`. -/
theorem image_affine_annulus {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (fun w : ℂ => (r : ℂ) * w + z) '' ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ) =
      {x : ℂ | r / 2 < ‖x - z‖ ∧ ‖x - z‖ < 2 * r} := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  ext x
  simp only [mem_image, annulus, TopologicalSpace.Opens.coe_mk, mem_ofPred_eq, sub_zero]
  constructor
  · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
    rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨(r : ℂ)⁻¹ * (x - z), ?_, ?_⟩
    · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le]
      constructor
      · rw [lt_inv_mul_iff₀ hr]; linarith
      · rw [inv_mul_lt_iff₀ hr]; linarith
    · field_simp
      ring

omit [MeasurableSpace Ω] in
/-- On the diameter event for the unit circle in `A_{1/2, 2}(0)`, any two points of `∂B_r(z)` are at internal distance
at most `C e^{ξ (h_r(z) + Q log r)}` in the annulus `A_{r/2, 2r}(z)`. -/
theorem internalMetric_sphere_le_of_mem_scaledInternalSupEvent {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {C r : ℝ} (hr : 0 < r) {z : ℂ} {ω : Ω}
    (hω : ω ∈ scaledInternalSupEvent γ ξ 𝔇 hC hcirc (sphere (0 : ℂ) 1)
      ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ) C r z)
    {p p' : ℂ} (hp : p ∈ sphere z r) (hp' : p' ∈ sphere z r) :
    internalMetric (𝔇 (hC ω)) {x : ℂ | r / 2 < ‖x - z‖ ∧ ‖x - z‖ < 2 * r} p p' ≤
      ENNReal.ofReal (C * Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r))) := by
  have h1 : p ∈ (fun w : ℂ => (r : ℂ) * w + z) '' sphere (0 : ℂ) 1 := by
    rw [image_affine_sphere_zero_one hr]; exact hp
  have h2 : p' ∈ (fun w : ℂ => (r : ℂ) * w + z) '' sphere (0 : ℂ) 1 := by
    rw [image_affine_sphere_zero_one hr]; exact hp'
  refine le_trans ?_ hω
  rw [← image_affine_annulus hr z]
  exact le_iSup₂_of_le p h1 (le_iSup₂_of_le p' h2 le_rfl)

/-- The good-circle event: the diameter event for the unit circle in `A_{1/2, 2}(0)` at scale `r` and centre `z`,
together with the agreement of the circle average `h_r(z)` of the GFF with that of the version `H`. -/
def goodCircleEvent (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (H : Ω → DistC) (C r : ℝ) (z : ℂ) : Set Ω :=
  scaledInternalSupEvent γ ξ 𝔇 hC hcirc (sphere (0 : ℂ) 1)
      ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ) C r z ∩
    {ω | hcirc ω r z = circleAvg (H ω) r z}

/-- An almost sure modification of an event local on an annulus is local on the annulus. -/
theorem AeAnnulusEvent.congr_ae {h : Ω → DistC} {z : ℂ} {ρ : ℝ} {G G' : Set Ω} (hG : AeAnnulusEvent P h z ρ G)
    (hGG : G =ᵐ[P] G') : AeAnnulusEvent P h z ρ G' := by
  obtain ⟨E, hE, hEG⟩ := hG
  exact ⟨E, hE, hEG.trans hGG⟩

/-- **The good-circle event is almost surely local on an annulus.** -/
theorem IsLQGMetric.aeAnnulusEvent_goodCircleEvent [IsProbabilityMeasure P] (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {H : Ω → DistC}
    (hH : LQGMetric.IsWholePlaneGFF H P) (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) {ρ : ℝ} (hρ : 0 < ρ)
    (z : ℂ) (C : ℝ) : AeAnnulusEvent P H z ρ (goodCircleEvent γ ξ 𝔇 hC hcirc H C ρ z) := by
  have hKU : sphere (0 : ℂ) 1 ⊆ ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ) := by
    intro w hw
    rw [mem_sphere_iff_norm, sub_zero] at hw
    simp only [annulus, TopologicalSpace.Opens.coe_mk, mem_ofPred_eq, sub_zero, hw]
    norm_num
  have hUA : ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆
      ((annulus (0 : ℂ) (1 / 2) (5 / 2) : TopologicalSpace.Opens ℂ) : Set ℂ) := by
    intro w hw
    simp only [annulus] at hw ⊢
    exact ⟨hw.1, by linarith [hw.2]⟩
  have hS := h𝔇.aeAnnulusEvent_scaledInternalSupEvent hG hH hHC hHcirc (annulus (0 : ℂ) (1 / 2) 2).isOpen
    (isCompact_sphere _ _) hKU hUA hρ z C
  refine hS.congr_ae ?_
  filter_upwards [hHcirc ρ hρ z] with ω hω
  exact propext ⟨fun h => ⟨h, hω⟩, fun h => h.1⟩

/-- **The good-circle event has probability at least `p`, uniformly.** For a γ-LQG metric `𝔇` and `p < 1` there is
`C > 1` such that for every whole-plane GFF `(hC, hcirc)` with a version `H` whose circle averages agree almost surely
with `hcirc`, every `r > 0` and every `z`, the probability of the good-circle event is at least `p`. -/
theorem IsLQGMetric.exists_le_measure_goodCircleEvent (h𝔇 : IsLQGMetric γ ξ 𝔇) {p : ℝ} (hp1 : p < 1) :
    ∃ C : ℝ, 1 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ H : Ω → DistC,
      (∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      ENNReal.ofReal p ≤ P (goodCircleEvent γ ξ 𝔇 hC hcirc H C r z) := by
  have hKU : sphere (0 : ℂ) 1 ⊆ ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ) := by
    intro w hw
    rw [mem_sphere_iff_norm, sub_zero] at hw
    simp only [annulus, TopologicalSpace.Opens.coe_mk, mem_ofPred_eq, sub_zero, hw]
    norm_num
  have hKc : IsPreconnected (sphere (0 : ℂ) 1) :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) (0 : ℂ)
      zero_le_one).isPreconnected
  obtain ⟨C₁, hC₁⟩ := h𝔇.exists_measure_scaled_iSup_internalMetric_gt_le (annulus (0 : ℂ) (1 / 2) 2).isOpen
    (isCompact_sphere _ _) hKc hKU (ε := ENNReal.ofReal (1 - p)) (by simpa using hp1)
  refine ⟨max C₁ 2, lt_of_lt_of_le one_lt_two (le_max_right _ _), ?_⟩
  intro Ω _ P _ hC hcirc hG H hH r hr z
  set G := scaledInternalSupEvent γ ξ 𝔇 hC hcirc (sphere (0 : ℂ) 1)
    ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ) (max C₁ 2) r z with hGdef
  have hGc : Gᶜ ⊆ {ω | ENNReal.ofReal (C₁ * Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r))) <
        ⨆ x ∈ (fun w : ℂ => (r : ℂ) * w + z) '' sphere (0 : ℂ) 1, ⨆ y ∈ (fun w : ℂ => (r : ℂ) * w + z) '' sphere (0 : ℂ) 1,
          internalMetric (𝔇 (hC ω)) ((fun w : ℂ => (r : ℂ) * w + z) ''
            ((annulus (0 : ℂ) (1 / 2) 2 : TopologicalSpace.Opens ℂ) : Set ℂ)) x y} := by
    intro ω hω
    simp only [hGdef, scaledInternalSupEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    refine lt_of_le_of_lt ?_ hω
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hPc : P Gᶜ ≤ ENNReal.ofReal (1 - p) := (measure_mono hGc).trans (hC₁ Ω P hC hcirc hG r hr z)
  have hE : P {ω | hcirc ω r z = circleAvg (H ω) r z}ᶜ = 0 := ae_iff.1 (hH r hr z)
  have hcA : P (goodCircleEvent γ ξ 𝔇 hC hcirc H (max C₁ 2) r z)ᶜ ≤ ENNReal.ofReal (1 - p) := by
    rw [goodCircleEvent, Set.compl_inter]
    calc P (Gᶜ ∪ {ω | hcirc ω r z = circleAvg (H ω) r z}ᶜ) ≤ P Gᶜ + P {ω | hcirc ω r z = circleAvg (H ω) r z}ᶜ :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 - p) := by rw [hE, add_zero]; exact hPc
  have h1 : (1 : ℝ≥0∞) ≤ P (goodCircleEvent γ ξ 𝔇 hC hcirc H (max C₁ 2) r z) + ENNReal.ofReal (1 - p) :=
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ = P (goodCircleEvent γ ξ 𝔇 hC hcirc H (max C₁ 2) r z ∪ (goodCircleEvent γ ξ 𝔇 hC hcirc H (max C₁ 2) r z)ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ P (goodCircleEvent γ ξ 𝔇 hC hcirc H (max C₁ 2) r z) + P (goodCircleEvent γ ξ 𝔇 hC hcirc H (max C₁ 2) r z)ᶜ :=
          measure_union_le _ _
      _ ≤ _ := add_le_add_right hcA _
  have h2 : ENNReal.ofReal p = 1 - ENNReal.ofReal (1 - p) := by
    have := ENNReal.ofReal_sub 1 (show 0 ≤ 1 - p by linarith)
    rw [ENNReal.ofReal_one] at this
    rw [← this]
    congr 1
    ring
  rw [h2]
  exact tsub_le_iff_right.2 h1

end LatticeProb.LQG
