import LatticeProb.LQG.AnnulusIterateNoGood
import LatticeProb.LQG.InternalMetricCompactSupMeasurable
import LatticeProb.LQG.LQGMetricInternalScaling
import LatticeProb.Prob.AeEqSigma

/-!
# The diameter event of a γ-LQG metric is local on an annulus

For a γ-LQG metric `𝔇`, a whole-plane GFF `h`, a compact set `K` in an open set `U` of the annulus `A_{1/2, 5/2}(0)`,
a radius `r > 0` and a centre `z`, the event
`{sup_{x, y ∈ r K + z} D_h(x, y; r U + z) ≤ C e^{ξ (h_r(z) + Q log r)}}`
is almost surely an event of the recentred field `h(r · + z) - h_r(z)` restricted to `U`
(`exists_measurableSet_ae_eq_scaledInternalSupEvent`), and hence, for a version `H` of `h` with values in the space of
distributions, almost surely an event of `(h - h_{3r}(z))(· + z)` restricted to `A_{r/2, 5r/2}(0)` (the form
`AeAnnulusEvent` of the annulus iteration).

## Main statements

* `LatticeProb.LQG.scaledInternalSupEvent`
* `LatticeProb.LQG.IsLQGMetric.exists_measurableSet_ae_eq_scaledInternalSupEvent`
* `LatticeProb.LQG.aeAnnulusEvent_of_measurableSet_recentredPairing`
* `LatticeProb.LQG.IsLQGMetric.aeAnnulusEvent_scaledInternalSupEvent`
-/

open MeasureTheory Set LatticeProb.Gauss LQGMetric LQGMetric.Blueprint LQGMetric.GM LQGMetric.GFFInv
open scoped ENNReal

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The event that `sup_{x, y ∈ r K + z} D_h(x, y; r U + z) ≤ C e^{ξ (h_r(z) + Q log r)}`, the complement of the event
bounded in `IsLQGMetric.exists_measure_scaled_iSup_internalMetric_gt_le`. -/
def scaledInternalSupEvent (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (K U : Set ℂ) (C r : ℝ) (z : ℂ) : Set Ω :=
  {ω | (⨆ x ∈ (fun w : ℂ => (r : ℂ) * w + z) '' K, ⨆ y ∈ (fun w : ℂ => (r : ℂ) * w + z) '' K,
      internalMetric (𝔇 (hC ω)) ((fun w : ℂ => (r : ℂ) * w + z) '' U) x y) ≤
    ENNReal.ofReal (C * Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r)))}

/-- **The diameter event is almost surely an event of the recentred field on `U`.** For a γ-LQG metric `𝔇`, a
whole-plane GFF, a compact set `K` in an open set `U`, `r > 0` and `z ∈ ℂ`, the event
`sup_{x, y ∈ r K + z} D_h(x, y; r U + z) ≤ C e^{ξ (h_r(z) + Q log r)}` is almost surely equal to a set which is
measurable for the pairings of `h(r · + z) - h_r(z)` with test functions supported in `U`. -/
theorem IsLQGMetric.exists_measurableSet_ae_eq_scaledInternalSupEvent (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {r : ℝ}
    (hr : 0 < r) (z : ℂ) (C : ℝ) :
    ∃ S : Set Ω, MeasurableSet[pairingSigmaAlgebra (recentredPairing hC hcirc r z) U] S ∧
      S =ᵐ[P] scaledInternalSupEvent γ ξ 𝔇 hC hcirc K U C r z := by
  obtain ⟨T, hTm, hTae⟩ := h𝔇.exists_measurable_iSup_internalMetric
    (isWholePlaneGFF_recentredPairing hG hr z) hU hK hKU
  refine ⟨T ⁻¹' Iic (ENNReal.ofReal C), hTm measurableSet_Iic, ?_⟩
  filter_upwards [hTae, h𝔇.ae_internalMetric_scaling hG hr z] with ω hT hω
  apply propext
  set a := ENNReal.ofReal (Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r))) with ha
  have hsup : (⨆ x ∈ (fun w : ℂ => (r : ℂ) * w + z) '' K, ⨆ y ∈ (fun w : ℂ => (r : ℂ) * w + z) '' K,
        internalMetric (𝔇 (hC ω)) ((fun w : ℂ => (r : ℂ) * w + z) '' U) x y) =
      a * ⨆ u ∈ K, ⨆ v ∈ K, internalMetric (𝔇 (recentredPairing hC hcirc r z ω)) U u v := by
    simp only [iSup_image, hω, ENNReal.mul_iSup]
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  show T ω ≤ ENNReal.ofReal C ↔ _ ≤ ENNReal.ofReal (C * Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r)))
  rw [hsup, ← hT, ENNReal.ofReal_mul' (Real.exp_pos _).le, mul_comm (ENNReal.ofReal C) a]
  exact (ENNReal.mul_le_mul_iff_right ha0 ENNReal.ofReal_ne_top).symm


/-- **Transfer of an event of the recentred field to an annulus event of a distribution-valued version.** Let `H` be a
normalized whole-plane GFF with values in the space of distributions whose pairings with test functions and circle
averages agree almost surely with those of `(hC, hcirc)`. An event `G` which is almost surely equal to an event
measurable for the pairings of `h(ρ · + z) - h_ρ(z)` with test functions supported in an open subset `U` of the annulus
`A_{1/2, 5/2}(0)` is almost surely an event of `(H - H_{3ρ}(z))(· + z) = H(· + z) - H_{3ρ}(z)` restricted to the
annulus `A_{ρ/2, 5ρ/2}(0)`, normalized at radius `3ρ`. -/
theorem aeAnnulusEvent_of_measurableSet_recentredPairing [IsProbabilityMeasure P] {H : Ω → DistC}
    (hH : LQGMetric.IsWholePlaneGFF H P) (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) {U : Set ℂ}
    (hUA : U ⊆ ((annulus 0 (1 / 2) (5 / 2) : TopologicalSpace.Opens ℂ) : Set ℂ)) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ)
    {S G : Set Ω} (hS : MeasurableSet[pairingSigmaAlgebra (recentredPairing hC hcirc ρ z) U] S)
    (hSG : S =ᵐ[P] G) : AeAnnulusEvent P H z ρ G := by
  classical
  set M : Ω → DistC := fun ω => addConst (H ω) (-circleAvg (H ω) (3 * ρ) z) with hM
  set Uz : TopologicalSpace.Opens ℂ := annulus z (ρ / 2) (5 / 2 * ρ) with hUz
  let φC : {φ : ℂ → ℝ // IsTestFunction U φ} → TestC := fun i => ⟨i.1, i.2.1, i.2.2.1, subset_univ _⟩
  let ψ : {φ : ℂ → ℝ // IsTestFunction U φ} → TestC := fun i => testAffinePull ρ z (φC i)
  have hψ : ∀ i y, ψ i y = i.1 ((y - z) / ρ) := fun i y => testAffinePull_apply ρ z hρ.ne' (φC i) y
  have hψint : ∀ i, ∫ x, ψ i x = ρ ^ 2 * ∫ x, i.1 x := fun i => integral_testAffinePull (φC i) hρ z
  have htsupp : ∀ i, tsupport (ψ i : ℂ → ℝ) ⊆ (Uz : Set ℂ) := by
    intro i y hy
    have hg : Continuous fun y : ℂ => (y - z) / (ρ : ℂ) := (continuous_id.sub continuous_const).div_const _
    have hsub : tsupport (ψ i : ℂ → ℝ) ⊆ (fun y : ℂ => (y - z) / (ρ : ℂ)) ⁻¹' tsupport i.1 := by
      refine closure_minimal (fun y hy => ?_) ((isClosed_tsupport _).preimage hg)
      have : ψ i y ≠ 0 := hy
      rw [hψ] at this
      exact subset_tsupport _ this
    have h2 : (1 / 2 : ℝ) < ‖(y - z) / (ρ : ℂ) - 0‖ ∧ ‖(y - z) / (ρ : ℂ) - 0‖ < 5 / 2 :=
      hUA (i.2.2.2 (hsub hy))
    rw [sub_zero, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le] at h2
    obtain ⟨h3, h4⟩ := h2
    rw [lt_div_iff₀ hρ] at h3
    rw [div_lt_iff₀ hρ] at h4
    show ρ / 2 < ‖y - z‖ ∧ ‖y - z‖ < 5 / 2 * ρ
    constructor <;> linarith
  have hcirc_m : Measurable[fieldSigma M Uz] fun ω => circleAvg (M ω) ρ z := by
    refine (measurable_circleAvg_fieldSigma M ρ z (ε := ρ / 2) (by positivity)).mono (fieldSigma_mono M ?_) le_rfl
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx
    have hyz : ‖y - z‖ = ρ := by rw [mem_sphere_iff_norm.1 hy, abs_of_pos hρ]
    have hxy' : ‖x - y‖ < ρ / 2 := by rwa [← dist_eq_norm]
    have h1 := norm_sub_le_norm_sub_add_norm_sub x y z
    have h2 := norm_sub_le_norm_sub_add_norm_sub y x z
    rw [norm_sub_rev y x] at h2
    show ρ / 2 < ‖x - z‖ ∧ ‖x - z‖ < 5 / 2 * ρ
    constructor <;> linarith
  have hYm : ∀ i : {φ : ℂ → ℝ // IsTestFunction U φ}, Measurable[fieldSigma M Uz]
      fun ω => (ρ ^ 2)⁻¹ * M ω (ψ i) - circleAvg (M ω) ρ z * ∫ x, i.1 x := by
    intro i
    let _ := fieldSigma M Uz
    exact ((measurable_pair_fieldSigma M (ψ i) (htsupp i)).const_mul _).sub (hcirc_m.mul_const _)
  have hXY : ∀ i : {φ : ℂ → ℝ // IsTestFunction U φ}, (fun ω => recentredPairing hC hcirc ρ z ω i.1) =ᵐ[P]
      fun ω => (ρ ^ 2)⁻¹ * M ω (ψ i) - circleAvg (M ω) ρ z * ∫ x, i.1 x := by
    intro i
    filter_upwards [hHC (ψ i), hHcirc ρ hρ z, CircleAvg.ae_circleAvg_addConst hH z hρ] with ω h1 h2 h3
    have hf : (⇑(ψ i) : ℂ → ℝ) = fun y => i.1 ((y - z) / ρ) := funext (hψ i)
    show (ρ ^ 2)⁻¹ * hC ω (fun y => i.1 ((y - z) / ρ)) - hcirc ω ρ z * ∫ x, i.1 x =
      (ρ ^ 2)⁻¹ * addConst (H ω) (-circleAvg (H ω) (3 * ρ) z) (ψ i) -
        circleAvg (addConst (H ω) (-circleAvg (H ω) (3 * ρ) z)) ρ z * ∫ x, i.1 x
    rw [addConst_apply, h3, hψint, ← hf, ← h1, h2]
    field_simp
    ring
  have hpair : pairingSigmaAlgebra (recentredPairing hC hcirc ρ z) U =
      ⨆ i : {φ : ℂ → ℝ // IsTestFunction U φ},
        MeasurableSpace.comap (fun ω => recentredPairing hC hcirc ρ z ω i.1) inferInstance := by
    unfold pairingSigmaAlgebra
    refine le_antisymm (iSup₂_le fun φ hφ => le_iSup (fun i : {φ : ℂ → ℝ // IsTestFunction U φ} =>
      MeasurableSpace.comap (fun ω => recentredPairing hC hcirc ρ z ω i.1) inferInstance) ⟨φ, hφ⟩)
      (iSup_le fun i => le_iSup₂_of_le i.1 i.2 le_rfl)
  rw [hpair] at hS
  obtain ⟨t, ht, hst⟩ := exists_measurableSet_ae_eq_iSup_comap (α := fun _ => ℝ)
    (fun (i : {φ : ℂ → ℝ // IsTestFunction U φ}) ω => recentredPairing hC hcirc ρ z ω i.1)
    (fun (i : {φ : ℂ → ℝ // IsTestFunction U φ}) ω => (ρ ^ 2)⁻¹ * M ω (ψ i) - circleAvg (M ω) ρ z * ∫ x, i.1 x)
    hXY hS
  have hle : (⨆ i : {φ : ℂ → ℝ // IsTestFunction U φ}, MeasurableSpace.comap
      (fun ω => (ρ ^ 2)⁻¹ * M ω (ψ i) - circleAvg (M ω) ρ z * ∫ x, i.1 x) inferInstance) ≤
      fieldSigma M Uz := iSup_le fun i => (hYm i).comap_le
  have hF := hle t ht
  have hFG : t =ᵐ[P] G := hst.symm.trans hSG
  have hUV : ∀ y : ℂ, y ∈ annulus 0 (1 / 6 * (3 * ρ)) (5 / 6 * (3 * ρ)) ↔
      (1 : ℝ) • y + z ∈ annulus z (ρ / 2) (5 / 2 * ρ) := fun y => by
    show 1 / 6 * (3 * ρ) < ‖y - 0‖ ∧ ‖y - 0‖ < 5 / 6 * (3 * ρ) ↔
      ρ / 2 < ‖(1 : ℝ) • y + z - z‖ ∧ ‖(1 : ℝ) • y + z - z‖ < 5 / 2 * ρ
    simp only [sub_zero, one_smul, add_sub_cancel_right]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hF2 := fieldSigma_le_affineComp one_pos hUV _ t hF
  obtain ⟨B, hB, hBF⟩ := hF2
  refine ⟨_, ⟨B, hB, rfl⟩, ?_⟩
  have hz := hH.affineComp one_pos z
  refine Filter.EventuallyEq.trans ?_ hFG
  rw [← hBF]
  filter_upwards [CircleAvg.ae_circleAvg_addConst hz 0 (show (0 : ℝ) < 3 * ρ by positivity)] with ω hω
  simp only [hM, mem_preimage]
  rw [affineComp_addConst one_pos, hω, Tight.circleAvg_affineComp_one, Tight.circleAvg_affineComp_one,
    GFFLaw.addConst_addConst]
  congr! 3
  ring

/-- **The diameter event of the γ-LQG metric is almost surely local on an annulus.** For a γ-LQG metric `𝔇`, a
whole-plane GFF `(hC, hcirc)` with a distribution-valued version `H` (pairings and circle averages agree almost
surely), a compact set `K` in an open set `U` of the annulus `A_{1/2, 5/2}(0)`, `ρ > 0`, `z ∈ ℂ` and `C`, the event
`sup_{x, y ∈ ρ K + z} D_h(x, y; ρ U + z) ≤ C e^{ξ (h_ρ(z) + Q log ρ)}` is almost surely an event of
`(H - H_{3ρ}(z))(· + z)` restricted to `A_{ρ/2, 5ρ/2}(0)` (`AeAnnulusEvent`). -/
theorem IsLQGMetric.aeAnnulusEvent_scaledInternalSupEvent [IsProbabilityMeasure P] (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {H : Ω → DistC} (hH : LQGMetric.IsWholePlaneGFF H P)
    (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) {U K : Set ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hUA : U ⊆ ((annulus 0 (1 / 2) (5 / 2) : TopologicalSpace.Opens ℂ) : Set ℂ)) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ)
    (C : ℝ) : AeAnnulusEvent P H z ρ (scaledInternalSupEvent γ ξ 𝔇 hC hcirc K U C ρ z) := by
  obtain ⟨S, hS, hSG⟩ := h𝔇.exists_measurableSet_ae_eq_scaledInternalSupEvent hG hU hK hKU hρ z C
  exact aeAnnulusEvent_of_measurableSet_recentredPairing hH hHC hHcirc hUA hρ z hS hSG

end LatticeProb.LQG
