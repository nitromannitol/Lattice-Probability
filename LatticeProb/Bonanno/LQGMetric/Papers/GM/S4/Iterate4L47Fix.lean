/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4L47Fix at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L47

/-!
# GM Lemma 4.7 per `k`: from the candidate pairs to `𝒵^E_k`, `𝒵^𝔈_k` (DEC-89, packet B)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7, l. 1914–1940:
(4.17) for the finitely many candidate pairs `(z, r)` (`gm_L4_7_fixed`), then (4.14)
(`gm_h47_of_fixed`). Here the unions over the pairs are compared with the events
`{𝒵^E_k ≠ ∅}` (contained in the union of the pairs of `S` on `G`, GM l. 1925: on `G`, `𝒵_k` is a
subset of the finite set of candidates) and `{𝒵^𝔈_k ≠ ∅}` (containing the union).

* `gm_h47_of_pairs`: the hypothesis `h47` of `gm_P4_17_ae` at index `k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric.GM

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **GM (4.14) at index `k` from the candidate pairs** (l. 1914–1940) -/
theorem gm_h47_of_pairs [IsProbabilityMeasure μ] {F ℱk : MeasurableSpace Ω} (hF : F ≤ mΩ)
    (hcond : ∀ f : Ω → ℝ, μ[f | F] =ᵐ[μ] μ[f | ℱk])
    {ι : Type} (S : Finset ι) (A B Z : ι → Set Ω) (W G ZE ZF Reg : Set Ω)
    (hA : ∀ i, MeasurableSet[mΩ] (A i)) (hB : ∀ i, MeasurableSet[mΩ] (B i))
    (hZ : ∀ i, MeasurableSet[F] (Z i)) (hAZ : ∀ i, A i ⊆ Z i) (hG : MeasurableSet[F] G)
    (hZEm : MeasurableSet[mΩ] ZE) (hZFm : MeasurableSet[mΩ] ZF)
    (hZE : ZE ∩ G ⊆ ⋃ i ∈ S, A i) (hZF : ⋃ i ∈ S, B i ⊆ ZF)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hpair : ∀ i ∈ S, ∀ᵐ x ∂μ,
      (μ⟦A i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x ≤
        Λ * ((μ⟦B i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x))
    {K Cp δ : ℝ} (hK : 0 < K) (hCp : 0 ≤ Cp) (hδ : 0 < δ) {N : Ω → ℝ}
    (hNm : Measurable[mΩ] N) (hNi : Integrable N μ)
    (hN : ∀ x, ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x ≤ N x)
    (hNG : ∀ x ∈ G, N x ≤ Cp) (hP : μ.real ({x | K < N x} ∩ G) ≤ δ)
    (hReg : ∀ᵐ ω ∂μ, ω ∈ Reg → ω ∈ W ∩ G) :
    μ.real {ω | ω ∈ Reg ∧ μ[ZF.indicator (fun _ => (1 : ℝ)) | ℱk] ω <
      (Λ * K)⁻¹ * μ[ZE.indicator (fun _ => (1 : ℝ)) | ℱk] ω - Cp * Real.sqrt δ / K} ≤
        Real.sqrt δ := by
  have hfix := gm_L4_7_fixed hF S A B Z W G hA hB hZ hAZ hG hΛ hpair hK.le hCp hδ hNm hNi hN
    hNG hP
  refine gm_h47_of_fixed hcond hK hΛ hReg
    (le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae ?_)) hfix)
  have hUA : MeasurableSet[mΩ] (⋃ i ∈ S, A i) := Finset.measurableSet_biUnion S fun i _ => hA i
  have hUB : MeasurableSet[mΩ] (⋃ i ∈ S, B i) := Finset.measurableSet_biUnion S fun i _ => hB i
  have hGm : MeasurableSet[mΩ] (Gᶜ) := (hF _ hG).compl
  have hi : ∀ {T : Set Ω}, MeasurableSet[mΩ] T → Integrable (T.indicator fun _ => (1 : ℝ)) μ :=
    fun hT => (integrable_const (1 : ℝ)).indicator hT
  -- `μ⟦⋃ B | F⟧ ≤ μ⟦ZF | F⟧`
  have h1 : μ⟦⋃ i ∈ S, B i | F⟧ ≤ᵐ[μ] μ⟦ZF | F⟧ :=
    condExp_mono (hi hUB) (hi hZFm) (Eventually.of_forall fun x =>
      indicator_le_indicator_of_subset hZF (fun _ => zero_le_one) x)
  -- `μ⟦ZE | F⟧ ≤ μ⟦⋃ A | F⟧ + 1_{Gᶜ}`
  have h2 : μ⟦ZE | F⟧ ≤ᵐ[μ] μ[(⋃ i ∈ S, A i).indicator (fun _ => (1 : ℝ)) +
      Gᶜ.indicator (fun _ => (1 : ℝ)) | F] := by
    refine condExp_mono (hi hZEm) ((hi hUA).add (hi hGm)) (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ZE
    · by_cases hxG : x ∈ G
      · have : x ∈ ⋃ i ∈ S, A i := hZE ⟨hx, hxG⟩
        simp only [Pi.add_apply, indicator_of_mem hx, indicator_of_mem this]
        exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ => zero_le_one) x)
      · have : x ∈ Gᶜ := hxG
        simp only [Pi.add_apply, indicator_of_mem hx, indicator_of_mem this]
        exact le_add_of_nonneg_left (indicator_nonneg (fun _ _ => zero_le_one) x)
    · simp only [Pi.add_apply, indicator_of_notMem hx]
      exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) x)
        (indicator_nonneg (fun _ _ => zero_le_one) x)
  have h3 := condExp_add (m := F) (hi hUA) (hi hGm)
  have h4 : μ[Gᶜ.indicator (fun _ => (1 : ℝ)) | F] = Gᶜ.indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable hF
      ((stronglyMeasurable_const.indicator (MeasurableSet.compl (m := F) hG)))
      (hi hGm)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hbad
  obtain ⟨⟨hxW, hxG⟩, hlt⟩ := hbad
  refine ⟨⟨hxW, hxG⟩, ?_⟩
  have hGc : Gᶜ.indicator (fun _ => (1 : ℝ)) x = 0 := indicator_of_notMem (by simpa using hxG) _
  rw [hx3, Pi.add_apply, h4, hGc, add_zero] at hx2
  have hK' : K * (μ⟦⋃ i ∈ S, B i | F⟧) x ≤ K * (μ⟦ZF | F⟧) x :=
    mul_le_mul_of_nonneg_left hx1 hK.le
  have hΛ' : Λ⁻¹ * (μ⟦ZE | F⟧) x ≤ Λ⁻¹ * (μ⟦⋃ i ∈ S, A i | F⟧) x :=
    mul_le_mul_of_nonneg_left hx2 (inv_nonneg.2 hΛ.le)
  linarith

end LQGMetric.GM
