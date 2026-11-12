/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ConditionalCount at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Conditional

/-!
# GM Lemma 4.8 (conditional step) and GM Lemma 4.7 at fixed `ε`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, §4.2.

* `gm_L4_8_cond` — the last part of the proof of GM Lemma 4.8 (`lem-good-annulus-count`,
  l. 1824–1836): from the unconditional bound (4.19) `P[#𝒵_k(P) > K, G] ≤ δ`
  (`G = {𝓑^•_{t_k} ⊆ B_{ε^{-M}𝕣}(𝕫)} ∈ 𝓕_k`) and the trivial bound (4.20) `#𝒵_k(P) ≤ C_p` on `G`,
  Markov's inequality for `P[#𝒵_k(P) > K, G | 𝓕_k]` gives, outside an event of probability
  `≤ √δ`, `1_G E[#𝒵_k(P) 1_{#𝒵_k(P) > K} | 𝓕_k] ≤ C_p √δ` (GM (4.18) with `δ = o^∞_ε(ε)`,
  `C_p = O(ε^{-2M(1+ν)} log ε^{-1})`, so `C_p √δ = o^∞_ε(ε)`).
* `gm_L4_7_fixed` — GM (4.17) (l. 1931–1936) at fixed `ε`: combining `gm_L4_7_quant` with
  `gm_L4_8_cond`, outside an event of probability `≤ √δ`, on `W ∩ G`,
  `Λ⁻¹ P[𝒵^E_k ≠ ∅ | 𝓕_k] ≤ K P[𝒵^𝔈_k ≠ ∅ | 𝓕_k] + C_p √δ`.
  With `K = ε^{-2ν-ζ}` this is GM's last display before "sending `ζ → 0`".

The unconditional estimate (4.19) itself (from GM Lemma 2.12 = DFGPS Prop 4.3 via GM.S4.8 and the
ball-overlap count, l. 1806–1822) is not proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric.GM

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **GM Lemma 4.8, conditional step** (l. 1824–1836): Markov's inequality turns (4.19) and
(4.20) into the conditional bound (4.18) outside an event of probability `≤ √δ`. -/
theorem gm_L4_8_cond [IsProbabilityMeasure μ] {F : MeasurableSpace Ω} (hF : F ≤ mΩ)
    {G : Set Ω} (hG : MeasurableSet[F] G) {N : Ω → ℝ} (hNm : Measurable[mΩ] N)
    (hNi : Integrable N μ) {K Cp δ : ℝ} (hCp : 0 ≤ Cp) (hδ : 0 < δ)
    (hNG : ∀ x ∈ G, N x ≤ Cp) (hP : μ.real ({x | K < N x} ∩ G) ≤ δ) :
    μ.real {x | Cp * Real.sqrt δ <
      G.indicator (fun _ => (1 : ℝ)) x * (μ[{y | K < N y}.indicator N | F]) x} ≤ Real.sqrt δ := by
  set A : Set Ω := {y | K < N y}
  have hA : MeasurableSet[mΩ] A := measurableSet_lt measurable_const hNm
  have hGm : MeasurableSet[mΩ] G := hF _ hG
  have hAG : MeasurableSet[mΩ] (A ∩ G) := hA.inter hGm
  set E' := μ⟦A ∩ G | F⟧
  -- (1) `1_G E[N 1_A | F] ≤ C_p E'`
  have h1 : ∀ᵐ x ∂μ, G.indicator (fun _ => (1 : ℝ)) x * (μ[A.indicator N | F]) x ≤ Cp * E' x := by
    have hpt : G.indicator (A.indicator N) ≤ᵐ[μ] Cp • (A ∩ G).indicator fun _ => (1 : ℝ) := by
      refine Eventually.of_forall (fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hxG : x ∈ G <;> by_cases hxA : x ∈ A
      · simp [hxG, hxA, hNG x hxG]
      · simp [hxG, hxA]
      · simp [hxG, hxA]
      · simp [hxG, hxA]
    have hm := condExp_mono (m := F) ((hNi.indicator hA).indicator hGm)
      ((integrable_indOne hAG).smul Cp) hpt
    filter_upwards [hm, condExp_indicator (m := F) (hNi.indicator hA) hG,
      condExp_smul (μ := μ) Cp ((A ∩ G).indicator fun _ => (1 : ℝ)) F,
      condExp_nonneg (m := F) (μ := μ) (f := (A ∩ G).indicator fun _ => (1 : ℝ))
        (Eventually.of_forall (fun x => indicator_nonneg (fun _ _ => zero_le_one) x))]
      with x hx1 hx2 hx3 hx4
    rw [hx2, hx3] at hx1
    simp only [Pi.smul_apply, smul_eq_mul] at hx1
    by_cases hxG : x ∈ G
    · simpa [hxG] using hx1
    · simp only [indicator_of_notMem hxG, zero_mul]
      exact mul_nonneg hCp hx4
  -- (2) Markov: `P[√δ ≤ E'] ≤ √δ`
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have h2 : μ.real {x | Real.sqrt δ ≤ E' x} ≤ Real.sqrt δ := by
    have hm := mul_meas_ge_le_integral_of_nonneg (f := E')
      (condExp_nonneg (m := F) (μ := μ) (f := (A ∩ G).indicator fun _ => (1 : ℝ))
        (Eventually.of_forall (fun x => indicator_nonneg (fun _ _ => zero_le_one) x)))
      integrable_condExp (Real.sqrt δ)
    rw [integral_condExp hF, integral_indicator hAG, setIntegral_const, smul_eq_mul,
      mul_one] at hm
    have hδ' : δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ.le).symm
    have := hm.trans (hP.trans_eq hδ')
    exact le_of_mul_le_mul_left this hsq
  -- (3) the bad set is a.e. inside `{√δ ≤ E'}`
  refine le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae ?_)) h2
  filter_upwards [h1] with x hx hlt
  have hlt' : Cp * Real.sqrt δ < Cp * E' x := hlt.trans_le hx
  exact (lt_of_mul_lt_mul_left hlt' hCp).le

/-- **GM (4.17) at fixed `ε`** (proof of GM Lemma 4.7, l. 1931–1936): outside an event of
probability `≤ √δ`, on `W ∩ G`, `Λ⁻¹ P[⋃ A | 𝓕] ≤ K P[⋃ B | 𝓕] + C_p √δ`, given (4.13) for each
candidate pair and the hypotheses (4.19), (4.20) of `gm_L4_8_cond` for a count `N ≥ #𝒵^𝔈_k`. -/
theorem gm_L4_7_fixed [IsProbabilityMeasure μ] {F : MeasurableSpace Ω} (hF : F ≤ mΩ)
    {ι : Type} (S : Finset ι) (A B Z : ι → Set Ω) (W G : Set Ω)
    (hA : ∀ i, MeasurableSet[mΩ] (A i)) (hB : ∀ i, MeasurableSet[mΩ] (B i))
    (hZ : ∀ i, MeasurableSet[F] (Z i)) (hAZ : ∀ i, A i ⊆ Z i) (hG : MeasurableSet[F] G)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hpair : ∀ i ∈ S, ∀ᵐ x ∂μ,
      (μ⟦A i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x ≤
        Λ * ((μ⟦B i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x))
    {K Cp δ : ℝ} (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (hδ : 0 < δ) {N : Ω → ℝ}
    (hNm : Measurable[mΩ] N) (hNi : Integrable N μ)
    (hN : ∀ x, ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x ≤ N x)
    (hNG : ∀ x ∈ G, N x ≤ Cp) (hP : μ.real ({x | K < N x} ∩ G) ≤ δ) :
    μ.real {x | x ∈ W ∩ G ∧ K * (μ⟦⋃ i ∈ S, B i | F⟧) x + Cp * Real.sqrt δ <
      Λ⁻¹ * (μ⟦⋃ i ∈ S, A i | F⟧) x} ≤ Real.sqrt δ := by
  refine le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae ?_))
    (gm_L4_8_cond hF hG hNm hNi hCp hδ hNG hP)
  filter_upwards [gm_L4_7_quant S A B Z W hA hB hZ hAZ hΛ hpair hK hNm hNi hN] with x hx hbad
  obtain ⟨⟨hxW, hxG⟩, hlt⟩ := hbad
  show Cp * Real.sqrt δ < G.indicator (fun _ => (1 : ℝ)) x *
    (μ[{y | K < N y}.indicator N | F]) x
  rw [indicator_of_mem hxG, one_mul]
  have := hx hxW
  linarith

end LQGMetric.GM
