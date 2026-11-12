/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Conditional at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepDetermined
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# GM Lemma 4.7: comparison of `E_r(z)` and `𝔈_r(z)` given `𝓕_k` (conditional-expectation core)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, §4.2, proof of Lemma 4.7
(`lem-annulus-choose`, statement l. 1782–1790, proof l. 1883–1938), using GM Lemma 4.9
(`lem-cond-expectation`, l. 1839–1880; proved: `LQGMetric.condExp_inter_le_of_sup_singleton`).

* `gm_L4_7_pair` — GM (4.12) ⇒ (4.13) (l. 1890–1912): for one pair `(z,r)`, from the hypothesis
  (4.2) of Theorem 4.2 on `G = {(z,r) ∈ 𝒵_k} ∩ {𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})}`, the facts of GM
  Lemma 4.6 (`Stab_{k,r}(z)` a.s. determined by `h|_{ℂ∖B_r(z)}`; `F ∩ Stab ∩ {P ∩ B_r(z) ≠ ∅}`
  a.s. in `σ(h|_{ℂ∖B_r(z)}) ∨ σ(Stab ∩ {P ∩ B_r(z) ≠ ∅})` for `F ∈ 𝓕_k`) and `G ∈ 𝓕_k ∩ 𝒢`,
  conclude `P[(z,r) ∈ 𝒵^E_k | 𝓕_k] 1_G ≤ Λ P[(z,r) ∈ 𝒵^𝔈_k | 𝓕_k] 1_G`. GM's step "(4.2) and
  `Stab ∈ σ(h|_{ℂ∖B_r(z)})` give (4.12)" is `gm_condExp_inter_of_aeEvent` (pull out a
  `𝒢`-measurable indicator), then GM Lemma 4.9 with `E = Stab ∩ {P ∩ B_r(z) ≠ ∅}`,
  `H₁ = E_r(z) ∩ {P ∩ B_{λ₂r}(z) ≠ ∅}`, `H₂ = 𝔈_r(z) ∩ {P ∩ B_{λ₂r}(z) ≠ ∅}` (l. 1898).
* `gm_L4_7_quant` — GM (4.15)–(4.17) (l. 1914–1938) for a finite deterministic index set `S`
  of candidate pairs (on `{𝓑^•_{t_k} ⊆ B_{ε^{-M}𝕣}(𝕫)}` all pairs of `𝒵_k` lie in such a set,
  GM (4.20), l. 1830): summing (4.13), `#𝒵^E ≥ 1_{𝒵^E ≠ ∅}` and the Paley–Zygmund split
  `#𝒵^𝔈 ≤ K 1_{𝒵^𝔈 ≠ ∅} + N 1_{N > K}` (`N` any count dominating `#𝒵^𝔈`, e.g. `#𝒵_k(P)` of
  GM Lemma 4.8) give, a.s. on `{𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})}`,
  `Λ⁻¹ P[𝒵^E ≠ ∅ | 𝓕_k] ≤ K P[𝒵^𝔈 ≠ ∅ | 𝓕_k] + E[N 1_{N > K} | 𝓕_k]`.
  With `K = ε^{-2ν-ζ}` and GM Lemma 4.8 for the last term this is GM (4.17); sending `ζ → 0`
  gives (4.14).

The statements are abstract in the σ-algebras and events, so they apply verbatim with
`𝓕 = 𝓕_k`, `𝒢 = fieldSigmaClosed h (ℂ ∖ B_{λ₃r}(z))` (general `λ₃`, DV-B1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric.GM

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `P[A ∩ S | 𝒢] = 1_{S'} P[A | 𝒢]` when `S` is a.s. equal to `S' ∈ 𝒢` -/
theorem gm_condExp_inter_of_aeEvent [IsFiniteMeasure μ] {G : MeasurableSpace Ω}
    {A S S' : Set Ω} (hA : MeasurableSet[mΩ] A) (hS' : MeasurableSet[G] S')
    (hSS : S =ᵐ[μ] S') :
    μ⟦A ∩ S | G⟧ =ᵐ[μ] fun x => S'.indicator (fun _ => (1 : ℝ)) x * (μ⟦A | G⟧) x := by
  have e1 : (A ∩ S).indicator (fun _ => (1 : ℝ)) =ᵐ[μ]
      S'.indicator (A.indicator fun _ => (1 : ℝ)) := by
    rw [indicator_indicator]
    refine indOne_ae_eq_of_ae_eq ?_
    have : A ∩ S =ᵐ[μ] A ∩ S' := EventuallyEqSet.inter (EventuallyEq.refl _ A) hSS
    exact this.trans (by rw [inter_comm])
  refine (condExp_congr_ae e1).trans ?_
  refine (condExp_indicator (integrable_indOne hA) hS').trans ?_
  refine Eventually.of_forall (fun x => ?_)
  by_cases hx : x ∈ S' <;> simp [hx]

/-- **GM (4.12) ⇒ (4.13)** (proof of GM Lemma 4.7, l. 1890–1912) for one pair `(z, r)`. -/
theorem gm_L4_7_pair [IsProbabilityMeasure μ] {F G : MeasurableSpace Ω} (hF : F ≤ mΩ)
    (hG : G ≤ mΩ) {Er Ef Stab Hit Hit2 G₀ : Set Ω} (hEr : MeasurableSet[mΩ] Er)
    (hEf : MeasurableSet[mΩ] Ef) (hStab : MeasurableSet[mΩ] Stab) (hHit : MeasurableSet[mΩ] Hit)
    (hHit2 : MeasurableSet[mΩ] Hit2) (hsub : Hit2 ⊆ Hit)
    (hG₀F : MeasurableSet[F] G₀) (hG₀G : MeasurableSet[G] G₀)
    (hStabG : @Blueprint.AEEventIn Ω mΩ μ G Stab)
    (hL46 : ∀ F', MeasurableSet[F] F' →
      ∃ t, MeasurableSet[G ⊔ generateFrom {Stab ∩ Hit}] t ∧ F' ∩ (Stab ∩ Hit) =ᵐ[μ] t)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (h42 : ∀ᵐ x ∂μ, x ∈ G₀ → (μ⟦Er ∩ Hit2 | G⟧) x ≤ Λ * (μ⟦Ef ∩ Hit2 | G⟧) x) :
    ∀ᵐ x ∂μ, (μ⟦Er ∩ Stab ∩ Hit2 | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((μ⟦Ef ∩ Stab ∩ Hit2 | F⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x) := by
  obtain ⟨S', hS', hSS⟩ := hStabG
  have eset : ∀ H : Set Ω, (H ∩ Hit2) ∩ (Stab ∩ Hit) = (H ∩ Hit2) ∩ Stab := by
    intro H
    ext x
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3, hsub h2⟩
  have eset' : ∀ H : Set Ω, (H ∩ Hit2) ∩ (Stab ∩ Hit) = H ∩ Stab ∩ Hit2 := by
    intro H
    rw [eset]
    ext x
    simp only [mem_inter_iff]
    tauto
  have hpre : ∀ᵐ x ∂μ, (μ⟦(Er ∩ Hit2) ∩ (Stab ∩ Hit) | G⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((μ⟦(Ef ∩ Hit2) ∩ (Stab ∩ Hit) | G⟧) x * G₀.indicator (fun _ => (1 : ℝ)) x) := by
    rw [eset, eset]
    filter_upwards [gm_condExp_inter_of_aeEvent (hEr.inter hHit2) hS' hSS,
      gm_condExp_inter_of_aeEvent (hEf.inter hHit2) hS' hSS, h42] with x h1 h2 h3
    rw [h1, h2]
    by_cases hx : x ∈ G₀
    · have := h3 hx
      by_cases hxS : x ∈ S' <;> simp [hx, hxS, this]
    · simp [hx]
  have := condExp_inter_le_of_sup_singleton hF hG (hStab.inter hHit) hL46 hG₀F hG₀G
    (hEr.inter hHit2) (hEf.inter hHit2) hΛ hpre
  simpa only [eset'] using this

/-- **GM (4.15)–(4.17)** (proof of GM Lemma 4.7, l. 1914–1938) for a finite index set `S` of
candidate pairs: `A i = {i ∈ 𝒵^E_k}`, `B i = {i ∈ 𝒵^𝔈_k}`, `Z i = {i ∈ 𝒵_k} ∈ 𝓕_k`,
`W = {𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})} ∈ 𝓕_k`, (4.13) on `Z i ∩ W` for each `i`, and `N ≥ #𝒵^𝔈_k`. -/
theorem gm_L4_7_quant [IsProbabilityMeasure μ] {F : MeasurableSpace Ω}
    {ι : Type*} (S : Finset ι) (A B Z : ι → Set Ω) (W : Set Ω)
    (hA : ∀ i, MeasurableSet[mΩ] (A i)) (hB : ∀ i, MeasurableSet[mΩ] (B i))
    (hZ : ∀ i, MeasurableSet[F] (Z i)) (hAZ : ∀ i, A i ⊆ Z i) {Λ : ℝ} (hΛ : 0 < Λ)
    (hpair : ∀ i ∈ S, ∀ᵐ x ∂μ,
      (μ⟦A i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x ≤
        Λ * ((μ⟦B i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x))
    {K : ℝ} (hK : 0 ≤ K) {N : Ω → ℝ} (hNm : Measurable[mΩ] N) (hNi : Integrable N μ)
    (hN : ∀ x, ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x ≤ N x) :
    ∀ᵐ x ∂μ, x ∈ W → Λ⁻¹ * (μ⟦⋃ i ∈ S, A i | F⟧) x ≤
      K * (μ⟦⋃ i ∈ S, B i | F⟧) x + (μ[{y | K < N y}.indicator N | F]) x := by
  classical
  have hAU : MeasurableSet[mΩ] (⋃ i ∈ S, A i) :=
    Finset.measurableSet_biUnion S (fun i _ => hA i)
  have hBU : MeasurableSet[mΩ] (⋃ i ∈ S, B i) :=
    Finset.measurableSet_biUnion S (fun i _ => hB i)
  have hNK : MeasurableSet[mΩ] {y | K < N y} := measurableSet_lt measurable_const hNm
  have hint : ∀ (T : Finset ι) (C : ι → Set Ω), (∀ i, MeasurableSet[mΩ] (C i)) →
      Integrable (∑ i ∈ T, (C i).indicator fun _ => (1 : ℝ)) μ :=
    fun T C hC => integrable_finsetSum' T (fun i _ => integrable_indOne (hC i))
  -- (a) union bound: `P[⋃ A | F] ≤ Σ P[A i | F]`
  have hUA : μ⟦⋃ i ∈ S, A i | F⟧ ≤ᵐ[μ] ∑ i ∈ S, μ⟦A i | F⟧ := by
    refine (condExp_mono (integrable_indOne hAU) (hint S A hA)
      (Eventually.of_forall (fun x => ?_))).trans_eq
      (condExp_finsetSum (fun i _ => integrable_indOne (hA i)) F)
    simp only [Finset.sum_apply]
    by_cases hx : x ∈ ⋃ i ∈ S, A i
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      rw [indicator_of_mem hx]
      calc (1 : ℝ) = (A i).indicator (fun _ => (1 : ℝ)) x := by rw [indicator_of_mem hxi]
        _ ≤ ∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x :=
          Finset.single_le_sum (f := fun j => (A j).indicator (fun _ => (1 : ℝ)) x)
            (fun j _ => indicator_nonneg (fun _ _ => zero_le_one) x) hi
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => zero_le_one) x)
  -- (b) `P[A i | F] = 1_{Z i} P[A i | F]`
  have hAZc : ∀ i, μ⟦A i | F⟧ =ᵐ[μ]
      fun x => (Z i).indicator (fun _ => (1 : ℝ)) x * (μ⟦A i | F⟧) x := by
    intro i
    have := gm_condExp_inter_of_aeEvent (μ := μ) (hA i) (hZ i) (EventuallyEq.refl _ (Z i))
    rwa [inter_eq_left.mpr (hAZ i)] at this
  -- (c) the Paley–Zygmund split: `Σ 1_{B i} ≤ K 1_{⋃ B} + N 1_{N > K}`
  have hsplit : ∀ x, ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x ≤
      K * (⋃ i ∈ S, B i).indicator (fun _ => (1 : ℝ)) x + {y | K < N y}.indicator N x := by
    intro x
    have hnn : 0 ≤ ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x :=
      Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => zero_le_one) x)
    have hind : 0 ≤ {y | K < N y}.indicator N x := by
      by_cases hx : x ∈ {y | K < N y}
      · rw [indicator_of_mem hx]; exact hK.trans hx.le
      · rw [indicator_of_notMem hx]
    by_cases hKx : ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x ≤ K
    · by_cases hx : x ∈ ⋃ i ∈ S, B i
      · rw [indicator_of_mem hx, mul_one]; linarith
      · have h0 : ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ)) x = 0 := by
          refine Finset.sum_eq_zero (fun i hi => indicator_of_notMem (fun hxi => hx ?_) _)
          exact mem_iUnion₂.mpr ⟨i, hi, hxi⟩
        rw [h0]
        exact add_nonneg (mul_nonneg hK (indicator_nonneg (fun _ _ => zero_le_one) x)) hind
    · have hlt := not_le.mp hKx
      have hmem : x ∈ {y | K < N y} := hlt.trans_le (hN x)
      rw [indicator_of_mem hmem]
      have := hN x
      have h2 : 0 ≤ K * (⋃ i ∈ S, B i).indicator (fun _ => (1 : ℝ)) x :=
        mul_nonneg hK (indicator_nonneg (fun _ _ => zero_le_one) x)
      linarith
  have hUB : ∑ i ∈ S, μ⟦B i | F⟧ ≤ᵐ[μ]
      fun x => K * (μ⟦⋃ i ∈ S, B i | F⟧) x + (μ[{y | K < N y}.indicator N | F]) x := by
    refine (condExp_finsetSum (fun i _ => integrable_indOne (hB i)) F).symm.le.trans ?_
    refine (condExp_mono (hint S B hB)
      (((integrable_indOne hBU).const_mul K).add (hNi.indicator hNK))
      (Eventually.of_forall (fun x => ?_))).trans ?_
    · simpa only [Finset.sum_apply, Pi.add_apply] using hsplit x
    · refine (condExp_add ((integrable_indOne hBU).const_mul K) (hNi.indicator hNK) F).le.trans ?_
      have hsm := condExp_smul (μ := μ) K ((⋃ i ∈ S, B i).indicator fun _ => (1 : ℝ)) F
      filter_upwards [hsm] with x hx
      simp only [Pi.add_apply]
      have e : (fun y => K * (⋃ i ∈ S, B i).indicator (fun _ => (1 : ℝ)) y) =
          K • (⋃ i ∈ S, B i).indicator fun _ => (1 : ℝ) := rfl
      rw [e, hx]
      rfl
  -- combine
  have hpairS : ∀ᵐ x ∂μ, ∀ i ∈ S,
      (μ⟦A i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x ≤
        Λ * ((μ⟦B i | F⟧) x * (Z i ∩ W).indicator (fun _ => (1 : ℝ)) x) :=
    (ae_ball_iff S.countable_toSet).mpr hpair
  have hAZS : ∀ᵐ x ∂μ, ∀ i ∈ S,
      (μ⟦A i | F⟧) x = (Z i).indicator (fun _ => (1 : ℝ)) x * (μ⟦A i | F⟧) x :=
    (ae_ball_iff S.countable_toSet).mpr (fun i _ => hAZc i)
  have hBn : ∀ᵐ x ∂μ, ∀ i ∈ S, 0 ≤ (μ⟦B i | F⟧) x :=
    (ae_ball_iff S.countable_toSet).mpr (fun i _ =>
      condExp_nonneg (Eventually.of_forall (fun x => indicator_nonneg (fun _ _ => zero_le_one) x)))
  filter_upwards [hUA, hUB, hpairS, hAZS, hBn] with x h1 h2 h3 h4 h5 hxW
  have hterm : ∀ i ∈ S, (μ⟦A i | F⟧) x ≤ Λ * (μ⟦B i | F⟧) x := by
    intro i hi
    by_cases hxZ : x ∈ Z i
    · have := h3 i hi
      rwa [indicator_of_mem (show x ∈ Z i ∩ W from ⟨hxZ, hxW⟩), mul_one, mul_one] at this
    · rw [h4 i hi, indicator_of_notMem hxZ, zero_mul]
      exact mul_nonneg hΛ.le (h5 i hi)
  simp only [Finset.sum_apply] at h1 h2
  have hsum : ∑ i ∈ S, (μ⟦A i | F⟧) x ≤ Λ * ∑ i ∈ S, (μ⟦B i | F⟧) x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hΛi : 0 < Λ⁻¹ := inv_pos.mpr hΛ
  calc Λ⁻¹ * (μ⟦⋃ i ∈ S, A i | F⟧) x ≤ Λ⁻¹ * (Λ * ∑ i ∈ S, (μ⟦B i | F⟧) x) :=
        mul_le_mul_of_nonneg_left (h1.trans hsum) hΛi.le
    _ = ∑ i ∈ S, (μ⟦B i | F⟧) x := by field_simp
    _ ≤ _ := h2

end LQGMetric.GM
