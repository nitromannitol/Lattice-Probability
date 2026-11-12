/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcA
import LatticeProb.Bonanno.LQGMetric.Prob.Median

/-!
# Concentration from a Lipschitz property on a good set (P2-DZZCONC)

The abstract core of the proof of DZZ Proposition 3.17 (arXiv:1807.00422, `LBM_LGDarXiv.tex`,
l. 1595–1613 for (eq-concentration-approximate), repeated at l. 1640–1651 for
(eq-concentration-approximate-2)), done once for both inequalities. Data: a random variable `Y`
(DZZ: `log D'_{γ,δ}(u,v)`), a centered Gaussian process `X` (DZZ: the coarse field `𝒳_δ`) with
`Var ≤ σ²`, a good set `𝒜` of paths (DZZ: `𝒜`) with `P(X ∉ 𝒜) ≤ ε` on which `Y = F(X)` and `F` is
`(ℓ, τ)`-Lipschitz for the sup norm (DZZ (eq-distance-Lip): `‖x − x'‖_∞ ≤ ℓ_δ ⇒ |F x − F x'| ≤
ι log δ⁻¹`), plus a finite net (`gauss_far_le`).

* `dev_median_le`: DZZ (eq-upper-tail-deviation), (eq-lower-tail-deviation) around a median `m`
  (DZZ's `d'_{u,v}` with `P(𝒜') ≥ 1/2`; we use a median of `Y` and `P(𝒜') ≥ 1/4`):
  `P(|Y − m| > τ) ≤ 2ε + 2 exp(−(ℓ − η − Cσ)²/(2σ²))`.
* `abs_integral_sub_median_le`: DZZ l. 1609–1611 ("uniform square integrability … we conclude
  `|E log D' − log d'| ≤ 2ι log δ⁻¹`"): `|E Y − m| ≤ τ + 3V/M + 2Mp` for `E Y² ≤ V`
  (own elementary proof: `|y| ≤ y²/M + M` on the bad event and Markov for the median).
* **`conc_of_lip`**: `P(|Y − E Y| > 2τ + 3V/M + 2Mp) ≤ p`, `p = 2ε + 2 exp(…)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

universe u v

/-- **DZZ (eq-upper-tail-deviation), (eq-lower-tail-deviation)** around a median. -/
theorem dev_median_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {T : Type v} (X : T → Ω → ℝ), IsGaussianProcess X P →
    (∀ t, ∫ ω, X t ω ∂P = 0) → ∀ σ : ℝ, 0 ≤ σ → (∀ t, Var[X t; P] ≤ σ ^ 2) →
    ∀ (Y : Ω → ℝ) (m : ℝ), 2⁻¹ ≤ P.real {ω | Y ω ≤ m} → 2⁻¹ ≤ P.real {ω | m ≤ Y ω} →
    ∀ (𝒜 : Set (T → ℝ)) (F : (T → ℝ) → ℝ),
    (∀ᵐ ω ∂P, (fun s => X s ω) ∈ 𝒜 → Y ω = F (fun s => X s ω)) →
    ∀ ε : ℝ, P.real {ω | (fun s => X s ω) ∉ 𝒜} ≤ ε →
    ∀ ℓ τ : ℝ, (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) → |F x - F x'| ≤ τ) →
    ∀ (η : ℝ) (n : ℕ) (t : Fin n → T),
    (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + η) →
    ε ≤ 4⁻¹ → C * σ + η ≤ ℓ →
    P.real {ω | τ < |Y ω - m|} ≤ 2 * ε + 2 * exp (-(ℓ - η - C * σ) ^ 2 / (2 * σ ^ 2)) := by
  obtain ⟨C, hC1, hC⟩ := gauss_far_le.{u, v} (4⁻¹ : ℝ) (by norm_num)
  refine ⟨C, hC1, ?_⟩
  intro Ω _ P _ T X hX h0 σ hσ hvar Y m hm1 hm2 𝒜 F hYF ε hε ℓ τ hlip η n t hnet hε4 hℓ
  set G : Ω → T → ℝ := fun ω s => X s ω
  set Nb : Set Ω := {ω | ¬(G ω ∈ 𝒜 → Y ω = F (G ω))}
  have hNb : P.real Nb = 0 := by
    rw [measureReal_def, ae_iff.1 hYF]; rfl
  -- one side, for `(Y, F, m)` arbitrary with the same Lipschitz property
  have side : ∀ (Y' : Ω → ℝ) (F' : (T → ℝ) → ℝ) (m' : ℝ), 2⁻¹ ≤ P.real {ω | Y' ω ≤ m'} →
      (∀ ω, ω ∉ Nb → G ω ∈ 𝒜 → Y' ω = F' (G ω)) →
      (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) → |F' x - F' x'| ≤ τ) →
      P.real {ω | m' + τ < Y' ω} ≤ ε + exp (-(ℓ - η - C * σ) ^ 2 / (2 * σ ^ 2)) := by
    intro Y' F' m' hm' hYF' hlip'
    set 𝒜₁ : Set (T → ℝ) := {x | x ∈ 𝒜 ∧ F' x ≤ m'}
    have hA1 : 4⁻¹ ≤ P.real {ω | G ω ∈ 𝒜₁} := by
      have hsub : {ω | Y' ω ≤ m'} ⊆ ({ω | G ω ∉ 𝒜} ∪ Nb) ∪ {ω | G ω ∈ 𝒜₁} := by
        intro ω hω
        by_cases hA : G ω ∈ 𝒜
        · by_cases hN : ω ∈ Nb
          · exact Or.inl (Or.inr hN)
          · refine Or.inr ⟨hA, ?_⟩
            rw [← hYF' ω hN hA]; exact hω
        · exact Or.inl (Or.inl hA)
      have h1 := measureReal_mono (μ := P) hsub (measure_ne_top P _)
      have h2 := measureReal_union_le (μ := P) ({ω | G ω ∉ 𝒜} ∪ Nb) {ω | G ω ∈ 𝒜₁}
      have h3 := measureReal_union_le (μ := P) {ω | G ω ∉ 𝒜} Nb
      rw [hNb] at h3
      have : P.real {ω | G ω ∉ 𝒜} ≤ ε := hε
      linarith
    have hfar := hC P X hX h0 σ hσ hvar 𝒜 𝒜₁ η n t
      (fun x hx x' hx' s => hnet x hx x' hx'.1 s) hA1 ℓ hℓ
    have hsub : {ω | m' + τ < Y' ω} ⊆ ({ω | G ω ∉ 𝒜} ∪ Nb) ∪
        {ω | G ω ∈ 𝒜 ∧ ∀ x' ∈ 𝒜₁, ∃ s, ℓ < |X s ω - x' s|} := by
      intro ω hω
      by_cases hA : G ω ∈ 𝒜
      · by_cases hN : ω ∈ Nb
        · exact Or.inl (Or.inr hN)
        · refine Or.inr ⟨hA, fun x' hx' => ?_⟩
          by_contra hcon
          push Not at hcon
          have h1 := hlip' _ hA x' hx'.1 hcon
          have h2 := hYF' ω hN hA
          simp only [mem_setOf_eq] at hω
          rw [h2] at hω
          have h3 := hx'.2
          have := le_abs_self (F' (G ω) - F' x')
          linarith
      · exact Or.inl (Or.inl hA)
    have h1 := measureReal_mono (μ := P) hsub (measure_ne_top P _)
    have h2 := measureReal_union_le (μ := P) ({ω | G ω ∉ 𝒜} ∪ Nb)
      {ω | G ω ∈ 𝒜 ∧ ∀ x' ∈ 𝒜₁, ∃ s, ℓ < |X s ω - x' s|}
    have h3 := measureReal_union_le (μ := P) {ω | G ω ∉ 𝒜} Nb
    rw [hNb] at h3
    have : P.real {ω | G ω ∉ 𝒜} ≤ ε := hε
    linarith
  have hup := side Y F m hm1 (fun ω hN hA => by
    simp only [Nb, mem_setOf_eq, not_not] at hN; exact hN hA) hlip
  have hlow := side (fun ω => -Y ω) (fun x => -F x) (-m) (by
      refine hm2.trans_eq ?_; congr 1; ext ω; simp)
    (fun ω hN hA => by
      have : Y ω = F (G ω) := by
        simp only [Nb, mem_setOf_eq, not_not] at hN; exact hN hA
      simp [this])
    (fun x hx x' hx' hxx => by
      have := hlip x hx x' hx' hxx
      rw [show -F x - -F x' = -(F x - F x') by ring, abs_neg]; exact this)
  have hsub : {ω | τ < |Y ω - m|} ⊆ {ω | m + τ < Y ω} ∪ {ω | -m + τ < -Y ω} := by
    intro ω hω
    simp only [mem_setOf_eq, mem_union] at hω ⊢
    rcases lt_abs.1 hω with h | h
    · left; linarith
    · right; linarith
  have h1 := measureReal_mono (μ := P) hsub (measure_ne_top P _)
  have h2 := measureReal_union_le (μ := P) {ω | m + τ < Y ω} {ω | -m + τ < -Y ω}
  linarith

/-- `|y| ≤ y²/M + M` -/
lemma abs_le_sq_div_add {y M : ℝ} (hM : 0 < M) : |y| ≤ y ^ 2 / M + M := by
  rw [div_add' _ _ _ hM.ne', le_div_iff₀ hM]
  nlinarith [sq_nonneg (|y| - M), sq_abs y, abs_nonneg y]

/-- **Mean versus median** (DZZ l. 1609–1611), own elementary proof. -/
theorem abs_integral_sub_median_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P) {V : ℝ}
    (hV : ∫ ω, Y ω ^ 2 ∂P ≤ V) {m : ℝ} (hm1 : 2⁻¹ ≤ P.real {ω | Y ω ≤ m})
    (hm2 : 2⁻¹ ≤ P.real {ω | m ≤ Y ω}) {τ p M : ℝ} (hM : 0 < M) (hτ : 0 ≤ τ)
    (hp : P.real {ω | τ < |Y ω - m|} ≤ p) :
    |(∫ ω, Y ω ∂P) - m| ≤ τ + 3 * V / M + 2 * M * p := by
  have hYi : Integrable Y P := hY.integrable one_le_two
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := hY.integrable_sq
  -- `m² ≤ 2V`
  have hm : m ^ 2 ≤ 2 * V := by
    have hS : 2⁻¹ ≤ P.real {ω | m ^ 2 ≤ Y ω ^ 2} := by
      rcases le_total 0 m with h | h
      · refine hm2.trans (measureReal_mono fun ω hω => ?_)
        simp only [mem_setOf_eq] at hω ⊢; nlinarith
      · refine hm1.trans (measureReal_mono fun ω hω => ?_)
        simp only [mem_setOf_eq] at hω ⊢; nlinarith
    have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg (Y ω))
      hY2 (m ^ 2)
    nlinarith [sq_nonneg m]
  set B : Set Ω := {ω | τ < |Y ω - m|}
  set B' := toMeasurable P B
  have hB' : P.real B' = P.real B := by rw [measureReal_def, measure_toMeasurable]; rfl
  have hpt : ∀ ω, |Y ω - m| ≤ τ + Y ω ^ 2 / M + m ^ 2 / M + 2 * M * B'.indicator 1 ω := by
    intro ω
    have h0 : 0 ≤ Y ω ^ 2 / M := by positivity
    have h0' : 0 ≤ m ^ 2 / M := by positivity
    by_cases hω : ω ∈ B'
    · rw [indicator_of_mem hω]
      have := abs_le_sq_div_add (y := Y ω) hM
      have := abs_le_sq_div_add (y := m) hM
      have := abs_sub (Y ω) m
      simp only [Pi.one_apply]
      linarith
    · rw [indicator_of_notMem hω]
      have : ω ∉ B := fun h => hω (subset_toMeasurable P B h)
      simp only [B, mem_setOf_eq, not_lt] at this
      linarith
  have hint : Integrable (fun ω => τ + Y ω ^ 2 / M + m ^ 2 / M + 2 * M * B'.indicator 1 ω) P :=
    (((integrable_const τ).add (hY2.div_const M)).add (integrable_const _)).add
      (((integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable P B)).const_mul _)
  have hI : ∫ ω, (τ + Y ω ^ 2 / M + m ^ 2 / M + 2 * M * B'.indicator 1 ω) ∂P =
      τ + (∫ ω, Y ω ^ 2 ∂P) / M + m ^ 2 / M + 2 * M * P.real B' := by
    have i1 : Integrable (fun ω => τ + Y ω ^ 2 / M) P := (integrable_const τ).add (hY2.div_const M)
    have i2 : Integrable (fun ω => τ + Y ω ^ 2 / M + m ^ 2 / M) P := i1.add (integrable_const _)
    have i3 : Integrable (fun ω => 2 * M * B'.indicator 1 ω) P :=
      ((integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable P B)).const_mul _
    rw [integral_add (f := fun ω => τ + Y ω ^ 2 / M + m ^ 2 / M) i2 i3,
      integral_add (f := fun ω => τ + Y ω ^ 2 / M) i1 (integrable_const _),
      integral_add (f := fun _ => τ) (integrable_const τ) (hY2.div_const M), integral_const_mul,
      integral_indicator_one (measurableSet_toMeasurable P B), integral_div]
    simp [B']
  have e1 : (∫ ω, Y ω ∂P) - m = ∫ ω, (Y ω - m) ∂P := by
    rw [integral_sub hYi (integrable_const m)]; simp
  rw [e1]
  refine (abs_integral_le_integral_abs).trans ((integral_mono
    ((hYi.sub (integrable_const m)).abs) hint hpt).trans ?_)
  rw [hI, hB']
  have h3 : (∫ ω, Y ω ^ 2 ∂P) / M ≤ V / M := div_le_div_of_nonneg_right hV hM.le
  have h4 : m ^ 2 / M ≤ 2 * V / M := div_le_div_of_nonneg_right hm hM.le
  have h5 : 2 * M * P.real B ≤ 2 * M * p := mul_le_mul_of_nonneg_left hp (by positivity)
  have e : 3 * V / M = V / M + 2 * V / M := by ring
  linarith

end DZZ
end LQGMetric
