/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L212 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.12: iterating events in outward annuli

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), Lemma 2.12 (`lem-annulus-iterate-inverse`, confluence-final.tex 785–799):
for `1 < S₁ < S₂`, an increasing sequence `r_k` with `r_{k+1}/r_k ≥ S₂` and events
`E_{r_k} ∈ σ((h − h_{r_k}(0))|_{𝔸_{S₁r_k,S₂r_k}(0)})`, the number `N(K)` of `k ∈ [1,K]` with
`E_{r_k}` satisfies the conclusions of LM Lemma 3.1.

CONF proves it "by the exact same argument" as Lemma 2.11 or from Lemma 2.11 and the inversion
invariance Lemma 2.13 (C:801–802). Following decision D47 (decisions/DEC-D.md (d), deviation
DV-CONF-212) we use a third route: the lemma is stated for events determined modulo additive
constants (the only use, CONF L3.4, C:1154, 1270, has such events), and for each fixed `K` the
first `K` radii are reversed, `r′_j = S₁S₂·r_{K+1−j}`, continued geometrically with ratio
`1/S₂` and trivial events for `j > K`, and LM Lemma 3.1 (`Blueprint.LMLem3_1a/b`) is applied
with `s₁ = 1/S₂`, `s₂ = 1/S₁`; then `𝔸_{s₁r′_j, s₂r′_j} = 𝔸_{S₁r_{K+1−j}, S₂r_{K+1−j}}` and
the counts agree. LM's constants depend only on `(a, b, s₁, s₂)`, hence are uniform in `K`.
-/

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric.CONF

open Blueprint

/-- **CONF Lemma 2.12 (1)** (C:785–795), for events determined modulo additive constants
(D47 / DV-CONF-212). -/
def CONFLem2_12a : Prop :=
  ∀ S₁ S₂ : ℝ, 1 < S₁ → S₁ < S₂ → ∀ a : ℝ, 0 < a → ∀ b : ℝ, 0 < b → b < 1 →
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWPGFF h P → ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
        (∀ k, 0 < r k) → (∀ k, S₂ ≤ r (k + 1) / r k) →
        (∀ k, ∀ ρ : ℝ, 0 < ρ → MeasurableSet[fieldSigma
          (fun ω => addConst (h ω) (-circleAvg (h ω) ρ 0)) (annulus 0 (S₁ * r k) (S₂ * r k))] (E k)) →
        (∀ k, ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K))

/-- the reversed radii `r′_j = S₁S₂·r_{K+1−j}·(1/S₂)^{j−K}` (natural subtraction): equal to
`S₁S₂ r_{K+1−j}` for `j ≤ K`, geometric with ratio `1/S₂` beyond (D47). -/
noncomputable def confRevR (S₁ S₂ : ℝ) (r : ℕ → ℝ) (K j : ℕ) : ℝ :=
  S₁ * S₂ * r (K + 1 - j) * (1 / S₂) ^ (j - K)

/-- the reversed events: `E′_j = E_{K+1−j}` for `j ≤ K`, `univ` beyond (D47). -/
def confRevE {Ω : Type} (E : ℕ → Set Ω) (K j : ℕ) : Set Ω :=
  if j ≤ K then E (K + 1 - j) else univ

lemma confRevR_pos {S₁ S₂ : ℝ} (h1 : 1 < S₁) (h12 : S₁ < S₂) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (K j : ℕ) : 0 < confRevR S₁ S₂ r K j := by
  unfold confRevR
  have h2 : 0 < S₂ := by linarith
  have h1' : 0 < S₁ := by linarith
  exact mul_pos (mul_pos (mul_pos h1' h2) (hr _)) (pow_pos (one_div_pos.mpr h2) _)

lemma confRevR_succ_le {S₁ S₂ : ℝ} (h1 : 1 < S₁) (h12 : S₁ < S₂) {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hS : ∀ k, S₂ ≤ r (k + 1) / r k) (K j : ℕ) :
    confRevR S₁ S₂ r K (j + 1) ≤ 1 / S₂ * confRevR S₁ S₂ r K j := by
  have hS₂ : 0 < S₂ := by linarith
  have hS₁ : 0 < S₁ := by linarith
  have hstep : ∀ m, r m ≤ 1 / S₂ * r (m + 1) := by
    intro m
    have h := hS m
    rw [le_div_iff₀ (hr m)] at h
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hS₂]
    linarith
  unfold confRevR
  rcases lt_or_ge j K with hj | hj
  · obtain ⟨m, rfl⟩ : ∃ m, K = j + 1 + m := ⟨K - (j + 1), by omega⟩
    have e1 : j + 1 + m + 1 - (j + 1) = m + 1 := by omega
    have e2 : j + 1 + m + 1 - j = m + 1 + 1 := by omega
    have e3 : j + 1 - (j + 1 + m) = 0 := by omega
    have e4 : j - (j + 1 + m) = 0 := by omega
    rw [e1, e2, e3, e4, pow_zero, mul_one, mul_one]
    have := hstep (m + 1)
    have hp : 0 < S₁ * S₂ := by positivity
    nlinarith
  · have e1 : K + 1 - (j + 1) = 0 := by omega
    have e3 : j + 1 - K = (j - K) + 1 := by omega
    rw [e1, e3, pow_succ]
    have hq : 0 < (1 / S₂) ^ (j - K) := by positivity
    have hp : 0 < S₁ * S₂ := by positivity
    have hr0 : r 0 ≤ r (K + 1 - j) := by
      rcases eq_or_lt_of_le hj with h | h
      · subst h
        have e : K + 1 - K = 0 + 1 := by omega
        rw [e]
        have h0 := hstep 0
        have : 1 / S₂ < 1 := by rw [div_lt_one hS₂]; linarith
        nlinarith [hr 1]
      · have e : K + 1 - j = 0 := by omega
        rw [e]
    have : 0 < 1 / S₂ := by positivity
    have key : S₁ * S₂ * r 0 * (1 / S₂) ^ (j - K) ≤
        S₁ * S₂ * r (K + 1 - j) * (1 / S₂) ^ (j - K) := by
      apply mul_le_mul_of_nonneg_right _ hq.le
      exact mul_le_mul_of_nonneg_left hr0 hp.le
    nlinarith

lemma confRev_count {Ω : Type} (E : ℕ → Set Ω) (K : ℕ) (ω : Ω) :
    countOcc (confRevE E K) K ω = countOcc E K ω := by
  classical
  unfold countOcc
  refine Finset.card_nbij' (fun j => K + 1 - j) (fun j => K + 1 - j) ?_ ?_ ?_ ?_
  · intro j hj
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hj
    unfold confRevE at h3
    simp only [h2, ↓reduceIte] at h3
    exact ⟨⟨by omega, by omega⟩, h3⟩
  · intro k hk
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    unfold confRevE
    have hk' : K + 1 - k ≤ K := by omega
    rw [show K + 1 - (K + 1 - k) = k by omega]
    simp only [hk', ↓reduceIte]
    exact h3
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj
    show K + 1 - (K + 1 - j) = j
    omega
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk
    show K + 1 - (K + 1 - k) = k
    omega

/-- the reversed data satisfy the hypotheses of LM Lemma 3.1 with `s₁ = 1/S₂`, `s₂ = 1/S₁`. -/
lemma confRev_annulusIterHyp {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC) {S₁ S₂ : ℝ}
    (h1 : 1 < S₁) (h12 : S₁ < S₂) {r : ℕ → ℝ} {E : ℕ → Set Ω}
    (hr : ∀ k, 0 < r k) (hS : ∀ k, S₂ ≤ r (k + 1) / r k)
    (hE : ∀ k, ∀ ρ : ℝ, 0 < ρ → MeasurableSet[fieldSigma
          (fun ω => addConst (h ω) (-circleAvg (h ω) ρ 0)) (annulus 0 (S₁ * r k) (S₂ * r k))] (E k))
    (K : ℕ) :
    AnnulusIterHyp h (1 / S₂) (1 / S₁) (confRevR S₁ S₂ r K) (confRevE E K) := by
  have hS₂ : 0 < S₂ := by linarith
  have hS₁ : 0 < S₁ := by linarith
  have hpos := confRevR_pos h1 h12 hr K
  have hsucc := confRevR_succ_le h1 h12 hr hS K
  refine ⟨hpos, ?_, ?_, ?_⟩
  · refine antitone_nat_of_succ_le fun j => ?_
    have := hsucc j
    have h' : 1 / S₂ < 1 := by rw [div_lt_one hS₂]; linarith
    nlinarith [hpos j]
  · intro j
    rw [div_le_iff₀ (hpos j)]
    exact hsucc j
  · intro j
    unfold confRevE
    split_ifs with hj
    · have e : annulus 0 (1 / S₂ * confRevR S₁ S₂ r K j) (1 / S₁ * confRevR S₁ S₂ r K j) =
          annulus 0 (S₁ * r (K + 1 - j)) (S₂ * r (K + 1 - j)) := by
        unfold confRevR
        rw [show j - K = 0 by omega, pow_zero, mul_one]
        congr 1 <;> field_simp
      rw [e]
      exact hE _ _ (hpos j)
    · exact MeasurableSet.univ

lemma confRev_prob {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp1 : p < 1) {E : ℕ → Set Ω} (hE : ∀ k, ENNReal.ofReal p ≤ P (E k)) (K j : ℕ) :
    ENNReal.ofReal p ≤ P (confRevE E K j) := by
  unfold confRevE
  split_ifs
  · exact hE _
  · rw [measure_univ]
    exact ENNReal.ofReal_le_one.mpr hp1.le

/-- **CONF Lemma 2.12 (1)** from LM Lemma 3.1 (1) (D47). -/
theorem confLem2_12a_of_LM (hLM : LMLem3_1a) : CONFLem2_12a := by
  intro S₁ S₂ h1 h12 a ha b hb0 hb1
  have hS₂ : 0 < S₂ := by linarith
  have hS₁ : 0 < S₁ := by linarith
  obtain ⟨p, c, hp0, hp1, hc, hLMc⟩ := hLM (1 / S₂) (1 / S₁) (by positivity)
    (one_div_lt_one_div_of_lt hS₁ h12) (by rw [div_lt_one hS₁]; exact h1) a ha b hb0 hb1
  refine ⟨p, c, hp0, hp1, hc, ?_⟩
  intro Ω _ P _ h hh r E hr hS hE hpE K
  have := hLMc P h hh (confRevR S₁ S₂ r K) (confRevE E K)
    (confRev_annulusIterHyp h h1 h12 hr hS hE K) (confRev_prob P hp1 hpE K) K
  simpa only [confRev_count] using this

end LQGMetric.CONF
