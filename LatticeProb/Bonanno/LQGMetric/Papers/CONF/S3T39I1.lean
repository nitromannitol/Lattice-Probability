/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39I1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9 for a fixed initial arc family, with almost sure iteration inputs (D119 S5)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1514–1738. Copy-and-adapt of `t39g_arcs` (S3T39G5) in which the recursion
`s_{k+1} = σ^{ε_k}_{s_k,𝕣}` (C:1530–1545), the count (3.21′) and the kill step (C:1600–1617)
are only required **almost surely** (D119 S5: `σ^ε_{s,𝕣} = ∞` on a null set, where no real
`s_{k+1}` exists). The proof is that of `t39g_arcs`, run on the conull set `Ω₀` on which all
these a.s. inputs hold (countably many `k`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Classical in
/-- **CONF Theorem 3.9 for a fixed `𝓘_0`** (C:1514–1516, proof C:1520–1738); see the module
docstring for the hypotheses -/
theorem t39i_arcs {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {χ α C₀ a : ℝ} (hχ : 0 < χ) (hα : 0 < α) (hC₀ : 0 ≤ C₀) (ha : 0 < a) (ha1 : a ≤ 1)
    (N₀ : ℕ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧
    ∀ {Ω : Type} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC) (z₀ : ℂ) (R : ℝ), 0 < R → ∀ {ι : Type} [Fintype ι]
      (I₀ : ι → Ω → Set ℂ) (τ : Ω → ℝ) (s : ℕ → Ω → ℝ) (n : ℕ → Ω → ℕ)
      (𝓕 : ℕ → MeasurableSpace Ω) (Act G : ℕ → ι → Set Ω),
      (∀ᵐ ω ∂P, 0 < τ ω ∧ Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω))) →
      (∀ i ω, I₀ i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω))) →
      (∀ᵐ ω ∂P, τ ω ≤ tauR D h z₀ (2 * R) ω) →
      (∀ ω, 0 < scaleFac (xiGamma γ) c (h ω) R z₀) →
      (∀ ω, s 0 ω = τ ω) →
      (∀ k, ∀ᵐ ω ∂P, ENNReal.ofReal (s (k + 1) ω) = confSigma (xiGamma γ) c D P h p z₀ R
          ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) (s k ω) ω) →
      (∀ k ω, n k ω = (Finset.univ.filter fun i =>
          (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty).card) →
      Monotone 𝓕 → (∀ k, 𝓕 k ≤ m0) → (∀ k, Measurable[𝓕 k] (n k)) →
      (∀ k i, MeasurableSet[𝓕 k] (Act k i)) → (∀ k i, MeasurableSet[𝓕 (k + 1)] (G k i)) →
      (∀ k i, ∀ᵐ ω ∂P, ω ∈ Act k i → 1 - C₀ * ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) ^ α ≤
          P[(G k i).indicator (fun _ => (1 : ℝ)) | 𝓕 k] ω) →
      (∀ k i ω, ω ∈ Act k i → (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty) →
      (∀ᵐ ω ∂P, ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k, s k ω < tauR D h z₀ (3 * R) ω →
        N₀ ≤ n k ω → 4 * (Finset.univ.filter fun i =>
          (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧ ω ∉ Act k i).card ≤ n k ω) →
      (∀ᵐ ω ∂P, ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k, s k ω < tauR D h z₀ (3 * R) ω →
        N₀ ≤ n k ω → ∀ i, ω ∈ Act k i → ω ∈ G k i →
          t39gArc (D (h ω)) z₀ (s (k + 1) ω) (I₀ i ω) = ∅) →
      ∀ N : ℕ, 1 ≤ N →
        P {ω | ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a ∧
          N ≤ (Finset.univ.filter fun i => (I₀ i ω ∩ hitSetLM (D (h ω)) z₀ (τ ω)
            (τ ω + (N : ℝ) ^ (-(χ / 8 / 4)) * scaleFac (xiGamma γ) c (h ω) R z₀)).Nonempty).card} ≤
          ENNReal.ofReal (b₀ * Real.exp (-(N : ℝ) ^ (χ / 8 / 4))) := by
  have hθ : 0 < χ / 8 := by positivity
  obtain ⟨N₀a, hN₀a⟩ := t39g_eventually_le (K := 14) (q := 1 / 8) (by norm_num) ha
  have h2θ : 0 < 1 - (2 : ℝ) ^ (-(χ / 8)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := 2) (by norm_num) (by linarith : -(χ / 8) < 0)
    linarith
  have hcθ : 0 ≤ (2 : ℝ) ^ (χ / 8 + 1) / (1 - (2 : ℝ) ^ (-(χ / 8))) := by positivity
  have hCc : 0 ≤ (14 : ℝ) ^ χ := by positivity
  set N₁ := max N₀ (max N₀a 1) with hN₁def
  obtain ⟨b₀', hb₀', hL⟩ := t39g_lem311_unif (C₁ := 4 * C₀ * 2 ^ α) (a := α / 4)
    (by positivity) (by positivity) hθ N₁
  obtain ⟨N₃, hN₃⟩ := t39g_eventually_le
    (K := (14 : ℝ) ^ χ * ((2 : ℝ) ^ (χ / 8 + 1) / (1 - (2 : ℝ) ^ (-(χ / 8)))))
    (q := χ / 8 / 4) (by positivity) one_pos
  obtain ⟨N₃', hN₃'⟩ := t39g_eventually_le
    (K := (14 : ℝ) ^ χ * ((2 : ℝ) ^ (χ / 8 + 1) / (1 - (2 : ℝ) ^ (-(χ / 8)))))
    (q := χ / 8 / 2) (by positivity) ha
  set N₄ := max (max N₃ N₃') N₁ with hN₄def
  refine ⟨max b₀' (Real.exp ((N₄ : ℝ) ^ (χ / 8 / 4))), lt_max_of_lt_left hb₀', ?_⟩
  intro Ω m0 P _ h z₀ R hR ι _ I₀ τ s n 𝓕 Act G hτb hI₀ hτ2 hS hs0 hsucc hn hmono h𝓕 hnm
    hActm hGm hcond hActAl hstar hkill N hN
  rcases lt_or_ge N N₄ with hlt | hge
  · -- small `N`: the bound is at least `1`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : (N : ℝ) ^ (χ / 8 / 4) ≤ (N₄ : ℝ) ^ (χ / 8 / 4) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt.le) (by positivity)
    calc (1 : ℝ) = Real.exp ((N₄ : ℝ) ^ (χ / 8 / 4)) * Real.exp (-(N₄ : ℝ) ^ (χ / 8 / 4)) := by
          rw [← Real.exp_add]; simp
      _ ≤ max b₀' (Real.exp ((N₄ : ℝ) ^ (χ / 8 / 4))) * Real.exp (-(N : ℝ) ^ (χ / 8 / 4)) := by
          gcongr
          · exact le_max_right _ _
  -- the iteration is monotone
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set Ω₀ : Set Ω := {ω | 0 < τ ω ∧ Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω)) ∧
    (∀ k, ENNReal.ofReal (s (k + 1) ω) = confSigma (xiGamma γ) c D P h p z₀ R
          ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) (s k ω) ω) ∧
    (ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k, s k ω < tauR D h z₀ (3 * R) ω →
        N₀ ≤ n k ω → 4 * (Finset.univ.filter fun i =>
          (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧ ω ∉ Act k i).card ≤ n k ω) ∧
    (ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k, s k ω < tauR D h z₀ (3 * R) ω →
        N₀ ≤ n k ω → ∀ i, ω ∈ Act k i → ω ∈ G k i →
          t39gArc (D (h ω)) z₀ (s (k + 1) ω) (I₀ i ω) = ∅)} with hΩ₀
  have hΩ₀ae : ∀ᵐ ω ∂P, ω ∈ Ω₀ := by
    filter_upwards [hτb, ae_all_iff.2 hsucc, hstar, hkill] with ω h1 h2 h3 h4
    exact ⟨h1.1, h1.2, h2, h3, h4⟩
  have hstepmono : ∀ k, ∀ ω ∈ Ω₀, 0 < s k ω → s k ω ≤ s (k + 1) ω := by
    intro k ω hω₀ hpos
    have h1 := t39g_le_confSigma (xiGamma γ) c D P h p z₀ R ((2 : ℝ)⁻¹ ^ t39gExp (n k ω))
      (s k ω) ω
    rw [← hω₀.2.2.1 k] at h1
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 h1) with h2 | h2
    · exact h2
    · linarith
  have hτs : ∀ k, ∀ ω ∈ Ω₀, τ ω ≤ s k ω := by
    intro k ω hω₀
    induction k with
    | zero => rw [hs0]
    | succ k ih => exact ih.trans (hstepmono k ω hω₀ (hω₀.1.trans_le ih))
  have hsle : ∀ k, ∀ ω ∈ Ω₀, s k ω ≤ s (k + 1) ω := fun k ω hω₀ =>
    hstepmono k ω hω₀ (hω₀.1.trans_le (hτs k ω hω₀))
  have hnmono0 : ∀ ω ∈ Ω₀, ∀ k, n (k + 1) ω ≤ n k ω := by
    intro ω hω₀ k
    rw [hn, hn]
    refine Finset.card_le_card fun i hi => ?_
    rw [Finset.mem_filter] at hi ⊢
    obtain ⟨x, hx⟩ := hi.2
    exact ⟨hi.1, t39gArc_restr hω₀.1 (hτs k ω hω₀) (hsle k ω hω₀) hω₀.2.1 (hI₀ i ω) hx⟩
  set nn := t39gRunMin n with hnn
  -- the bad steps
  set Bad : ℕ → Set Ω := fun k => {ω | t39Count Finset.univ (Act k) ω <
    4 * t39Count Finset.univ (fun i => Act k i ∩ (G k i)ᶜ) ω} with hBad
  have hBadm : ∀ k, MeasurableSet[𝓕 (k + 1)] (Bad k) := by
    intro k
    have hA1 : ∀ i, MeasurableSet[𝓕 (k + 1)] (Act k i) := fun i =>
      hmono (Nat.le_succ k) _ (hActm k i)
    have hY : Measurable[𝓕 (k + 1)] (t39Count Finset.univ (Act k)) :=
      Finset.measurable_sum _ fun i _ => measurable_const.indicator (hA1 i)
    have hX : Measurable[𝓕 (k + 1)] (t39Count Finset.univ (fun i => Act k i ∩ (G k i)ᶜ)) :=
      Finset.measurable_sum _ fun i _ => measurable_const.indicator ((hA1 i).inter (hGm k i).compl)
    exact measurableSet_lt hY (hX.const_mul 4)
  have hstep : ∀ k (b : ℕ) (A : Set Ω), 1 ≤ b → MeasurableSet[𝓕 k] A →
      A ⊆ {ω | b ≤ n k ω} →
      P (A ∩ Bad k) ≤ ENNReal.ofReal (4 * C₀ * 2 ^ α * (b : ℝ) ^ (-(α / 4))) * P A :=
    fun k b A hb hA hAb => t39g_hstep P (𝓕 k) (h𝓕 k) Finset.univ (Act k) (G k) (hActm k)
      (fun i => h𝓕 _ _ (hGm k i)) (n k) (fun ω => (2 : ℝ)⁻¹ ^ t39gExp (n k ω)) hC₀ hα
      (fun ω => by positivity) (fun ω h1 => (t39gExp_bounds h1).2) (hcond k) b hb A hA hAb
  set E := confReg (xiGamma γ) c D P h p χ z₀ R a with hE
  set Alive : ℕ → Ω → Prop := fun k ω => s k ω < tauR D h z₀ (3 * R) ω with hAlive
  have hN₀N₁ : N₀ ≤ N₁ := le_max_left _ _
  have hN₀aN₁ : N₀a ≤ N₁ := (le_max_left _ _).trans (le_max_right _ _)
  have h1N₁ : 1 ≤ N₁ := (le_max_right _ _).trans (le_max_right _ _)
  have hdet : ∀ ω ∈ E ∩ Ω₀, ∀ k, Alive k ω → N₁ ≤ nn k ω → ω ∉ Bad k →
      2 * nn (k + 1) ω ≤ nn k ω := by
    rintro ω ⟨hω, hω₀⟩ k hal hnk hnb
    rw [hnn, t39gRunMin_eq n (hnmono0 ω hω₀), t39gRunMin_eq n (hnmono0 ω hω₀)] at *
    have := t39g_count_half Finset.univ
      (fun i => {ω | (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty})
      (fun i => {ω | (t39gArc (D (h ω)) z₀ (s (k + 1) ω) (I₀ i ω)).Nonempty}) (Act k) (G k) ω
      (fun i _ hi => hActAl k i ω hi)
      (fun i _ hi => ⟨by
        obtain ⟨x, hx⟩ := hi
        exact t39gArc_restr hω₀.1 (hτs k ω hω₀) (hsle k ω hω₀) hω₀.2.1 (hI₀ i ω) hx,
        fun ⟨ha', hg⟩ => by
          have := hω₀.2.2.2.2 hω k hal (hN₀N₁.trans hnk) i ha' hg
          exact (Set.nonempty_iff_ne_empty.1 hi) this⟩)
      (by
        have := hω₀.2.2.2.1 hω k hal (hN₀N₁.trans hnk)
        rw [hn] at this
        exact this) hnb
    rw [hn, hn]
    exact this
  have hstep1 : ∀ ω ∈ E ∩ Ω₀, ∀ k, Alive k ω → N₁ ≤ nn k ω →
      s (k + 1) ω ≤ s k ω + (14 : ℝ) ^ χ * (nn k ω : ℝ) ^ (-(χ / 8)) *
        scaleFac (xiGamma γ) c (h ω) R z₀ := by
    rintro ω ⟨hω, hω₀⟩ k hal hnk
    rw [hnn, t39gRunMin_eq n (hnmono0 ω hω₀)] at *
    have hn1 : 1 ≤ n k ω := h1N₁.trans hnk
    have hspos : 0 < s k ω := hω₀.1.trans_le (hτs k ω hω₀)
    have h1 := t39g_step1_n hω hR hχ (hS ω) ha1 hn1 (hN₀a _ (hN₀aN₁.trans hnk)).le hspos.le
      (t39g_filledBall_subset_of_lt_tauR hspos hal)
    rw [← hω₀.2.2.1 k] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have := hS ω; positivity)).1 h1
  have hNN₁ : N₁ ≤ N := (le_max_right _ _).trans hge
  have hL' := hL P 𝓕 hmono h𝓕 nn (t39gRunMin_measurable hmono n hnm)
    (fun ω k => t39gRunMin_succ_le n k ω) Bad hBadm
    (fun k b A hb hA hAb => hstep k b A hb hA
      (hAb.trans fun ω hω => le_trans hω (t39gRunMin_le n k ω))) (E ∩ Ω₀) Alive hdet s τ
    (fun ω => scaleFac (xiGamma γ) c (h ω) R z₀) hs0 hCc (fun ω _ => (hS ω).le) hstep1 N hN hNN₁
  -- the event is contained (a.s.) in the event of Lemma 3.11
  have hN3 := hN₃ N ((le_max_left _ _).trans ((le_max_left _ _).trans hge))
  have hN3' := hN₃' N ((le_max_right _ _).trans ((le_max_left _ _).trans hge))
  have hsplit : (N : ℝ) ^ (-(χ / 8 / 2)) = (N : ℝ) ^ (-(χ / 8 / 4)) * (N : ℝ) ^ (-(χ / 8 / 4)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hNq : 0 < (N : ℝ) ^ (-(χ / 8 / 4)) := Real.rpow_pos_of_pos hNpos _
  have hKle : (14 : ℝ) ^ χ * ((2 : ℝ) ^ (χ / 8 + 1) / (1 - (2 : ℝ) ^ (-(χ / 8)))) *
      (N : ℝ) ^ (-(χ / 8 / 2)) ≤ (N : ℝ) ^ (-(χ / 8 / 4)) := by
    rw [hsplit, ← mul_assoc]
    nlinarith
  have hsub : {ω | ω ∈ E ∧ N ≤ (Finset.univ.filter fun i => (I₀ i ω ∩ hitSetLM (D (h ω)) z₀
      (τ ω) (τ ω + (N : ℝ) ^ (-(χ / 8 / 4)) * scaleFac (xiGamma γ) c (h ω) R z₀)).Nonempty).card}
      ≤ᵐ[P] {ω | ω ∈ E ∩ Ω₀ ∧ ¬ ∃ K : ℕ, s K ω ≤ τ ω + (14 : ℝ) ^ χ *
          ((2 : ℝ) ^ (χ / 8 + 1) / (1 - (2 : ℝ) ^ (-(χ / 8)))) * (N : ℝ) ^ (-(χ / 8 / 2)) *
          scaleFac (xiGamma γ) c (h ω) R z₀ ∧ (¬ Alive K ω ∨ nn K ω < N)} := by
    filter_upwards [hτ2, hΩ₀ae] with ω hω2 hω₀ hmem
    obtain ⟨hωE, hcount⟩ := hmem
    refine ⟨⟨hωE, hω₀⟩, ?_⟩
    rintro ⟨K, hsK, hstop⟩
    have hS0 := hS ω
    have hlt3 : s K ω < tauR D h z₀ (3 * R) ω := t39g_lt_tau3 hωE hS0 hω2
      (c := (14 : ℝ) ^ χ * ((2 : ℝ) ^ (χ / 8 + 1) / (1 - (2 : ℝ) ^ (-(χ / 8)))) *
        (N : ℝ) ^ (-(χ / 8 / 2))) hsK hN3'
    have hnK : n K ω < N := by
      have := hstop.resolve_left (fun h' => h' hlt3)
      rwa [hnn, t39gRunMin_eq n (hnmono0 ω hω₀)] at this
    have htt' : s K ω ≤ τ ω + (N : ℝ) ^ (-(χ / 8 / 4)) * scaleFac (xiGamma γ) c (h ω) R z₀ := by
      have := mul_le_mul_of_nonneg_right hKle hS0.le
      linarith
    have hc := t39g_hit_count_le hω₀.1 (hτs K ω hω₀) htt' hω₀.2.1 Finset.univ (fun i => I₀ i ω)
      (fun i => hI₀ i ω)
    rw [← hn] at hc
    omega
  refine (measure_mono_ae hsub).trans (hL'.trans (ENNReal.ofReal_le_ofReal ?_))
  have hpow : (N : ℝ) ^ (χ / 8 / 4) ≤ (N : ℝ) ^ (χ / 8 / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  calc b₀' * Real.exp (-(N : ℝ) ^ (χ / 8 / 2))
      ≤ max b₀' (Real.exp ((N₄ : ℝ) ^ (χ / 8 / 4))) * Real.exp (-(N : ℝ) ^ (χ / 8 / 4)) := by
        gcongr
        · exact le_max_left _ _

end CONF
end LQGMetric
