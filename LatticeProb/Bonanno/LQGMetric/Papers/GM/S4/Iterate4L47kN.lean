/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4L47kN at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L47kC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ConditionalL48

/-!
# GM Lemma 4.7 at index `k`: the count bound (4.19) on `G` (DEC-89, packet B)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, (4.19) (l. 1806–1823, Lemma 4.8) as
used in the proof of Lemma 4.7 (l. 1925–1936): on `G = {𝓑^•_{t_k} ⊆ B_{(4λ₄ε)^{-M}𝕣}(𝕫),
𝕨 ∉ 𝓑^•_{t_k}}`, the number `N` of pairs of `𝒵^𝔈_k` among the candidates is at most
`K = #ℛ (4λ₄ε)^{2−1/M} 𝕣² / σ²`, `σ = λ₁ ε^{1+ν} 𝕣 / 4`, outside the exceptional event of
`gm_L4_8_uncondU`.

* `gm_h47_count`: the hypothesis `hP` of `gm_h47_k_core`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **the count bound (4.19) for `𝒵^𝔈_k` on `G`** (GM l. 1925–1936, from Lemma 4.8) -/
theorem gm_h47_count (R : RegPar) {𝕫 𝕨 : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨)
    (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)))
    {𝕣 ε β M δ : ℝ} (k : ℕ) (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hδ : 0 ≤ δ)
    (hlam0 : 0 < R.lam 0) (hlam3 : 0 < R.lam 3) (hlam02 : R.lam 0 ≤ 2) (hlam11 : R.lam 1 ≤ 1)
    (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) (Rads : Finset ℝ)
    (hRads : (Rads : Set ℝ) = p4Rads R 𝕣 ε)
    (hRadsI : ∀ r ∈ p4Rads R 𝕣 ε, ε ^ (1 + R.ν) * 𝕣 ≤ r ∧ r ≤ ε * 𝕣)
    (S : Finset (ℂ × ℝ))
    (hL48 : P {ω | ∀ t : ℝ, 0 < t →
      filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 ((4 * R.lam 3 * ε) ^ (-M) * 𝕣) →
      𝕨 ∉ filledBall (D (h ω)) 𝕫 t → ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) G L 𝕫 𝕨 →
      ∀ σ : ℝ, 0 < σ → σ ≤ R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 →
      ∀ Rads : Finset ℝ, (∀ r ∈ Rads, 2 * σ ≤ r ∧ r ≤ ε * 𝕣) →
      ∀ S : Finset (ℂ × ℝ), (∀ p ∈ S, p ∈ candSet (filledBall (D (h ω)) 𝕫 t) (R.lam 0) (R.lam 3)
          ε R.ν 𝕣 (Rads : Set ℝ) ∧ (G '' Icc 0 L ∩ ball p.1 p.2).Nonempty) →
      (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤
        Rads.card * ENNReal.ofReal ((4 * R.lam 3 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2)}ᶜ ≤
      ENNReal.ofReal δ) :
    P.real ({x | (Rads.card * ((4 * R.lam 3 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2)) /
        (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ^ 2 < ∑ i ∈ S,
      {ω | i ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω}.indicator (fun _ => (1 : ℝ)) x} ∩
      ({ω | filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆
          ball 𝕫 ((4 * R.lam 3 * ε) ^ (-M) * 𝕣)} ∩
        {ω | 𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)})) ≤ δ := by
  classical
  set σ : ℝ := R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 with hσdef
  have hσ : 0 < σ := by
    have := Real.rpow_pos_of_pos hε (1 + R.ν); positivity
  set X : ℝ := (4 * R.lam 3 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2
  refine ENNReal.toReal_le_of_le_ofReal hδ (le_trans (measure_mono_ae ?_) hL48)
  filter_upwards [hη] with ω hω hbad hgood
  obtain ⟨hlt, hsub, hw⟩ := hbad
  simp only [mem_setOf_eq] at hlt hsub hw hgood
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω
  have ht : 0 < t := by
    simp only [t]; rw [gm_s4T_eq]
    have hτ := gm_tauD_pos (D (h ω)) 𝕫 hℓ𝕣
    have : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    have : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
    positivity
  set S' : Finset (ℂ × ℝ) := S.filter (fun i => i ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω)
  have hL : 0 < (D (h ω)).1 (𝕫, 𝕨) := lt_of_le_of_ne (gm_D_nonneg _ 𝕫 𝕨)
    (fun h0 => h𝕫𝕨 ((D (h ω)).2.eq_of_eq_zero 𝕫 𝕨 h0.symm))
  have hcnt := hgood t ht hsub hw _ _ (gm_geodL_isGeodesicL hω h𝕫𝕨) σ hσ le_rfl Rads
    (fun r hr => by
      have hr' : r ∈ p4Rads R 𝕣 ε := by rw [← hRads]; exact hr
      obtain ⟨hl, hu⟩ := hRadsI r hr'
      refine ⟨le_trans ?_ hl, hu⟩
      have : 0 < ε ^ (1 + R.ν) * 𝕣 := by have := Real.rpow_pos_of_pos hε (1 + R.ν); positivity
      simp only [σ]; nlinarith) S'
    (fun p hp => by
      obtain ⟨-, hp⟩ := Finset.mem_filter.1 (show p ∈ S.filter _ from hp)
      obtain ⟨hc, -, -, ⟨_, ⟨v, rfl⟩, hv⟩⟩ := hp
      refine ⟨by rw [hRads]; exact hc, ⟨_, ⟨v * (D (h ω)).1 (𝕫, 𝕨), ⟨mul_nonneg v.2.1 hL.le,
        mul_le_of_le_one_left hL.le v.2.2⟩, rfl⟩, ?_⟩⟩
      have hPv : geodL (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) (v * (D (h ω)).1 (𝕫, 𝕨)) =
          sel 𝕫 𝕨 (h ω) v := by
        simp only [geodL]
        congr 1
        rw [mul_div_cancel_right₀ _ hL.ne']
        exact projIcc_val zero_le_one v
      rw [hPv]
      have hr0 : 0 ≤ p.2 := by
        have hr' : p.2 ∈ p4Rads R 𝕣 ε := hc.2.2.1
        obtain ⟨hl, -⟩ := hRadsI _ hr'
        exact le_trans (by have := Real.rpow_pos_of_pos hε (1 + R.ν); positivity) hl
      exact ball_subset_ball (mul_le_of_le_one_left hr0 hlam11) hv)
  -- back to real numbers
  have hX : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hX)] at hcnt
  have hN : ∑ i ∈ S, {ω | i ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω}.indicator (fun _ => (1 : ℝ)) ω =
      (S'.card : ℝ) := by
    simp only [Set.indicator_apply, mem_setOf_eq, S']
    rw [Finset.sum_boole]
  rw [hN] at hlt
  have : (S'.card : ℝ) ≤ Rads.card * X / σ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hcnt
  linarith

end LQGMetric.GM
