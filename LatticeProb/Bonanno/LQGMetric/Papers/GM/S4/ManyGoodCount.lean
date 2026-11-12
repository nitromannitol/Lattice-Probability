/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodCount at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.BinomialGM
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# GM Lemma 4.15, Step 4 (GM.S4.10): binomial domination, Hoeffding and the `o^∞_ε(ε)` rate

Source: GM = Gwynne–Miller, *Existence and uniqueness of the LQG metric for γ ∈ (0,2)*,
arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.15
(`lem-stab-endpt`), Step 4, l. 2187–2211 (GM_B: GM.S4.10).

* `gm_L4_15_step4` — GM l. 2189–2211: if the events `A_k ∈ 𝓕_{k+1}` (`k ∈ [0,K]`; GM:
  `A_k = ⋂_y G_y ∪ {σ_k > s_{k+1}} ∪ {#Conf_k > ε^{-ω}}`) have conditional probability
  `≥ 1 − s` given `𝓕_k` (GM (4.43): `s = ε^ω`), and on `ℰ ∩ Badᶜ` (GM: `Bad = ⋃_k {#Conf_k >
  ε^{-ω}}`, and `σ_k ≤ s_{k+1}` on `ℰ_𝕣` by (4.41)) `A_k` implies the good event `Good_k`
  (GM: `⋂_y G_y`), then
  `P[ℰ, #{k ∈ [0,K] : Good_k} < (1−t)K] ≤ P[ℰ ∩ Bad] + exp(−2(t−s)²(K+1))` — GM (4.44) before
  the asymptotics. The binomial domination + Hoeffding step is `LQGMetric.gm_count_lower_tail`
  (iterated conditioning in place of the coupling, DV-B7).
* `gm_hoeffding_superpoly` — GM l. 2202–2205: with `K + 1 = ⌊aε^{-β}⌋` (GM (4.35)),
  `exp(−2(ε^θ − ε^ω)²⌊aε^{-β}⌋) = o^∞_ε(ε)` for `0 < θ < min{ω, β/2}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace LQGMetric.GM

section Step4
variable {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0)

open scoped Classical in
/-- **GM Lemma 4.15, Step 4** (l. 2189–2211, GM.S4.10), before the asymptotics. -/
theorem gm_L4_15_step4 {μ : Measure Ω} [IsProbabilityMeasure μ] (K : ℕ) (A : ℕ → Set Ω)
    (hA : ∀ k ≤ K, MeasurableSet[ℱ (k + 1)] (A k)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1)
    (hq : ∀ k ≤ K, ∀ᵐ ω ∂μ, 1 - s ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω)
    (Ereg Bad : Set Ω) (Good : ℕ → Set Ω) (hgood : ∀ k ≤ K, Ereg ∩ Badᶜ ∩ A k ⊆ Good k) :
    μ.real (Ereg ∩ {ω | (((range (K + 1)).filter (fun k => ω ∈ Good k)).card : ℝ) <
        (1 - t) * K}) ≤
      μ.real (Ereg ∩ Bad) + Real.exp (-2 * (t - s) ^ 2 * (K + 1 : ℕ)) := by
  set A' : ℕ → Set Ω := fun k => if k ≤ K then A k else univ with hA'
  have hA'm : ∀ k, MeasurableSet[ℱ (k + 1)] (A' k) := by
    intro k
    by_cases hk : k ≤ K
    · simp only [hA', if_pos hk]; exact hA k hk
    · simp only [hA', if_neg hk]; exact MeasurableSet.univ
  have hq' : ∀ k, ∀ᵐ ω ∂μ, 1 - s ≤ μ[(A' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
    intro k
    by_cases hk : k ≤ K
    · simp only [hA', if_pos hk]; exact hq k hk
    · simp only [hA', if_neg hk, indicator_univ]
      rw [condExp_const (ℱ.le k)]
      exact Eventually.of_forall fun _ => by linarith
  have htail := gm_count_lower_tail ℱ A' hA'm hs hst ht hq' (K + 1)
  have hsub : Ereg ∩ {ω | (((range (K + 1)).filter (fun k => ω ∈ Good k)).card : ℝ) <
        (1 - t) * K} ⊆
      (Ereg ∩ Bad) ∪ {ω | ∑ k ∈ range (K + 1), (A' k).indicator 1 ω < (1 - t) * (K + 1 : ℕ)} := by
    rintro ω ⟨hE, hω⟩
    by_cases hB : ω ∈ Bad
    · exact Or.inl ⟨hE, hB⟩
    · right
      simp only [mem_setOf_eq] at hω ⊢
      have hle : ∑ k ∈ range (K + 1), (A' k).indicator (1 : Ω → ℝ) ω ≤
          (((range (K + 1)).filter (fun k => ω ∈ Good k)).card : ℝ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        by_cases hAk : ω ∈ A' k
        · have : ω ∈ Good k := by
            have hAk' : ω ∈ A k := by simpa [hA', if_pos hkK] using hAk
            exact hgood k hkK ⟨⟨hE, hB⟩, hAk'⟩
          simp [indicator_of_mem hAk, this]
        · simp only [indicator_of_notMem hAk]
          split_ifs <;> norm_num
      have h1t : 0 ≤ 1 - t := by linarith
      have : (1 - t) * (K : ℝ) ≤ (1 - t) * ((K + 1 : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ h1t; push_cast; linarith
      linarith
  calc _ ≤ μ.real ((Ereg ∩ Bad) ∪
        {ω | ∑ k ∈ range (K + 1), (A' k).indicator 1 ω < (1 - t) * (K + 1 : ℕ)}) :=
        measureReal_mono hsub
    _ ≤ μ.real (Ereg ∩ Bad) +
        μ.real {ω | ∑ k ∈ range (K + 1), (A' k).indicator 1 ω < (1 - t) * (K + 1 : ℕ)} :=
        measureReal_union_le _ _
    _ ≤ μ.real (Ereg ∩ Bad) + Real.exp (-2 * (t - s) ^ 2 * (K + 1 : ℕ)) :=
        add_le_add le_rfl htail

end Step4

/-! ## The `o^∞_ε(ε)` rate of the Hoeffding bound (GM l. 2202–2205) -/

/-- `exp(−c x^γ) ≤ C x^{-M}`-type bound in the variable `ε`: for `b, γ > 0` and `M`, eventually as
`ε → 0⁺`, `exp(−b ε^{-γ}) ≤ ε^M`. -/
theorem gm_exp_neg_rpow_le_rpow {b γ : ℝ} (hb : 0 < b) (hγ : 0 < γ) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, Real.exp (-b * ε ^ (-γ)) ≤ ε ^ M := by
  -- `x = ε^{-γ}`: `x^{M/γ} exp(−b x) → 0`
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (M / γ) b hb
  obtain ⟨X, hX⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  set X' := max X 1
  refine ⟨X' ^ (-γ⁻¹), Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _, ?_⟩
  rintro ε ⟨hε0, hεX⟩
  have hX'0 : 0 < X' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set x := ε ^ (-γ) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hε0 _
  have hxX : X ≤ x := by
    have h1 : ε ^ (-γ) ≥ (X' ^ (-γ⁻¹)) ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos hε0 hεX.le (by linarith)
    rw [← Real.rpow_mul hX'0.le, show -γ⁻¹ * -γ = 1 by field_simp, Real.rpow_one] at h1
    exact (le_max_left _ _).trans h1
  have hkey := hX x hxX
  -- `ε^M = x^{-M/γ}`
  have hεM : ε ^ M = x ^ (-(M / γ)) := by
    rw [hx, ← Real.rpow_mul hε0.le]; congr 1; field_simp
  rw [hεM]
  have hxp : 0 < x ^ (M / γ) := Real.rpow_pos_of_pos hx0 _
  rw [Real.rpow_neg hx0.le, le_inv_comm₀ (Real.exp_pos _) hxp, ← Real.exp_neg, neg_mul, neg_neg]
  -- `x^{M/γ} exp(−b x) < 1` gives `x^{M/γ} ≤ exp(b x)`
  have : x ^ (M / γ) * Real.exp (-b * x) < 1 := hkey
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)] at this
  exact this.le

/-- **GM l. 2202–2205**: for `a, β > 0` and `0 < θ < min{ω, β/2}`, the Hoeffding bound
`exp(−2(ε^θ − ε^ω)²⌊aε^{-β}⌋)` (with `K + 1 = ⌊aε^{-β}⌋`, GM (4.35)) is `O(ε^M)` for every `M`. -/
theorem gm_hoeffding_superpoly {a β θ ω : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hθω : θ < ω)
    (hθβ : θ < β / 2) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      Real.exp (-2 * (ε ^ θ - ε ^ ω) ^ 2 * (⌊a * ε ^ (-β)⌋₊ : ℝ)) ≤ ε ^ M := by
  have hβ : 0 < β := by linarith
  obtain ⟨ε₁, hε₁, h₁⟩ := gm_exp_neg_rpow_le_rpow (b := a / 4) (by positivity)
    (show 0 < β - 2 * θ by linarith) M
  -- `ε^{ω−θ} ≤ 1/2` and `a ε^{-β} ≥ 1` for small `ε`
  have hc1 : Tendsto (fun ε : ℝ => ε ^ (ω - θ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (ω - θ) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto (fun ε : ℝ => a * ε ^ (-β)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -β < 0)).const_mul_atTop ha
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (ω - θ) ≤ 1 / 2 :=
    hc1.eventually (Iic_mem_nhds (by norm_num))
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 ≤ a * ε ^ (-β) := hc2.eventually_ge_atTop 1
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min ε₁ 1) :=
    Ioo_mem_nhdsGT (lt_min hε₁ one_pos)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (ω - θ) ≤ 1 / 2 ∧ 1 ≤ a * ε ^ (-β) ∧ ε < ε₁ ∧ ε < 1 :=
    (e1.and (e2.and e3)).mono fun ε h =>
      ⟨h.1, h.2.1, lt_of_lt_of_le h.2.2.2 (min_le_left _ _),
        lt_of_lt_of_le h.2.2.2 (min_le_right _ _)⟩
  obtain ⟨ε₀, hε₀, hε₀'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  refine ⟨ε₀, hε₀, fun ε hε => ?_⟩
  obtain ⟨hh, ha1, hεε₁, hε1⟩ := hε₀' hε
  have hε0 := hε.1
  refine le_trans ?_ (h₁ ε ⟨hε0, hεε₁⟩)
  apply Real.exp_le_exp.2
  -- `(ε^θ − ε^ω)² ≥ ε^{2θ}/4`, `⌊aε^{-β}⌋ ≥ aε^{-β}/2`
  have hω' : ε ^ ω = ε ^ θ * ε ^ (ω - θ) := by
    rw [← Real.rpow_add hε0]; congr 1; ring
  have hθp : 0 < ε ^ θ := Real.rpow_pos_of_pos hε0 _
  have hd : ε ^ θ / 2 ≤ ε ^ θ - ε ^ ω := by rw [hω']; nlinarith
  have hsq : (ε ^ θ) ^ 2 / 4 ≤ (ε ^ θ - ε ^ ω) ^ 2 := by nlinarith
  have hfl : a * ε ^ (-β) / 2 ≤ (⌊a * ε ^ (-β)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (a * ε ^ (-β))
    have h1 : (1 : ℝ) ≤ ⌊a * ε ^ (-β)⌋₊ := by exact_mod_cast Nat.one_le_floor_iff _ |>.2 ha1
    linarith
  have hprod : (ε ^ θ) ^ 2 / 4 * (a * ε ^ (-β) / 2) ≤
      (ε ^ θ - ε ^ ω) ^ 2 * (⌊a * ε ^ (-β)⌋₊ : ℝ) :=
    mul_le_mul hsq hfl (by positivity) (sq_nonneg _)
  have hpow : (ε ^ θ) ^ 2 * ε ^ (-β) = ε ^ (-(β - 2 * θ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le, ← Real.rpow_add hε0]; congr 1; push_cast; ring
  have : a / 4 * ε ^ (-(β - 2 * θ)) ≤ 2 * ((ε ^ θ - ε ^ ω) ^ 2 * (⌊a * ε ^ (-β)⌋₊ : ℝ)) := by
    rw [← hpow]; nlinarith
  linarith


open scoped Classical in
/-- **GM Lemma 4.15, Step 4 with the rate** (l. 2189–2211, GM (4.44) from (4.43)): with
`K = ⌊aε^{-β}⌋ − 1` (GM (4.35)), conditional probabilities `≥ 1 − ε^ω` and `0 < θ < min{ω, β/2}`,
for every `M` and all small `ε` (uniformly in everything else),
`P[ℰ, #{k ∈ [0,K] : Good_k} < (1−ε^θ)K] ≤ P[ℰ ∩ Bad] + ε^M`. -/
theorem gm_L4_15_step4_rate {a β θ ω : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hθω : θ < ω)
    (hθβ : θ < β / 2) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
    ∀ {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {μ : Measure Ω}
      [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (Ereg Bad : Set Ω) (Good : ℕ → Set Ω),
      (∀ k ≤ ⌊a * ε ^ (-β)⌋₊ - 1, MeasurableSet[ℱ (k + 1)] (A k)) →
      (∀ k ≤ ⌊a * ε ^ (-β)⌋₊ - 1,
        ∀ᵐ x ∂μ, 1 - ε ^ ω ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] x) →
      (∀ k ≤ ⌊a * ε ^ (-β)⌋₊ - 1, Ereg ∩ Badᶜ ∩ A k ⊆ Good k) →
      μ.real (Ereg ∩ {x | (((range (⌊a * ε ^ (-β)⌋₊ - 1 + 1)).filter
          (fun k => x ∈ Good k)).card : ℝ) < (1 - ε ^ θ) * (⌊a * ε ^ (-β)⌋₊ - 1 : ℕ)}) ≤
        μ.real (Ereg ∩ Bad) + ε ^ M := by
  obtain ⟨ε₁, hε₁, h₁⟩ := gm_hoeffding_superpoly ha hθ hθω hθβ M
  have hβ : 0 < β := by linarith
  have hc2 : Tendsto (fun ε : ℝ => a * ε ^ (-β)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -β < 0)).const_mul_atTop ha
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 ≤ a * ε ^ (-β) := hc2.eventually_ge_atTop 1
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min ε₁ 1) :=
    Ioo_mem_nhdsGT (lt_min hε₁ one_pos)
  obtain ⟨ε₀, hε₀, hε₀'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (e2.and e3)
  refine ⟨ε₀, hε₀, fun ε hε Ω m0 ℱ μ _ A Ereg Bad Good hA hq hgood => ?_⟩
  obtain ⟨ha1, hεm⟩ := hε₀' hε
  have hε0 := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hεm.2 (min_le_right _ _)
  have hεε₁ : ε < ε₁ := lt_of_lt_of_le hεm.2 (min_le_left _ _)
  have hω0 : 0 ≤ ε ^ ω := (Real.rpow_pos_of_pos hε0 _).le
  have hωθ : ε ^ ω ≤ ε ^ θ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hθω.le
  have hθ1 : ε ^ θ ≤ 1 := Real.rpow_le_one hε0.le hε1.le hθ.le
  have hstep := gm_L4_15_step4 ℱ (⌊a * ε ^ (-β)⌋₊ - 1) A hA hω0 hωθ hθ1 hq Ereg Bad Good hgood
  refine hstep.trans (add_le_add le_rfl ?_)
  have hK : ((⌊a * ε ^ (-β)⌋₊ - 1 + 1 : ℕ) : ℝ) = (⌊a * ε ^ (-β)⌋₊ : ℝ) := by
    congr 1; have := Nat.one_le_floor_iff _ |>.2 ha1; omega
  rw [hK]
  exact h₁ ε ⟨hε0, hεε₁⟩

end LQGMetric.GM
