/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.IterateP417 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateCount
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateRate

/-!
# GM Proposition 4.17 for abstract events (with GM's thresholds and rates)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.21 (`lem-nomax-cond`,
l. 2361–2398) and Proposition 4.17 (`prop-nomax-quant`, l. 2276–2279, proof l. 2404–2433).

`gm_P4_17_abstract`: for `β, θ` with `θ < β`, `ν ≥ 0`, `ζ > 0` with `4ν + ζ < β` (GM: "`4ν < β ∧ θ`"
and "`ζ` small") and every `M`, for small `ε` and every `K ≥ bε^{-β} − 2` (GM (4.35):
`K = ⌊aε^{-β}⌋ − 1`), the inputs

* (Lemma 4.19/4.20) `F_k ∈ 𝓕_{k+1}`, `{𝒵^E_k ≠ ∅} ∩ F_k ∈ 𝓕_{k+1}`,
  `{𝒵^𝔈_k ≠ ∅} ∩ F_k ∈ 𝓕_{k+1}`, `ℰ_𝕣 ⊆ F_k` for `k ≤ K`;
* (Proposition 4.12) `P[ℰ_𝕣, #{k ≤ K : 𝒵^E_k ≠ ∅} < (1 − ε^θ)K] ≤ δ₁`;
* (Lemma 4.7) for each `k ≤ K`, `P[ℰ_𝕣, P[𝒵^𝔈_k ≠ ∅ | 𝓕_k] < κ P[𝒵^E_k ≠ ∅ | 𝓕_k] − e] ≤ δ₂`
  with `κ/2 − e ≥ ε^{2ν+ζ/2}` (GM: `κ = ε^{2ν+o(1)}`, `e = o^∞_ε(ε)`)

give `P[ℰ_𝕣, #{k ≤ K : 𝒵^𝔈_k ≠ ∅} < ε^{2ν+ζ}K] ≤ δ₁ + (K+1)δ₂ + 2ε^M`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace LQGMetric.GM

open scoped Classical in
/-- **GM Proposition 4.17** (with Lemma 4.21) for abstract events -/
theorem gm_P4_17_abstract {b β θ ν ζ : ℝ} (hb : 0 < b) (hθ : 0 < θ) (hθβ : θ < β)
    (hζ : 0 < ζ) (hβν : 4 * ν + ζ < β) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∀ K : ℕ, b * ε ^ (-β) ≤ K + 2 →
    ∀ {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {μ : Measure Ω}
      [IsProbabilityMeasure μ] (Reg : Set Ω) (F ZE ZF : ℕ → Set Ω) {δ₁ δ₂ κ e : ℝ},
      (∀ k, MeasurableSet[ℱ (k + 1)] (F k)) →
      (∀ k, MeasurableSet[ℱ (k + 1)] (ZE k ∩ F k)) →
      (∀ k, MeasurableSet[ℱ (k + 1)] (ZF k ∩ F k)) →
      (∀ k, MeasurableSet (ZE k)) → (∀ k, MeasurableSet (ZF k)) →
      (∀ k ≤ K, Reg ⊆ F k) →
      0 ≤ κ → ε ^ (2 * ν + ζ / 2) ≤ κ / 2 - e → κ / 2 - e ≤ 1 →
      μ.real (Reg ∩ {ω | ((((range (K + 1)).filter (fun k => ω ∈ ZE k)).card : ℕ) : ℝ) <
        (1 - ε ^ θ) * K}) ≤ δ₁ →
      (∀ k ≤ K, μ.real {ω | ω ∈ Reg ∧ μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω <
        κ * μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω - e} ≤ δ₂) →
      μ.real (Reg ∩ {ω | ((((range (K + 1)).filter (fun k => ω ∈ ZF k)).card : ℕ) : ℝ) <
        ε ^ (2 * ν + ζ) * K}) ≤ δ₁ + (K + 1) * δ₂ + 2 * ε ^ M := by
  obtain ⟨ε₀, hε₀, hrate⟩ := gm_P4_17_rate hb hθ hθβ hζ hβν M
  refine ⟨ε₀, hε₀, fun ε hε K hK Ω m0 ℱ μ _ Reg F ZE ZF δ₁ δ₂ κ e hF hZE hZF hZEm hZFm hReg
    hκ hp hp1 h412 h47 => ?_⟩
  obtain ⟨hA, hmK, hC1, hD⟩ := hrate ε hε K hK
  have hp0 : 0 < κ / 2 - e := (Real.rpow_pos_of_pos hε.1 _).trans_le hp
  obtain ⟨hC2, hcnt⟩ := hD (κ / 2 - e) hp
  have h412' : μ.real (Reg ∩ {ω | ∑ k ∈ range (K + 1), (ZE k).indicator 1 ω <
      ((K + 1 : ℕ) : ℝ) - (p417m ε θ K : ℝ) / 4}) ≤ δ₁ := by
    refine le_trans (measureReal_mono ?_) h412
    rintro ω ⟨hR, hlt⟩
    refine ⟨hR, ?_⟩
    simp only [Set.mem_ofPred_eq] at hlt ⊢
    rw [gm_sum_indicator_eq_card] at hlt
    linarith
  have h47' : ∀ k < K + 1, μ.real {ω | ω ∈ Reg ∧
      μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω <
        κ * μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω - e} ≤ δ₂ :=
    fun k hk => h47 k (Nat.lt_succ_iff.1 hk)
  have hReg' : ∀ k < K + 1, Reg ⊆ F k := fun k hk => hReg k (Nat.lt_succ_iff.1 hk)
  have hcore := gm_P4_17_core ℱ (μ := μ) (K + 1) (p417m ε θ K) Reg F ZE ZF hF hZE hZF hZEm hZFm
    hReg' hκ hp0 hp1 h412' h47'
  refine le_trans (measureReal_mono ?_) (hcore.trans ?_)
  · rintro ω ⟨hR, hlt⟩
    refine ⟨hR, ?_⟩
    simp only [Set.mem_ofPred_eq] at hlt ⊢
    rw [gm_sum_indicator_eq_card]
    linarith
  · push_cast at hC1 hC2 ⊢
    linarith

end LQGMetric.GM
