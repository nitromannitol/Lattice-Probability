/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2Ae at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateP417
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# GM Proposition 4.17 with almost-sure measurability inputs

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.19 (`lem-holder-balls`,
l. 2318–2327), Lemma 4.20 (`lem-nomax-msrble`, l. 2332–2360), Proposition 4.17 (l. 2276–2279,
proof l. 2404–2433).

GM's measurability statements `F_k ∈ 𝓕_{k+1}`, `{𝒵^E_k ≠ ∅} ∩ F_k ∈ 𝓕_{k+1}` and the inclusion
`ℰ_𝕣 ⊂ F_k` come from Axiom II (locality), which holds only almost surely; in the model they are
therefore available as `AEEventIn` statements (as `gm_L4_7_pair_ae` takes them for L4.7). The
conditional expectations and the probabilities in Proposition 4.17 do not see null sets, so
`gm_P4_17_ae` (= `gm_P4_17_abstract` with these inputs only a.s.) follows from
`gm_P4_17_abstract` applied to a.s.-equal versions of `F_k`, `𝒵^E_k`, `𝒵^𝔈_k` and `ℰ_𝕣`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

section
variable {Ω : Type} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem gm_measureReal_congr_set {s t : Set Ω} (h : ∀ᵐ ω ∂μ, (ω ∈ s ↔ ω ∈ t)) :
    μ.real s = μ.real t :=
  measureReal_congr (Filter.eventuallyEqSet_iff.2 h)

open scoped Classical in
theorem gm_card_congr {A B : ℕ → Set Ω} {ω : Ω} (n : ℕ) (h : ∀ k, (ω ∈ A k ↔ ω ∈ B k)) :
    ((range n).filter (fun k => ω ∈ A k)).card = ((range n).filter (fun k => ω ∈ B k)).card := by
  congr 1
  exact Finset.filter_congr fun k _ => h k

/-- an `m`-version of a set with an a.s. `m`-version which agrees with it on `G` -/
theorem gm_exists_version {m : MeasurableSpace Ω} {Z G : Set Ω}
    (hZG : @AEEventIn Ω m0 μ m (Z ∩ G)) {G' : Set Ω} (hGG' : G =ᵐ[μ] G') (hG' : MeasurableSet[m] G') :
    ∃ Z' : Set Ω, MeasurableSet[m] (Z' ∩ G') ∧ Z' =ᵐ[μ] Z ∧
      (MeasurableSet[m0] Z → m ≤ m0 → MeasurableSet[m0] G' → MeasurableSet[m0] Z') := by
  obtain ⟨T, hT, hZT⟩ := hZG
  refine ⟨T ∪ (Z \ G'), ?_, ?_, fun hZ hm hG'm => (hm _ hT).union (hZ.diff hG'm)⟩
  · have e : (T ∪ (Z \ G')) ∩ G' = T ∩ G' := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]; tauto
    rw [e]; exact hT.inter hG'
  · rw [Filter.eventuallyEqSet_iff] at hZT hGG' ⊢
    filter_upwards [hZT, hGG'] with ω h1 h2
    simp only [Set.mem_union, Set.mem_diff, ← h1, Set.mem_inter_iff, h2]
    tauto

end

open scoped Classical in
/-- **GM Proposition 4.17** (with Lemma 4.21) for abstract events, with the Lemma 4.19/4.20
inputs only almost surely -/
theorem gm_P4_17_ae {b β θ ν ζ : ℝ} (hb : 0 < b) (hθ : 0 < θ) (hθβ : θ < β)
    (hζ : 0 < ζ) (hβν : 4 * ν + ζ < β) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∀ K : ℕ, b * ε ^ (-β) ≤ K + 2 →
    ∀ {Ω : Type} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {μ : Measure Ω}
      [IsProbabilityMeasure μ] (Reg : Set Ω) (F ZE ZF : ℕ → Set Ω) {δ₁ δ₂ κ e : ℝ},
      (∀ k, AEEventIn μ (ℱ (k + 1)) (F k)) →
      (∀ k, AEEventIn μ (ℱ (k + 1)) (ZE k ∩ F k)) →
      (∀ k, AEEventIn μ (ℱ (k + 1)) (ZF k ∩ F k)) →
      (∀ k, MeasurableSet (ZE k)) → (∀ k, MeasurableSet (ZF k)) →
      (∀ k ≤ K, ∀ᵐ ω ∂μ, ω ∈ Reg → ω ∈ F k) →
      0 ≤ κ → ε ^ (2 * ν + ζ / 2) ≤ κ / 2 - e → κ / 2 - e ≤ 1 →
      μ.real (Reg ∩ {ω | ((((range (K + 1)).filter (fun k => ω ∈ ZE k)).card : ℕ) : ℝ) <
        (1 - ε ^ θ) * K}) ≤ δ₁ →
      (∀ k ≤ K, μ.real {ω | ω ∈ Reg ∧ μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω <
        κ * μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω - e} ≤ δ₂) →
      μ.real (Reg ∩ {ω | ((((range (K + 1)).filter (fun k => ω ∈ ZF k)).card : ℕ) : ℝ) <
        ε ^ (2 * ν + ζ) * K}) ≤ δ₁ + (K + 1) * δ₂ + 2 * ε ^ M := by
  obtain ⟨ε₀, hε₀, H⟩ := gm_P4_17_abstract hb hθ hθβ hζ hβν M
  refine ⟨ε₀, hε₀, fun ε hε K hK Ω m0 ℱ μ _ Reg F ZE ZF δ₁ δ₂ κ e hF hZE hZF hZEm hZFm hReg
    hκ hp hp1 h412 h47 => ?_⟩
  choose F' hF' hFF' using hF
  have hFF : ∀ k, F k =ᵐ[μ] F' k := hFF'
  have hver : ∀ (Z : ℕ → Set Ω), (∀ k, AEEventIn μ (ℱ (k + 1)) (Z k ∩ F k)) →
      (∀ k, MeasurableSet (Z k)) → ∃ Z' : ℕ → Set Ω, (∀ k, MeasurableSet[ℱ (k + 1)] (Z' k ∩ F' k))
        ∧ (∀ k, Z' k =ᵐ[μ] Z k) ∧ (∀ k, MeasurableSet (Z' k)) := by
    intro Z hZ hZm
    choose Z' h1 h2 h3 using fun k => gm_exists_version (hZ k) (hFF k) (hF' k)
    exact ⟨Z', h1, h2, fun k => h3 k (hZm k) (ℱ.le _) (ℱ.le _ _ (hF' k))⟩
  obtain ⟨ZE', hZE'1, hZE'2, hZE'3⟩ := hver ZE hZE hZEm
  obtain ⟨ZF', hZF'1, hZF'2, hZF'3⟩ := hver ZF hZF hZFm
  set Reg' : Set Ω := Reg ∩ {ω | ∀ k ≤ K, ω ∈ F' k}
  have hRR : ∀ᵐ ω ∂μ, (ω ∈ Reg' ↔ ω ∈ Reg) := by
    have h1 : ∀ᵐ ω ∂μ, ∀ k, (ω ∈ F k ↔ ω ∈ F' k) :=
      ae_all_iff.2 fun k => (Filter.eventuallyEqSet_iff.1 (hFF k))
    have h2 : ∀ᵐ ω ∂μ, ∀ k ≤ K, ω ∈ Reg → ω ∈ F k := by
      rw [ae_all_iff]; intro k
      by_cases hk : k ≤ K
      · filter_upwards [hReg k hk] with ω hω _ ; exact hω
      · exact Eventually.of_forall fun ω h => absurd h hk
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨fun h => h.1, fun h => ⟨h, fun k hk => (h1 k).1 (h2 k hk h)⟩⟩
  have hE : ∀ᵐ ω ∂μ, ∀ k, (ω ∈ ZE' k ↔ ω ∈ ZE k) :=
    ae_all_iff.2 fun k => Filter.eventuallyEqSet_iff.1 (hZE'2 k)
  have hFf : ∀ᵐ ω ∂μ, ∀ k, (ω ∈ ZF' k ↔ ω ∈ ZF k) :=
    ae_all_iff.2 fun k => Filter.eventuallyEqSet_iff.1 (hZF'2 k)
  have hind : ∀ (Z' Z : Set Ω), Z' =ᵐ[μ] Z → ∀ k,
      μ[Z'.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ] μ[Z.indicator (fun _ => (1 : ℝ)) | ℱ k] :=
    fun Z' Z h k => condExp_congr_ae (indicator_ae_eq_of_ae_eq_set h)
  have key := H ε hε K hK ℱ (μ := μ) Reg' F' ZE' ZF' hF' hZE'1 hZF'1 hZE'3 hZF'3
    (fun k hk ω hω => hω.2 k hk) hκ hp hp1 (by
      refine le_trans (le_of_eq ?_) h412
      refine gm_measureReal_congr_set ?_
      filter_upwards [hRR, hE] with ω h1 h2
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [h1, gm_card_congr (K + 1) h2]) (fun k hk => by
      refine le_trans (le_of_eq ?_) (h47 k hk)
      refine gm_measureReal_congr_set ?_
      filter_upwards [hRR, hind _ _ (hZF'2 k) k, hind _ _ (hZE'2 k) k] with ω h1 h2 h3
      show (_ ∧ _) ↔ (_ ∧ _)
      rw [h1, h2, h3])
  refine le_trans (le_of_eq ?_) key
  refine gm_measureReal_congr_set ?_
  filter_upwards [hRR, hFf] with ω h1 h2
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [h1, gm_card_congr (K + 1) h2]

end LQGMetric.GM
