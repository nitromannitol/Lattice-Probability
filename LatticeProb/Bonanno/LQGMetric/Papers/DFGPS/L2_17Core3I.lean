/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3I at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3H

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the stages (exhaustions, bumps, margins) (R3)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 2 (T:1226–1230: dyadic domains `W, W'` with `W̄ ⊂ V`, `W̄' ⊂ ℂ ∖ V̄`, a bump `φ ≡ 1` near
`W̄'` vanishing outside a compact subset of `ℂ ∖ V̄`, and `ε` small enough that
`B_ε(W') ⊂ φ⁻¹(1)`) and Step 4 (T:1278: "letting `W` increase to `V` and `W'` increase to
`ℂ ∖ V̄`").

* `exists_stage_data` — for finite families `𝒲` (closures in `V`) and `𝒲'` (closures in `U`),
  a bump `φ`, the open set `U₁ ⊆ φ⁻¹(1)` and a shift `m` of the scales with the `√ε` margins;
* `dyFin` — the finite family of the first `k` dyadic domains (in a fixed enumeration) with
  closure in a given set; monotone in `k`, exhausting.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip

theorem isCompact_closure_dyadicDomainsC (W : dyadicDomainsC) : IsCompact (closure (W : Set ℂ)) :=
  isCompact_iff_compactSpace.2 inferInstance

/-- **the data of one stage** (T:1226–1230) -/
theorem exists_stage_data {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U) {εn : ℕ → ℝ}
    (hε0 : Tendsto εn atTop (𝓝 0)) (𝒲 𝒲' : Finset dyadicDomainsC)
    (h𝒲 : ∀ W ∈ 𝒲, closure (W : Set ℂ) ⊆ V) (h𝒲' : ∀ W ∈ 𝒲', closure (W : Set ℂ) ⊆ U) :
    ∃ (φ : C(ℂ, ℝ)) (U₁ : Set ℂ) (δ : ℝ) (m : ℕ), HasCompactSupport φ ∧ IsOpen U₁ ∧
      (∀ x ∈ U₁, φ x = 1) ∧ 0 < δ ∧ (∀ x, φ x ≠ 0 → closedBall x δ ⊆ U) ∧
      (∀ k, ∀ W ∈ 𝒲, ∀ y ∈ closure (W : Set ℂ), closedBall y (Real.sqrt (εn (k + m))) ⊆ V) ∧
      (∀ k, ∀ W ∈ 𝒲', ∀ y ∈ closure (W : Set ℂ),
        closedBall y (Real.sqrt (εn (k + m))) ⊆ U₁) := by
  set K := ⋃ W ∈ 𝒲, closure (W : Set ℂ)
  set K' := ⋃ W ∈ 𝒲', closure (W : Set ℂ)
  have hK : IsCompact K := 𝒲.isCompact_biUnion fun W _ => isCompact_closure_dyadicDomainsC W
  have hK' : IsCompact K' := 𝒲'.isCompact_biUnion fun W _ => isCompact_closure_dyadicDomainsC W
  have hKV : K ⊆ V := iUnion₂_subset h𝒲
  have hK'U : K' ⊆ U := iUnion₂_subset h𝒲'
  obtain ⟨φ, U₁, δ, hφc, hU₁, hK'U₁, hφ1, hδ, hφU⟩ := exists_bump_of_isCompact hK' hU hK'U
  obtain ⟨η, hη, hηV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨η', hη', hη'U⟩ := hK'.exists_cthickening_subset_open hU₁ hK'U₁
  have hsq : Tendsto (fun n => Real.sqrt (εn n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hε0
    rwa [Real.sqrt_zero] at this
  obtain ⟨m, hm⟩ := eventually_atTop.1 (hsq.eventually (gt_mem_nhds (lt_min hη hη')))
  refine ⟨φ, U₁, δ, m, hφc, hU₁, hφ1, hδ, hφU, fun k W hW y hy => ?_, fun k W hW y hy => ?_⟩
  · have hlt := hm (k + m) (by omega)
    refine (closedBall_subset_closedBall (hlt.le.trans (min_le_left _ _))).trans
      ((closedBall_subset_cthickening (mem_biUnion hW hy) η).trans hηV)
  · have hlt := hm (k + m) (by omega)
    refine (closedBall_subset_closedBall (hlt.le.trans (min_le_right _ _))).trans
      ((closedBall_subset_cthickening (mem_biUnion hW hy) η').trans hη'U)

section Enum

attribute [local instance] Encodable.ofCountable

/-- the dyadic domains among the first `k` (fixed enumeration) with closure in `A` -/
def dyFin (A : Set ℂ) (k : ℕ) : Finset dyadicDomainsC :=
  (((Set.finite_lt_nat k).preimage (Encodable.encode_injective.injOn)).subset
    (fun W (hW : W ∈ {W : dyadicDomainsC | Encodable.encode W < k ∧
      closure (W : Set ℂ) ⊆ A}) => hW.1)).toFinset

theorem mem_dyFin {A : Set ℂ} {k : ℕ} {W : dyadicDomainsC} :
    W ∈ dyFin A k ↔ Encodable.encode W < k ∧ closure (W : Set ℂ) ⊆ A := by
  simp only [dyFin, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem dyFin_mono (A : Set ℂ) : Monotone (dyFin A) := fun _ _ hkl _ hW =>
  mem_dyFin.2 ⟨(mem_dyFin.1 hW).1.trans_le hkl, (mem_dyFin.1 hW).2⟩

theorem exists_mem_dyFin {A : Set ℂ} {W : dyadicDomainsC} (hW : closure (W : Set ℂ) ⊆ A) :
    ∃ k, W ∈ dyFin A k :=
  ⟨Encodable.encode W + 1, mem_dyFin.2 ⟨Nat.lt_succ_self _, hW⟩⟩

end Enum

end L217

end LQGMetric.DFGPS
