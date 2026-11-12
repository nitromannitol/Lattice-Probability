/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412fUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# GM (4.40′): the conditional union bound over the endpoints

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3, (4.40′)
(`eqn-stab-union`, l. 2176–2179): "we can take a union bound over at most `ε^{-ω}` elements of
`𝒴_k` to get `P[⋂_y G_y | 𝓑^•_{t_k}, h|] ≥ 1 − C₀ε^{ακ−ω}`".

`p412f_condExp_iInter`: if `P[G_j | 𝓕] ≥ 1 − c` a.s. for `j < N`, then
`P[⋂_{j<N} G_j | 𝓕] ≥ 1 − N c` a.s. (from `1_{⋂ G_j} ≥ 1 − Σ_j (1 − 1_{G_j})`, monotonicity and
linearity of the conditional expectation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace LQGMetric.GM

/-- **conditional union bound** (GM (4.40′)) -/
theorem p412f_condExp_iInter {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : MeasurableSpace Ω} (hF : F ≤ m0) (N : ℕ) (G : ℕ → Set Ω)
    (hG : ∀ j, @NullMeasurableSet Ω m0 (G j) μ) {c : ℝ}
    (hc : ∀ j < N, ∀ᵐ x ∂μ, 1 - c ≤ μ[(G j).indicator (fun _ => (1 : ℝ)) | F] x) :
    ∀ᵐ x ∂μ, 1 - N * c ≤
      μ[(⋂ j ∈ Finset.range N, G j).indicator (fun _ => (1 : ℝ)) | F] x := by
  set ind : ℕ → Ω → ℝ := fun j => (G j).indicator (fun _ => (1 : ℝ)) with hind
  set g : ℕ → Ω → ℝ := fun j => (fun _ => (1 : ℝ)) - ind j with hg
  set S : Ω → ℝ := ∑ j ∈ Finset.range N, g j with hS
  set f : Ω → ℝ := (fun _ => (1 : ℝ)) - S with hf
  have hint : ∀ j, Integrable (ind j) μ := fun j => (integrable_const 1).indicator₀ (hG j)
  have hgint : ∀ j, Integrable (g j) μ := fun j => (integrable_const _).sub (hint j)
  have hSint : Integrable S μ := integrable_finsetSum' _ fun j _ => hgint j
  have hIm : @NullMeasurableSet Ω m0 (⋂ j ∈ Finset.range N, G j) μ :=
    NullMeasurableSet.biInter (Finset.range N).countable_toSet fun j _ => hG j
  have hind01 : ∀ j x, 0 ≤ ind j x ∧ ind j x ≤ 1 := fun j x => by
    simp only [hind, indicator]; split_ifs <;> norm_num
  -- `f ≤ 1_{⋂ G_j}` pointwise
  have hle : f ≤ᵐ[μ] (⋂ j ∈ Finset.range N, G j).indicator (fun _ => (1 : ℝ)) := by
    refine Eventually.of_forall fun x => ?_
    have hg0 : ∀ j, 0 ≤ g j x := fun j => by
      simp only [hg, Pi.sub_apply]; linarith [(hind01 j x).2]
    have hSx : S x = ∑ j ∈ Finset.range N, g j x := by simp [hS, Finset.sum_apply]
    simp only [hf, Pi.sub_apply]
    by_cases hx : x ∈ ⋂ j ∈ Finset.range N, G j
    · rw [indicator_of_mem hx, hSx]
      linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.range N) => hg0 j]
    · rw [indicator_of_notMem hx]
      obtain ⟨j, hj, hxj⟩ : ∃ j ∈ Finset.range N, x ∉ G j := by
        by_contra hne; simp only [not_exists, not_and, not_not] at hne; exact hx (mem_iInter₂.2 hne)
      have h1 : g j x = 1 := by simp [hg, hind, indicator_of_notMem hxj]
      have := Finset.single_le_sum (fun i (_ : i ∈ Finset.range N) => hg0 i) hj
      rw [hSx]; linarith
  have hmono := condExp_mono (m := F) ((integrable_const _).sub hSint)
    ((integrable_const 1).indicator₀ hIm) hle
  have hfe : μ[f | F] =ᵐ[μ] (fun _ => (1 : ℝ)) - μ[S | F] := by
    refine (condExp_sub (integrable_const _) hSint F).trans ?_
    rw [condExp_const hF]
  have hSe : μ[S | F] =ᵐ[μ] ∑ j ∈ Finset.range N, μ[g j | F] :=
    condExp_finsetSum (fun j _ => hgint j) F
  have hge : ∀ j, μ[g j | F] =ᵐ[μ] (fun _ => (1 : ℝ)) - μ[ind j | F] := fun j => by
    refine (condExp_sub (integrable_const _) (hint j) F).trans ?_
    rw [condExp_const hF]
  have hge' : ∀ᵐ x ∂μ, ∀ j, μ[g j | F] x = 1 - μ[ind j | F] x :=
    ae_all_iff.2 fun j => (hge j).mono fun x hx => by rw [hx]; rfl
  have hc' : ∀ᵐ x ∂μ, ∀ j, j < N → 1 - c ≤ μ[ind j | F] x :=
    ae_all_iff.2 fun j => by
      by_cases hj : j < N
      · exact (hc j hj).mono fun x hx _ => hx
      · exact Eventually.of_forall fun x h => absurd h hj
  filter_upwards [hmono, hfe, hSe, hge', hc'] with x hm hfx hSx hgx hcx
  have hsum : (∑ j ∈ Finset.range N, μ[g j | F]) x ≤ N * c := by
    rw [Finset.sum_apply]
    calc ∑ j ∈ Finset.range N, μ[g j | F] x ≤ ∑ _j ∈ Finset.range N, c :=
          Finset.sum_le_sum fun j hj => by
            rw [hgx j]; linarith [hcx j (Finset.mem_range.1 hj)]
      _ = N * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : μ[f | F] x = 1 - μ[S | F] x := by rw [hfx]; rfl
  rw [← hf] at hm
  linarith [hSx ▸ hsum]

/-- a lower bound `1 − c > 0` for `μ[1_G | F]` forces `G` to be null-measurable -/
theorem p412f_nullMeas_of_condExp {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : MeasurableSpace Ω} {G : Set Ω} {c : ℝ} (hc : c < 1)
    (h : ∀ᵐ x ∂μ, 1 - c ≤ μ[G.indicator (fun _ => (1 : ℝ)) | F] x) :
    @NullMeasurableSet Ω m0 G μ := by
  by_contra hn
  have hni : ¬ Integrable (G.indicator (fun _ => (1 : ℝ))) μ := fun hi =>
    hn ((aemeasurable_indicator_const_iff (1 : ℝ)).1 hi.aestronglyMeasurable.aemeasurable)
  rw [condExp_of_not_integrable hni] at h
  obtain ⟨x, hx⟩ := h.exists
  simp only [Pi.zero_apply] at hx
  linarith

end LQGMetric.GM
