/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W6Red at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W0

/-!
`williamsDrift_of_good_hit`: strengthening of `williamsDrift_of_good` (W0) where one may also
assume that the negatively drifted path of `b'` hits every level `-d`, `d > 0`, for every `ω`.
Own bookkeeping (modification on a null set), same as `williamsDrift_of_good`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

theorem williamsDrift_of_good_hit
    (H : ∀ μ σ c : ℝ, 0 < μ → 0 < σ → 0 < c →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (b b' : ℝ≥0 → Ω → ℝ), GoodBM b P → GoodBM b' P →
        IndepFun (pathOf b) (pathOf b') P → (∀ ω, ∃ t, dpath σ (-μ) b ω t = -c) →
        (∀ ω (d : ℝ), 0 < d → ∃ t, dpath σ (-μ) b' ω t = -d) →
        P.map (fun ω u => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) u) =
          P.map (fun ω u => postLast (dpath σ μ b' ω) 0 u)) :
    WilliamsDriftDecomposition := by
  classical
  refine williamsDrift_of_good ?_
  intro μ σ c hμ hσ hc Ω _ P _ b b' hb hb' hind hhit
  have hs2 : (0 : ℝ) < √2 := by positivity
  set G' : Set Ω := {ω | ∀ n : ℕ, ∃ k : ℕ, σ * b' k ω - μ * k < -n} with hG'
  have hG'm : MeasurableSet G' := by
    have e : G' = ⋂ n : ℕ, ⋃ k : ℕ, {ω | σ * b' k ω - μ * k < -n} := by
      ext ω; simp [hG']
    rw [e]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
      measurableSet_lt (((hb'.meas _).const_mul _).sub_const _) measurable_const
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by
    simp only [hG', Set.mem_setOf_eq]
    refine ae_all_iff.2 fun n => ?_
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    filter_upwards [WedgeTrans.ae_exists_below hb'.pre hb'.meas (μ := μ * √2 / σ)
        (c := ((n : ℝ) + 1) * √2 / σ) (by positivity) (by positivity)] with ω h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    have e1 : σ * b' k ω - μ * k = σ / √2 * (√2 * b' k ω - μ * √2 / σ * k) := by
      field_simp
    have e2 : -((n : ℝ) + 1) = σ / √2 * (-(((n : ℝ) + 1) * √2 / σ)) := by field_simp
    have := mul_lt_mul_of_pos_left hk (show 0 < σ / √2 by positivity)
    rw [← e1, ← e2] at this
    linarith
  set b'' : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ G' then b' s ω else -(s : ℝ) with hb''
  have heq : ∀ᵐ ω ∂P, ∀ s, b' s ω = b'' s ω := by
    filter_upwards [hG'ae] with ω hω s
    simp only [hb'', if_pos hω]
  have hc'' : ∀ ω, Continuous (b'' · ω) := by
    intro ω
    by_cases hω : ω ∈ G'
    · simp only [hb'', if_pos hω]; exact hb'.cont ω
    · simp only [hb'', if_neg hω]; exact NNReal.continuous_coe.neg
  have hz'' : ∀ ω, b'' 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ G'
    · simp only [hb'', if_pos hω]; exact hb'.zero ω
    · simp [hb'', if_neg hω]
  have hgood : GoodBM b'' P :=
    ⟨hb'.pre.congr fun s => heq.mono fun ω h => h s,
      fun t => Measurable.ite hG'm (hb'.meas t) measurable_const, hc'', hz''⟩
  have hind'' : IndepFun (pathOf b) (pathOf b'') P := by
    refine hind.congr (Filter.EventuallyEq.refl _ _) ?_
    filter_upwards [heq] with ω h
    funext s; exact h s
  have hhit'' : ∀ ω (d : ℝ), 0 < d → ∃ t, dpath σ (-μ) b'' ω t = -d := by
    intro ω d hd
    have hcont : Continuous (dpath σ (-μ) b'' ω) := by
      unfold dpath; exact (continuous_const.mul (hc'' ω)).add
        (continuous_const.mul NNReal.continuous_coe)
    have h0 : dpath σ (-μ) b'' ω 0 = 0 := by simp [dpath, hz'']
    obtain ⟨n, hn⟩ := exists_nat_ge (d / σ)
    have hdn : d ≤ σ * n := by rwa [div_le_iff₀ hσ, mul_comm] at hn
    by_cases hω : ω ∈ G'
    · obtain ⟨m, hm⟩ := exists_nat_ge d
      obtain ⟨k, hk⟩ := hω m
      refine exists_eq_of_le hcont h0 hd (t := k) ?_
      simp only [dpath, hb'', if_pos hω, NNReal.coe_natCast]
      linarith
    · refine exists_eq_of_le hcont h0 hd (t := n) ?_
      simp only [dpath, hb'', if_neg hω, NNReal.coe_natCast]
      nlinarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have hmain := H μ σ c hμ hσ hc P b b'' hb hgood hind'' hhit hhit''
  have e1 : P.map (fun ω u => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) u) =
      P.map (fun ω u => glued c (dpath σ (-μ) b ω) (dpath σ μ b'' ω) u) := by
    refine Measure.map_congr ?_
    filter_upwards [heq] with ω h
    have : dpath σ μ b' ω = dpath σ μ b'' ω := funext fun t => by simp only [dpath, h t]
    rw [this]
  have e2 : P.map (fun ω u => postLast (dpath σ μ b' ω) 0 u) =
      P.map (fun ω u => postLast (dpath σ μ b'' ω) 0 u) := by
    refine Measure.map_congr ?_
    filter_upwards [heq] with ω h
    have : dpath σ μ b' ω = dpath σ μ b'' ω := funext fun t => by simp only [dpath, h t]
    rw [this]
  rw [e1, e2]
  exact hmain

end QuantumZipper.Williams
