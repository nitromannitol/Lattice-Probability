/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W6Tail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Hat

/-!
For `Ŷ = postLast Y 0`, `Y = dpath σ μ b`, `μ > 0`: a.s., for every horizon `U`,
`lastPass Ŷ a > U` for all large `a`. Own elementary proof (transience `ae_eventually_gt`,
closedness of the zero set, intermediate value theorem).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- a.s., for every horizon `U`, the last passage of `Ŷ = postLast Y 0` at level `a` exceeds `U`
for all large `a`. -/
theorem ae_tendsto_lastPass_postLast (hb : GoodBM b P) (hμ : 0 < μ) :
    ∀ᵐ ω ∂P, ∀ U : ℝ≥0, ∃ A : ℝ, ∀ a, A ≤ a → U < lastPass (postLast (dpath σ μ b ω) 0) a := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ T : ℝ≥0, ∀ t, T ≤ t → (n : ℝ) < dpath σ μ b ω t :=
    ae_all_iff.2 fun n => ae_eventually_gt hb hμ n
  filter_upwards [hall] with ω h U
  set Y := dpath σ μ b ω with hY
  have hc : Continuous Y := continuous_dpath hb σ μ ω
  set Yh := postLast Y 0 with hYh
  have hYhc : Continuous Yh := by
    simp only [hYh]
    exact (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  refine ⟨Yh U + 1, fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt a
  obtain ⟨T, hT⟩ := h n
  have hbig : ∀ t, T ≤ t → a < Yh t := fun t ht => by
    simp only [hYh, postLast, sub_zero]
    exact hn.trans (hT _ (ht.trans le_add_self))
  have hBdd : BddAbove {t | Yh t = a} := ⟨T, fun t (ht : Yh t = a) => by
    by_contra hlt
    exact (hbig t (le_of_not_ge hlt)).ne' ht⟩
  rw [lt_lastPass_iff hBdd]
  have hU : Yh U < a := by linarith
  obtain ⟨t, ⟨ht1, _⟩, ht⟩ := intermediate_value_Icc (le_max_left U T) hYhc.continuousOn
    ⟨hU.le, (hbig _ (le_max_right U T)).le⟩
  refine ⟨t, lt_of_le_of_ne ht1 ?_, ht⟩
  rintro rfl
  exact hU.ne ht

end QuantumZipper.Williams
