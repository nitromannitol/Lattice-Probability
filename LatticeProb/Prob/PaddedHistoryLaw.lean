import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import LatticeProb.Prob.KernelProkhorovHistory
import LatticeProb.Prob.KernelProkhorovChainIterate

/-!
# The history law of a process from its one-step conditional laws

For random positions `Y 0, Y 1, …` on a probability space `(Ω, μ)`, the padded history after `n`
steps is `paddedHistory Y n ω = (Y 0 ω, …, Y n ω, Y n ω, …, Y n ω) : Fin (N + 1) → E`; it satisfies
`paddedHistory Y (n + 1) = padAfter n (paddedHistory Y n) (Y (n + 1))`.

If, for each step `n < N`, the joint law of the history after `n` steps and of the next position is
the composition-product `μ.map (paddedHistory Y n) ⊗ₘ κ n` of the history law with a Markov kernel
`κ n` (that is, `κ n` is a version of the regular conditional law of `Y (n + 1)` given the history
`(Y 0, …, Y n)`), then the history law after `n ≤ N` steps is the `n`-th law of the chain on
histories with steps `paddedHistoryKernel m (κ m)` started from the constant history
(`map_paddedHistory_eq_chainSeqLaw`). This is the disintegration of the law of a finite sequence
into successive conditional laws (Kallenberg, *Foundations of Modern Probability*, 2nd ed.,
Theorem 6.3 and Theorem 6.4).

Mixtures preserve one-sided Lévy–Prokhorov bounds against a fixed law
(`prokhorovLE_bind_left_of_ae`): if almost every component of a mixture is `(r, e)`-close to `ν`,
so is the mixture.

## Main results

* `paddedHistory_succ`: one step of the padded history is `padAfter`.
* `map_padAfter_eq_bind_paddedHistoryKernel`: one step of the history law.
* `map_paddedHistory_eq_chainSeqLaw`: the history law is the chain law of the conditional kernels.
* `prokhorovLE_bind_left_of_ae`: one-sided Lévy–Prokhorov bounds for mixtures.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb

section Padded

variable {Ω E : Type*} {N : ℕ}

/-- The history of the positions `Y 0, …, Y n`, padded with `Y n` after the index `n`. -/
def paddedHistory (Y : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Fin (N + 1) → E :=
  fun i => Y (min (i : ℕ) n) ω

theorem paddedHistory_zero (Y : ℕ → Ω → E) (ω : Ω) :
    (paddedHistory Y 0 ω : Fin (N + 1) → E) = fun _ => Y 0 ω := by
  funext i
  simp [paddedHistory]

theorem paddedHistory_succ (Y : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    (paddedHistory Y (n + 1) ω : Fin (N + 1) → E) =
      padAfter n (paddedHistory Y n ω) (Y (n + 1) ω) := by
  funext i
  by_cases hi : (i : ℕ) ≤ n
  · rw [padAfter_of_le _ _ hi]
    simp only [paddedHistory, min_eq_left hi, min_eq_left (hi.trans n.le_succ)]
  · rw [padAfter_of_lt _ _ (not_le.1 hi)]
    simp only [paddedHistory, min_eq_right (Nat.succ_le_of_lt (not_le.1 hi))]

/-- After `N` steps the padded history is the full history `(Y 0, …, Y N)`. -/
theorem paddedHistory_self (Y : ℕ → Ω → E) (ω : Ω) :
    (paddedHistory Y N ω : Fin (N + 1) → E) = fun i : Fin (N + 1) => Y i ω := by
  funext i
  simp only [paddedHistory, min_eq_left (Nat.lt_succ_iff.1 i.isLt)]

theorem measurable_paddedHistory [MeasurableSpace Ω] [MeasurableSpace E] {Y : ℕ → Ω → E}
    (hY : ∀ n, Measurable (Y n)) (n : ℕ) :
    Measurable (paddedHistory (N := N) Y n) :=
  measurable_pi_iff.2 fun _ => hY _

end Padded

section Law

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {N : ℕ}

/-- **One step of the history law.** If the joint law of `(H, Y)` is the composition-product of
the law of `H` with a Markov kernel `κ`, then padding `H` after the index `n` by `Y` has the law
of one step of `paddedHistoryKernel n κ` started from the law of `H`. -/
theorem map_padAfter_eq_bind_paddedHistoryKernel {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : Ω → Fin (N + 1) → E} {Y : Ω → E} (hH : Measurable H) (hY : Measurable Y) (n : ℕ)
    (κ : Kernel (Fin (N + 1) → E) E) [IsMarkovKernel κ]
    (h : μ.map (fun ω => (H ω, Y ω)) = μ.map H ⊗ₘ κ) :
    μ.map (fun ω => padAfter n (H ω) (Y ω)) = (μ.map H).bind (paddedHistoryKernel n κ) := by
  ext A hA
  have hpad := measurable_padAfter_uncurry (E := E) (N := N) n
  have hHY : Measurable fun ω => (H ω, Y ω) := hH.prodMk hY
  have hm : Measurable fun ω => padAfter n (H ω) (Y ω) := hpad.comp hHY
  rw [Measure.map_apply hm hA,
    Measure.bind_apply hA (measurable_paddedHistoryKernel n κ.measurable).aemeasurable]
  have h1 : (fun ω => padAfter n (H ω) (Y ω)) ⁻¹' A =
      (fun ω => (H ω, Y ω)) ⁻¹' ((fun q : (Fin (N + 1) → E) × E => padAfter n q.1 q.2) ⁻¹' A) :=
    rfl
  rw [h1, ← Measure.map_apply hHY (hpad hA), h, Measure.compProd_apply (hpad hA)]
  refine lintegral_congr fun g => ?_
  rw [paddedHistoryKernel, Measure.map_apply (measurable_padAfter n g) hA]
  rfl

/-- **The history law from the one-step conditional laws.** Let `Y 0 = z` and, for every step
`n < N`, let the joint law of the padded history after `n` steps and of the next position
`Y (n + 1)` be `μ.map (paddedHistory Y n) ⊗ₘ κ n`. Then for `n ≤ N` the padded history after `n`
steps has the `n`-th law of the chain on histories with steps `paddedHistoryKernel m (κ m)`,
started from the constant history at `z`. -/
theorem map_paddedHistory_eq_chainSeqLaw {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → E} (hY : ∀ n, Measurable (Y n)) {z : E} (hY0 : ∀ ω, Y 0 ω = z)
    (κ : ℕ → Kernel (Fin (N + 1) → E) E) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n < N, μ.map (fun ω => ((paddedHistory Y n ω : Fin (N + 1) → E), Y (n + 1) ω)) =
      μ.map (paddedHistory Y n) ⊗ₘ κ n) :
    ∀ n ≤ N, μ.map (paddedHistory (N := N) Y n) =
      chainSeqLaw (fun m => paddedHistoryKernel m (κ m)) (Measure.dirac fun _ => z) n := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : (paddedHistory (N := N) Y 0) = fun _ => fun _ => z := by
      funext ω
      rw [paddedHistory_zero, hY0]
    rw [h0, Measure.map_const, measure_univ, one_smul, chainSeqLaw_zero]
  | succ n ih =>
    intro hn
    have hs : (paddedHistory (N := N) Y (n + 1)) =
        fun ω => padAfter n (paddedHistory Y n ω) (Y (n + 1) ω) := by
      funext ω
      exact paddedHistory_succ Y n ω
    rw [hs, map_padAfter_eq_bind_paddedHistoryKernel (measurable_paddedHistory hY n) (hY _) n
      (κ n) (hκ n hn), ih (n.le_succ.trans hn), chainSeqLaw_succ]

/-- The full history `(Y 0, …, Y N)` has the `N`-th law of the chain on histories. -/
theorem map_history_eq_chainSeqLaw {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → E} (hY : ∀ n, Measurable (Y n)) {z : E} (hY0 : ∀ ω, Y 0 ω = z)
    (κ : ℕ → Kernel (Fin (N + 1) → E) E) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n < N, μ.map (fun ω => ((paddedHistory Y n ω : Fin (N + 1) → E), Y (n + 1) ω)) =
      μ.map (paddedHistory Y n) ⊗ₘ κ n) :
    μ.map (fun ω => fun i : Fin (N + 1) => Y i ω) =
      chainSeqLaw (fun m => paddedHistoryKernel m (κ m)) (Measure.dirac fun _ => z) N := by
  have h := map_paddedHistory_eq_chainSeqLaw hY hY0 κ hκ N le_rfl
  have hs : (paddedHistory (N := N) Y N) = fun ω => fun i : Fin (N + 1) => Y i ω := by
    funext ω
    exact paddedHistory_self Y ω
  rwa [hs] at h

end Law

section Mixture

variable {E X : Type*} [MeasurableSpace E] [PseudoMetricSpace X] [MeasurableSpace X]

/-- **Mixtures and one-sided Lévy–Prokhorov bounds.** If `ρ`-almost every component `κ u` of the
mixture `ρ.bind κ` is `(r, e)`-close to `ν` in the one-sided Lévy–Prokhorov sense, so is the
mixture. -/
theorem prokhorovLE_bind_left_of_ae {ρ : Measure E} [IsProbabilityMeasure ρ] {κ : E → Measure X}
    (hκ : Measurable κ) {ν : Measure X} {r e : ℝ}
    (h : ∀ᵐ u ∂ρ, ProkhorovLE (κ u) ν r e) : ProkhorovLE (ρ.bind κ) ν r e := by
  intro A hA
  rw [Measure.bind_apply hA hκ.aemeasurable]
  calc ∫⁻ u, κ u A ∂ρ ≤ ∫⁻ _, ν (thickening r A) + ENNReal.ofReal e ∂ρ :=
        lintegral_mono_ae (h.mono fun u hu => hu A hA)
    _ = ν (thickening r A) + ENNReal.ofReal e := by
        rw [lintegral_const, measure_univ, mul_one]

end Mixture

end LatticeProb
