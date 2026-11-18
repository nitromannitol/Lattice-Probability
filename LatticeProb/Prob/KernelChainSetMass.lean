import LatticeProb.Prob.KernelProkhorovChainIterate
import LatticeProb.Prob.KernelProkhorovHistory

/-!
# Accumulation of mass of a fixed set along a Markov chain

Let `D` be a measurable set and let the kernel `κ m` used at step `m` of a time-inhomogeneous
Markov chain satisfy `κ m x D ≤ 1_D(x) + β m`: a point of `D` may stay in `D` (for instance a
frozen point whose kernel is the Dirac mass at itself), and a step brings at most the mass `β m`
into `D`. Then the mass of `D` grows by at most `β m` at step `m`
(`bind_apply_le_add_of_ae_le`), so after `n` steps it is at most `μ D + ∑_{m < n} β m`
(`chainSeqLaw_apply_le_add_sum`), and at most `∑_{m ≤ n} β m` after `n + 1` steps when the first
step already gives mass at most `β 0` (`chainSeqLaw_succ_apply_le_sum`).

For the padded history chains of `paddedHistoryKernel`, a position kernel read at the last
coordinate moves the last coordinate to the new position at the steps `m < N`, and leaves the
history unchanged at the steps `m ≥ N`; the hypothesis therefore passes from the position kernel
to the history kernel and the set `{g | g (Fin.last N) ∈ D}`
(`paddedHistoryKernel_apply_last_le`). Started from a constant history `fun _ => z` with `N > 0`,
the last coordinate after `n + 1` steps lies in `D` with probability at most `∑_{m ≤ n} β m` as
soon as `q 0 z D ≤ β 0` (`chainSeqLaw_paddedHistory_last_le_sum`). For `N = 0` the history never
moves, and the bound fails when `z ∈ D`.

## Main results

* `bind_apply_le_add_of_ae_le`, `chainSeqLaw_apply_le_add_sum`, `chainSeqLaw_succ_apply_le_sum`.
* `paddedHistoryKernel_apply_last_le`, `chainSeqLaw_paddedHistory_last_le_sum`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

variable {E : Type*} [MeasurableSpace E]

/-- **One step.** If `κ x D ≤ 1_D(x) + β` for `ν`-almost every `x`, then the law after one
step of the kernel `κ` from the probability measure `ν` gives mass at most `ν D + β` to `D`. -/
theorem bind_apply_le_add_of_ae_le {ν : Measure E} [IsProbabilityMeasure ν] {κ : E → Measure E}
    (hκ : Measurable κ) {D : Set E} (hD : MeasurableSet D) {β : ℝ≥0∞}
    (hβ : ∀ᵐ x ∂ν, κ x D ≤ D.indicator 1 x + β) : ν.bind κ D ≤ ν D + β := by
  rw [Measure.bind_apply hD hκ.aemeasurable]
  calc ∫⁻ x, κ x D ∂ν ≤ ∫⁻ x, (D.indicator 1 x + β) ∂ν := lintegral_mono_ae hβ
    _ = ν D + β := by
      rw [lintegral_add_left (measurable_one.indicator hD), lintegral_indicator_one hD,
        lintegral_const, measure_univ, mul_one]

/-- **Accumulation of mass.** If at every step `m < n` the kernel `κ m` brings at most the mass
`β m` into `D` (`κ m x D ≤ 1_D(x) + β m` almost surely under the `m`-step law), then the
`n`-step law gives mass at most `μ D + ∑_{m < n} β m` to `D`. -/
theorem chainSeqLaw_apply_le_add_sum {κ : ℕ → E → Measure E} (hκ : ∀ n, Measurable (κ n))
    [∀ n x, IsProbabilityMeasure (κ n x)] {μ : Measure E} [IsProbabilityMeasure μ] {D : Set E}
    (hD : MeasurableSet D) {β : ℕ → ℝ≥0∞} {n : ℕ}
    (hβ : ∀ m < n, ∀ᵐ x ∂(chainSeqLaw κ μ m), κ m x D ≤ D.indicator 1 x + β m) :
    chainSeqLaw κ μ n D ≤ μ D + ∑ m ∈ Finset.range n, β m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := isProbabilityMeasure_chainSeqLaw hκ (μ := μ) n
    rw [chainSeqLaw_succ, Finset.sum_range_succ, ← add_assoc]
    calc (chainSeqLaw κ μ n).bind (κ n) D ≤ chainSeqLaw κ μ n D + β n :=
          bind_apply_le_add_of_ae_le (hκ n) hD (hβ n n.lt_succ_self)
      _ ≤ μ D + ∑ m ∈ Finset.range n, β m + β n := by
          gcongr
          exact ih fun m hm => hβ m (hm.trans n.lt_succ_self)

/-- **Accumulation of mass after a fresh first step.** If the first step gives mass at most
`β 0` to `D` and every later step `m ≤ n` brings at most the mass `β m` into `D`, then the
`(n + 1)`-step law gives mass at most `∑_{m ≤ n} β m` to `D`. -/
theorem chainSeqLaw_succ_apply_le_sum {κ : ℕ → E → Measure E} (hκ : ∀ n, Measurable (κ n))
    [∀ n x, IsProbabilityMeasure (κ n x)] {μ : Measure E} [IsProbabilityMeasure μ] {D : Set E}
    (hD : MeasurableSet D) {β : ℕ → ℝ≥0∞} {n : ℕ} (h1 : chainSeqLaw κ μ 1 D ≤ β 0)
    (hβ : ∀ m, 0 < m → m ≤ n → ∀ᵐ x ∂(chainSeqLaw κ μ m), κ m x D ≤ D.indicator 1 x + β m) :
    chainSeqLaw κ μ (n + 1) D ≤ ∑ m ∈ Finset.range (n + 1), β m := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    have := isProbabilityMeasure_chainSeqLaw hκ (μ := μ) (n + 1)
    rw [chainSeqLaw_succ, Finset.sum_range_succ]
    calc (chainSeqLaw κ μ (n + 1)).bind (κ (n + 1)) D ≤ chainSeqLaw κ μ (n + 1) D + β (n + 1) :=
          bind_apply_le_add_of_ae_le (hκ (n + 1)) hD (hβ (n + 1) n.succ_pos le_rfl)
      _ ≤ ∑ m ∈ Finset.range (n + 1), β m + β (n + 1) := by
          gcongr
          exact ih fun m hm hmn => hβ m hm (hmn.trans n.le_succ)

section History

variable {N : ℕ}

/-- **Mass brought into `D` by a history kernel.** For the step-`m` history kernel of a position
kernel `q` read at the last coordinate, the bound `q y D ≤ 1_D(y) + β` at the last coordinate
`y` of the history `h` passes to the set of histories whose last coordinate lies in `D`. -/
theorem paddedHistoryKernel_apply_last_le (m : ℕ) {q : E → Measure E}
    [∀ x, IsProbabilityMeasure (q x)] {D : Set E} (hD : MeasurableSet D) {β : ℝ≥0∞}
    (h : Fin (N + 1) → E) (hq : q (h (Fin.last N)) D ≤ D.indicator 1 (h (Fin.last N)) + β) :
    paddedHistoryKernel m (fun g => q (g (Fin.last N))) h {g | g (Fin.last N) ∈ D} ≤
      {g : Fin (N + 1) → E | g (Fin.last N) ∈ D}.indicator 1 h + β := by
  have hind : {g : Fin (N + 1) → E | g (Fin.last N) ∈ D}.indicator (1 : (Fin (N + 1) → E) → ℝ≥0∞) h =
      D.indicator 1 (h (Fin.last N)) := by
    by_cases hh : h (Fin.last N) ∈ D <;> simp [hh]
  have hD' : MeasurableSet {g : Fin (N + 1) → E | g (Fin.last N) ∈ D} :=
    measurable_pi_apply (Fin.last N) hD
  rw [hind]
  simp only [paddedHistoryKernel]
  rw [Measure.map_apply (measurable_padAfter m h) hD']
  by_cases hm : m < N
  · have hi : m < ((Fin.last N : Fin (N + 1)) : ℕ) := by simpa using hm
    have hpre : padAfter m h ⁻¹' {g | g (Fin.last N) ∈ D} = D := by
      ext x
      show padAfter m h x (Fin.last N) ∈ D ↔ x ∈ D
      rw [padAfter_of_lt h x hi]
    rw [hpre]
    exact hq
  · have hle : ((Fin.last N : Fin (N + 1)) : ℕ) ≤ m := by simpa using not_lt.1 hm
    by_cases hh : h (Fin.last N) ∈ D
    · calc q (h (Fin.last N)) (padAfter m h ⁻¹' {g | g (Fin.last N) ∈ D}) ≤ 1 := prob_le_one
        _ = D.indicator 1 (h (Fin.last N)) := by simp [hh]
        _ ≤ D.indicator 1 (h (Fin.last N)) + β := le_self_add
    · have hpre : padAfter m h ⁻¹' {g | g (Fin.last N) ∈ D} = ∅ := by
        ext x
        show padAfter m h x (Fin.last N) ∈ D ↔ x ∈ (∅ : Set E)
        rw [padAfter_of_le h x hle]
        simp [hh]
      rw [hpre, measure_empty]
      simp

/-- **Last coordinate of a padded history chain.** Run the padded history chain of position
kernels `q m` read at the last coordinate from the constant history `fun _ => z`, with `N > 0`.
If the first step from `z` gives mass at most `β 0` to `D` and every later step `m ≤ n` brings
at most the mass `β m` into `D` (`q m x D ≤ 1_D(x) + β m` for all `x`), then after `n + 1` steps
the last coordinate lies in `D` with probability at most `∑_{m ≤ n} β m`. -/
theorem chainSeqLaw_paddedHistory_last_le_sum (hN : 0 < N) (z : E) {q : ℕ → E → Measure E}
    (hq : ∀ n, Measurable (q n)) [∀ n x, IsProbabilityMeasure (q n x)] {D : Set E}
    (hD : MeasurableSet D) {β : ℕ → ℝ≥0∞} {n : ℕ} (hβ0 : q 0 z D ≤ β 0)
    (hβ : ∀ m, 0 < m → m ≤ n → ∀ x, q m x D ≤ D.indicator 1 x + β m) :
    chainSeqLaw (fun m => paddedHistoryKernel m (fun g => q m (g (Fin.last N))))
      (Measure.dirac fun _ => z) (n + 1) {g | g (Fin.last N) ∈ D} ≤
      ∑ m ∈ Finset.range (n + 1), β m := by
  have hq' : ∀ m, Measurable fun g : Fin (N + 1) → E => q m (g (Fin.last N)) := fun m =>
    (hq m).comp (measurable_pi_apply (Fin.last N))
  have : ∀ m (g : Fin (N + 1) → E), IsProbabilityMeasure ((fun g => q m (g (Fin.last N))) g) :=
    fun m g => inferInstanceAs (IsProbabilityMeasure (q m (g (Fin.last N))))
  have hκ : ∀ m, Measurable (paddedHistoryKernel m fun g => q m (g (Fin.last N))) := fun m =>
    measurable_paddedHistoryKernel m (hq' m)
  have hD' : MeasurableSet {g : Fin (N + 1) → E | g (Fin.last N) ∈ D} :=
    measurable_pi_apply (Fin.last N) hD
  refine chainSeqLaw_succ_apply_le_sum hκ hD' ?_
    fun m hm hmn => ae_of_all _ fun g =>
      paddedHistoryKernel_apply_last_le m hD g (hβ m hm hmn (g (Fin.last N)))
  rw [chainSeqLaw_succ, chainSeqLaw_zero, Measure.dirac_bind (hκ 0)]
  simp only [paddedHistoryKernel]
  rw [Measure.map_apply (measurable_padAfter 0 _) hD']
  have hi : 0 < ((Fin.last N : Fin (N + 1)) : ℕ) := by simpa using hN
  have hpre : padAfter 0 (fun _ : Fin (N + 1) => z) ⁻¹' {g | g (Fin.last N) ∈ D} = D := by
    ext x
    show padAfter 0 (fun _ : Fin (N + 1) => z) x (Fin.last N) ∈ D ↔ x ∈ D
    rw [padAfter_of_lt _ x hi]
  rw [hpre]
  exact hβ0

end History

end LatticeProb
