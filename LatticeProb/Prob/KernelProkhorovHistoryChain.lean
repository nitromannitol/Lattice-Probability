import LatticeProb.Prob.KernelProkhorovChainIterate
import LatticeProb.Prob.KernelProkhorovHistory

/-!
# Comparison of two Markov chains on histories of a fixed length

Two chains run on the histories `Fin (N + 1) → E` (sup metric), with padded history kernels
(`paddedHistoryKernel`): at step `n` the first chain samples the next position from a kernel
`p n h` that may depend on the whole history `h`, while the second chain samples it from a
position kernel `q n` read at one coordinate `j n` of the history (for chains started from a
constant history, `j n = Fin.last N` reads the current position at every step `n < N`).

If at every step the kernel `p n h` is uniformly `ε n`-close to `q n (h (j n))` in the one-sided
Prokhorov sense, the position kernel `q n` is continuous in its starting point at the thickening
radius `r n` with mass error `η n` between starting points in `H n` and `G n` at distance less
than the current radius `R n ≤ r n`, the first chain reads a point of `H n` almost surely, and the
second reads a point outside `G n` with probability at most `ρ n`, then the `n`-step laws of the
two history chains are `(R n, e n)`-close, with `R (m + 1) = ε m + r m` and
`e (m + 1) = ε m + η m + ρ m + e m`. This is `prokhorovLE_chainSeqLaw` on the history space, whose
kernel hypotheses are transferred from the position kernels by `prokhorovLE_paddedHistoryKernel`
and `paddedHistoryKernel_le_thickening_add`.

## Main results

* `prokhorovLE_chainSeqLaw_paddedHistory`: the `n`-step comparison of the two history chains.
* `prokhorovLE_chainSeqLaw_paddedHistory_const`: both chains started from the same constant
  history `fun _ => z`, with the error `∑_{m < n} (ε m + η m + ρ m)`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

variable {E : Type*} {N : ℕ} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopology E]

/-- **Joint laws of two chains on padded histories.** The first chain samples the next position
from the history kernel `p n`, the second from the position kernel `q n` read at the coordinate
`j n` of the history. Uniform `ε n`-closeness of `p n h` and `q n (h (j n))`, continuity of `q n`
at the thickening radius `r n ≥ R n` with mass error `η n` between points of `H n` and `G n` at
distance less than `R n`, and the support conditions on the coordinate `j n` give
`(R n, e n)`-closeness of the `n`-step laws, with `R (m + 1) = ε m + r m` and
`e (m + 1) = ε m + η m + ρ m + e m`. -/
theorem prokhorovLE_chainSeqLaw_paddedHistory {μ ν : Measure (Fin (N + 1) → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : ℕ → (Fin (N + 1) → E) → Measure E}
    {q : ℕ → E → Measure E} (hp : ∀ n, Measurable (p n)) (hq : ∀ n, Measurable (q n))
    [∀ n h, IsProbabilityMeasure (p n h)] [∀ n x, IsProbabilityMeasure (q n x)]
    (j : ℕ → Fin (N + 1)) {ε r η ρ R e : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n) (hη : ∀ n, 0 ≤ η n)
    (hρ : ∀ n, 0 ≤ ρ n) (he0 : 0 ≤ e 0) (hR : ∀ n, R (n + 1) = ε n + r n)
    (hRr : ∀ n, R n ≤ r n) (he : ∀ n, e (n + 1) = ε n + η n + ρ n + e n)
    (hP : ProkhorovLE μ ν (R 0) (e 0))
    (hK : ∀ n h, ProkhorovLE (p n h) (q n (h (j n))) (ε n) (ε n)) {H G : ℕ → Set E}
    (hH : ∀ n, MeasurableSet (H n))
    (hμH : ∀ n, chainSeqLaw (fun m => paddedHistoryKernel m (p m)) μ n
      {h | h (j n) ∈ H n}ᶜ = 0)
    (hG : ∀ n, chainSeqLaw (fun m => paddedHistoryKernel m (fun g => q m (g (j m)))) ν n
      {h | h (j n) ∈ G n}ᶜ ≤ ENNReal.ofReal (ρ n))
    (hcont : ∀ n, ∀ b ∈ G n, ∀ y ∈ H n, dist y b < R n → ∀ A : Set E, MeasurableSet A →
      q n y A ≤ q n b (thickening (r n) A) + ENNReal.ofReal (η n)) (n : ℕ) :
    ProkhorovLE (chainSeqLaw (fun m => paddedHistoryKernel m (p m)) μ n)
      (chainSeqLaw (fun m => paddedHistoryKernel m (fun g => q m (g (j m)))) ν n) (R n) (e n) := by
  have hq' : ∀ m, Measurable fun g : Fin (N + 1) → E => q m (g (j m)) := fun m =>
    (hq m).comp (measurable_pi_apply (j m))
  have : ∀ m (g : Fin (N + 1) → E), IsProbabilityMeasure ((fun g => q m (g (j m))) g) :=
    fun m g => inferInstanceAs (IsProbabilityMeasure (q m (g (j m))))
  exact prokhorovLE_chainSeqLaw (fun m => measurable_paddedHistoryKernel m (hp m))
    (fun m => measurable_paddedHistoryKernel m (hq' m)) hε hη hρ he0 hR he hP
    (fun m h => prokhorovLE_paddedHistoryKernel m (hK m h))
    (fun m => measurable_pi_apply (j m) (hH m)) hμH hG
    (fun m b hb y hy hd A hA =>
      paddedHistoryKernel_le_thickening_add m (j m) (hRr m) le_rfl (hcont m) hb hy hd hA) n

/-- **Joint laws from a common constant history.** As `prokhorovLE_chainSeqLaw_paddedHistory`,
with both chains started from the constant history `fun _ => z`, initial radius `R 0 > 0` and
the error after `n` steps written as `∑_{m < n} (ε m + η m + ρ m)`. -/
theorem prokhorovLE_chainSeqLaw_paddedHistory_const (z : E)
    {p : ℕ → (Fin (N + 1) → E) → Measure E} {q : ℕ → E → Measure E}
    (hp : ∀ n, Measurable (p n)) (hq : ∀ n, Measurable (q n))
    [∀ n h, IsProbabilityMeasure (p n h)] [∀ n x, IsProbabilityMeasure (q n x)]
    (j : ℕ → Fin (N + 1)) {ε r η ρ R : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n) (hη : ∀ n, 0 ≤ η n)
    (hρ : ∀ n, 0 ≤ ρ n) (hR0 : 0 < R 0) (hR : ∀ n, R (n + 1) = ε n + r n)
    (hRr : ∀ n, R n ≤ r n)
    (hK : ∀ n h, ProkhorovLE (p n h) (q n (h (j n))) (ε n) (ε n)) {H G : ℕ → Set E}
    (hH : ∀ n, MeasurableSet (H n))
    (hμH : ∀ n, chainSeqLaw (fun m => paddedHistoryKernel m (p m))
      (Measure.dirac fun _ => z) n {h | h (j n) ∈ H n}ᶜ = 0)
    (hG : ∀ n, chainSeqLaw (fun m => paddedHistoryKernel m (fun g => q m (g (j m))))
      (Measure.dirac fun _ => z) n {h | h (j n) ∈ G n}ᶜ ≤ ENNReal.ofReal (ρ n))
    (hcont : ∀ n, ∀ b ∈ G n, ∀ y ∈ H n, dist y b < R n → ∀ A : Set E, MeasurableSet A →
      q n y A ≤ q n b (thickening (r n) A) + ENNReal.ofReal (η n)) (n : ℕ) :
    ProkhorovLE (chainSeqLaw (fun m => paddedHistoryKernel m (p m)) (Measure.dirac fun _ => z) n)
      (chainSeqLaw (fun m => paddedHistoryKernel m (fun g => q m (g (j m))))
        (Measure.dirac fun _ => z) n) (R n)
      (∑ m ∈ Finset.range n, (ε m + η m + ρ m)) := by
  refine prokhorovLE_chainSeqLaw_paddedHistory (e := fun n => ∑ m ∈ Finset.range n,
    (ε m + η m + ρ m)) hp hq j hε hη hρ (by simp) hR hRr (fun m => ?_) ?_ hK hH hμH hG hcont n
  · simp only [Finset.sum_range_succ]
    ring
  · simpa using prokhorovLE_refl (Measure.dirac fun _ : Fin (N + 1) => z) hR0

end LatticeProb
