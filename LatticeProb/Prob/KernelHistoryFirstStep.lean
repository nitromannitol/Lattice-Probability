import LatticeProb.Prob.KernelProkhorovHistory
import LatticeProb.Prob.KernelProkhorovChainIterate

/-!
# First-step decomposition of the history law of a Markov chain

For a Markov kernel `κ` on `E` and a starting point `x`, `chainHistoryLaw κ N x` is the law of the
first `N + 1` positions `(X₀, …, X_N)` of the chain of `κ` started at `x`, built forwards in time:
it is the `N`-th law of the chain on histories `Fin (N + 1) → E` whose `n`-th step samples the next
position from `κ` at the last coordinate and pads the history after `n` (`paddedHistoryKernel`),
started from the constant history `fun _ => x`.

The main result is the first-step (backward) decomposition
`chainHistoryLaw κ (N + 1) z = ((κ z).bind (chainHistoryLaw κ N)).map (consHistory z)`:
the history of length `N + 2` started at `z` is `z` followed by the history of length `N + 1`
started at a point sampled from `κ z`. Consequently any family of laws with the same initial value
and the same first-step recursion is the history law (`eq_chainHistoryLaw_of_succ`); this is how the
joint law of the positions of a strong Markov process at successive stopping times is identified
with the history law of its one-step kernel, using the strong Markov property only at the first
stopping time.

## Main results

* `chainSeqLaw_succ_eq_shift`, `chainSeqLaw_bind`: splitting off the first step of a
  time-inhomogeneous chain, and linearity in the initial law.
* `consHistory`, `padAfter_succ_consHistory`, `paddedHistoryKernel_succ_consHistory`.
* `chainHistoryLaw`, `measurable_chainHistoryLaw`, `chainHistoryLaw_succ`,
  `eq_chainHistoryLaw_of_succ`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

section Cons

variable {E : Type*} {N : ℕ}

/-- The history `g` of length `N + 1` preceded by the position `z`. -/
def consHistory (z : E) (g : Fin (N + 1) → E) : Fin (N + 1 + 1) → E :=
  Fin.cons z g

@[simp]
theorem consHistory_zero (z : E) (g : Fin (N + 1) → E) : consHistory z g 0 = z :=
  Fin.cons_zero _ _

@[simp]
theorem consHistory_succ (z : E) (g : Fin (N + 1) → E) (i : Fin (N + 1)) :
    consHistory z g i.succ = g i :=
  Fin.cons_succ _ _ _

theorem consHistory_last (z : E) (g : Fin (N + 1) → E) :
    consHistory z g (Fin.last (N + 1)) = g (Fin.last N) := by
  rw [← Fin.succ_last, consHistory_succ]

/-- Padding commutes with prepending a position, with the padding index shifted by one. -/
theorem padAfter_succ_consHistory (m : ℕ) (z : E) (g : Fin (N + 1) → E) (x : E) :
    padAfter (m + 1) (consHistory z g) x = consHistory z (padAfter m g x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [padAfter]
  · simp [padAfter, Fin.val_succ]

/-- The constant history padded after the first coordinate. -/
theorem padAfter_zero_const (z x : E) :
    padAfter 0 (fun _ : Fin (N + 1 + 1) => z) x = consHistory z (fun _ : Fin (N + 1) => x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [padAfter]
  · simp [padAfter, Fin.val_succ]

end Cons

section Measure

variable {E F G : Type*} [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]

/-- The image of a mixture is the mixture of the images. -/
theorem map_bind_eq_bind_map {μ : Measure E} {K : E → Measure F} (hK : Measurable K) {f : F → G}
    (hf : Measurable f) : (μ.bind K).map f = μ.bind fun x => (K x).map f := by
  have hm : Measurable fun x => (K x).map f := (Measure.measurable_map f hf).comp hK
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) hK.aemeasurable,
    Measure.bind_apply hs hm.aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply hf hs]

/-- A mixture over an image law is the mixture of the composed kernel. -/
theorem bind_map_eq_bind_comp {μ : Measure E} {f : E → F} (hf : Measurable f) {K : F → Measure G}
    (hK : Measurable K) : (μ.map f).bind K = μ.bind fun x => K (f x) := by
  have hm : Measurable fun x => K (f x) := hK.comp hf
  ext s hs
  have hKs : Measurable fun y => K y s := (Measure.measurable_coe hs).comp hK
  rw [Measure.bind_apply hs hK.aemeasurable, Measure.bind_apply hs hm.aemeasurable,
    lintegral_map hKs hf]

/-- An image law as a mixture of Dirac masses. -/
theorem map_eq_bind_dirac {μ : Measure E} {f : E → F} (hf : Measurable f) :
    μ.map f = μ.bind fun x => Measure.dirac (f x) := by
  have hm : Measurable fun x => Measure.dirac (f x) := Measure.measurable_dirac.comp hf
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply hs hm.aemeasurable,
    ← lintegral_indicator_one (hf hs)]
  refine lintegral_congr fun x => ?_
  rw [Measure.dirac_apply' _ hs]
  rfl

end Measure

section Chain

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- **Splitting off the first step** of a time-inhomogeneous chain. -/
theorem chainSeqLaw_succ_eq_shift (κ : ℕ → E → Measure E) (μ : Measure E) (m : ℕ) :
    chainSeqLaw κ μ (m + 1) = chainSeqLaw (fun k => κ (k + 1)) (μ.bind (κ 0)) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [chainSeqLaw_succ, ih]; rfl

theorem measurable_chainSeqLaw_comp {κ : ℕ → E → Measure E} (hκ : ∀ n, Measurable (κ n))
    {ρ : F → Measure E} (hρ : Measurable ρ) (m : ℕ) :
    Measurable fun x => chainSeqLaw κ (ρ x) m := by
  induction m with
  | zero => exact hρ
  | succ m ih => exact (Measure.measurable_bind' (hκ m)).comp ih

/-- **Linearity in the initial law**: the chain started from a mixture is the mixture of the
chains. -/
theorem chainSeqLaw_bind {κ : ℕ → E → Measure E} (hκ : ∀ n, Measurable (κ n)) (μ : Measure F)
    {ρ : F → Measure E} (hρ : Measurable ρ) (m : ℕ) :
    chainSeqLaw κ (μ.bind ρ) m = μ.bind fun x => chainSeqLaw κ (ρ x) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [chainSeqLaw_succ, ih, Measure.bind_bind (measurable_chainSeqLaw_comp hκ hρ m).aemeasurable
      (hκ m).aemeasurable]
    rfl

end Chain

section History

variable {E : Type*} [MeasurableSpace E] {N : ℕ}

theorem measurable_consHistory (z : E) :
    Measurable (consHistory (N := N) z) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using measurable_pi_apply j

theorem measurable_const_history : Measurable fun x : E => fun _ : Fin (N + 1) => x :=
  measurable_pi_iff.2 fun _ => measurable_id

/-- The position kernel reading the last coordinate of a history. -/
theorem measurable_lastPositionKernel {κ : E → Measure E} (hκ : Measurable κ) :
    Measurable fun h : Fin (N + 1) → E => κ (h (Fin.last N)) :=
  hκ.comp (measurable_pi_apply _)

/-- Prepending a position commutes with one padded step of the chain of `κ`. -/
theorem paddedHistoryKernel_succ_consHistory (κ : E → Measure E) (m : ℕ) (z : E)
    (g : Fin (N + 1) → E) :
    paddedHistoryKernel (m + 1) (fun h : Fin (N + 1 + 1) → E => κ (h (Fin.last (N + 1))))
        (consHistory z g) =
      (paddedHistoryKernel m (fun h : Fin (N + 1) → E => κ (h (Fin.last N))) g).map
        (consHistory z) := by
  simp only [paddedHistoryKernel]
  rw [Measure.map_map (measurable_consHistory z) (measurable_padAfter m g), consHistory_last]
  congr 1
  funext x
  exact padAfter_succ_consHistory m z g x

/-- The padded history chain with the step index shifted by one, started from histories with a
prepended position. -/
theorem chainSeqLaw_paddedHistory_map_consHistory {κ : E → Measure E} (hκ : Measurable κ)
    [∀ x, IsProbabilityMeasure (κ x)] (z : E) (ν : Measure (Fin (N + 1) → E)) (m : ℕ) :
    chainSeqLaw (fun k => paddedHistoryKernel (k + 1)
        (fun h : Fin (N + 1 + 1) → E => κ (h (Fin.last (N + 1))))) (ν.map (consHistory z)) m =
      (chainSeqLaw (fun k => paddedHistoryKernel k
        (fun h : Fin (N + 1) → E => κ (h (Fin.last N)))) ν m).map (consHistory z) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [chainSeqLaw_succ, chainSeqLaw_succ, ih,
      bind_map_eq_bind_comp (measurable_consHistory z)
        (measurable_paddedHistoryKernel (m + 1) (measurable_lastPositionKernel hκ)),
      map_bind_eq_bind_map (measurable_paddedHistoryKernel m (measurable_lastPositionKernel hκ))
        (measurable_consHistory z)]
    congr 1
    funext g
    exact paddedHistoryKernel_succ_consHistory κ m z g

/-- The law of the first `N + 1` positions of the chain of `κ` started at `x`, as the `N`-th law
of the padded history chain started from the constant history. -/
noncomputable def chainHistoryLaw (κ : E → Measure E) (N : ℕ) (x : E) :
    Measure (Fin (N + 1) → E) :=
  chainSeqLaw (fun m => paddedHistoryKernel m fun h : Fin (N + 1) → E => κ (h (Fin.last N)))
    (Measure.dirac fun _ => x) N

theorem chainHistoryLaw_zero (κ : E → Measure E) (x : E) :
    chainHistoryLaw κ 0 x = Measure.dirac fun _ => x :=
  rfl

theorem measurable_chainHistoryLaw {κ : E → Measure E} (hκ : Measurable κ)
    [∀ x, IsProbabilityMeasure (κ x)] (N : ℕ) : Measurable (chainHistoryLaw κ N) :=
  measurable_chainSeqLaw_comp
    (fun m => measurable_paddedHistoryKernel m (measurable_lastPositionKernel hκ))
    (Measure.measurable_dirac.comp measurable_const_history) N

/-- **First-step decomposition of the history law**: the history of length `N + 2` started at `z`
is `z` followed by the history of length `N + 1` started at a point sampled from `κ z`. -/
theorem chainHistoryLaw_succ {κ : E → Measure E} (hκ : Measurable κ)
    [∀ x, IsProbabilityMeasure (κ x)] (N : ℕ) (z : E) :
    chainHistoryLaw κ (N + 1) z = ((κ z).bind (chainHistoryLaw κ N)).map (consHistory z) := by
  have h0 : paddedHistoryKernel 0
      (fun h : Fin (N + 1 + 1) → E => κ (h (Fin.last (N + 1)))) (fun _ => z) =
      ((κ z).map fun x => fun _ : Fin (N + 1) => x).map (consHistory z) := by
    rw [Measure.map_map (measurable_consHistory z) measurable_const_history]
    simp only [paddedHistoryKernel]
    congr 1
    funext x
    exact padAfter_zero_const z x
  have hd : Measurable fun x : E => Measure.dirac fun _ : Fin (N + 1) => x :=
    Measure.measurable_dirac.comp measurable_const_history
  have hL : chainHistoryLaw κ (N + 1) z =
      chainSeqLaw (fun m => paddedHistoryKernel m
        fun h : Fin (N + 1 + 1) → E => κ (h (Fin.last (N + 1)))) (Measure.dirac fun _ => z)
        (N + 1) := rfl
  rw [hL, chainSeqLaw_succ_eq_shift,
    Measure.dirac_bind (measurable_paddedHistoryKernel 0 (measurable_lastPositionKernel hκ)), h0,
    chainSeqLaw_paddedHistory_map_consHistory hκ z, map_eq_bind_dirac measurable_const_history,
    chainSeqLaw_bind (fun m => measurable_paddedHistoryKernel m (measurable_lastPositionKernel hκ))
      _ hd]
  rfl

/-- **Identification by the first-step recursion**: a family of laws of histories that starts
from the Dirac mass at the constant history and satisfies the first-step recursion of `κ` is the
history law of `κ`. -/
theorem eq_chainHistoryLaw_of_succ {κ : E → Measure E} (hκ : Measurable κ)
    [∀ x, IsProbabilityMeasure (κ x)] (L : (N : ℕ) → E → Measure (Fin (N + 1) → E))
    (h0 : ∀ x, L 0 x = Measure.dirac fun _ => x)
    (hsucc : ∀ N z, L (N + 1) z = ((κ z).bind (L N)).map (consHistory z)) (N : ℕ) :
    L N = chainHistoryLaw κ N := by
  induction N with
  | zero => funext x; exact h0 x
  | succ N ih => funext z; rw [hsucc, ih, chainHistoryLaw_succ hκ]

theorem isProbabilityMeasure_chainHistoryLaw {κ : E → Measure E} (hκ : Measurable κ)
    [∀ x, IsProbabilityMeasure (κ x)] (N : ℕ) (x : E) :
    IsProbabilityMeasure (chainHistoryLaw κ N x) :=
  isProbabilityMeasure_chainSeqLaw
    (fun m => measurable_paddedHistoryKernel m (measurable_lastPositionKernel hκ)) N

end History

end LatticeProb
