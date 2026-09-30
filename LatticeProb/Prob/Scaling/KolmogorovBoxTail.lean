/-
Generic packaging of the library's own Kolmogorov-Chentsov boundedness theorem
(`LatticeProb.kolmogorovBoundPi`, from the module `LatticeProb.Prob.KolmogorovBound`) into a
`Good`/`M`/`hGoodBound`/`hgoodtail` shape suited to a continuum random field built as a
countable increasing union of boxes.

`X` is an arbitrary continuous real-valued field indexed by `Fin k → ℝ` (time-and-space
coordinates combined into one Euclidean index, `k` arbitrary), on an arbitrary probability
space; nothing here mentions any model-specific object.

`LatticeProb.kolmogorovBoundPi` already is the dyadic-chaining Kolmogorov-Chentsov
construction: given a `p`-th moment Hölder bound `E|X u - X v|^p ≤ M · dist(u,v)^q` on a box
with `q` exceeding the box's dimension `k`, it produces an explicit bound `B` such that `X`
stays below `B` on the whole box outside an event of probability at most any prescribed `ε`.
Applying it once per box `n` (with its own moment bound `M n` and exceptional probability
`ε n`) and taking `Good n` to be the complement of the `n`-th exceptional event gives the
family `hGoodBound`/`hgoodtail` needs, with no further dyadic chaining construction required.

Moved from Parking-Sharpness.
-/
import Mathlib
import LatticeProb.Prob.KolmogorovBound

open MeasureTheory Filter Topology
open scoped ENNReal

namespace LatticeProb.Scaling.KolmogorovBoxTail

/-- **From a per-box Kolmogorov-Chentsov moment bound to a summable-tail family of "good"
events on which a continuous field is uniformly bounded on the box.**  `X : (Fin k → ℝ) → Ω → ℝ`
is any continuous field; for each `n`, given the `p`-th moment Hölder bound
`E|X u - X v|^p ≤ M n · dist(u,v)^q` on the box `Icc (a n) (b n)` (same `p`, `q` with
`q > k` for every `n`; `M n` may grow with `n`) and a base-point moment bound at the box's own
corner `a n`, there is a "good" event `Good n` of exceptional probability at most a prescribed
summable `ε n`, on which `X` is bounded by an explicit `Bd n` throughout the box. -/
theorem exists_good_bound_of_moment_bound {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (X : (Fin k → ℝ) → Ω → ℝ) (hXmeas : ∀ u, Measurable (X u))
    (hXcont : ∀ ω, Continuous fun u => X u ω)
    (p q : ℝ) (hp : 0 < p) (hq : (k : ℝ) < q)
    (a b : ℕ → Fin k → ℝ)
    (M : ℕ → ℝ)
    (hint : ∀ n, ∀ u ∈ Set.Icc (a n) (b n), ∀ v ∈ Set.Icc (a n) (b n),
      Integrable (fun ω => |X u ω - X v ω| ^ p) Q)
    (hbound : ∀ n, ∀ u ∈ Set.Icc (a n) (b n), ∀ v ∈ Set.Icc (a n) (b n),
      ∫ ω, |X u ω - X v ω| ^ p ∂Q ≤ M n * dist u v ^ q)
    (hu0int : ∀ n, Integrable (fun ω => |X (a n) ω| ^ p) Q)
    (hu0bound : ∀ n, ∫ ω, |X (a n) ω| ^ p ∂Q ≤ M n)
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hεsum : Summable ε) :
    ∃ (Good : ℕ → Set Ω) (Bd : ℕ → ℝ),
      (∀ n, ∀ ω ∈ Good n, ∀ u ∈ Set.Icc (a n) (b n), |X u ω| ≤ Bd n) ∧
      (∀ n, Q (Good n)ᶜ ≤ ENNReal.ofReal (ε n)) ∧
      (∑' n, Q (Good n)ᶜ ≠ ⊤) := by
  choose Bd hBd using fun n =>
    LatticeProb.kolmogorovBoundPi k (a n) (b n) p q (M n) hp hq (ε n) (hε0 n)
  have hcomp : ∀ n, ({ω | ∀ u ∈ Set.Icc (a n) (b n), |X u ω| ≤ Bd n})ᶜ
      = {ω | ∃ u ∈ Set.Icc (a n) (b n), Bd n < |X u ω|} := by
    intro n
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le]
    tauto
  have hstep : ∀ n, Q ({ω | ∀ u ∈ Set.Icc (a n) (b n), |X u ω| ≤ Bd n})ᶜ ≤ ENNReal.ofReal (ε n) := by
    intro n
    rw [hcomp n]
    exact hBd n Q inferInstance X hXmeas (hint n) (hbound n) (hu0int n) (hu0bound n)
      (fun ω => (hXcont ω).continuousOn)
  refine ⟨fun n => {ω | ∀ u ∈ Set.Icc (a n) (b n), |X u ω| ≤ Bd n}, Bd, ?_, hstep, ?_⟩
  · intro n ω hω u hu
    exact hω u hu
  · have htop : (∑' n, ENNReal.ofReal (ε n)) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hε0 n).le) hεsum]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top htop (ENNReal.tsum_le_tsum hstep)

end LatticeProb.Scaling.KolmogorovBoxTail
