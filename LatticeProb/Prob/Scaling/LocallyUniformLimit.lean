/-
**Monotonicity in one coordinate and joint continuity are closed under locally uniform
limits.**

General-purpose, no probability, no model-specific object: for `f : ι → ℝ × E → ℝ` with every
`f i` continuous and monotone in the first ("time") coordinate, a locally uniform limit `g` of
`f` (along a nontrivial filter) is itself continuous and monotone in the first coordinate.

This is the deterministic half of an argument for the regularity of a scaling-limit value
function `Uc`: if a discrete rescaled field is monotone in time and continuous for every scale,
and it converges in law to `Uc` locally uniformly, then monotonicity in time and joint
continuity are closed properties of a field under locally uniform limits, so the limit law is
carried by monotone continuous fields (Portmanteau at a closed set), and the witness `Uc` is
that field. Continuity is Mathlib's own `TendstoLocallyUniformly.continuous`; monotonicity is
the elementary fact that a pointwise limit of monotone functions is monotone
(`le_of_tendsto_of_tendsto'`, using that `TendstoLocallyUniformly` implies pointwise
convergence, `TendstoLocallyUniformlyOn.tendsto_at`). Applying this lemma requires a genuine
a.s. locally uniform convergence of representative paths, obtained separately from
finite-dimensional convergence, tightness and equicontinuity by Portmanteau/Skorokhod
arguments; this file supplies only the deterministic closure fact, independent of that step.

Moved from Parking-Sharpness.
-/
import Mathlib

open Filter Topology

namespace LatticeProb.Scaling.LocallyUniformLimit

/-- **A locally uniform limit of continuous, time-monotone functions is continuous and
time-monotone.** General: `E` is an arbitrary topological space, `l` an arbitrary nontrivial
filter (`ℕ`'s `atTop`, `ℝ`'s `atTop`, or any other index). -/
theorem continuous_and_monotone_of_tendstoLocallyUniformly
    {E : Type*} [TopologicalSpace E] {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → ℝ × E → ℝ} {g : ℝ × E → ℝ}
    (hfc : ∀ i, Continuous (f i)) (hfmono : ∀ i x, Monotone (fun s => f i (s, x)))
    (hconv : TendstoLocallyUniformly f g l) :
    Continuous g ∧ ∀ x, Monotone (fun s => g (s, x)) := by
  constructor
  · exact hconv.continuous (Filter.Eventually.frequently (Eventually.of_forall hfc))
  · intro x s s' hss'
    have h1 : Tendsto (fun i => f i (s, x)) l (𝓝 (g (s, x))) :=
      hconv.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ (s, x))
    have h2 : Tendsto (fun i => f i (s', x)) l (𝓝 (g (s', x))) :=
      hconv.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ (s', x))
    exact le_of_tendsto_of_tendsto' h1 h2 (fun i => hfmono i x hss')

end LatticeProb.Scaling.LocallyUniformLimit
