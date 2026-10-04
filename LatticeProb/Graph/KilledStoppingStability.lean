/-
# Stability of killed optimal-stopping values

A bounded start on `Sandpile.External.CubeStoppingStability`, the cited input of
`rem:dlt4-killed-scaling` (`sandpile.tex:1929-1950`) and of the two nodes that carry it
(`rem-dlt4-killed-scaling` and `thm-d23-critical-level-percolation`).  The paper cites it to
Coquet and Toldo, *Convergence of values in optimal stopping and convergence of optimal
stopping times*, EJP 12 (2007), Theorem 3 and Corollary 4: the stability of optimal-stopping
values under uniform convergence of bounded rewards, together with the invariance principle
for the stopped walk, applied with both problems killed on exiting a cube.

## What this file contains

1. **The killed value for an arbitrary terminal reward**, in the library's own graph vocabulary.
   `LatticeProb.Graph.killedStopValues` (`LatticeProb/Graph/Killed.lean`) is the killed value of
   the specific scenery payoff.  The paper's killed problem has an arbitrary reward evaluated at
   the stopping position, so the general set `killedRewardValues` and its value
   `killedRewardValue` are recorded here, with the same killing condition as
   `Sandpile.killedSet`: the stopping time `τ ≤ n` must not have left `D` strictly before it
   stops.

2. **The smallest independent sub-lemma, proved.**  `abs_killedRewardValue_sub_le`: the killed
   value is `1`-Lipschitz in the reward under the uniform norm.  This is the whole content of the
   "stability of optimal-stopping values under uniform convergence of bounded rewards" half of
   the cited theorem on the discrete side; it uses no Brownian motion, no invariance principle,
   and no comparison between the two problems.  `abs_killedRewardValue_sub_le_of_bdd` discharges
   the two bounded-above hypotheses from pointwise bounds on the rewards.

3. **The target statement.**  `LatticeProb.CubeStopping.CubeStoppingStability` is the library
   analogue of the frozen `Sandpile.External.CubeStoppingStability`, with the discrete side read
   through `killedRewardValue` on `lattice d` and the continuum side through the cube-killed
   Brownian discount `cubeDiscount` introduced in this file over `EuclideanSpace ℝ (Fin d)` and
   `IsBrownianSpace`.

4. **Well-posedness of the continuum value.**  `cubePayoffs_nonempty`, `bddAbove_cubePayoffs`
   and the measurability/integrability lemmas below make the `sSup` in `cubeDiscount` genuine in
   the `CubeStoppingStability` context: the payoff set is nonempty and bounded above, hence
   `cubeDiscount` is its least upper bound.

## The exact remaining gap

The sub-lemma of item 2 is proved, and the continuum side is now well posed: in the
`CubeStoppingStability` context the `cubeDiscount` payoff set is nonempty and bounded above
(`cubePayoffs_nonempty`, `bddAbove_cubePayoffs`, `integrable_stopped_payoff_of_bounded`,
`cubeDiscount_genuine_of_continuous`, `isLUB_cubePayoffs_of_continuous`), so its `sSup` is
genuine.  What the *whole* `CubeStoppingStability` still needs is the other half of
Coquet-Toldo, and this file deliberately stops there.

- **The invariance principle for the killed stopped walk.**  From
  `LatticeProb.Graph.Zd.localizedStopping'` the killed discrete problem is the value of the
  killed walk; what is missing is the convergence of its *law* under the parabolic rescaling
  `X_k ↦ X_k / R`, killed on the box, to `IsBrownianSpace` on `EuclideanSpace ℝ (Fin d)` killed on
  the cube.  The library has the walk side (`Graph/ZdKilled.lean`, `Graph/Killed.lean`), the
  Brownian side (`Prob/BrownianExit.lean`, `Prob/BrownianContAll.lean`), and the finite-dimensional
  invariance principle (`Prob/Scaling/`, `Prob/Invariance.lean`), but not the killed-process
  invariance principle.
- **Matching the two killed rule families.**  Even with both invariance principles, the
  comparison of the two suprema needs the *same* stopping rule realized on both sides, i.e. the
  coupling of the killed discrete walk to the killed Brownian motion, uniform over the compact
  set of starting points and the horizon window.  `abs_killedRewardValue_sub_le` is the
  order-theoretic tool the comparison uses once the coupling is available; it does not supply the
  coupling.
- **Resolved: the continuum `sSup` is genuine.**  `cubePayoffs_nonempty` (the rule that stops
  at time `0`) and `bddAbove_cubePayoffs`, with `integrable_stopped_payoff_of_bounded` supplying
  the integrability of a continuous bounded stopped payoff from the stopped-position
  measurability `aemeasurable_stopped_position`, give that in the `CubeStoppingStability` context
  the payoff set is nonempty and bounded above, so `cubeDiscount` is the genuine least upper
  bound of its payoff set (`isLUB_cubePayoffs_of_continuous`, `cubeDiscount_genuine_in_context`).
  Nothing further is needed for well-posedness.

The frozen `Sandpile.External.CubeStoppingStability` and every frozen statement of the paper
repository are untouched: this file only states the library analogue and proves the sub-lemma.
-/

import LatticeProb.Graph.Killed
import LatticeProb.Graph.Zd
import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.BrownianMarkov

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

namespace Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The killed optimal-stopping value of an arbitrary terminal reward -/

/-- The payoffs `E_x[F(τ,X)]` attained by the stopping times `τ ≤ n` which have not left `D`
strictly before they stop.  This is `LatticeProb.Graph.killedStopValues` with the scenery payoff
replaced by an arbitrary terminal reward `F`. -/
def killedRewardValues (G : SimpleGraph V) [G.LocallyFinite] (D : Set V)
    (F : ℕ → (ℕ → V) → ℝ) (n : ℕ) (x : V) : Set ℝ :=
  {a : ℝ | ∃ τ : (ℕ → V) → ℕ, IsStopping τ ∧ (∀ X, τ X ≤ n) ∧
    (∀ X, ∀ j < τ X, X j ∈ D) ∧ a = walkExp G n x (fun X => F (τ X) X)}

/-- The value `sup_τ E_x[F(τ,X)]` of the problem killed on leaving `D`. -/
noncomputable def killedRewardValue (G : SimpleGraph V) [G.LocallyFinite] (D : Set V)
    (F : ℕ → (ℕ → V) → ℝ) (n : ℕ) (x : V) : ℝ :=
  sSup (killedRewardValues G D F n x)

/-- `killedRewardValue` unfolds to the supremum of `killedRewardValues`. -/
theorem killedRewardValue_eq_sSup (D : Set V) (F : ℕ → (ℕ → V) → ℝ) (n : ℕ) (x : V) :
    killedRewardValue G D F n x = sSup (killedRewardValues G D F n x) := rfl

/-- The killed reward set is nonempty: `τ = 0` is admissible. -/
theorem killedRewardValues_nonempty (D : Set V) (F : ℕ → (ℕ → V) → ℝ) (n : ℕ) (x : V) :
    (killedRewardValues G D F n x).Nonempty :=
  ⟨_, ⟨fun _ => 0, fun _ _ _ _ h => h, fun _ => Nat.zero_le n,
    fun X j hj => absurd hj (by simp), rfl⟩⟩

/-- A pointwise bound on the reward bounds the killed reward set above. -/
theorem bddAbove_killedRewardValues (hdeg : ∀ v : V, 0 < G.degree v)
    (D : Set V) (F : ℕ → (ℕ → V) → ℝ) (n : ℕ) (x : V) (M : ℝ)
    (hF : ∀ k ≤ n, ∀ X : ℕ → V, |F k X| ≤ M) :
    BddAbove (killedRewardValues G D F n x) := by
  refine ⟨M, ?_⟩
  rintro a ⟨τ, hτ, hτn, hkill, rfl⟩
  have hle : ∀ X : ℕ → V, F (τ X) X ≤ M := fun X =>
    le_trans (le_abs_self _) (hF (τ X) (hτn X) X)
  calc walkExp G n x (fun X => F (τ X) X)
      ≤ walkExp G n x (fun _ => M) := walkExp_mono hle
    _ = M := walkExp_const' hdeg n x M

/-! ### The smallest independent sub-lemma: `1`-Lipschitz stability in the reward -/

/-- **The killed value is `1`-Lipschitz in the reward.**  If two rewards agree to within `E`
pointwise on every time `k ≤ n` and every trajectory, then the two killed values differ by at
most `E`.  This is the discrete, deterministic half of Coquet-Toldo's stability theorem: a
supremum of integrals of rewards within `E` of each other moves by at most `E`. -/
theorem abs_killedRewardValue_sub_le (hdeg : ∀ v : V, 0 < G.degree v)
    (D : Set V) (F F' : ℕ → (ℕ → V) → ℝ) (n : ℕ) (x : V)
    (E : ℝ)
    (hbdd : BddAbove (killedRewardValues G D F n x))
    (hbdd' : BddAbove (killedRewardValues G D F' n x))
    (hFF' : ∀ k ≤ n, ∀ X : ℕ → V, |F k X - F' k X| ≤ E) :
    |killedRewardValue G D F n x - killedRewardValue G D F' n x| ≤ E := by
  rw [killedRewardValue_eq_sSup, killedRewardValue_eq_sSup, abs_sub_le_iff]
  have hconst : ∀ c : ℝ, walkExp G n x (fun _ : ℕ → V => c) = c :=
    fun c => walkExp_const' hdeg n x c
  have hwalk : ∀ (τ : (ℕ → V) → ℕ) (_hτ : IsStopping τ) (hτn : ∀ X, τ X ≤ n)
      (_hkill : ∀ X, ∀ j < τ X, X j ∈ D),
      walkExp G n x (fun X => F (τ X) X) ≤ walkExp G n x (fun X => F' (τ X) X) + E := by
    intro τ _hτ hτn _hkill
    have hpt : ∀ X : ℕ → V, F (τ X) X ≤ F' (τ X) X + E := by
      intro X
      have h := hFF' (τ X) (hτn X) X
      rw [abs_le] at h
      linarith [h.1]
    calc walkExp G n x (fun X => F (τ X) X)
        ≤ walkExp G n x (fun X => F' (τ X) X + E) := walkExp_mono hpt
      _ = walkExp G n x (fun X => F' (τ X) X) + E := by
          rw [walkExp_add (F := fun X => F' (τ X) X) (F' := fun _ => E), hconst E]
  have hwalk' : ∀ (τ : (ℕ → V) → ℕ) (_hτ : IsStopping τ) (hτn : ∀ X, τ X ≤ n)
      (_hkill : ∀ X, ∀ j < τ X, X j ∈ D),
      walkExp G n x (fun X => F' (τ X) X) ≤ walkExp G n x (fun X => F (τ X) X) + E := by
    intro τ _hτ hτn _hkill
    have hpt : ∀ X : ℕ → V, F' (τ X) X ≤ F (τ X) X + E := by
      intro X
      have h := hFF' (τ X) (hτn X) X
      rw [abs_le] at h
      linarith [h.2]
    calc walkExp G n x (fun X => F' (τ X) X)
        ≤ walkExp G n x (fun X => F (τ X) X + E) := walkExp_mono hpt
      _ = walkExp G n x (fun X => F (τ X) X) + E := by
          rw [walkExp_add (F := fun X => F (τ X) X) (F' := fun _ => E), hconst E]
  constructor
  · refine sub_le_iff_le_add.2
      (csSup_le (killedRewardValues_nonempty D F n x) ?_)
    rintro a ⟨τ, hτ, hτn, hkill, rfl⟩
    have h1 := hwalk τ hτ hτn hkill
    have h2 : walkExp G n x (fun X => F' (τ X) X) ≤ sSup (killedRewardValues G D F' n x) :=
      le_csSup hbdd' ⟨τ, hτ, hτn, hkill, rfl⟩
    linarith
  · refine sub_le_iff_le_add.2
      (csSup_le (killedRewardValues_nonempty D F' n x) ?_)
    rintro a ⟨τ, hτ, hτn, hkill, rfl⟩
    have h1 := hwalk' τ hτ hτn hkill
    have h2 : walkExp G n x (fun X => F (τ X) X) ≤ sSup (killedRewardValues G D F n x) :=
      le_csSup hbdd ⟨τ, hτ, hτn, hkill, rfl⟩
    linarith

/-- **The killed value is `1`-Lipschitz in the reward**, with the bounded-above hypotheses
discharged from pointwise bounds on the two rewards. -/
theorem abs_killedRewardValue_sub_le_of_bdd (hdeg : ∀ v : V, 0 < G.degree v)
    (D : Set V) (F F' : ℕ → (ℕ → V) → ℝ) (n : ℕ) (x : V) (E M M' : ℝ)
    (hF : ∀ k ≤ n, ∀ X : ℕ → V, |F k X| ≤ M)
    (hF' : ∀ k ≤ n, ∀ X : ℕ → V, |F' k X| ≤ M')
    (hFF' : ∀ k ≤ n, ∀ X : ℕ → V, |F k X - F' k X| ≤ E) :
    |killedRewardValue G D F n x - killedRewardValue G D F' n x| ≤ E :=
  abs_killedRewardValue_sub_le (G := G) hdeg D F F' n x E
    (bddAbove_killedRewardValues (G := G) hdeg D F n x M hF)
    (bddAbove_killedRewardValues (G := G) hdeg D F' n x M' hF') hFF'

end Graph

/-! ### The continuum cube-killed discount, and the target statement -/

namespace CubeStopping

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stopping rule of the natural filtration of a Brownian motion whose slices are strongly
measurable.  This is the library's `natFiltration` stopping class; the strong measurability is
supplied by a version of the motion with continuous paths
(`LatticeProb.IsBrownianSpace.cont` and `LatticeProb.exists_isBrownianSpace_cont`). -/
def IsBrownianStopping {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : ∀ t, StronglyMeasurable (B t)) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime (natFiltration B hB) fun ω => (τ ω : ℝ≥0∞)

/-- The payoffs attainable in the cube-killed Brownian discount: the payoffs of the stopping
rules bounded by `T` which have not left the cube of half-width `L` about `u` strictly before
they stop.  This is `Sandpile.Continuum.cubeStoppingPayoffs` in the library's Brownian
vocabulary. -/
def cubePayoffs {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : ∀ t, StronglyMeasurable (B t)) (P : Measure Ω)
    (h : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (T L : ℝ) (u : EuclideanSpace ℝ (Fin d)) : Set ℝ :=
  {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B hB τ ∧ (∀ ω, (τ ω : ℝ) ≤ T) ∧
    (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L) ∧
    a = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P}

/-- The cube-killed Brownian discount `𝒟_{h,□}(T,u)`. -/
noncomputable def cubeDiscount {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : ∀ t, StronglyMeasurable (B t)) (P : Measure Ω)
    (h : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (T L : ℝ) (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup (cubePayoffs B hB P h T L u)

/-- The cube-killed payoff set is nonempty: the rule that stops at time `0` is admissible when
`0 ≤ T`, so `cubeDiscount`'s `sSup` is never `sSup ∅ = 0`. -/
theorem cubePayoffs_nonempty {d : ℕ} (B : NNReal → Ω → EuclideanSpace ℝ (Fin d))
    (hB : ∀ t, StronglyMeasurable (B t)) (P : Measure Ω)
    (h : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (T L : ℝ) (u : EuclideanSpace ℝ (Fin d))
    (hT : 0 ≤ T) :
    (cubePayoffs B hB P h T L u).Nonempty := by
  refine ⟨∫ ω, -h (T - 0) (B 0 ω) ∂P, ?_⟩
  refine ⟨fun _ => (0 : NNReal), ?_, ?_, ?_, rfl⟩
  · rw [IsBrownianStopping, IsStoppingTime]
    intro t
    simp
  · intro ω; simpa using hT
  · filter_upwards with ω s hs
    exact absurd hs (not_lt.mpr (by simp))

/-- The cube-killed payoff set is bounded above as soon as the reward is bounded and the
integrand is integrable for every admissible stopping rule. -/
theorem bddAbove_cubePayoffs {d : ℕ} (B : NNReal → Ω → EuclideanSpace ℝ (Fin d))
    (hB : ∀ t, StronglyMeasurable (B t)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (T L M : ℝ) (u : EuclideanSpace ℝ (Fin d))
    (hb : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin d)), |h s y| ≤ M)
    (hint : ∀ τ : Ω → NNReal, IsBrownianStopping B hB τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P) :
    BddAbove (cubePayoffs B hB P h T L u) := by
  refine ⟨M, ?_⟩
  rintro a ⟨τ, hτ, hτT, _hcube, rfl⟩
  calc ∫ ω, -h (T - (τ ω : ℝ)) (B (τ ω) ω) ∂P ≤ ∫ _ω : Ω, M ∂P := by
        refine integral_mono (hint τ hτ hτT) (integrable_const M) ?_
        intro ω
        exact le_trans (neg_le_abs _) (hb _ _)
    _ = M := by simp

/-! ### Well-posedness in the `CubeStoppingStability` context -/

/-- A `natFiltration` Brownian stopping time is measurable for the ambient σ-algebra. -/
theorem measurable_of_isBrownianStopping {d : ℕ} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {hB : ∀ t, StronglyMeasurable (B t)} {τ : Ω → ℝ≥0} (hτ : IsBrownianStopping B hB τ) :
    Measurable τ :=
  measurable_coe_nnreal_ennreal_iff.1 hτ.measurable'

/-- The stopped position `ω ↦ B (τ ω) ω` is almost-everywhere measurable, from
almost-everywhere continuity of the paths and almost-everywhere measurability of the stopping
time.  Off the null set of discontinuous paths `B` is replaced by the identically zero process,
which is jointly measurable, and the two agree almost everywhere. -/
theorem aemeasurable_stopped_position {d : ℕ} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {τ : Ω → ℝ≥0} (P : Measure Ω)
    (hm : ∀ t, AEMeasurable (B t) P) (hc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (hτ : AEMeasurable τ P) : AEMeasurable (fun ω => B (τ ω) ω) P := by
  classical
  let S : Set Ω := {ω | Continuous fun t => B t ω}
  have hS : NullMeasurableSet S P := by
    simpa only [compl_compl] using
      (NullMeasurableSet.of_null (show P Sᶜ = 0 from ae_iff.1 hc)).compl
  let C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d) :=
    fun t => S.piecewise (B t) (fun _ => 0)
  have hmC : ∀ t, @Measurable (NullMeasurableSpace Ω P) (EuclideanSpace ℝ (Fin d))
      inferInstance inferInstance (C t) := fun t =>
    (hm t).nullMeasurable.measurable'.piecewise hS measurable_const
  have hcC : ∀ ω, Continuous fun t => C t ω := by
    intro ω
    by_cases hω : ω ∈ S
    · simpa only [C, Set.piecewise, if_pos hω] using
        (show Continuous (fun t => B t ω) from hω)
    · simpa only [C, Set.piecewise, if_neg hω] using
        (continuous_const : Continuous fun _ : ℝ≥0 => (0 : EuclideanSpace ℝ (Fin d)))
  have hY : NullMeasurable (fun ω => C (τ ω) ω) P :=
    (measurable_uncurry_of_continuous_of_measurable hcC hmC).comp
      (hτ.nullMeasurable.measurable'.prodMk measurable_id)
  refine hY.aemeasurable.congr ?_
  filter_upwards [hc] with ω hω
  exact if_pos hω

/-- A stopped payoff with a continuous reward and a Brownian stopping time is almost-everywhere
measurable. -/
theorem aemeasurable_stopped_payoff {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω}
    (hB : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    {τ : Ω → ℝ≥0} (hτ : IsBrownianStopping B hB τ)
    (G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin d) => G q.1 q.2)) (T : ℝ) :
    AEMeasurable (fun ω => G (T - τ ω) (B (τ ω) ω)) P := by
  have ht : AEMeasurable τ P := (measurable_of_isBrownianStopping hτ).aemeasurable
  have hY : AEMeasurable (fun ω => B (τ ω) ω) P :=
    aemeasurable_stopped_position P (fun t => (hB t).aemeasurable) hcont ht
  exact hG.measurable.comp_aemeasurable
    (((aemeasurable_const (b := T)).sub
      (measurable_coe_nnreal_real.comp_aemeasurable ht)).prodMk hY)

/-- A stopped payoff with a continuous bounded reward is integrable, by comparison with the
constant reward bound. -/
theorem integrable_stopped_payoff_of_bounded {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} [IsFiniteMeasure P]
    (hB : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    {τ : Ω → ℝ≥0} (hτ : IsBrownianStopping B hB τ)
    (G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin d) => G q.1 q.2))
    (T M : ℝ) (hGM : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin d)), |G s y| ≤ M) :
    Integrable (fun ω => G (T - τ ω) (B (τ ω) ω)) P :=
  Integrable.of_bound (aemeasurable_stopped_payoff hB hcont hτ G hG T).aestronglyMeasurable M <| by
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hGM _ _

/-- **`cubeDiscount` is genuine when the reward is continuous and bounded**: the cube-killed
payoff set is nonempty and bounded above, so its `sSup` is not a junk value. -/
theorem cubeDiscount_genuine_of_continuous {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin d) => G q.1 q.2))
    (T L M : ℝ) (hT : 0 ≤ T) (u : EuclideanSpace ℝ (Fin d))
    (hGM : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin d)), |G s y| ≤ M) :
    (cubePayoffs B hB P (fun s y => -G s y) T L u).Nonempty ∧
      BddAbove (cubePayoffs B hB P (fun s y => -G s y) T L u) :=
  ⟨cubePayoffs_nonempty B hB P (fun s y => -G s y) T L u hT,
    bddAbove_cubePayoffs B hB P (fun s y => -G s y) T L M u
      (fun s y => by simpa using hGM s y)
      (fun τ hτ _hτT => by
        simpa using integrable_stopped_payoff_of_bounded hB hcont hτ G hG T M hGM)⟩

/-- **The cube-killed discount is the least upper bound of its payoff set** in the
`CubeStoppingStability` context, so it is the genuine value of the killed stopping problem. -/
theorem isLUB_cubePayoffs_of_continuous {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin d) => G q.1 q.2))
    (T L M : ℝ) (hT : 0 ≤ T) (u : EuclideanSpace ℝ (Fin d))
    (hGM : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin d)), |G s y| ≤ M) :
    IsLUB (cubePayoffs B hB P (fun s y => -G s y) T L u)
      (cubeDiscount B hB P (fun s y => -G s y) T L u) := by
  obtain ⟨hne, hbdd⟩ := cubeDiscount_genuine_of_continuous hB hcont G hG T L M hT u hGM
  simpa [cubeDiscount] using isLUB_csSup hne hbdd

/-- The `CubeStoppingStability` context: for the family `B` indexed by the starting point, the
continuous reward `G` bounded by `M`, and a horizon `T ≥ 0`, the `cubeDiscount` appearing in the
statement is the genuine least upper bound of its payoff set. -/
theorem cubeDiscount_genuine_in_context {d : ℕ}
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : EuclideanSpace ℝ (Fin d) → ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d))
    (hBrown : ∀ y : EuclideanSpace ℝ (Fin d), IsBrownianSpace d y (B y) PB)
    (hBsm : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0), StronglyMeasurable (B y t))
    (G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin d) => G q.1 q.2))
    (T L M : ℝ) (hT : 0 ≤ T) (x : EuclideanSpace ℝ (Fin d))
    (hGM : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin d)), |G s y| ≤ M) :
    (cubePayoffs (B x) (hBsm x) PB (fun s y => -G s y) T L x).Nonempty ∧
      BddAbove (cubePayoffs (B x) (hBsm x) PB (fun s y => -G s y) T L x) :=
  cubeDiscount_genuine_of_continuous (hBsm x) ((hBrown x).cont) G hG T L M hT x hGM


/-- The lattice box `Q(⌊Rx⌋,R)` of the paper, as the ball of radius `R` for the
`ℓ^∞` metric about a lattice site. -/
def latticeBox {d : ℕ} (x : Site d) (R : ℝ) : Set (Site d) :=
  {y | ∀ i, |(y i : ℝ) - (x i : ℝ)| ≤ R}

/-- The site `⌊Rx⌋` of the paper: the coordinatewise floor of `R x`. -/
noncomputable def floorSite {d : ℕ} (R : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Site d :=
  fun i => ⌊R * x i⌋

/-- The rescaled site `X_k / R`, read as a point of `ℝ^d`.  This is
`Sandpile.External.Lclt.scaledSite` in the library's `EuclideanSpace`. -/
noncomputable def scaledSite {d : ℕ} (R : ℝ) (y : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i : Fin d => (y i : ℝ) / R)

/-- **The library statement of cube-killed optimal-stopping stability.**  This is the
`Sandpile.External.CubeStoppingStability` statement read in the vocabulary of this library:
the discrete value is `killedRewardValue` on the lattice box, the continuum value is
`cubeDiscount` of the Brownian motion killed on the cube of half-width one, and the conclusion
is the `ε`-`R₀` form of the comparison, uniform over the horizon window `[T₀,T₁]` and the
compact set `K` of starting points.  The two halves of the cited input are the invariance
principle for the killed stopped walk and the stability of the values, the latter being
`abs_killedRewardValue_sub_le` on the discrete side.

This is the target; it is not proved here.  See the module docstring for the exact gap. -/
def CubeStoppingStability : Prop :=
  ∀ (d : ℕ) (_hd : 1 ≤ d)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : EuclideanSpace ℝ (Fin d) → ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d))
    (_hBrown : ∀ y : EuclideanSpace ℝ (Fin d), IsBrownianSpace d y (B y) PB)
    (hBsm : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T₀ T₁ : ℝ) (_hT₀ : 0 < T₀) (_hT : T₀ ≤ T₁)
    (K : Set (EuclideanSpace ℝ (Fin d))) (_hK : IsCompact K)
    (G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (_hG : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => G p.1 p.2))
    (G' : ℝ → ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (M : ℝ)
    (_hGM : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin d)), |G s y| ≤ M)
    (_hG'M : ∀ (R s : ℝ) (y : EuclideanSpace ℝ (Fin d)), |G' R s y| ≤ M)
    (_hconv : ∀ ε : ℝ, 0 < ε → ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
      ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : EuclideanSpace ℝ (Fin d),
        |G' R s y - G s y| ≤ ε)
    (ε : ℝ) (_hε : 0 < ε),
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
        |Graph.killedRewardValue (lattice d) (latticeBox (floorSite R x) R)
              (fun (k : ℕ) (X : ℕ → Site d) =>
                G' R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (scaledSite R (X k)))
              ⌊R ^ 2 * T⌋₊ (floorSite R x)
          - cubeDiscount (B x) (hBsm x) PB (fun s y => -G s y) T 1 x| ≤ ε

end CubeStopping

end LatticeProb

end
