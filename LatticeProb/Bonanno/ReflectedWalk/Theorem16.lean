/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Theorem16 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.ContinuousTimeChain
import LatticeProb.Bonanno.ReflectedWalk.UniquenessLimit
import LatticeProb.Bonanno.ReflectedWalk.MarkovProperty

/-!
# The capstone: Theorem 1.6 of Gwynne–Sung (arXiv:2506.18827, p. 5)

`Theorem16Statement.lean` states Theorem 1.6 as an unproved `Prop`; `Existence.lean` and
`UniquenessLimit.lean` prove its two halves.  This file **assembles them** into

  `theorem16 … : Theorem16Statement G hmin`

and closes two infrastructure gaps that the files below it flagged.

## 1.  The capstone `theorem16`

The existential clause is `existence_half'` (`MarkovProperty.lean`: `Existence.existence_half`
with property (iv) discharged by `markovProperty_hiv`), and the uniqueness conjunct is
`Theorem16.uniqueness_half`; the only work the capstone itself does is to package Step 2 of
the uniqueness proof (`Theorem16.approximatedBy_of_approximated`).

**One hypothesis remains**, `hstep1`, an explicitly named statement of a result that is being
proved elsewhere; it is not a `sorry`, an `axiom` or a placeholder, and it is discharged by a
one-line substitution of the result named:

* `hstep1` — **Step 1 of the uniqueness proof** (p. 26), in exactly the two pieces Step 1
  produces: the time-changed processes `X̃ⁿ` of (3.32), approximating `X̃` at fixed times
  (`Theorem16.ApproximatedAtFixedTimes`, the conclusion of Step 2 for them; see
  `approximatedBy_of_approximated` for why the literal (3.33) is not used), and the identity
  in law `X̃ⁿ =ᵈ Xⁿ` at one time, i.e. that their one-time marginals are a family `q` not
  depending on the process.  For the paper `q` is the transition function of the
  continuous-time chain (3.15), which is `ContinuousTimeChain.chainFamily_transition_eq`
  below.  It is discharged by `UniquenessGeneralSide.lean` (whose `chainLaw_embedded` is the
  identification of the embedded chain that yields `q`); the theorems there carry right
  continuity at `∞` of the process as a standing hypothesis `hR`, which `IsReflectedWalk` now
  supplies itself (`(h𝓨 x).2.2.2.1`).

### The former hypothesis `hR`, and the approved repair of the statement

Earlier versions of this capstone carried a second hypothesis `hR`: right continuity at `∞`
(`Theorem16.RightContinuousAtInfty`) for an *arbitrary* family satisfying the printed
properties (i)–(vi) — the right-hand form of the paper's Lemma 3.11.  `Lemma311.not_hR`
proves that this hypothesis is **false**: for every countably infinite connected `G` there is a
family satisfying the printed (i)–(vi) verbatim (a single-time kill of the constructed walk, at
the atomless start of its first return sojourn) which is not right continuous at `∞`.  So the
capstone as then routed was vacuous, and the paper's Lemma 3.11 — whose proof presupposes its
conclusion, by taking `τ_k(x)` to be the *smallest* `s` with `X_s = x` — does not hold for the
class cut out by the printed clauses.

The repair, approved by the user and recorded in `Theorem16Statement.lean` and
`STATEMENT_SPEC.md`, completes property (ii): the printed (ii) constrains the path only at
times where `X_t ∈ VG`, and right continuity into the state space `VG ∪ {∞}` (the one-point
compactification, `VG` discrete) additionally requires that at a time with `X_t = ∞` every
vertex is avoided on some `(t, t + ε)` — which is exactly `RightContinuousAtInfty`.  It is now
a conjunct of `IsReflectedWalk`, immediately after `RightContinuous`.  The constructed process
has it (`Existence.rightContinuousAtInfty`, from `RightContinuityAtInfty.lean`, which bypasses
the strong Markov property), so `existence_half'` remains unconditional, and every place that
took `hR` now reads it off `IsReflectedWalk`.  `Lemma311.not_hR` survives, restated for the
class `IsReflectedWalkWeak` cut out by the printed clauses alone, as the justification of the
repair: that class is strictly larger than `IsReflectedWalk`
(`Lemma311.not_forall_isReflectedWalkWeak_isReflectedWalk`).

`SojournRegularity.lean` records that inside Step 2 only a weaker pathwise consequence of
(ii) + `RightContinuousAtInfty` is used (`PathAlmostEverywhereDefined`), and that the weakening
does not extend to Step 1; with the clause part of the statement this no longer affects the
hypothesis list.

The packaging lemma that read `hR` and routed Step 2 through the literal (3.33)
(`approximatedBy_of_shiftBound`) went with the hypothesis: `ShiftBound` is **false** as printed
(`approximatedBy_of_approximated` says why), so nothing may route through it, and
`approximatedBy_of_approximated` — which takes the *conclusion* of Step 2 directly — is the
only packaging of Step 2 this file offers.

## 2.  Gap-fill: the level-`n` holding times diverge (`∑_j Tⁿ_j = ∞` a.s.)

`ContinuousTimeChain.exists_inLevelInterval` and `ContinuousTimeChain.Xn_ne_none` carry the
hypothesis `∑' j, holding Gs Y w E (addr Gs Y n j) = ⊤`, and `RateFunction.lean` proves it
almost surely only for the level `0` (`jointLaw_ae_tsum_holding_addr_zero_eq_top`).
`ConductanceGraph.Exhaustion.jointLaw_ae_tsum_holding_addr_eq_top` proves it for **every**
level: the level-`(n₀+i)` chain also returns to `z` infinitely often
(`chainLaw_ae_exists_gt_eq`), and the unit holding times of the classes `[(n,j)]`, `j ∈ ℕ`,
are an i.i.d. `Exponential(1)` sequence for every `n`, not only for `n = 0`
(`expFamily_map_comp_addr`), so the divergence of a countable sum of exponentials
(`expFamily_ae_tsum_div_eq_top`) applies at every level once it is transported along the
reindexing (`expFamily_ae_tsum_div_addr_eq_top`).  The consequence `Xⁿ_t ≠ ∞` is then
unconditional, and with a single null set for every level and every time, because the
divergence does not mention the time and the levels are countably many:
`ContinuousTimeChain.jointLaw_ae_forall_Xn_ne_none` and, under the paper's `P_z`,
`ContinuousTimeChain.sampleLaw_ae_forall_chainX_ne_none` (fixed-level, fixed-time corollaries
`jointLaw_ae_Xn_ne_none`, `sampleLaw_ae_chainX_ne_none`); the other consumer of the divergence
hypothesis becomes unconditional in the same way
(`ContinuousTimeChain.jointLaw_ae_forall_exists_inLevelInterval`).

## 3.  Gap-fill: the transition-function bridge

`ContinuousTimeChain.lean` dropped its `ReflectedWalk.TransitionUniqueness` import, so its
`chainFamily_transition` is stated as a raw measure equality rather than through
`ProcessFamily.transition`.  `ContinuousTimeChain.chainFamily_transition_eq` is the bridge,
which is what `Theorem16.identDistrib_of_transition` and the `q` of `hstep1` consume.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

universe u

namespace ReflectedWalk

open IndexSet

variable {V : Type u}

/-! ## 1.  Divergence of the level-`n` holding times (Lemma 3.5, Step 0, at every level)

`RateFunction.lean` proves "`∑_j T_{[(0,j)]} = ∞` almost surely" by dominating the level-`0`
holding times by a countable sum of i.i.d. `Exponential(w(z))` variables along the infinitely
many times at which the level-`0` chain is at `z`.  The same argument works at every level:
the only level-specific ingredients are the recurrence of the level-`n` chain and the fact
that the unit holding times indexed by the level-`n` classes are i.i.d. `Exponential(1)`.
Both are available for every level, so the hypothesis of
`ContinuousTimeChain.exists_inLevelInterval` can be discharged a.s. at every level. -/

section Divergence

/-- The set of sequences whose rescaled series diverges is measurable. -/
private lemma measurableSet_tsum_ofReal_div_eq_top (g : ℕ → ℝ) :
    MeasurableSet {u : ℕ → ℝ | ∑' k, ENNReal.ofReal (u k / g k) = ⊤} := by
  have h : Measurable fun u : ℕ → ℝ => ∑' k, ENNReal.ofReal (u k / g k) :=
    Measurable.tsum fun k =>
      ENNReal.measurable_ofReal.comp ((measurable_pi_apply k).div measurable_const)
  exact h (measurableSet_singleton ⊤)

/-- **Divergence of a countable sum of i.i.d. exponentials, along the level-`n` classes.**
`RateFunction.expFamily_ae_tsum_div_eq_top` is the statement for the level-`0` classes
`[(0,k)] = Finsupp.single 0 k`, which are the only addresses that do not depend on the path.
For a *fixed* path `y` the level-`n` addresses `[(n,k)] = addr Gs y n k` are an injective
sequence too, and `expFamily_map_comp_addr` says that reading the i.i.d. family along either
sequence gives the same law `expSeq` on `ℕ → ℝ`; so the divergence transports from level `0`
to level `n`. -/
lemma expFamily_ae_tsum_div_addr_eq_top (Gs : ℕ → Set V) (y : ℕ → ℕ → V) (n : ℕ) {K : Set ℕ}
    (hK : K.Infinite) (g : ℕ → ℝ) {D : ℝ} (hD : 0 < D) (hg : ∀ k ∈ K, 0 < g k ∧ g k ≤ D) :
    ∀ᵐ e ∂expFamily, ∑' k, ENNReal.ofReal (e (addr Gs y n k) / g k) = ⊤ := by
  have hS := measurableSet_tsum_ofReal_div_eq_top g
  have hm : ∀ m : ℕ, Measurable fun e : (ℕ →₀ ℕ) → ℝ => fun j : ℕ => e (addr Gs y m j) :=
    fun _ => Measurable.of_eval fun _ => measurable_pi_apply _
  have h1 : ∀ᵐ u ∂expSeq, ∑' k, ENNReal.ofReal (u k / g k) = ⊤ := by
    rw [← expFamily_map_comp_addr Gs y 0, ae_map_iff (hm 0).aemeasurable hS]
    exact expFamily_ae_tsum_div_eq_top hK g hD hg
  rw [← expFamily_map_comp_addr Gs y n] at h1
  exact (ae_map_iff (hm n).aemeasurable hS).mp h1

namespace ConductanceGraph.Exhaustion

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
  {G : ConductanceGraph V} (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)

/-- **Lemma 3.5, Step 0 at every level** (p. 21): for every level offset `i`, the level-`(n₀+i)`
holding times diverge almost surely.  This is
`jointLaw_ae_tsum_holding_addr_zero_eq_top` with `i` in place of `0`: the level-`(n₀+i)` chain
visits `z` at arbitrarily large times (`chainLaw_ae_exists_gt_eq`, Remark 3.1), so the
holding-time series dominates a countable sum of i.i.d. `Exponential(w(z))` variables
(`expFamily_ae_tsum_div_addr_eq_top`), which is a.s. infinite. -/
theorem jointLaw_ae_tsum_holding_addr_eq_top (n₀ : ℕ) {z : V} (hz : z ∈ E.Gsub n₀) (w : V → ℝ)
    (hw : ∀ x, 0 < w x) (i : ℕ) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z,
      ∑' k, holding (E.levelSets n₀) p.1 w p.2 (addr (E.levelSets n₀) p.1 i k) = ⊤ := by
  have hS : MeasurableSet {u : ℕ → ℝ | ∑' k, ENNReal.ofReal (u k) = ⊤} :=
    (Measurable.tsum fun k => ENNReal.measurable_ofReal.comp (measurable_pi_apply k))
      (measurableSet_singleton ⊤)
  have hmeas : MeasurableSet {p : Existence.Sample V |
      ∑' k, ENNReal.ofReal (ContinuousTimeChain.holdingSeq E w n₀ i p k) = ⊤} :=
    ContinuousTimeChain.measurable_holdingSeq E w n₀ i hS
  have hA : ∀ᵐ p ∂E.jointLaw hG n₀ z,
      ∑' k, ENNReal.ofReal (ContinuousTimeChain.holdingSeq E w n₀ i p k) = ⊤ := by
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    filter_upwards [E.coupling_ae_of_ae hG n₀ z i
      (E.chainLaw_ae_exists_gt_eq hG (n₀ + i) (E.mono (Nat.le_add_right n₀ i) hz) z)] with y hrec
    have hK : {k | y i k = z}.Infinite :=
      Set.infinite_of_forall_exists_gt fun N => let ⟨k, hk, h⟩ := hrec N; ⟨k, h, hk⟩
    exact expFamily_ae_tsum_div_addr_eq_top (E.levelSets n₀) y i hK (fun k => w (y i k)) (hw z)
      (fun k hk => by rw [show y i k = z from hk]; exact ⟨hw z, le_rfl⟩)
  filter_upwards [hA, E.jointLaw_ae_consistent hG n₀ z] with p hp hcons
  have e : ∀ k, holding (E.levelSets n₀) p.1 w p.2 (addr (E.levelSets n₀) p.1 i k) =
      ENNReal.ofReal (ContinuousTimeChain.holdingSeq E w n₀ i p k) :=
    fun k => ContinuousTimeChain.holding_addr_eq _ _ _ _ hcons i k
  rw [tsum_congr e]
  exact hp

/-- The same under the paper's `P_z` of Section 3.3 (base level `n_z`). -/
theorem sampleLaw_ae_tsum_holding_addr_eq_top (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V) (i : ℕ) :
    ∀ᵐ ω ∂Existence.sampleLaw E hG z,
      ∑' k, holding (E.levelSets (E.nz z)) ω.1 w ω.2
        (addr (E.levelSets (E.nz z)) ω.1 i k) = ⊤ :=
  E.jointLaw_ae_tsum_holding_addr_eq_top hG (E.nz z) (E.mem_Gsub_nz z) w hw i

end ConductanceGraph.Exhaustion

namespace ContinuousTimeChain

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
  {G : ConductanceGraph V} (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)

/-- **`Xⁿ_t ≠ ∞` almost surely**, with no hypothesis beyond `w > 0`, and with a *single* null
set serving every level and every time: the time change of (3.15) covers `[0,∞)` because the
level-`n` holding times diverge (`jointLaw_ae_tsum_holding_addr_eq_top`), that divergence does
not mention the time, and the levels are countably many (`ae_all_iff`).

This is the unconditional form of `Xn_ne_none`, whose hypothesis
`∑' j, holding Gs Y w E (addr Gs Y n j) = ⊤` was previously available almost surely only at
level `0`. -/
theorem jointLaw_ae_forall_Xn_ne_none (w : V → ℝ) (hw : ∀ x, 0 < w x) (n₀ : ℕ) {z : V}
    (hz : z ∈ E.Gsub n₀) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z, ∀ (i : ℕ) (t : ℝ≥0),
      PathProperties.Xn (E.levelSets n₀) p.1 w p.2 i t ≠ none := by
  refine ae_all_iff.2 fun i => ?_
  filter_upwards [E.jointLaw_ae_tsum_holding_addr_eq_top hG n₀ hz w hw i] with p hp
  exact fun t => Xn_ne_none _ _ _ _ hp t

/-- `jointLaw_ae_forall_Xn_ne_none` at a fixed level and a fixed time. -/
theorem jointLaw_ae_Xn_ne_none (w : V → ℝ) (hw : ∀ x, 0 < w x) (n₀ : ℕ) {z : V}
    (hz : z ∈ E.Gsub n₀) (i : ℕ) (t : ℝ≥0) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z, PathProperties.Xn (E.levelSets n₀) p.1 w p.2 i t ≠ none :=
  (jointLaw_ae_forall_Xn_ne_none hG E w hw n₀ hz).mono fun _ h => h i t

/-- The unconditional form of `exists_inLevelInterval`, the other consumer of the divergence
hypothesis: almost surely, at every level the holding intervals of (3.15) cover `[0,∞)`. -/
theorem jointLaw_ae_forall_exists_inLevelInterval (w : V → ℝ) (hw : ∀ x, 0 < w x) (n₀ : ℕ)
    {z : V} (hz : z ∈ E.Gsub n₀) :
    ∀ᵐ p ∂E.jointLaw hG n₀ z, ∀ (i : ℕ) (t : ℝ≥0),
      ∃ k, PathProperties.InLevelInterval (E.levelSets n₀) p.1 w p.2 i k t := by
  refine ae_all_iff.2 fun i => ?_
  filter_upwards [E.jointLaw_ae_tsum_holding_addr_eq_top hG n₀ hz w hw i] with p hp
  exact fun t => exists_inLevelInterval _ _ _ _ hp t

/-- **`Xⁿ_t ∈ VG` almost surely** for the process family of the continuous-time approximating
chain, under the paper's `P_z`: the "`X_t ∈ VG`" clause of property (i) of Theorem 1.6 for
`Xⁿ`, at every level and every time simultaneously. -/
theorem sampleLaw_ae_forall_chainX_ne_none (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V) :
    ∀ᵐ ω ∂Existence.sampleLaw E hG z, ∀ (i : ℕ) (t : ℝ≥0),
      (chainFamily E w hG i).X t ω ≠ none := by
  filter_upwards [jointLaw_ae_forall_Xn_ne_none hG E w hw (E.nz z) (E.mem_Gsub_nz z),
    Existence.sampleLaw_ae_start E hG z] with ω hω h0
  intro i t
  show PathProperties.processN (E.levelSets (E.nz (ω.1 0 0))) w Prod.fst Prod.snd i t ω ≠ none
  rw [h0 0]
  exact hω i t

/-- `sampleLaw_ae_forall_chainX_ne_none` at a fixed level and a fixed time. -/
theorem sampleLaw_ae_chainX_ne_none (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V) (i : ℕ)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Existence.sampleLaw E hG z, (chainFamily E w hG i).X t ω ≠ none :=
  (sampleLaw_ae_forall_chainX_ne_none hG E w hw z).mono fun _ h => h i t

/-- **The transition function of `Xⁿ` as a `ProcessFamily.transition`.**  The bridge between
`chainFamily_transition` — stated as a raw measure equality, so that
`ContinuousTimeChain.lean` need not import `ReflectedWalk.TransitionUniqueness` — and the
`ProcessFamily.transition` that `Theorem16.identDistrib_of_transition` and the family of laws
`q` of the uniqueness argument consume. -/
theorem chainFamily_transition_eq (w : V → ℝ) (hw : ∀ x, 0 < w x) (i : ℕ) (z : V) (t : ℝ≥0)
    (y : V) :
    (chainFamily E w hG i).transition z t y =
      (E.chainLaw hG (E.nz z + i) z ⊗ₘ holdingKernel w)
        {p : (ℕ → V) × (ℕ → ℝ) | jumpPath p t = some y} :=
  chainFamily_transition E w hG hw i z t y

end ContinuousTimeChain

end Divergence

/-! ## 2.  Step 2 of the uniqueness proof, packaged as `ApproximatedBy` -/

namespace Theorem16

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}

/-- `ApproximatedBy` from the *conclusion* of Step 2 supplied directly.

`ShiftBound` is the literal transcription of the paper's (3.33), and it is **false as
stated**: `TimeChange.stepSum_le_stepAt` shows `Sⁿ_k ≤ tⁿ_k`, so the compressed clock of
(3.32) runs *behind* the real one and `X̃ⁿ_t` reports `X̃` at a **later** time, not at
`t − Rⁿ`.  The correct pair is the transpose of (3.33) together with (3.34), which is
`TimeChange.RewindBound`.  Nothing is lost: `ApproximatedBy` only ever consumes
`ApproximatedAtFixedTimes`, which `TimeChange.approximatedAtFixedTimes_processN` proves
directly for the time change (3.32).  This is the form the capstone uses. -/
theorem approximatedBy_of_approximated [Countable V] {q : V → ℕ → ℝ≥0 → V → ℝ≥0∞}
    {𝓨 : ProcessFamily V}
    (hstep : ∀ x : V, ∃ Xn : ℕ → ℝ≥0 → 𝓨.Ω → Option V,
      (∀ n s, Measurable (Xn n s)) ∧
        ApproximatedAtFixedTimes (𝓨.P x) 𝓨.X Xn ∧
        ∀ n t y, 𝓨.P x {ω | Xn n t ω = some y} = q x n t y) :
    ApproximatedBy 𝓨 q := by
  intro x
  obtain ⟨Xn, hXn, happ, hlaw⟩ := hstep x
  exact ⟨Xn, hXn, happ, hlaw⟩

end Theorem16

/-! ## 3.  The capstone -/

/-- **Theorem 1.6** (Gwynne–Sung, arXiv:2506.18827, p. 5), assembled.

For a countably infinite connected conductance graph `G` there is a rate function
`w* : VG → (0,∞)` such that for every `w : VG → (0,∞)` with `w ≥ w*` and every starting point
`z`, there is a process `X` with `X₀ = z` satisfying properties (i)–(vi) — with (ii) in its
complete form, i.e. including right continuity at `∞`, the approved modification of the printed
statement recorded in `Theorem16Statement.lean` — and it is unique in law among such processes.
The statement is `Theorem16Statement G hmin`, which is `Theorem16Statement.lean`'s target
verbatim; `hmin` is the Proposition 1.3 energy minimiser of property (vi), instantiated by
`⟨G.energyMin hG, G.energyMin_eqOn hG, G.energyMin_hasFiniteEnergy hG,
  G.energyMin_le_energy hG⟩`.

The existential clause is `existence_half'` (unconditional; `MarkovProperty.lean`) and the
uniqueness conjunct is `Theorem16.uniqueness_half`; the proof below is their assembly together
with the packaging of Step 2 (`Theorem16.approximatedBy_of_approximated`).

The single hypothesis, and the result that discharges it (see the module docstring):

* `hstep1` — Step 1 of the uniqueness proof (p. 26): the time changes `X̃ⁿ` of (3.32),
  approximating the process at fixed times, with the one-time marginals `q` of the
  continuous-time chain (3.15) (`UniquenessGeneralSide.lean`; `q` is
  `ContinuousTimeChain.chainFamily_transition_eq`).  Right continuity at `∞` of the process,
  which every theorem of `UniquenessGeneralSide.lean` carries as `hR`, is available from
  `IsReflectedWalk` itself, so `hstep1` takes nothing beyond `IsReflectedWalk`.

The hypothesis is an honestly named statement, not a placeholder: substituting the result
closes Theorem 1.6 with no further work. -/
theorem theorem16 (G : ConductanceGraph V) (hmin : G.EnergyMinimizer)
    (hstep1 : ∀ w : V → ℝ, (∀ x, 0 < w x) →
      ∃ q : V → ℕ → ℝ≥0 → V → ℝ≥0∞, ∀ 𝓨 : ProcessFamily V, IsReflectedWalk G w hmin 𝓨 →
        ∀ x : V, ∃ Xn : ℕ → ℝ≥0 → 𝓨.Ω → Option V,
          (∀ n s, Measurable (Xn n s)) ∧
            Theorem16.ApproximatedAtFixedTimes (𝓨.P x) 𝓨.X Xn ∧
            ∀ n t y, 𝓨.P x {ω | Xn n t ω = some y} = q x n t y) :
    Theorem16Statement G hmin := by
  intro hV hinf hG
  have : Countable V := hV
  obtain ⟨wstar, hwstar, hex⟩ := existence_half' G hmin hV hinf hG
  refine ⟨wstar, hwstar, fun w hw hge z => ?_⟩
  obtain ⟨𝓧, h𝓧⟩ := hex w hw hge z
  obtain ⟨q, hq⟩ := hstep1 w hw
  exact ⟨𝓧, h𝓧, Theorem16.uniqueness_half h𝓧
    (fun 𝓨 h𝓨 => Theorem16.approximatedBy_of_approximated (hq 𝓨 h𝓨)) z⟩

end ReflectedWalk
