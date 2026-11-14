import Mathlib
import LatticeProb.Prob.CrossingTimesClock2
import LatticeProb.Prob.CrossingTimesStopping
import LatticeProb.Prob.BrownianPathMap

/-!
# The crossing clock as a measurable functional of the path

For a path `f : ℝ≥0 → E` and a normalisation `m ∈ [0, ∞]` the crossing clock is
`crossClock m f u = limsup_n m 4⁻ⁿ N_n(u)`, where `N_n(u)` is the number of `2⁻ⁿ`-crossings of `f`
in `[0, u]`.  It is nondecreasing in `u` for every path and is invariant under increasing
reparametrisations of time in the sense of the crossing count.

* `crossClock`, `crossClock_mono`;
* `eq_self_of_monotone_of_grid`: a nondecreasing `H : ℝ≥0 → ℝ≥0∞` equal to the identity at the
  rationals `i / (j + 1)` is the identity;
* `crossClock_ofReal_eq_of_tendsto`: for continuous `f`, the real-valued convergence
  `m 4⁻ⁿ N_n(u) → u` gives `crossClock m f u = u`;
* `measurable_crossCount`, `measurable_crossClock`, `measurableSet_forall_crossClock_eq`: on the
  space `C(ℝ≥0, E)` of continuous paths the crossing count, the crossing clock and the set of paths
  whose clock is the identity are measurable;
* `exists_ae_crossClock_eq_self`: for Brownian motion in `ℝ ^ d`, almost surely the crossing clock
  with a normalisation depending only on `d` is the identity, at all times simultaneously;
* `ae_map_pathMap_crossClock_eq_self`: the same statement for the law of the path on `C(ℝ≥0, E)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Deterministic

variable {E : Type*} [PseudoMetricSpace E]

/-- **The crossing clock.**  `crossClock m f u = limsup_n m 4⁻ⁿ N_n(u)` in `ℝ≥0∞`, where `N_n(u)`
is the number of `2⁻ⁿ`-crossings of `f` in `[0, u]`. -/
def crossClock (m : ℝ≥0∞) (f : ℝ≥0 → E) (u : ℝ≥0) : ℝ≥0∞ :=
  limsup (fun n : ℕ => m * 4⁻¹ ^ n * ENat.toENNReal (crossCount ((2 : ℝ)⁻¹ ^ n) f u)) atTop

/-- The crossing clock is nondecreasing in time, for every path. -/
theorem crossClock_mono (m : ℝ≥0∞) (f : ℝ≥0 → E) : Monotone (crossClock m f) := by
  intro u v huv
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  have h : ENat.toENNReal (crossCount ((2 : ℝ)⁻¹ ^ n) f u) ≤
      ENat.toENNReal (crossCount ((2 : ℝ)⁻¹ ^ n) f v) :=
    ENat.toENNReal_le.2 (crossCount_mono _ f huv)
  gcongr

end Deterministic

/-- **A nondecreasing function equal to the identity on the rational grid is the identity.**  If
`H : ℝ≥0 → ℝ≥0∞` is nondecreasing and `H (i / (j + 1)) = i / (j + 1)` for all `i, j`, then `H x = x`
for all `x`. -/
theorem eq_self_of_monotone_of_grid {H : ℝ≥0 → ℝ≥0∞} (hH : Monotone H)
    (hgrid : ∀ i j : ℕ, H ((i : ℝ≥0) / ((j : ℝ≥0) + 1)) =
      (((i : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)) (x : ℝ≥0) : H x = x := by
  have hfin : ∀ y : ℝ≥0, min (H y) ((y : ℝ≥0∞) + 1) ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hmono : ∀ _ : ℕ, Monotone fun y : ℝ≥0 => (min (H y) ((y : ℝ≥0∞) + 1)).toReal := by
    intro _ y z hyz
    refine ENNReal.toReal_mono (hfin z) (min_le_min (hH hyz) ?_)
    have : (y : ℝ≥0∞) ≤ z := by exact_mod_cast hyz
    gcongr
  have hgrid' : ∀ i j : ℕ, Tendsto
      (fun _ : ℕ => (min (H ((i : ℝ≥0) / ((j : ℝ≥0) + 1)))
        ((((i : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) + 1)).toReal) atTop
      (𝓝 (((i : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ)) := by
    intro i j
    have h1 : (min (H ((i : ℝ≥0) / ((j : ℝ≥0) + 1)))
        ((((i : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) + 1)).toReal =
        (((i : ℝ≥0) / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ) := by
      rw [hgrid, min_eq_left (le_self_add), ENNReal.coe_toReal]
    rw [h1]
    exact tendsto_const_nhds
  have h2 := tendsto_of_monotone_of_grid (G := fun _ y => (min (H y) ((y : ℝ≥0∞) + 1)).toReal)
    hmono (fun i j => hgrid' i j) x
  have hx : (min (H x) ((x : ℝ≥0∞) + 1)).toReal = (x : ℝ) := tendsto_nhds_unique tendsto_const_nhds h2
  have ha : min (H x) ((x : ℝ≥0∞) + 1) = x := by
    rw [← ENNReal.ofReal_toReal (hfin x), hx, ENNReal.ofReal_coe_nnreal]
  by_cases h : H x ≤ (x : ℝ≥0∞) + 1
  · rw [min_eq_left h] at ha
    exact ha
  · push Not at h
    rw [min_eq_right h.le] at ha
    exact absurd ha (ne_of_gt (ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero))

/-- The crossing clock of a continuous path is the identity at time `u` as soon as the real-valued
sequence `m 4⁻ⁿ N_n(u)` converges to `u`. -/
theorem crossClock_ofReal_eq_of_tendsto {E : Type*} [PseudoMetricSpace E] {f : ℝ≥0 → E}
    (hf : Continuous f) {m : ℝ} (hm : 0 < m) {u : ℝ≥0}
    (h : Tendsto (fun n : ℕ => m * (4⁻¹ : ℝ) ^ n *
      ((crossCount ((2 : ℝ)⁻¹ ^ n) f u).toNat : ℝ)) atTop (𝓝 (u : ℝ))) :
    crossClock (ENNReal.ofReal m) f u = u := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal m * 4⁻¹ ^ n *
      ENat.toENNReal (crossCount ((2 : ℝ)⁻¹ ^ n) f u) =
      ENNReal.ofReal (m * (4⁻¹ : ℝ) ^ n * ((crossCount ((2 : ℝ)⁻¹ ^ n) f u).toNat : ℝ)) := by
    intro n
    have hc := (crossCount_lt_top hf (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n) u).ne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hc
    rw [← hk]
    simp only [ENat.toNat_natCast, ENat.toENNReal_coe]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_natCast]
    simp
  unfold crossClock
  rw [show (fun n : ℕ => ENNReal.ofReal m * 4⁻¹ ^ n *
      ENat.toENNReal (crossCount ((2 : ℝ)⁻¹ ^ n) f u)) = fun n : ℕ => ENNReal.ofReal
      (m * (4⁻¹ : ℝ) ^ n * ((crossCount ((2 : ℝ)⁻¹ ^ n) f u).toNat : ℝ)) from funext hterm]
  have h2 := ENNReal.tendsto_ofReal h
  rw [ENNReal.ofReal_coe_nnreal] at h2
  exact h2.limsup_eq

section Measurability

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The number of `ε`-crossings in `[0, u]` is a measurable function of a continuous path. -/
theorem measurable_crossCount {ε : ℝ} (hε : 0 < ε) (u : ℝ≥0) :
    Measurable fun y : C(ℝ≥0, E) => crossCount ε (fun s => y s) u := by
  rw [ENat.measurable_iff]
  intro n
  have h1 : MeasurableSet {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) n ≤ u} :=
    measurableSet_le (measurable_crossTime hε n) measurable_const
  have h2 : MeasurableSet {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) (n + 1) ≤ u} :=
    measurableSet_le (measurable_crossTime hε (n + 1)) measurable_const
  have h3 : (fun y : C(ℝ≥0, E) => crossCount ε (fun s => y s) u) ⁻¹' {(n : ℕ∞)} =
      {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) n ≤ u} \
        {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) (n + 1) ≤ u} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    rw [← le_crossCount_iff, ← le_crossCount_iff]
    generalize crossCount ε (fun s => y s) u = c
    constructor
    · rintro rfl
      exact ⟨le_rfl, fun h => by have := Nat.cast_le.1 h; omega⟩
    · rintro ⟨h1, h2⟩
      induction c using ENat.recTopCoe with
      | top => exact absurd le_top h2
      | coe k =>
        have h1' := Nat.cast_le.1 h1
        have h2' : ¬ (n + 1 ≤ k) := fun h => h2 (Nat.cast_le.2 h)
        have : k = n := by omega
        rw [this]
  rw [h3]
  exact h1.diff h2

/-- The crossing clock at a fixed time is a measurable function of a continuous path. -/
theorem measurable_crossClock (m : ℝ≥0∞) (u : ℝ≥0) :
    Measurable fun y : C(ℝ≥0, E) => crossClock m (fun s => y s) u := by
  refine Measurable.limsup fun n => ?_
  have h1 := measurable_crossCount (E := E) (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n) u
  have h2 : Measurable fun y : C(ℝ≥0, E) =>
      ENat.toENNReal (crossCount ((2 : ℝ)⁻¹ ^ n) (fun s => y s) u) :=
    (Measurable.of_discrete (f := ENat.toENNReal)).comp h1
  exact measurable_const.mul h2

/-- The set of continuous paths whose crossing clock is the identity at all times is measurable. -/
theorem measurableSet_forall_crossClock_eq (m : ℝ≥0∞) :
    MeasurableSet {y : C(ℝ≥0, E) | ∀ u : ℝ≥0, crossClock m (fun s => y s) u = u} := by
  have h : {y : C(ℝ≥0, E) | ∀ u : ℝ≥0, crossClock m (fun s => y s) u = u} =
      ⋂ p : ℕ × ℕ, {y : C(ℝ≥0, E) | crossClock m (fun s => y s)
        ((p.1 : ℝ≥0) / ((p.2 : ℝ≥0) + 1)) =
          (((p.1 : ℝ≥0) / ((p.2 : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hy p
      exact hy _
    · intro hy u
      exact eq_self_of_monotone_of_grid (crossClock_mono m _) (fun i j => hy (i, j)) u
  rw [h]
  exact MeasurableSet.iInter fun p => measurable_crossClock m _ (measurableSet_singleton _)

/-- **Transfer to the law of the path.**  If almost surely the crossing clock of the sample path is
the identity, then the same holds for the law of the path on `C(ℝ≥0, E)`. -/
theorem ae_map_pathMap_crossClock_eq_self {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : ℝ≥0 → Ω → E) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (m : ℝ≥0∞) (h : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, crossClock m (fun t => B t ω) u = u) :
    ∀ᵐ y ∂(P.map (pathMap B hcont)), ∀ u : ℝ≥0, crossClock m (fun s => y s) u = u :=
  (ae_map_iff (measurable_pathMap B hm hcont).aemeasurable
    (measurableSet_forall_crossClock_eq m)).2 h

end Measurability

/-- **The crossing clock of Brownian motion is the identity.**  There is `m ∈ (0, ∞)`, depending
only on `d`, such that for every Brownian motion `B` in `ℝ ^ d` with continuous paths, almost surely
`crossClock m B u = u` for all times `u ≥ 0`. -/
theorem exists_ae_crossClock_eq_self (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ⊤ ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin d))
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
      (∀ ω, Continuous fun t => B t ω) → ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        crossClock m (fun t => B t ω) u = u := by
  obtain ⟨m, hm, h⟩ := exists_ae_tendsto_crossCount_all d hd
  refine ⟨ENNReal.ofReal m, ENNReal.ofReal_pos.2 hm, ENNReal.ofReal_lt_top, ?_⟩
  intro Ω _ P _ x B hB hmeas hcont
  filter_upwards [h Ω P x B hB hmeas hcont] with ω hω u
  exact crossClock_ofReal_eq_of_tendsto (hcont ω) hm (hω u)

end LatticeProb
