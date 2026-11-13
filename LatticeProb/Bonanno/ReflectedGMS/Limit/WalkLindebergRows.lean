/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.WalkLindebergRows at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedRescaledLindeberg
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedBracketIncrement
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualArrayLocalizerBounds
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedArrayProducer
import LatticeProb.Bonanno.ReflectedGMS.Limit.CompactContainmentProducer

/-!
# Conditional Lindeberg for rescaled stopped rows (manuscript `p:lem:lindeberg`, tex:1599)

The manuscript proves the conditional Lindeberg condition `p:eq:lindeberg` by one observation
(tex:1626): on the event that the rescaled path stays in a bounded region up to the horizon, the
Lindeberg integrand vanishes identically for small `ε`, because **every possible** neighbouring
jump from a state of that region is `o(1)` after scaling (`p:eq:allpossiblejumps`); compact
containment then removes the event.  This file is that argument, for an abstract plane-valued
càdlàg path `M` and for every row that is a *stopped rescaled projection* of it.

## The two walk-level inputs, as predicates on `M`

* `SmallJumpsFromBoundedRegion P M` — `p:eq:allpossiblejumps` read along the paths: for every
  radius `R` and tolerance `δ` there is `ε₀ > 0` such that, almost surely, at every time `u`
  whose left limit lies in `B̄(0, R/e)`, the jump of `M` at `u` is at most `δ/e`, for every
  scale `0 < e ≤ ε₀`.  At the walk it follows deterministically from `HasOnlyOrdinaryJumps`,
  coercivity and `CoercivitySmallJumps.exists_pos_forall_neighbor_smallJump`
  (`Limit/WalkLindeberg`).
* `RescaledCompactContainment P M` — for every scale sequence `ε → 0⁺`, horizon `H` and level
  `γ > 0` there is ONE radius `R` (chosen before the scale) with
  `P(∃ u ≤ H, R < εₖ ‖M(εₖ⁻² u)‖) ≤ γ` eventually.  Produced here from localized martingale
  arrays (`rescaledCompactContainment_of_arrays`, the Doob step of
  `CompactContainmentProducer`).

## The rows

`IsRescaledStopRow P M η e N`: almost surely `N r = a · e ⟪η, M(e⁻² g r)⟫` with `|a| ≤ 1` and a
time map `g` that is `1`-Lipschitz with `g r ≤ r`.  The unstopped rescaled projection is one
(`isRescaledStopRow_rescaledProjection`), and the class is closed under the project's exact
`{τ > 0}`-indicator stopping at ANY random time (`IsRescaledStopRow.indicator_stopped`).  So it
contains both the singly-stopped rows `N' k` of `StoppedRescaledLindeberg`
(`isRescaledStopRow_stoppedRescaledProjection`) and the doubly-stopped rows `N'' k` (localizer,
then bracket threshold) of the local CLT lane (`isRescaledStopRow_twice`); starting from the
written-out projection (`isRescaledStopRow_rescaled_inner`) or from a coordinate row of the
`harray` binder (`isRescaledStopRow_coord`), any finite chain of indicator stops is covered by
`IsRescaledStopRow.indicator_stopped`.

## Main results (all for arbitrary rescaled stopped rows)

* `eventually_measureReal_bigIncrementSet_le_of_rows` — **(i)** small increments in probability.
* `exists_terminalSquareTail_of_rows` — **(iii)** uniform square tails of the terminal
  increment; the rows only need to be square-integrable martingales with a compensator in
  `[0, K]`.  Mechanism: stop again at the spatial exit `σ` of `B̄(0, 2R)`; the twice-stopped
  increment is bounded by `4‖η‖(2R+1)` pathwise (every jump from the region is at most `1`
  after scaling), and the remainder has `E[(N_t - N_{t∧σ})²] = E[B_t - B_{t∧σ}] ≤ K·P(σ ≤ t)`
  by optional stopping.  No uniform integrability is assumed anywhere.
* `lindeberg_of_rows` / `lindeberg_of_rescaledStopRows` — the Lindeberg field of
  `ApproximateBracketCLT.LocalizedBracketArray`, from (i) and (iii).
* `stoppedRescaledSmallIncrements_of_smallJumps`, `stoppedRescaledTerminalSquareTail_of_smallJumps`
  — the named atoms of `Limit/StoppedRescaledLindeberg`, and
  `rescaledIncrementCharFunLimit_of_bracket_data_of_smallJumps` — that consumer with both atoms
  replaced by `SmallJumpsFromBoundedRegion` and `RescaledCompactContainment`.

The large-jump defect of tex:1628 (compound Poisson with rate `1/n`, jumps `±√n`) is excluded
exactly by `SmallJumpsFromBoundedRegion`: it bounds every jump from the region, realized or not.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology InnerProductSpace

namespace ReflectedGMS.WalkLindeberg

open ReflectedGMS.MartingaleLimit ReflectedGMS.ApproximateBracketCLT
open ReflectedGMS.RescaledFddCharFun ReflectedGMS.GaussianLimitIdentification
open ReflectedGMS.StatementIngredients

/-! ## Deterministic helpers -/

section Deterministic

/-- Near one time, the oscillation of a càdlàg path in a pseudo-metric space is at most the jump
there plus an error.  (The metric-space form of
`MartingaleLimit.IsCadlag.exists_radius_pairwise_dist_lt_jump_add`.) -/
theorem exists_radius_pairwise_dist_lt_jump_add {E : Type*} [PseudoMetricSpace E]
    {f : ℝ≥0 → E} (hf : IsCadlag f) (x : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ s ∈ Metric.ball x r, ∀ t ∈ Metric.ball x r,
      dist (f s) (f t) < dist (f.leftLim x) (f x) + ε := by
  obtain ⟨rL, hrL, hL⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (hf.tendsto_nhdsLT_leftLim x) (ε / 2) (half_pos hε)
  obtain ⟨rR, hrR, hR⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (hf.isRightContinuous x) (ε / 2) (half_pos hε)
  let g : ℝ≥0 → E := fun y => if y < x then f.leftLim x else f x
  have hnear (y : ℝ≥0) (hy : y ∈ Metric.ball x (min rL rR)) :
      dist (f y) (g y) < ε / 2 := by
    have hyd := Metric.mem_ball.mp hy
    by_cases hyl : y < x
    · simpa [g, hyl] using hL hyl (lt_of_lt_of_le hyd (min_le_left _ _))
    · rcases lt_or_eq_of_le (le_of_not_gt hyl) with hxy | hxy
      · simpa [g, hyl] using hR hxy (lt_of_lt_of_le hyd (min_le_right _ _))
      · subst y
        simpa [g] using half_pos hε
  refine ⟨min rL rR, lt_min hrL hrR, ?_⟩
  intro s hs t ht
  have hstep : dist (g s) (g t) ≤ dist (f.leftLim x) (f x) := by
    dsimp [g]
    split_ifs <;> simp_all [dist_comm, dist_nonneg]
  have htri : dist (f s) (f t) ≤
      dist (f s) (g s) + dist (g s) (g t) + dist (f t) (g t) := by
    calc
      dist (f s) (f t) ≤ dist (f s) (g s) + dist (g s) (f t) := dist_triangle _ _ _
      _ ≤ dist (f s) (g s) + (dist (g s) (g t) + dist (g t) (f t)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ = _ := by rw [dist_comm (g t) (f t)]; ring
  linarith [hnear s hs, hnear t ht]

/-- **One mesh for a càdlàg path with bounded jumps**, in a pseudo-metric space: on `[0, T]`,
increments over gaps below the mesh are at most the jump bound plus any positive error.  (The
metric-space form of `MartingaleLimit.IsCadlag.exists_mesh_dist_lt_jump_bound_add`.) -/
theorem exists_mesh_dist_lt_jump_bound_add {E : Type*} [PseudoMetricSpace E]
    {f : ℝ≥0 → E} (hf : IsCadlag f) (T : ℝ≥0) {J ε : ℝ}
    (hjump : ∀ x ≤ T, dist (f.leftLim x) (f x) ≤ J) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ≤ T, ∀ t ≤ T, dist s t < δ → dist (f s) (f t) < J + ε := by
  classical
  let K := Icc (0 : ℝ≥0) T
  have hlocal (x : K) := exists_radius_pairwise_dist_lt_jump_add hf x.val hε
  choose r hr hosc using hlocal
  have hcover : K ⊆ ⋃ x : K, Metric.ball x.val (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using hr ⟨x, hx⟩⟩
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric
    (s := K) isCompact_Icc (fun x : K => Metric.isOpen_ball) hcover
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hst
  obtain ⟨x, hx⟩ := hδcover s ⟨bot_le, hs⟩
  have hsb : s ∈ Metric.ball s δ := by simpa using hδ
  have htb : t ∈ Metric.ball s δ := by simpa [dist_comm] using hst
  exact (hosc x s (hx hsb) t (hx htb)).trans_le (add_le_add (hjump x x.property.2) le_rfl)

/-- On `ℝ≥0` there is nothing strictly to the left of `0`, so the left limit at `0` is the
value there. -/
theorem leftLim_zero {E : Type*} [TopologicalSpace E] (f : ℝ≥0 → E) :
    Function.leftLim f 0 = f 0 := by
  refine leftLim_eq_of_eq_bot f ?_
  have h : Set.Iio (0 : ℝ≥0) = ∅ := by
    ext y
    simp
  rw [h, nhdsWithin_empty]

/-- A norm bound strictly before a time passes to the left limit there. -/
theorem norm_leftLim_le {E : Type*} [NormedAddCommGroup E] {f : ℝ≥0 → E} (hf : IsCadlag f)
    {x : ℝ≥0} {B : ℝ} (h0 : x = 0 → ‖f 0‖ ≤ B) (h : ∀ y < x, ‖f y‖ ≤ B) :
    ‖Function.leftLim f x‖ ≤ B := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ x) with hx | hx
  · rw [← hx, leftLim_zero]
    exact h0 hx.symm
  · have : NeBot (𝓝[<] x) := nhdsLT_neBot_of_exists_lt ⟨0, hx⟩
    refine le_of_tendsto (hf.tendsto_nhdsLT_leftLim x).norm ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h y hy

/-- The stopped time `r ∧ c`, read back in `ℝ≥0`. -/
noncomputable def stopTime (c : WithTop ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  (min (r : WithTop ℝ≥0) c).untopA

theorem stopTime_top (r : ℝ≥0) : stopTime ⊤ r = r := by
  simp [stopTime]
  rfl

theorem stopTime_coe (c r : ℝ≥0) : stopTime (c : WithTop ℝ≥0) r = min r c := by
  rw [stopTime, ← WithTop.coe_min]
  rfl

theorem stopTime_le (c : WithTop ℝ≥0) (r : ℝ≥0) : stopTime c r ≤ r := by
  induction c using WithTop.recTopCoe with
  | top => rw [stopTime_top]
  | coe c => rw [stopTime_coe]; exact min_le_left _ _

theorem coe_stopTime_le (c : WithTop ℝ≥0) (r : ℝ≥0) : ((stopTime c r : ℝ≥0) : WithTop ℝ≥0) ≤ c := by
  induction c using WithTop.recTopCoe with
  | top => exact le_top
  | coe c => rw [stopTime_coe]; exact_mod_cast min_le_right _ _

theorem dist_stopTime_le (c : WithTop ℝ≥0) (r r' : ℝ≥0) :
    dist (stopTime c r) (stopTime c r') ≤ dist r r' := by
  induction c using WithTop.recTopCoe with
  | top => rw [stopTime_top, stopTime_top]
  | coe c =>
    rw [stopTime_coe, stopTime_coe, NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_min,
      NNReal.coe_min]
    have h := abs_min_sub_min_le_max (r : ℝ) (c : ℝ) (r' : ℝ) (c : ℝ)
    rw [sub_self, abs_zero] at h
    exact h.trans (max_le le_rfl (abs_nonneg _))

theorem stopTime_zero_of_eq_bot {c : WithTop ℝ≥0} (hc : c = ⊥) (r : ℝ≥0) : stopTime c r = 0 := by
  have hc' : c = ((0 : ℝ≥0) : WithTop ℝ≥0) := hc
  rw [hc', stopTime_coe]
  exact min_eq_right zero_le

/-- Points of the uniform partition lie below the right end. -/
theorem uniformPartition_le_right {s t : ℝ≥0} (hst : s ≤ t) {n i : ℕ} (hi : i ≤ n) :
    uniformPartition s t n i ≤ t := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hi0 : i = 0 := by omega
    subst hi0
    rw [uniformPartition_zero]
    exact hst
  · have hdiv : (i : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast hi
    have hmul : (i : ℝ≥0) / (n : ℝ≥0) * (t - s) ≤ t - s := mul_le_of_le_one_left zero_le hdiv
    calc uniformPartition s t n i = s + (i : ℝ≥0) / (n : ℝ≥0) * (t - s) := rfl
      _ ≤ s + (t - s) := add_le_add le_rfl hmul
      _ = t := add_tsub_cancel_of_le hst

/-- Consecutive points of the uniform partition are `(t - s)/n` apart. -/
theorem dist_uniformPartition_succ {s t : ℝ≥0} (n i : ℕ) :
    dist (uniformPartition s t n (i + 1)) (uniformPartition s t n i)
      = ((t - s : ℝ≥0) : ℝ) / n := by
  rw [NNReal.dist_eq]
  have h : ((uniformPartition s t n (i + 1) : ℝ≥0) : ℝ) - (uniformPartition s t n i : ℝ)
      = ((t - s : ℝ≥0) : ℝ) / n := by
    simp only [uniformPartition, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_natCast]
    push_cast
    ring
  rw [h, abs_of_nonneg (by positivity)]

end Deterministic

/-! ## The two walk-level predicates and the rows -/

section Predicates

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Manuscript `p:eq:allpossiblejumps` along the paths.**  For every radius `R ≥ 0` and
tolerance `δ > 0` there is `ε₀ > 0` such that, almost surely, for every scale `0 < e ≤ ε₀` and
every time `u` whose left limit lies in `B̄(0, R/e)`, the scaled jump `e ‖ΔM u‖` is at most `δ`.
The scale threshold is deterministic: it bounds EVERY possible jump from the region, not only the
realized ones (tex:1626–1628). -/
def SmallJumpsFromBoundedRegion (P : Measure Ω) (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ᵐ ω ∂P, ∀ e : ℝ, 0 < e → e ≤ ε₀ →
    ∀ u : ℝ≥0, e * ‖Function.leftLim (fun r => M r ω) u‖ ≤ R →
      e * ‖M u ω - Function.leftLim (fun r => M r ω) u‖ ≤ δ

/-- **Compact containment of the rescaled path** (the first half of `p:lem:lindeberg`): along
every scale sequence `ε → 0⁺`, for every horizon `H` and level `γ > 0`, one radius `R`, chosen
before the scale, keeps `εₖ M(εₖ⁻² ·)` in `B̄(0, R)` on `[0, H]` up to probability `γ`,
eventually in `k`. -/
def RescaledCompactContainment (P : Measure Ω) (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) : Prop :=
  ∀ ε : ℕ → ℝ≥0, Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
    ∀ (H : ℝ≥0) (γ : ℝ≥0∞), 0 < γ → ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop,
      P {ω | ∃ u ∈ Icc (0 : ℝ≥0) H, R < (ε k : ℝ) * ‖M ((ε k)⁻¹ ^ 2 * u) ω‖} ≤ γ

/-- **A rescaled stopped row** of the projection `⟪η, e M(e⁻² ·)⟫`: almost surely
`N r = a · e ⟪η, M(e⁻² g r)⟫` for a constant `|a| ≤ 1` and a `1`-Lipschitz time map `g ≤ id`. -/
def IsRescaledStopRow (P : Measure Ω) (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (η : BouRabeeGwynne.Euc 2) (e : ℝ≥0) (N : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∃ a : ℝ, |a| ≤ 1 ∧ ∃ g : ℝ≥0 → ℝ≥0, (∀ r, g r ≤ r) ∧
    (∀ r r', dist (g r) (g r') ≤ dist r r') ∧
    ∀ r, N r ω = a * ((e : ℝ) * ⟪η, M (e⁻¹ ^ 2 * g r) ω⟫_ℝ)

/-- The unstopped rescaled projection is a rescaled stopped row. -/
theorem isRescaledStopRow_rescaledProjection (P : Measure Ω)
    (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (η : BouRabeeGwynne.Euc 2) (e : ℝ≥0) :
    IsRescaledStopRow P M η e (rescaledProjection M e η) :=
  Eventually.of_forall fun ω => ⟨1, by simp, id, fun _ => le_rfl, fun _ _ => le_rfl,
    fun r => by rw [one_mul, rescaledProjection_eq]; rfl⟩

/-- **Closure under the project's exact indicator stopping**, at an arbitrary random time. -/
theorem IsRescaledStopRow.indicator_stopped {P : Measure Ω}
    {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} {η : BouRabeeGwynne.Euc 2} {e : ℝ≥0}
    {N : ℝ≥0 → Ω → ℝ} (h : IsRescaledStopRow P M η e N) (τ : Ω → WithTop ℝ≥0) :
    IsRescaledStopRow P M η e (stoppedProcess (fun r => {ω | ⊥ < τ ω}.indicator (N r)) τ) := by
  filter_upwards [h] with ω ⟨a, ha, g, hg, hgL, hN⟩
  classical
  refine ⟨{ω | ⊥ < τ ω}.indicator (fun _ => a) ω, ?_, g ∘ stopTime (τ ω),
    fun r => (hg _).trans (stopTime_le _ r),
    fun r r' => (hgL _ _).trans (dist_stopTime_le _ r r'), fun r => ?_⟩
  · by_cases hω : ω ∈ {ω | ⊥ < τ ω}
    · rw [Set.indicator_of_mem hω]
      exact ha
    · rw [Set.indicator_of_notMem hω]
      simp
  · change {ω | ⊥ < τ ω}.indicator (N (stopTime (τ ω) r)) ω = _
    by_cases hω : ω ∈ {ω | ⊥ < τ ω}
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hN]
      rfl
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]

/-- The bracket-stopped rows `N' k` of `StoppedRescaledLindeberg` are rescaled stopped rows. -/
theorem isRescaledStopRow_stoppedRescaledProjection (P : Measure Ω)
    (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (A : ℝ≥0 → Ω → ℝ) (η : BouRabeeGwynne.Euc 2)
    (e : ℝ≥0) (K : ℝ) :
    IsRescaledStopRow P M η e (stoppedRescaledProjection M A η e K) :=
  (isRescaledStopRow_rescaledProjection P M η e).indicator_stopped _

end Predicates

/-! ## (i) Small increments in probability -/

section SmallIncrements

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The pathwise core of (i).**  If the rescaled path stays in `B̄(0, R)` up to the horizon `t`
and every jump from `B̄(0, R/e)` is at most `δ'/e`, then for all fine enough uniform partitions of
`[s, t]` no increment of the row exceeds `δ > 2‖η‖δ'`. -/
theorem exists_forall_notMem_bigIncrementSet_of_path {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2}
    {η : BouRabeeGwynne.Euc 2} {e : ℝ≥0} (he : 0 < e) {N : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : IsCadlag fun r => M r ω) {R δ' δ : ℝ} (hδ' : 0 < δ')
    (hJ : ∀ u : ℝ≥0, (e : ℝ) * ‖Function.leftLim (fun r => M r ω) u‖ ≤ R →
      (e : ℝ) * ‖M u ω - Function.leftLim (fun r => M r ω) u‖ ≤ δ')
    (hrep : ∃ a : ℝ, |a| ≤ 1 ∧ ∃ g : ℝ≥0 → ℝ≥0, (∀ r, g r ≤ r) ∧
      (∀ r r', dist (g r) (g r') ≤ dist r r') ∧
      ∀ r, N r ω = a * ((e : ℝ) * ⟪η, M (e⁻¹ ^ 2 * g r) ω⟫_ℝ))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hgood : ∀ u ∈ Icc (0 : ℝ≥0) t, (e : ℝ) * ‖M (e⁻¹ ^ 2 * u) ω‖ ≤ R)
    (hδ : 2 * ‖η‖ * δ' < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ω ∉ bigIncrementSet N δ s t n := by
  obtain ⟨a, ha, g, hg, hgL, hN⟩ := hrep
  set f : ℝ≥0 → BouRabeeGwynne.Euc 2 := fun r => M r ω with hfdef
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have he0 : e ≠ 0 := he.ne'
  set U : ℝ≥0 := e⁻¹ ^ 2 * t with hUdef
  -- the path below the horizon is in `B̄(0, R/e)`
  have hball : ∀ y ≤ U, (e : ℝ) * ‖f y‖ ≤ R := by
    intro y hy
    have hmem : e ^ 2 * y ∈ Icc (0 : ℝ≥0) t := by
      refine ⟨zero_le, ?_⟩
      calc e ^ 2 * y ≤ e ^ 2 * U := mul_le_mul_of_nonneg_left hy zero_le
        _ = t := by
          rw [hUdef, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ he0, one_pow, one_mul]
    have h := hgood _ hmem
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ he0, one_pow, one_mul] at h
  have hballR : ∀ y ≤ U, ‖f y‖ ≤ R / e := fun y hy => by
    rw [le_div_iff₀ heR, mul_comm]
    exact hball y hy
  -- hence so are the left limits, and the jumps are at most `δ'/e`
  have hjump : ∀ x ≤ U, dist (f.leftLim x) (f x) ≤ δ' / e := by
    intro x hx
    have hl : ‖f.leftLim x‖ ≤ R / e :=
      norm_leftLim_le hc (fun h0 => hballR 0 zero_le)
        (fun y hy => hballR y (hy.le.trans hx))
    have hl' : (e : ℝ) * ‖f.leftLim x‖ ≤ R := by
      have := mul_le_mul_of_nonneg_left hl heR.le
      rwa [mul_div_cancel₀ _ heR.ne'] at this
    have hj := hJ x hl'
    rw [dist_eq_norm, norm_sub_rev, le_div_iff₀ heR, mul_comm]
    exact hj
  obtain ⟨ρ, hρ, hmesh⟩ := exists_mesh_dist_lt_jump_bound_add hc U hjump (div_pos hδ' heR)
  -- a partition size beyond which the rescaled steps are below the mesh
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((((e⁻¹ ^ 2 : ℝ≥0) : ℝ) * ((t - s : ℝ≥0) : ℝ)) / ρ)
  refine ⟨n₀ + 1, fun n hn ω' => ?_⟩
  obtain ⟨i, hi, hbig⟩ := Set.mem_iUnion₂.1 ω'
  have hi' : i + 1 ≤ n := Finset.mem_range.1 hi
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set p1 := uniformPartition s t n (i + 1)
  set p0 := uniformPartition s t n i
  have hp1 : p1 ≤ t := uniformPartition_le_right hst hi'
  have hp0 : p0 ≤ t := uniformPartition_le_right hst (by omega)
  set A1 : ℝ≥0 := e⁻¹ ^ 2 * g p1
  set A0 : ℝ≥0 := e⁻¹ ^ 2 * g p0
  have hA1 : A1 ≤ U := mul_le_mul_of_nonneg_left ((hg p1).trans hp1) zero_le
  have hA0 : A0 ≤ U := mul_le_mul_of_nonneg_left ((hg p0).trans hp0) zero_le
  have hdistA : dist A1 A0 < ρ := by
    have hd : dist A1 A0 = ((e⁻¹ ^ 2 : ℝ≥0) : ℝ) * dist (g p1) (g p0) := by
      rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_mul, NNReal.coe_mul, ← mul_sub, abs_mul,
        abs_of_nonneg (NNReal.coe_nonneg _)]
    rw [hd]
    have hstep : dist (g p1) (g p0) ≤ ((t - s : ℝ≥0) : ℝ) / n :=
      (hgL p1 p0).trans (le_of_eq (dist_uniformPartition_succ n i))
    have hcoef : (0 : ℝ) ≤ ((e⁻¹ ^ 2 : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have hn₀n : (n₀ : ℝ) < n := by exact_mod_cast (show n₀ < n by omega)
    have hfrac : ((e⁻¹ ^ 2 : ℝ≥0) : ℝ) * (((t - s : ℝ≥0) : ℝ) / n) < ρ := by
      rw [div_lt_iff₀ hρ] at hn₀
      rw [← mul_div_assoc, div_lt_iff₀ hnpos]
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hstep hcoef) hfrac
  have hosc : dist (f A1) (f A0) < δ' / e + δ' / e := hmesh A1 hA1 A0 hA0 hdistA
  -- the increment of the row
  have hinc : |N p1 ω - N p0 ω| ≤ 2 * ‖η‖ * δ' := by
    rw [hN p1, hN p0, ← mul_sub, ← mul_sub, ← inner_sub_right, abs_mul, abs_mul,
      abs_of_nonneg heR.le]
    have h1 : |⟪η, M A1 ω - M A0 ω⟫_ℝ| ≤ ‖η‖ * ‖M A1 ω - M A0 ω‖ := abs_real_inner_le_norm _ _
    have h2 : ‖M A1 ω - M A0 ω‖ ≤ 2 * δ' / e := by
      have := hosc.le
      rw [dist_eq_norm] at this
      have h' : δ' / (e : ℝ) + δ' / e = 2 * δ' / e := by ring
      rw [h'] at this
      exact this
    have h3 : (e : ℝ) * |⟪η, M A1 ω - M A0 ω⟫_ℝ| ≤ 2 * ‖η‖ * δ' := by
      calc (e : ℝ) * |⟪η, M A1 ω - M A0 ω⟫_ℝ| ≤ (e : ℝ) * (‖η‖ * (2 * δ' / e)) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
              heR.le
        _ = 2 * ‖η‖ * δ' := by field_simp
    calc |a| * ((e : ℝ) * |⟪η, M A1 ω - M A0 ω⟫_ℝ|) ≤ 1 * ((e : ℝ) * |⟪η, M A1 ω - M A0 ω⟫_ℝ|) :=
          mul_le_mul_of_nonneg_right ha (mul_nonneg heR.le (abs_nonneg _))
      _ ≤ 2 * ‖η‖ * δ' := by rw [one_mul]; exact h3
  have hbig' : δ < |N p1 ω - N p0 ω| := hbig
  linarith

/-- **(i) Small increments in probability, for arbitrary rescaled stopped rows.**  Along every
`ε k → 0⁺`, eventually in `k` and then in the partition size `n`, the probability that some
increment of `N k` along the uniform partition of `[s, t]` exceeds `δ` is at most `γ`. -/
theorem eventually_measureReal_bigIncrementSet_le_of_rows [IsProbabilityMeasure P]
    {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} (η : BouRabeeGwynne.Euc 2)
    (hcad : ∀ᵐ ω ∂P, IsCadlag fun r => M r ω)
    (hjump : SmallJumpsFromBoundedRegion P M) (hcont : RescaledCompactContainment P M)
    {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)))
    {N : ℕ → ℝ≥0 → Ω → ℝ} (hrow : ∀ k, IsRescaledStopRow P M η (ε k) (N k))
    (hNm : ∀ k v, Measurable (N k v)) {s t : ℝ≥0} (hst : s ≤ t) {δ γ : ℝ} (hδ : 0 < δ)
    (hγ : 0 < γ) :
    ∀ᶠ k in atTop, ∀ᶠ n in atTop, P.real (bigIncrementSet (N k) δ s t n) ≤ γ := by
  obtain ⟨R, hRpos, hRev⟩ :=
    hcont ε hε t (ENNReal.ofReal (γ / 2)) (ENNReal.ofReal_pos.2 (by linarith))
  set δ' : ℝ := δ / (4 * (‖η‖ + 1)) with hδ'def
  have hη1 : 0 < ‖η‖ + 1 := by positivity
  have hδ' : 0 < δ' := div_pos hδ (by positivity)
  have hδδ' : 2 * ‖η‖ * δ' < δ := by
    rw [hδ'def, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg η]
  obtain ⟨ε₀, hε₀, hJ⟩ := hjump R hRpos.le δ' hδ'
  have hεpos : ∀ᶠ k in atTop, 0 < ε k := (tendsto_nhdsWithin_iff.1 hε).2
  have hεR : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 (tendsto_nhdsWithin_iff.1 hε).1
  have hεsmall : ∀ᶠ k in atTop, (ε k : ℝ) ≤ ε₀ :=
    ((tendsto_order.1 hεR).2 ε₀ hε₀).mono fun _ h => h.le
  filter_upwards [hRev, hεpos, hεsmall] with k hkR hkpos hksmall
  set F : ℕ → Set Ω := fun n₀ => ⋃ n ≥ n₀, bigIncrementSet (N k) δ s t n with hFdef
  have hFanti : Antitone F := by
    intro a b hab ω hω
    obtain ⟨n, hn, hmem⟩ := Set.mem_iUnion₂.1 hω
    exact Set.mem_iUnion₂.2 ⟨n, le_trans hab hn, hmem⟩
  have hFmeas : ∀ n₀, NullMeasurableSet (F n₀) P := fun n₀ =>
    (MeasurableSet.biUnion (Set.to_countable _) fun n _ =>
      measurableSet_bigIncrementSet (hNm k) δ s t n).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hFmeas hFanti ⟨0, measure_ne_top P _⟩
  have hInter : P (⋂ n₀, F n₀) ≤ ENNReal.ofReal (γ / 2) := by
    refine le_trans (measure_mono_ae ?_) hkR
    filter_upwards [hcad, hJ, hrow k] with ω hωc hωJ hωrep
    intro hmem
    by_contra hgood
    simp only [not_exists, not_and, not_lt] at hgood
    obtain ⟨n₀, hn₀⟩ := exists_forall_notMem_bigIncrementSet_of_path hkpos hωc hδ'
      (fun u hu => hωJ (ε k) (by exact_mod_cast hkpos) hksmall u hu) hωrep hst
      (fun u hu => hgood u hu) hδδ'
    have hmem' : ω ∈ F n₀ := Set.mem_iInter.1 hmem n₀
    obtain ⟨n, hn, hbig⟩ := Set.mem_iUnion₂.1 hmem'
    exact hn₀ n hn hbig
  have hlt : ENNReal.ofReal (γ / 2) < ENNReal.ofReal γ :=
    (ENNReal.ofReal_lt_ofReal_iff hγ).2 (by linarith)
  have hev := (tendsto_order.1 hlim).2 _ (lt_of_le_of_lt hInter hlt)
  filter_upwards [hev] with n hn
  have hsub : bigIncrementSet (N k) δ s t n ⊆ F n :=
    Set.subset_iUnion₂ (s := fun m (_ : m ≥ n) => bigIncrementSet (N k) δ s t m) n le_rfl
  have hle : P (bigIncrementSet (N k) δ s t n) ≤ ENNReal.ofReal γ :=
    (measure_mono hsub).trans hn.le
  exact ENNReal.toReal_le_of_le_ofReal hγ.le hle

end SmallIncrements

/-! ## (iii) Uniform square tails of the terminal increment -/

section TerminalTail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The pathwise core of (iii).**  Let `σ` be the first time the running supremum of
`e‖M(e⁻² ·)‖` reaches `2R`, and suppose every jump from `B̄(0, 2R/e)` is at most `1/e`.  Then a
rescaled stopped row, stopped once more at `σ`, moves by at most `2‖η‖(2R+1)` between any two
times: before `σ` the path is in `B̄(0, 2R/e)`, and the value at `σ` exceeds its left limit by at
most one scaled jump FROM the region.  If `σ = 0` the twice-stopped row is constant. -/
theorem abs_stopped_sub_le_of_path {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2}
    {η : BouRabeeGwynne.Euc 2} {e : ℝ≥0} (he : 0 < e) {N : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : IsCadlag fun r => M r ω) {R : ℝ} (hR : 0 ≤ R)
    (hJ : ∀ u : ℝ≥0, (e : ℝ) * ‖Function.leftLim (fun r => M r ω) u‖ ≤ 2 * R →
      (e : ℝ) * ‖M u ω - Function.leftLim (fun r => M r ω) u‖ ≤ 1)
    (hrep : ∃ a : ℝ, |a| ≤ 1 ∧ ∃ g : ℝ≥0 → ℝ≥0, (∀ r, g r ≤ r) ∧
      (∀ r r', dist (g r) (g r') ≤ dist r r') ∧
      ∀ r, N r ω = a * ((e : ℝ) * ⟪η, M (e⁻¹ ^ 2 * g r) ω⟫_ℝ))
    (r r' : ℝ≥0) :
    |N (stopTime (absThresholdStop (fun u ω => (e : ℝ) * ‖M (e⁻¹ ^ 2 * u) ω‖) (2 * R) ω) r) ω
      - N (stopTime (absThresholdStop (fun u ω => (e : ℝ) * ‖M (e⁻¹ ^ 2 * u) ω‖) (2 * R) ω)
          r') ω| ≤ 2 * (‖η‖ * (2 * R + 1)) := by
  obtain ⟨a, ha, g, hg, -, hN⟩ := hrep
  set Y : ℝ≥0 → Ω → ℝ := fun u ω => (e : ℝ) * ‖M (e⁻¹ ^ 2 * u) ω‖ with hYdef
  set σ : WithTop ℝ≥0 := absThresholdStop Y (2 * R) ω with hσdef
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have he0 : e ≠ 0 := he.ne'
  have hc₁ : 0 ≤ ‖η‖ * (2 * R + 1) := mul_nonneg (norm_nonneg _) (by linarith)
  by_cases hσ : σ = ⊥
  · rw [stopTime_zero_of_eq_bot hσ, stopTime_zero_of_eq_bot hσ, sub_self, abs_zero]
    positivity
  have hYnn : ∀ u, |Y u ω| = Y u ω := fun u =>
    abs_of_nonneg (mul_nonneg heR.le (norm_nonneg _))
  -- the key claim: up to and including `σ`, the rescaled path is in `B̄(0, 2R + 1)`
  have hkey : ∀ h : ℝ≥0, (h : WithTop ℝ≥0) ≤ σ →
      (e : ℝ) * ‖M (e⁻¹ ^ 2 * h) ω‖ ≤ 2 * R + 1 := by
    intro h hh
    rcases lt_or_eq_of_le hh with hlt | heq
    · have h1 := abs_lt_of_lt_absThresholdStop (N := Y) hlt
      rw [hYnn] at h1
      exact le_trans h1.le (by linarith)
    · have hhpos : 0 < h := by
        rw [pos_iff_ne_zero]
        rintro rfl
        exact hσ heq.symm
      set u : ℝ≥0 := e⁻¹ ^ 2 * h with hudef
      have hupos : 0 < u := mul_pos (pow_pos (inv_pos.2 he) 2) hhpos
      have hbefore : ∀ y < u, ‖M y ω‖ ≤ 2 * R / e := by
        intro y hy
        have hlt' : e ^ 2 * y < h := by
          have := mul_lt_mul_of_pos_left hy (pow_pos he 2)
          rwa [hudef, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ he0, one_pow, one_mul] at this
        have hlt : ((e ^ 2 * y : ℝ≥0) : WithTop ℝ≥0) < σ := by
          rw [← heq]
          exact_mod_cast hlt'
        have h1 := abs_lt_of_lt_absThresholdStop (N := Y) hlt
        rw [hYnn] at h1
        have h2 : Y (e ^ 2 * y) ω = (e : ℝ) * ‖M y ω‖ := by
          simp only [hYdef]
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ he0, one_pow, one_mul]
        rw [h2] at h1
        rw [le_div_iff₀ heR, mul_comm]
        exact h1.le
      have hl := norm_leftLim_le hc (fun h0 => absurd h0 hupos.ne') hbefore
      have hl' : (e : ℝ) * ‖Function.leftLim (fun r => M r ω) u‖ ≤ 2 * R := by
        have := mul_le_mul_of_nonneg_left hl heR.le
        rwa [mul_div_cancel₀ _ heR.ne'] at this
      have hj := hJ u hl'
      have htri : ‖M u ω‖ ≤ ‖Function.leftLim (fun r => M r ω) u‖
          + ‖M u ω - Function.leftLim (fun r => M r ω) u‖ := by
        have h := norm_add_le (Function.leftLim (fun r => M r ω) u)
          (M u ω - Function.leftLim (fun r => M r ω) u)
        rwa [add_sub_cancel] at h
      have := mul_le_mul_of_nonneg_left htri heR.le
      rw [mul_add] at this
      linarith
  have hbound : ∀ q : ℝ≥0, |N (stopTime σ q) ω| ≤ ‖η‖ * (2 * R + 1) := by
    intro q
    rw [hN]
    have hh : ((g (stopTime σ q) : ℝ≥0) : WithTop ℝ≥0) ≤ σ :=
      (WithTop.coe_le_coe.2 (hg _)).trans (coe_stopTime_le σ q)
    have hk := hkey _ hh
    rw [abs_mul, abs_mul, abs_of_nonneg heR.le]
    have hin : |⟪η, M (e⁻¹ ^ 2 * g (stopTime σ q)) ω⟫_ℝ|
        ≤ ‖η‖ * ‖M (e⁻¹ ^ 2 * g (stopTime σ q)) ω‖ := abs_real_inner_le_norm _ _
    calc |a| * ((e : ℝ) * |⟪η, M (e⁻¹ ^ 2 * g (stopTime σ q)) ω⟫_ℝ|)
        ≤ 1 * ((e : ℝ) * (‖η‖ * ‖M (e⁻¹ ^ 2 * g (stopTime σ q)) ω‖)) :=
          mul_le_mul ha (mul_le_mul_of_nonneg_left hin heR.le)
            (mul_nonneg heR.le (abs_nonneg _)) zero_le_one
      _ = ‖η‖ * ((e : ℝ) * ‖M (e⁻¹ ^ 2 * g (stopTime σ q)) ω‖) := by ring
      _ ≤ ‖η‖ * (2 * R + 1) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
  have h1 := hbound r
  have h2 := hbound r'
  calc |N (stopTime σ r) ω - N (stopTime σ r') ω|
      ≤ |N (stopTime σ r) ω| + |N (stopTime σ r') ω| := abs_sub _ _
    _ ≤ 2 * (‖η‖ * (2 * R + 1)) := by linarith

/-- Right continuity of the rescaled path `u ↦ M(e⁻² u)` from right continuity of `M`. -/
theorem isRightContinuous_rescale {E : Type*} [TopologicalSpace E] {f : ℝ≥0 → E}
    (hf : IsRightContinuous f) (c : ℝ≥0) : IsRightContinuous fun r => f (c * r) := by
  rcases eq_or_ne c 0 with h0 | h0
  · have heq : (fun r : ℝ≥0 => f (c * r)) = fun _ => f 0 := by
      funext r
      rw [h0, zero_mul]
    rw [heq]
    exact IsRightContinuous.const
  · intro r
    have hpos : 0 < c := pos_iff_ne_zero.2 h0
    refine (hf (c * r)).comp (f := fun r : ℝ≥0 => c * r) (s := Set.Ioi r)
      (continuous_const.mul continuous_id).continuousWithinAt ?_
    intro r' hr'
    exact mul_lt_mul_of_pos_left hr' hpos

/-- **(iii) Uniform square tails of the terminal increment, for arbitrary rescaled stopped
rows.**  The rows need only be square-integrable martingales for the rescaled filtrations with a
compensator taking values in `[0, K]`; `M` must be adapted (for the spatial exit to be a stopping
time), càdlàg, with small jumps from bounded regions, and compactly contained. -/
theorem exists_terminalSquareTail_of_rows [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} (η : BouRabeeGwynne.Euc 2)
    (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t))
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[𝔽 t] S)
    (hcad : ∀ᵐ ω ∂P, IsCadlag fun r => M r ω)
    (hjump : SmallJumpsFromBoundedRegion P M) (hcont : RescaledCompactContainment P M)
    {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)))
    {N B : ℕ → ℝ≥0 → Ω → ℝ} (hrow : ∀ k, IsRescaledStopRow P M η (ε k) (N k))
    (hN : ∀ k, Martingale (N k) (rescaleFiltration 𝔽 (ε k)) P)
    (hC : ∀ k, Martingale (fun r ω => N k r ω * N k r ω - B k r ω)
      (rescaleFiltration 𝔽 (ε k)) P)
    (h2 : ∀ k r, MemLp (N k r) 2 P)
    (hrN : ∀ k, ∀ᵐ ω ∂P, IsRightContinuous fun r => N k r ω)
    (hrC : ∀ k, ∀ᵐ ω ∂P, IsRightContinuous fun r => N k r ω * N k r ω - B k r ω)
    {K : ℝ} (hK : 0 ≤ K) (hBK : ∀ k, ∀ᵐ ω ∂P, ∀ r, 0 ≤ B k r ω ∧ B k r ω ≤ K)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ γ : ℝ, 0 < γ → ∃ m : ℝ, ∀ᶠ k in atTop,
      ∫ ω, max ((N k t ω - N k s ω) ^ 2 - m) 0 ∂P ≤ γ := by
  intro γ hγ
  set γ' : ℝ := γ / (8 * (K + 1)) with hγ'def
  have hγ' : 0 < γ' := div_pos hγ (by positivity)
  obtain ⟨R, hRpos, hRev⟩ := hcont ε hε t (ENNReal.ofReal γ') (ENNReal.ofReal_pos.2 hγ')
  obtain ⟨ε₀, hε₀, hJ⟩ := hjump (2 * R) (by positivity) 1 one_pos
  set c₁ : ℝ := ‖η‖ * (2 * R + 1) with hc₁def
  refine ⟨8 * c₁ ^ 2, ?_⟩
  have hεpos : ∀ᶠ k in atTop, 0 < ε k := (tendsto_nhdsWithin_iff.1 hε).2
  have hεR : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 (tendsto_nhdsWithin_iff.1 hε).1
  have hεsmall : ∀ᶠ k in atTop, (ε k : ℝ) ≤ ε₀ :=
    ((tendsto_order.1 hεR).2 ε₀ hε₀).mono fun _ h => h.le
  filter_upwards [hRev, hεpos, hεsmall] with k hkR hkpos hksmall
  set Y : ℝ≥0 → Ω → ℝ := fun u ω => (ε k : ℝ) * ‖M ((ε k)⁻¹ ^ 2 * u) ω‖ with hYdef
  set σ : Ω → WithTop ℝ≥0 := absThresholdStop Y (2 * R) with hσdef
  have hYad : Adapted (rescaleFiltration 𝔽 (ε k)) Y := fun u =>
    (((hadapt ((ε k)⁻¹ ^ 2 * u)).norm).const_mul (ε k : ℝ)).measurable
  have hYrc : ∀ᵐ ω ∂P, IsRightContinuous fun u => Y u ω := by
    filter_upwards [hcad] with ω hω
    have hcomp : IsRightContinuous fun r : ℝ≥0 => ‖M ((ε k)⁻¹ ^ 2 * r) ω‖ :=
      (isRightContinuous_rescale hω.isRightContinuous ((ε k)⁻¹ ^ 2)).continuous_comp
        continuous_norm
    exact IsRightContinuous.const.mul hcomp
  have hσ : IsStoppingTime (rescaleFiltration 𝔽 (ε k)) σ :=
    isStoppingTime_absThresholdStop hYad (fun u S hS => hnull _ S hS) hYrc
  -- the exit event before `t` is controlled by compact containment
  have hexit : P {ω | σ ω ≤ (t : WithTop ℝ≥0)} ≤ ENNReal.ofReal γ' := by
    refine le_trans (measure_mono_ae ?_) hkR
    filter_upwards [hYrc] with ω hω hle
    have h1 := (absThresholdStop_le_iff hω t).1 hle
    obtain ⟨u, hu, hlt⟩ :=
      exists_lt_abs_of_ofReal_le_absRunningSup h1 (show R < 2 * R by linarith)
    refine ⟨u, hu, ?_⟩
    rwa [abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))] at hlt
  have hexitR : P.real {ω | σ ω ≤ (t : WithTop ℝ≥0)} ≤ γ' :=
    ENNReal.toReal_le_of_le_ofReal hγ'.le hexit
  -- optional stopping: the post-exit part has second moment at most `K · P(σ ≤ q)`
  have hbr : ∀ q : ℝ≥0, q ≤ t →
      Integrable (fun ω => (N k q ω - stoppedProcess (N k) σ q ω) ^ 2) P ∧
        ∫ ω, (N k q ω - stoppedProcess (N k) σ q ω) ^ 2 ∂P ≤ K * γ' := by
    intro q hq
    obtain ⟨hint, hBint, heq⟩ := bounded_stopping_bracket_increment_integral (hN k) (hC k)
      ((isStoppingTime_const _ q).min hσ) (isStoppingTime_const _ q) q
      (fun ω => min_le_left _ _) (fun ω => le_rfl) (hrN k) (hrC k) (h2 k q)
    refine ⟨hint, ?_⟩
    have hSq : MeasurableSet {ω | σ ω ≤ (q : WithTop ℝ≥0)} :=
      (rescaleFiltration 𝔽 (ε k)).le q _ (hσ q)
    have hpt : ∀ᵐ ω ∂P, stoppedValue (B k) (fun _ => (q : WithTop ℝ≥0)) ω
        - stoppedValue (B k) (fun ω => min (q : WithTop ℝ≥0) (σ ω)) ω
        ≤ {ω | σ ω ≤ (q : WithTop ℝ≥0)}.indicator (fun _ => K) ω := by
      filter_upwards [hBK k] with ω hω
      by_cases hle : σ ω ≤ (q : WithTop ℝ≥0)
      · rw [Set.indicator_of_mem (show ω ∈ {ω | σ ω ≤ (q : WithTop ℝ≥0)} from hle)]
        have h1 : stoppedValue (B k) (fun _ => (q : WithTop ℝ≥0)) ω ≤ K := (hω q).2
        have h2' : 0 ≤ stoppedValue (B k) (fun ω => min (q : WithTop ℝ≥0) (σ ω)) ω :=
          (hω _).1
        linarith
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | σ ω ≤ (q : WithTop ℝ≥0)} from hle)]
        have hmin : min (q : WithTop ℝ≥0) (σ ω) = q := min_eq_left (le_of_not_ge hle)
        have hval : stoppedValue (B k) (fun ω => min (q : WithTop ℝ≥0) (σ ω)) ω
            = stoppedValue (B k) (fun _ => (q : WithTop ℝ≥0)) ω := by
          simp only [stoppedValue, hmin]
        rw [hval, sub_self]
    have hexq : P.real {ω | σ ω ≤ (q : WithTop ℝ≥0)} ≤ γ' :=
      (measureReal_mono fun ω (h : σ ω ≤ (q : WithTop ℝ≥0)) =>
        h.trans (by exact_mod_cast hq)).trans hexitR
    have hmain : ∫ ω, (stoppedValue (B k) (fun _ => (q : WithTop ℝ≥0)) ω
        - stoppedValue (B k) (fun ω => min (q : WithTop ℝ≥0) (σ ω)) ω) ∂P ≤ K * γ' := by
      calc ∫ ω, (stoppedValue (B k) (fun _ => (q : WithTop ℝ≥0)) ω
            - stoppedValue (B k) (fun ω => min (q : WithTop ℝ≥0) (σ ω)) ω) ∂P
          ≤ ∫ ω, {ω | σ ω ≤ (q : WithTop ℝ≥0)}.indicator (fun _ => K) ω ∂P :=
            integral_mono_ae hBint ((integrable_const K).indicator hSq) hpt
        _ = P.real {ω | σ ω ≤ (q : WithTop ℝ≥0)} * K := by
            rw [integral_indicator_const K hSq, smul_eq_mul]
        _ ≤ γ' * K := mul_le_mul_of_nonneg_right hexq hK
        _ = K * γ' := mul_comm _ _
    have hcomp : ∫ ω, (N k q ω - stoppedProcess (N k) σ q ω) ^ 2 ∂P
        = ∫ ω, (stoppedValue (N k) (fun _ => (q : WithTop ℝ≥0)) ω
          - stoppedValue (N k) (fun ω => min (q : WithTop ℝ≥0) (σ ω)) ω) ^ 2 ∂P := rfl
    rw [hcomp, heq]
    exact hmain
  -- the twice-stopped increment is bounded pathwise
  have hpath : ∀ᵐ ω ∂P, |stoppedProcess (N k) σ t ω - stoppedProcess (N k) σ s ω| ≤ 2 * c₁ := by
    filter_upwards [hcad, hJ, hrow k] with ω hωc hωJ hωrep
    exact abs_stopped_sub_le_of_path hkpos hωc hRpos.le
      (fun u hu => hωJ (ε k) (by exact_mod_cast hkpos) hksmall u hu) hωrep t s
  obtain ⟨hint_t, hmom_t⟩ := hbr t le_rfl
  obtain ⟨hint_s, hmom_s⟩ := hbr s hst
  have hmajor : Integrable (fun ω => 4 * (N k t ω - stoppedProcess (N k) σ t ω) ^ 2
      + 4 * (N k s ω - stoppedProcess (N k) σ s ω) ^ 2) P :=
    (hint_t.const_mul 4).add (hint_s.const_mul 4)
  have hKγ : K * γ' ≤ γ / 8 := by
    rw [hγ'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ∫ ω, max ((N k t ω - N k s ω) ^ 2 - 8 * c₁ ^ 2) 0 ∂P
      ≤ ∫ ω, (4 * (N k t ω - stoppedProcess (N k) σ t ω) ^ 2
          + 4 * (N k s ω - stoppedProcess (N k) σ s ω) ^ 2) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => le_max_right _ _)
          hmajor ?_
        filter_upwards [hpath] with ω hω
        set x := N k t ω - stoppedProcess (N k) σ t ω with hx
        set y := N k s ω - stoppedProcess (N k) σ s ω with hy
        set z := stoppedProcess (N k) σ t ω - stoppedProcess (N k) σ s ω with hz
        have hsplit : N k t ω - N k s ω = (x - y) + z := by
          rw [hx, hy, hz]
          ring
        have hz2 : z ^ 2 ≤ 4 * c₁ ^ 2 := by
          have h0 : 0 ≤ |z| := abs_nonneg z
          have h1 : |z| ^ 2 ≤ (2 * c₁) ^ 2 := pow_le_pow_left₀ h0 hω 2
          rw [sq_abs] at h1
          nlinarith
        apply max_le
        · rw [hsplit]
          nlinarith [sq_nonneg ((x - y) - z), sq_nonneg (x + y)]
        · positivity
    _ = 4 * ∫ ω, (N k t ω - stoppedProcess (N k) σ t ω) ^ 2 ∂P
          + 4 * ∫ ω, (N k s ω - stoppedProcess (N k) σ s ω) ^ 2 ∂P := by
        rw [integral_add (hint_t.const_mul 4) (hint_s.const_mul 4), integral_const_mul,
          integral_const_mul]
    _ ≤ 4 * (K * γ') + 4 * (K * γ') := by linarith
    _ ≤ γ := by linarith

end TerminalTail

/-! ## The Lindeberg field from (i) and (iii) -/

section Lindeberg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The Lindeberg condition for an array of rows from (i) and (iii).**  The conclusion is
verbatim the `lindeberg` field of `ApproximateBracketCLT.LocalizedBracketArray`. -/
theorem lindeberg_of_rows [IsProbabilityMeasure P]
    {𝔽 : ℕ → Filtration ℝ≥0 mΩ} {N B : ℕ → ℝ≥0 → Ω → ℝ}
    (hN : ∀ k, Martingale (N k) (𝔽 k) P)
    (hC : ∀ k, Martingale (fun r ω => N k r ω * N k r ω - B k r ω) (𝔽 k) P)
    (h2 : ∀ k r, MemLp (N k r) 2 P) {s t : ℝ≥0} (hst : s ≤ t)
    (hBm : ∀ k, ∀ᵐ ω ∂P, MonotoneOn (fun v => B k v ω) (Set.Icc s t))
    {K : ℝ} (hK : 0 ≤ K) (hBK : ∀ k, ∀ᵐ ω ∂P, B k t ω - B k s ω ≤ K)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ γ : ℝ, 0 < γ →
      ∀ᶠ k in atTop, ∀ᶠ n in atTop, P.real (bigIncrementSet (N k) δ s t n) ≤ γ)
    (htail : ∀ γ : ℝ, 0 < γ → ∃ m : ℝ, ∀ᶠ k in atTop,
      ∫ ω, max ((N k t ω - N k s ω) ^ 2 - m) 0 ∂P ≤ γ) :
    ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ →
      ∀ᶠ k in atTop, ∀ᶠ n in atTop, lindebergSum P (N k) δ s t n ≤ ρ := by
  intro δ hδ ρ hρ
  obtain ⟨lam, hlam0, hlam⟩ :=
    exists_uniform_realizedQuadraticSum_tail hN hC h2 hst hBm hK hBK htail (ρ / 2) (by linarith)
  have hγ : 0 < ρ / (2 * (lam + 1)) := div_pos hρ (by linarith)
  filter_upwards [hlam, hsmall δ hδ (ρ / (2 * (lam + 1))) hγ] with k hk1 hk2
  filter_upwards [hk2] with n hn
  have hNm : ∀ v, Measurable (N k v) := fun v =>
    (((hN k).stronglyMeasurable v).mono ((𝔽 k).le v)).measurable
  have hred := lindebergSum_le_integral_max_add hNm (h2 k) δ s t n hlam0.le
  have h1 := hk1 n
  have hbig : lam * P.real (bigIncrementSet (N k) δ s t n) ≤ ρ / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hn hlam0.le
    have hfrac : lam * (ρ / (2 * (lam + 1))) ≤ ρ / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  linarith

/-- **Conditional Lindeberg (`p:eq:lindeberg`) for arbitrary rescaled stopped rows.**  Every
array of square-integrable martingale rows of the rescaled filtrations that are rescaled stopped
rows of `M` and carry a monotone compensator with values in `[0, K]` satisfies the Lindeberg
field of `ApproximateBracketCLT.LocalizedBracketArray`, as soon as `M` is adapted, càdlàg, with
small jumps from bounded regions and compactly contained.  This covers the doubly-stopped rows of
the local CLT lane (`isRescaledStopRow_twice`). -/
theorem lindeberg_of_rescaledStopRows [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} (η : BouRabeeGwynne.Euc 2)
    (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t))
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[𝔽 t] S)
    (hcad : ∀ᵐ ω ∂P, IsCadlag fun r => M r ω)
    (hjump : SmallJumpsFromBoundedRegion P M) (hcont : RescaledCompactContainment P M)
    {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)))
    {N B : ℕ → ℝ≥0 → Ω → ℝ} (hrow : ∀ k, IsRescaledStopRow P M η (ε k) (N k))
    (hN : ∀ k, Martingale (N k) (rescaleFiltration 𝔽 (ε k)) P)
    (hC : ∀ k, Martingale (fun r ω => N k r ω * N k r ω - B k r ω)
      (rescaleFiltration 𝔽 (ε k)) P)
    (h2 : ∀ k r, MemLp (N k r) 2 P)
    (hrN : ∀ k, ∀ᵐ ω ∂P, IsRightContinuous fun r => N k r ω)
    (hrC : ∀ k, ∀ᵐ ω ∂P, IsRightContinuous fun r => N k r ω * N k r ω - B k r ω)
    (hBm : ∀ k, ∀ᵐ ω ∂P, Monotone fun r => B k r ω)
    {K : ℝ} (hK : 0 ≤ K) (hBK : ∀ k, ∀ᵐ ω ∂P, ∀ r, 0 ≤ B k r ω ∧ B k r ω ≤ K)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ →
      ∀ᶠ k in atTop, ∀ᶠ n in atTop, lindebergSum P (N k) δ s t n ≤ ρ :=
  lindeberg_of_rows hN hC h2 hst
    (fun k => (hBm k).mono fun ω hω => hω.monotoneOn _) hK
    (fun k => (hBK k).mono fun ω hω => by linarith [(hω t).2, (hω s).1])
    (fun δ hδ γ hγ => eventually_measureReal_bigIncrementSet_le_of_rows η hcad hjump hcont hε
      hrow (fun k v => (((hN k).stronglyMeasurable v).mono
        ((rescaleFiltration 𝔽 (ε k)).le v)).measurable) hst hδ hγ)
    (exists_terminalSquareTail_of_rows 𝔽 η hadapt hnull hcad hjump hcont hε hrow hN hC h2 hrN
      hrC hK hBK hst)

end Lindeberg

/-! ## Compact containment from localized martingale arrays -/

section Containment

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **`RescaledCompactContainment` from localized martingale arrays** (the `harray` binder of the
walk consumers): Doob's `L²` maximal inequality on each coordinate row, uniform in the row index
through the terminal constant, transported to the actual rescaled coordinates by `agree`.  The
radius is chosen before the scale.  (The Doob step of
`CompactContainmentProducer.compactContainment_of_arrays`, stopped before the passage to cell
representatives.) -/
theorem rescaledCompactContainment_of_arrays [IsProbabilityMeasure P]
    {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2}
    (harray : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (k : Fin 2) (H : ℝ≥0),
        Nonempty (WindowModulusGridTransfer.LocalizedMartingaleArray P
          (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) :
    RescaledCompactContainment P M := by
  classical
  intro ε hε H γ hγ
  set ε' : ℕ → ℝ≥0 := fun n => if 0 < ε n then ε n else 1 with hε'def
  have hε'pos : ∀ n, 0 < ε' n := by
    intro n
    simp only [hε'def]
    split_ifs with h
    · exact h
    · exact one_pos
  have hevEq : ∀ᶠ n in atTop, ε' n = ε n :=
    ((tendsto_nhdsWithin_iff.1 hε).2).mono fun n hn => by
      simp only [hε'def]
      exact ite_eq_left_iff.2 fun h => absurd hn h
  have hε'lim : Tendsto ε' atTop (𝓝 0) :=
    (tendsto_nhdsWithin_iff.1 hε).1.congr' (hevEq.mono fun n h => h.symm)
  have hτpos : (0 : ℝ≥0∞) < min γ 1 / 4 :=
    ENNReal.div_pos (lt_min hγ one_pos).ne' (by norm_num)
  obtain ⟨A0⟩ := harray ε' hε'pos hε'lim 0 H
  obtain ⟨A1⟩ := harray ε' hε'pos hε'lim 1 H
  obtain ⟨b, hbne, hbC⟩ :=
    CompactContainmentProducer.exists_nnreal_le_mul_sq (max A0.C A1.C) hτpos
  have hbpos : (0 : ℝ) < b := by exact_mod_cast pos_iff_ne_zero.2 hbne
  refine ⟨2 * b, by positivity, ?_⟩
  have hag0 := (ENNReal.tendsto_nhds_zero.1 A0.agree) (min γ 1 / 4) hτpos
  have hag1 := (ENNReal.tendsto_nhds_zero.1 A1.agree) (min γ 1 / 4) hτpos
  filter_upwards [hevEq, hag0, hag1] with n hnEq hn0 hn1
  have hb0 := CompactContainmentProducer.measure_exceed_le_of_array A0 n hbne
    (le_trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hbC) hn0
  have hb1 := CompactContainmentProducer.measure_exceed_le_of_array A1 n hbne
    (le_trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)) hbC) hn1
  have hsubset : {ω | ∃ u ∈ Icc (0 : ℝ≥0) H,
        2 * (b : ℝ) < (ε n : ℝ) * ‖M ((ε n)⁻¹ ^ 2 * u) ω‖} ⊆
      {ω | ∃ u ∈ Icc (0 : ℝ≥0) H, (b : ℝ) < |(ε' n : ℝ) * M ((ε' n)⁻¹ ^ 2 * u) ω 0|} ∪
      {ω | ∃ u ∈ Icc (0 : ℝ≥0) H, (b : ℝ) < |(ε' n : ℝ) * M ((ε' n)⁻¹ ^ 2 * u) ω 1|} := by
    rintro ω ⟨u, hu, hlt⟩
    rw [hnEq]
    by_contra hno
    simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hno
    have h0 := hno.1 u hu
    have h1 := hno.2 u hu
    have hn := WindowModulusGridTransfer.norm_le_abs_zero_add_abs_one (M ((ε n)⁻¹ ^ 2 * u) ω)
    have hεn : (0 : ℝ) ≤ (ε n : ℝ) := NNReal.coe_nonneg _
    rw [abs_mul, abs_of_nonneg hεn] at h0 h1
    nlinarith [mul_le_mul_of_nonneg_left hn hεn]
  calc P {ω | ∃ u ∈ Icc (0 : ℝ≥0) H, 2 * (b : ℝ) < (ε n : ℝ) * ‖M ((ε n)⁻¹ ^ 2 * u) ω‖}
      ≤ P ({ω | ∃ u ∈ Icc (0 : ℝ≥0) H, (b : ℝ) < |(ε' n : ℝ) * M ((ε' n)⁻¹ ^ 2 * u) ω 0|} ∪
        {ω | ∃ u ∈ Icc (0 : ℝ≥0) H, (b : ℝ) < |(ε' n : ℝ) * M ((ε' n)⁻¹ ^ 2 * u) ω 1|}) :=
        measure_mono hsubset
    _ ≤ P {ω | ∃ u ∈ Icc (0 : ℝ≥0) H, (b : ℝ) < |(ε' n : ℝ) * M ((ε' n)⁻¹ ^ 2 * u) ω 0|} +
        P {ω | ∃ u ∈ Icc (0 : ℝ≥0) H, (b : ℝ) < |(ε' n : ℝ) * M ((ε' n)⁻¹ ^ 2 * u) ω 1|} :=
        measure_union_le _ _
    _ ≤ (min γ 1 / 4 + min γ 1 / 4) + (min γ 1 / 4 + min γ 1 / 4) := add_le_add hb0 hb1
    _ = 4 * (min γ 1 / 4) := by ring
    _ ≤ γ := le_trans ENNReal.mul_div_le (min_le_left _ _)

end Containment

/-! ## The atoms of `StoppedRescaledLindeberg` and its consumer -/

section Atoms

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Right continuity of the bracket-stopped rescaled projection and of its compensated square. -/
theorem ae_rightContinuous_stoppedRescaledProjection (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (A : ℝ≥0 → Ω → ℝ) (η : BouRabeeGwynne.Euc 2) (e : ℝ≥0) (K : ℝ)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous fun u : ℝ≥0 => ⟪η, M u ω⟫_ℝ)
    (hAc : ∀ᵐ ω ∂P, Continuous fun u : ℝ≥0 => A u ω) :
    (∀ᵐ ω ∂P, IsRightContinuous fun r => stoppedRescaledProjection M A η e K r ω) ∧
      (∀ᵐ ω ∂P, IsRightContinuous fun r => stoppedRescaledProjection M A η e K r ω
        * stoppedRescaledProjection M A η e K r ω - stoppedRescaledBracket A e K r ω) := by
  have hNrc : ∀ᵐ ω ∂P, IsRightContinuous fun r => rescaledProjection M e η r ω := by
    filter_upwards [hrc] with ω hω
    have heq : (fun r => rescaledProjection M e η r ω)
        = fun r => (e : ℝ) * ⟪η, M (e⁻¹ ^ 2 * r) ω⟫_ℝ :=
      funext fun r => rescaledProjection_eq M e η r ω
    rw [heq]
    exact IsRightContinuous.const.mul (isRightContinuous_rescale hω (e⁻¹ ^ 2))
  have hBc : ∀ᵐ ω ∂P, Continuous fun r => rescaledBracketPath A e r ω := by
    filter_upwards [hAc] with ω hω
    exact continuous_const.mul (hω.comp (continuous_const.mul continuous_id))
  have hCrc : ∀ᵐ ω ∂P, IsRightContinuous fun r =>
      rescaledProjection M e η r ω * rescaledProjection M e η r ω
        - rescaledBracketPath A e r ω := by
    filter_upwards [hNrc, hBc] with ω h1 h2
    exact (h1.mul h1).sub h2.isRightContinuous
  refine ⟨?_, LocalizedArrayProducer.ae_rightContinuous_indicator_stopped_compensated _ hCrc⟩
  filter_upwards [hNrc] with ω hω
  exact LocalizedArrayProducer.isRightContinuous_indicator_stoppedProcess ω hω _

end Atoms

end ReflectedGMS.WalkLindeberg
