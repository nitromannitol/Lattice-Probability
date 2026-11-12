/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_1A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD6
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE1
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import Mathlib.Topology.MetricSpace.Sequences

/-!
# CONF Lemma 2.1, part A: deterministic radii and right-continuity (task P2-CONF21)

Source: CONF = Gwynne–Miller, arXiv:1905.00381, `confluence-final.tex`, Lemma 2.1
(`lem-ball-local`, C:476–479) and its proof (C:481–490): "For a deterministic radius `s`, the
event `{𝓑^•_s(z;D_h) ⊂ U}` … is determined by `h|_U`" (C:487–489; for closed balls the
commented-out lines C:483 "This event is determined by the internal metric of `D_h` on `U`, so is
determined by `h|_U` by Axiom II"); the limit step uses that the balls at the dyadic times
`2^{-n}⌈2^n τ⌉` decrease to the ball at `τ` (C:483/490, "local sets behave well under limits",
[QLE, Lemma 6.8]). For balls that last fact is the right-continuity proved here.

* `conf21_aeEventIn_det`: for a deterministic radius `s` and a family `𝒜` of closed, bounded,
  hit-measurable sets which is local for the internal metric (saturation), `{𝒜(D_h, s) ⊆ U}` is
  a.s. an event of `σ(h|_U)` (Axiom II through `LocalEvent.exists_fieldSigma_piece`);
* `conf21_rc_filled`, `conf21_rc_closed`: on `lenSet`, if `𝓑^•_t ⊆ U` (resp. `cl 𝓑_t ⊆ U`),
  `t > 0`, then the same holds at `t + ε` for some `ε > 0`.
The instantiations for filled and closed balls are `conf21_aeEventIn_filled/closed`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF
open GM LocalEvent

/-! ## Deterministic topology -/

/-- on `lenSet`, `{d(z,·) ≤ t} ⊆ cl 𝓑_t(z)` for `t > 0` (geodesics) -/
theorem conf21_le_mem_closure {d : ContMetric} (hd : d ∈ lenSet) {z y : ℂ} {t : ℝ}
    (ht : 0 < t) (hy : d.1 (z, y) ≤ t) : y ∈ closure (ballM d z t) := by
  rcases hy.lt_or_eq with hlt | heq
  · exact subset_closure hlt
  obtain ⟨η, h0, h1, hη⟩ :=
    exists_isGeod01_of_bcpt d (isLength_of_mem_lenSet hd) (bcpt_of_mem_lenSet hd) z y
  have hs : ∀ n : ℕ, (1 : ℝ) - 1 / ((n : ℝ) + 1) ∈ unitInterval := fun n => by
    have a1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have a2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    exact ⟨by linarith, by linarith⟩
  let u : ℕ → unitInterval := fun n => ⟨_, hs n⟩
  have hu : Tendsto u atTop (𝓝 1) := by
    rw [tendsto_subtype_rng]
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    exact this
  have hlim : Tendsto (fun n => η (u n)) atTop (𝓝 y) := by
    rw [← h1]; exact (η.continuous.tendsto 1).comp hu
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  show d.1 (z, η (u n)) < t
  have e := hη 0 (u n)
  rw [h0] at e
  rw [e, heq]
  have a1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have a2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  have : |((u n : unitInterval) : ℝ) - ((0 : unitInterval) : ℝ)| = 1 - 1 / ((n : ℝ) + 1) := by
    simp only [Set.Icc.coe_zero, sub_zero, u]
    exact abs_of_nonneg (by linarith)
  rw [this]
  nlinarith

/-- **robust exterior points**: on `lenSet`, a point outside `𝓑^•_t`, `t > 0`, has a
neighbourhood outside `𝓑^•_{t+ε}` for some `ε > 0` -/
theorem conf21_robust {d : ContMetric} (hd : d ∈ lenSet) (z : ℂ) {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∉ filledBall d z t) :
    ∃ ε > 0, ∃ r > 0, ∀ x' ∈ ball x r, x' ∉ filledBall d z (t + ε) := by
  set C := closure (ballM d z t) with hCdef
  have hO : IsOpen Cᶜ := isClosed_closure.isOpen_compl
  have hxC : x ∉ C := fun h => hx (Or.inl h)
  have hxb : ¬ Bornology.IsBounded (connectedComponentIn Cᶜ x) :=
    fun h => hx (Or.inr ⟨hxC, h⟩)
  obtain ⟨R, hR⟩ := (gm_filledBall_isBounded_of_lenSet hd z (t + 1)).subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨j, n, k, hxj, hball, hk0, hkO, hk1⟩ := (gmE_unbounded_iff hO hxC).1 hxb N
  set ρ := 1 / ((n : ℝ) + 1) with hρ
  set S := closedBall (qd j) ρ ∪ range (gmPth k) with hSdef
  have hSc : IsCompact S :=
    (isCompact_closedBall _ _).union (isCompact_range (gmPth k).continuous)
  have hSO : S ⊆ Cᶜ := union_subset hball hkO
  have hSne : S.Nonempty := ⟨qd j, Or.inl (mem_closedBall_self (by positivity))⟩
  obtain ⟨y₀, hy₀S, hmin⟩ :=
    hSc.exists_isMinOn hSne (gmE_continuous_dist0 d z).continuousOn
  have hgt : ∀ y ∈ S, t < d.1 (z, y) := fun y hy =>
    lt_of_not_ge fun hle => hSO hy (conf21_le_mem_closure hd ht hle)
  have hy₀ := hgt y₀ hy₀S
  set ε := min 1 ((d.1 (z, y₀) - t) / 2) with hεdef
  have hε : 0 < ε := lt_min one_pos (by linarith)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hSC' : S ⊆ (closure (ballM d z (t + ε)))ᶜ := by
    intro y hy hyc
    have h1 : d.1 (z, y) ≤ t + ε := gm_closure_ballM_subset d z (t + ε) hyc
    have h2 : d.1 (z, y₀) ≤ d.1 (z, y) := isMinOn_iff.1 hmin y hy
    have h3 : ε ≤ (d.1 (z, y₀) - t) / 2 := min_le_right _ _
    linarith
  refine ⟨ε, hε, ρ - dist x (qd j), sub_pos.2 hxj, fun x' hx' hx'B => ?_⟩
  have hx'S : x' ∈ S := Or.inl (by
    rw [mem_closedBall]
    have := mem_ball.1 hx'
    linarith [dist_triangle x' x (qd j)])
  have hpre : IsPreconnected S :=
    IsPreconnected.union (gmPth k 0) (by rw [mem_closedBall]; exact hk0.le)
      (mem_range_self 0) (convex_closedBall _ _).isPreconnected
      (isPreconnected_range (gmPth k).continuous)
  have hsub := hpre.subset_connectedComponentIn hx'S hSC'
  have hp : gmPth k 1 ∈ connectedComponentIn (closure (ballM d z (t + ε)))ᶜ x' :=
    hsub (Or.inr (mem_range_self 1))
  rcases hx'B with hc | ⟨-, hbd⟩
  · exact hSC' hx'S hc
  · have hpB : gmPth k 1 ∈ filledBall d z (t + ε) := by
      refine Or.inr ⟨hSC' (Or.inr (mem_range_self 1)), ?_⟩
      rwa [← connectedComponentIn_eq hp]
    have := hR (gm_filledBall_mono d z (by linarith) hpB)
    rw [mem_closedBall, dist_zero_right] at this
    linarith

lemma conf21_eventually_small {ε : ℝ} (hε : 0 < ε) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ᶠ k in atTop, 1 / ((φ k : ℝ) + 1) ≤ ε := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop m] with k hk
  have : (m : ℝ) ≤ φ k := by exact_mod_cast hk.trans (hφ.id_le k)
  exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hm.le

lemma conf21_one_div_le (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]

/-- **right-continuity of filled balls** (on `lenSet`, `t > 0`) -/
theorem conf21_rc_filled {d : ContMetric} (hd : d ∈ lenSet) (z : ℂ) {t : ℝ} (ht : 0 < t)
    {U : Set ℂ} (hU : IsOpen U) (hKU : filledBall d z t ⊆ U) :
    ∃ ε > 0, filledBall d z (t + ε) ⊆ U := by
  by_contra hcon
  push Not at hcon
  choose x hxB hxU using fun n : ℕ => not_subset.1 (hcon (1 / ((n : ℝ) + 1)) (by positivity))
  have hxb : ∀ n, x n ∈ filledBall d z (t + 1) := fun n =>
    gm_filledBall_mono d z (by linarith [conf21_one_div_le n]) (hxB n)
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (gm_filledBall_isBounded_of_lenSet hd z (t + 1)) hxb
  have haU : a ∉ U :=
    hU.isClosed_compl.mem_of_tendsto hlim (Eventually.of_forall fun n => hxU (φ n))
  obtain ⟨ε, hε, r, hr, hrob⟩ := conf21_robust hd z ht (fun h => haU (hKU h))
  have h1 : ∀ᶠ k in atTop, (x ∘ φ) k ∈ ball a r := hlim (ball_mem_nhds a hr)
  obtain ⟨k, hk1, hk2⟩ := (h1.and (conf21_eventually_small hε hφ)).exists
  exact hrob _ hk1 (gm_filledBall_mono d z (by linarith) (hxB (φ k)))

/-! ## Deterministic radii: `{𝒜(D_h, s) ⊆ U}` is determined by `h|_U` (Axiom II) -/

/-- a compact set lies in the open `U` iff it misses a uniform neighbourhood of `Uᶜ` -/
lemma conf21_subset_iff_thick {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) :
    K ⊆ U ↔ ∃ m : ℕ, ¬ (K ∩ thickening (1 / ((m : ℝ) + 1)) Uᶜ).Nonempty := by
  constructor
  · intro hKU
    obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open hU hKU
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun ⟨y, hyK, hyT⟩ => ?_⟩
    obtain ⟨w, hwU, hw⟩ := mem_thickening_iff.1 hyT
    exact hwU (hδK (mem_thickening_iff.2 ⟨y, hyK, by rw [dist_comm]; linarith⟩))
  · rintro ⟨m, hm⟩ y hyK
    by_contra hyU
    exact hm ⟨y, hyK, self_subset_thickening (by positivity) _ hyU⟩

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **CONF C:487–489 (deterministic radius)**: for a family `𝒜` of closed sets, bounded on
`lenSet`, with measurable hitting events and determined by the internal metric on any open set
containing it, `{𝒜(D_h, s) ⊆ U}` is a.s. an event of `σ(h|_U)`. -/
theorem conf21_aeEventIn_det {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) (𝒜 : ContMetric → ℝ → Set ℂ)
    (hb : ∀ d ∈ lenSet, ∀ s, Bornology.IsBounded (𝒜 d s)) (hc : ∀ d s, IsClosed (𝒜 d s))
    (hhit : ∀ s V, IsOpen V → MeasurableSet {d | (𝒜 d s ∩ V).Nonempty})
    (hsat : ∀ (d₁ d₂ : ContMetric) (s : ℝ) (U : Set ℂ), IsOpen U → d₁ ∈ lenSet → d₂ ∈ lenSet →
      d₁.internal U = d₂.internal U → 𝒜 d₁ s ⊆ U → 𝒜 d₂ s ⊆ U)
    (s : ℝ) (U : Set ℂ) (hU : IsOpen U) :
    AEEventIn P (fieldSigma h (toOpens U hU)) {ω | 𝒜 (D (h ω)) s ⊆ U} := by
  have hgp := detGFFPlusCont hh
  set M : Set ContMetric :=
    ⋃ m : ℕ, {d | (𝒜 d s ∩ thickening (1 / ((m : ℝ) + 1)) Uᶜ).Nonempty}ᶜ with hM
  have hMm : MeasurableSet M :=
    MeasurableSet.iUnion fun m => (hhit s _ isOpen_thickening).compl
  have hMe : ∀ d ∈ lenSet, (𝒜 d s ⊆ U ↔ d ∈ M) := fun d hd => by
    rw [conf21_subset_iff_thick (isCompact_of_isClosed_isBounded (hc d s) (hb d hd s)) hU]
    simp only [hM, mem_iUnion, mem_compl_iff, mem_ofPred_eq]
  set Bs : Set DistC := {g | 𝒜 (D g) s ⊆ U}
  have hnull : NullMeasurableSet Bs (P.map h) := by
    have hL : ∀ᵐ g ∂(P.map h), D g ∈ lenSet :=
      (ae_map_iff hgp.1.aemeasurable (measurableSet_lenSet.preimage hD.measurable)).2 hlen
    refine (hMm.preimage hD.measurable).nullMeasurableSet.congr ?_
    filter_upwards [hL] with g hg
    exact propext (hMe _ hg).symm
  exact exists_fieldSigma_piece hD P h hgp hlen hU hnull
    fun g₁ g₂ h1 h2 he hB => hsat _ _ s U hU h1 h2 he hB

/-- filled balls are determined by the internal metric on an open set containing them -/
theorem conf21_sat_filled (d₁ d₂ : ContMetric) (z : ℂ) (s : ℝ) (U : Set ℂ) (hU : IsOpen U)
    (h1 : d₁ ∈ lenSet) (h2 : d₂ ∈ lenSet) (he : d₁.internal U = d₂.internal U)
    (hB : filledBall d₁ z s ⊆ U) : filledBall d₂ z s ⊆ U := by
  rcases le_or_gt s 0 with hs | hs
  · rw [gm_filledBall_nonpos d₂ z hs]; exact empty_subset _
  have hball := gm_ballM_eq_of_internal_eq (isLength_of_mem_lenSet h1)
    (isLength_of_mem_lenSet h2) hU (fun x _ y _ => by rw [he]) hs
    (subset_closure.trans (subset_union_left.trans hB))
  rwa [gm_filledBall_congr hball]

theorem conf21_hit_filled (z : ℂ) (s : ℝ) (V : Set ℂ) (hV : IsOpen V) :
    MeasurableSet {d : ContMetric | (filledBall d z s ∩ V).Nonempty} := by
  have e : {d : ContMetric | (filledBall d z s ∩ V).Nonempty} =
      ⋃ i, {_d : ContMetric | TopologicalSpace.denseSeq ℂ i ∈ V} ∩
        {d | TopologicalSpace.denseSeq ℂ i ∈ filledBall d z s} := by
    ext d; simp only [mem_ofPred_eq, gm_filledBall_inter_open_iff _ _ _ hV, mem_iUnion,
      mem_inter_iff]
  rw [e]
  exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
    ((gmE_measurableSet_filledBall z).preimage
      (measurable_id.prodMk (measurable_const.prodMk measurable_const)))

end LQGMetric.CONF
