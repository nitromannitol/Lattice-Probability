/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event5C6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event5Dense

/-!
# GM Lemma 5.9: condition (6) of `E_r` is universally measurable (task P2-M2M8)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.9
(`lem-geo-event-msrble`, l. 3293–3302), condition (6) of `E_r` (l. 3249–3251): every path in
`B_{2ζr}(∂U_r^{x,y})` of Euclidean diameter `≥ ε₀r/100` has `D_h`-length `≥ 100 A 𝔠_r e^{ξ h_r(0)}`.
Own elementary argument, as condition 2 of `𝖤_r(z)` (`uMeasurableSet_gaLongB`, decision D30):

* the tubes `U x y` come from a finite family (`sqTubes`), so (6) is a countable intersection;
* for one open set `O`, paths are replaced by `η ∈ C([0,1], ℂ)` (`forall_path_iff`); "`range η ⊆ O`"
  is open, `η ↦ diam(range η)` is lower semicontinuous (`lowerSemicontinuous_ediam_range`) and
  `(g, η) ↦ len(η; D_g)` is Borel (`measurable_lenPath`), so the set is coanalytic
  (`UMeasurableSet.setOf_forall`, Lusin).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `η ↦ ediam (range η)` is lower semicontinuous -/
lemma lowerSemicontinuous_ediam_range :
    LowerSemicontinuous fun η : C(unitInterval, ℂ) => ediam (range η) := by
  have e : (fun η : C(unitInterval, ℂ) => ediam (range η)) =
      fun η => ⨆ s : unitInterval, ⨆ t : unitInterval, edist (η s) (η t) := by
    funext η; simp only [ediam, iSup_range]
  rw [e]
  exact lowerSemicontinuous_iSup fun s => lowerSemicontinuous_iSup fun t =>
    ((continuous_eval_const s).edist (continuous_eval_const t)).lowerSemicontinuous

lemma le_diam_range_iff_e5 (c : ℝ) (η : C(unitInterval, ℂ)) :
    c ≤ diam (range η) ↔ ENNReal.ofReal c ≤ ediam (range η) := by
  rw [Metric.diam, ENNReal.ofReal_le_iff_le_toReal
    (isCompact_range η.continuous).isBounded.ediam_ne_top]

/-- the Borel relation behind condition (6), for one open set `O` -/
def c6PathSet (D : DistC → ContMetric) (O : Set ℂ) (c k ξ : ℝ) (cc : ℝ → ℝ) (r : ℝ) :
    Set (DistC × C(unitInterval, ℂ)) :=
  {p | range p.2 ⊆ O → ENNReal.ofReal c ≤ ediam (range p.2) →
    ENNReal.ofReal (k * scaleFac ξ cc p.1 r 0) ≤ (D p.1).len (fun t => p.2 (pj t)) 0 1}

set_option maxHeartbeats 1000000 in
lemma measurableSet_c6PathSet {D : DistC → ContMetric} (hD : Measurable D) {O : Set ℂ}
    (hO : IsOpen O) (c k ξ : ℝ) (cc : ℝ → ℝ) (r : ℝ) :
    MeasurableSet (c6PathSet D O c k ξ cc r) := by
  have hopen : IsOpen {η : C(unitInterval, ℂ) | range η ⊆ O} := by
    have : {η : C(unitInterval, ℂ) | range η ⊆ O} =
        {η : C(unitInterval, ℂ) | MapsTo η univ O} := by
      ext η; simp only [mem_ofPred_eq, mapsTo_univ_iff, range_subset_iff]
    rw [this]
    exact ContinuousMap.isOpen_setOfPred_mapsTo (X := unitInterval) (Y := ℂ) isCompact_univ hO
  have m1 := measurable_of_set (hopen.measurableSet.preimage (measurable_snd (α := DistC)))
  have m2 := measurable_of_set (measurableSet_le (measurable_const (a := ENNReal.ofReal c))
    (lowerSemicontinuous_ediam_range.measurable.comp (measurable_snd (α := DistC))))
  have m3 := measurable_of_set (measurableSet_le
    ((measurable_ofReal_scaleFac k ξ cc r).comp measurable_fst) (measurable_lenPath hD))
  exact measurableSet_setOfPred.2 (m1.imp (m2.imp m3))

/-- condition (6) for one tube `W` -/
def c6Set (D : DistC → ContMetric) (S : EData) (r : ℝ) (W : Set ℂ) : Set DistC :=
  {g | ∀ (P : ℝ → ℂ) (s t : ℝ), s ≤ t → ContinuousOn P (Icc s t) →
    P '' Icc s t ⊆ thickening (2 * S.ζ * r) (frontier W) →
    S.ε₀ * r / 100 ≤ diam (P '' Icc s t) →
    ENNReal.ofReal (100 * S.A * scaleFac S.ξ S.c g r 0) ≤ (D g).len P s t}

/-- **condition (6) for one tube is universally measurable** (coanalytic) -/
theorem uMeasurableSet_c6Set {D : DistC → ContMetric} (hD : Measurable D) (S : EData) (r : ℝ)
    (W : Set ℂ) : UMeasurableSet (c6Set D S r W) := by
  set O := thickening (2 * S.ζ * r) (frontier W)
  convert UMeasurableSet.setOf_forall (measurableSet_c6PathSet hD isOpen_thickening
    (S.ε₀ * r / 100) (100 * S.A) S.ξ S.c r) using 1
  ext g
  have key := forall_path_iff (D g) (fun _ _ I l => I ⊆ O → S.ε₀ * r / 100 ≤ diam I →
    ENNReal.ofReal (100 * S.A * scaleFac S.ξ S.c g r 0) ≤ l)
  simp only [c6Set, c6PathSet, mem_ofPred_eq]
  constructor
  · intro H η hO hd
    exact key.1 (fun a b P hab hP => H P a b hab hP) η hO ((le_diam_range_iff_e5 _ η).2 hd)
  · intro H P s t hst hP
    exact key.2 (fun η hO hd => H η hO ((le_diam_range_iff_e5 _ η).1 hd)) s t P hst hP

/-- **condition (6) is universally measurable** -/
theorem uMeasurableSet_eventC6 {D : DistC → ContMetric} (hDm : Measurable D)
    (D' : DistC → ContMetric) {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r) (fb gb : Set ℂ → TestC) :
    UMeasurableSet (eventC6 D D' S U fb gb r) := by
  set I : Set (ℂ × ℂ) := {z | z.1 ∈ sphere (0 : ℂ) (2 * r) ∧ z.2 ∈ sphere (0 : ℂ) (2 * r) ∧
    S.δ * r ≤ ‖z.1 - z.2‖}
  have e : eventC6 D D' S U fb gb r = ⋂ W ∈ (fun z : ℂ × ℂ => U z.1 z.2) '' I, c6Set D S r W := by
    ext g
    simp only [mem_iInter]
    constructor
    · rintro H _ ⟨z, ⟨hz1, hz2, hz3⟩, rfl⟩
      exact H z.1 hz1 z.2 hz2 hz3
    · intro H x hx y hy hxy
      exact H _ ⟨(x, y), ⟨hx, hy, hxy⟩, rfl⟩
  have hε0 : 0 < S.ε₀ * r := mul_pos hS.2.2.2.2.1.1 hr
  have hT := sqTubes_finite_m2m2 (S.ε₀ * r) (squareSet_finite_m2m2 (R := 3 * r) hε0
    (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) (fun w hw => by
      rw [mem_ball, dist_zero_right]; linarith [hw.2]))
  have hc : ((fun z : ℂ × ℂ => U z.1 z.2) '' I).Countable := by
    refine hT.countable.mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact tube_mem_sqTubes_m2m2 (hU z.1 hz.1 z.2 hz.2.1 hz.2.2).2.2.2.1
  rw [e, biInter_eq_iInter]
  have := hc.to_subtype
  exact UMeasurableSet.iInter fun W => uMeasurableSet_c6Set hDm S r W

theorem l59MeasOf_eventC6 : L59MeasOf eventC6 := by
  intro γ D D' c cs Cs hPS _ _ _ S _ _ _ _ hS r hr U fb gb hU _ Ω _ P _ h hh
  exact (uMeasurableSet_eventC6 hPS.2.2.1.measurable D' hS hr hU fb gb).nullMeasurableSet _

end LQGMetric.GM
