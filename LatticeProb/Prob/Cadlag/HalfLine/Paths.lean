import LatticeProb.Prob.Cadlag.HalfLine.Defs
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

/-!
# Operations on half-line càdlàg paths

Local boundedness and stability under stopping and increasing time changes are proved
from right continuity and genuine left limits.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped Topology

variable {E : Type*} [MetricSpace E] {x y : Time → E}

/-- A càdlàg path is locally bounded at every half-line time. -/
theorem IsCadlag.eventually_dist_le (hx : IsCadlag x) (t : Time) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 t, dist (x s) (x t) ≤ M := by
  have hleft : ∃ M : ℝ, ∀ᶠ s in 𝓝[<] t, dist (x s) (x t) ≤ M := by
    by_cases ht : 0 < t
    · obtain ⟨l, hl⟩ := hx.2 t ht
      exact (hl.dist tendsto_const_nhds).isBoundedUnder_le
    · refine ⟨0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact False.elim (ht (lt_of_le_of_lt (show (0 : Time) ≤ s from zero_le) hs))
  obtain ⟨L, hL⟩ := hleft
  obtain ⟨R, hR⟩ := ((hx.1 t).dist continuousWithinAt_const).isBoundedUnder_le
  refine ⟨max L R, ?_⟩
  rw [← nhdsLT_sup_nhdsGE t, eventually_sup]
  exact ⟨hL.mono fun _ h => h.trans (le_max_left _ _),
    hR.mono fun _ h => h.trans (le_max_right _ _)⟩

/-- A càdlàg path has bounded image on each compact initial interval. -/
theorem IsCadlag.isBounded_image_Icc (hx : IsCadlag x) (T : Time) :
    Bornology.IsBounded (x '' Icc 0 T) := by
  apply Bornology.isBounded_image_of_isLocallyBounded_of_isCompact isCompact_Icc
  intro t
  obtain ⟨M, hM⟩ := hx.eventually_dist_le t
  refine ⟨{s | dist (x s) (x t) ≤ M}, hM,
    (Metric.isBounded_closedBall (x := x t) (r := M)).subset ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact hs

/-- Increasing onto time changes preserve half-line càdlàg paths. -/
theorem IsCadlag.comp_lambdaPrime (hx : IsCadlag x) (l : LambdaPrime) :
    IsCadlag (x ∘ l) := by
  constructor
  · intro t
    exact (hx.1 (l t)).comp l.continuous.continuousWithinAt
      (fun s hs => l.monotone hs)
  · intro t ht
    have hlt : 0 < l t := (show (0 : Time) ≤ l 0 from zero_le).trans_lt (l.strictMono ht)
    obtain ⟨a, ha⟩ := hx.2 (l t) hlt
    refine ⟨a, ha.comp ?_⟩
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨l.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact l.strictMono hs

/-- Stopping at a fixed half-line time preserves the càdlàg property. -/
theorem IsCadlag.stop (hx : IsCadlag x) (u : Time) :
    IsCadlag (fun t => x (min t u)) := by
  constructor
  · intro t
    have hm : ContinuousWithinAt (fun s : Time => min s u) (Ici t) t :=
      (continuous_id.min continuous_const).continuousWithinAt
    exact (hx.1 (min t u)).comp (f := fun s : Time => min s u) hm
      (fun s hs => min_le_min_right u hs)
  · intro t ht
    by_cases htu : t ≤ u
    · obtain ⟨a, ha⟩ := hx.2 t ht
      refine ⟨a, ha.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [min_eq_left (hs.le.trans htu)]
    · refine ⟨x u, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [mem_inf_of_left (Ioi_mem_nhds (lt_of_not_ge htu))] with s hs
      rw [min_eq_right hs.le]

/-- Stop a bundled half-line path at a fixed time. -/
def D.stop (x : D E) (u : Time) : D E := ⟨fun t => x.1 (min t u), x.2.stop u⟩

/-- Compose a bundled half-line path with an increasing onto time change. -/
def D.comp (x : D E) (l : LambdaPrime) : D E := ⟨x.1 ∘ l, x.2.comp_lambdaPrime l⟩

/-- Points where no open neighborhood has image diameter less than `ε`. -/
private def oscillationSet (x : Time → E) (ε : ℝ) : Set Time :=
  {t | ¬ ∃ U : Set Time, IsOpen U ∧ t ∈ U ∧
    ∀ a ∈ U, ∀ b ∈ U, dist (x a) (x b) < ε}

/-- Right continuity makes each positive oscillation set right-isolated. -/
private theorem IsCadlag.countable_oscillationSet (hx : IsCadlag x)
    {ε : ℝ} (hε : 0 < ε) : (oscillationSet x ε).Countable := by
  suffices h : ∀ t ∈ oscillationSet x ε,
      𝓝[oscillationSet x ε ∩ Ioi t] t = ⊥ by
    exact (countable_setOf_isolated_right_within
      (s := oscillationSet x ε)).mono (by
        intro t ht
        exact ⟨ht, h t ht⟩)
  intro t _
  have he := (hx.1 t) (Metric.ball_mem_nhds (x t) (half_pos hε))
  obtain ⟨U, hU, htU, hsub⟩ := mem_nhdsWithin.mp he
  apply empty_mem_iff_bot.mp
  apply mem_nhdsWithin.mpr
  refine ⟨U, hU, htU, ?_⟩
  rintro s ⟨hsU, hsbad, hts⟩
  apply hsbad
  refine ⟨U ∩ Ioi t, hU.inter isOpen_Ioi, ⟨hsU, hts⟩, ?_⟩
  intro a ha b hb
  have ha' := hsub ⟨ha.1, (show t < a from ha.2).le⟩
  have hb' := hsub ⟨hb.1, (show t < b from hb.2).le⟩
  have htri := dist_triangle (x a) (x t) (x b)
  rw [dist_comm (x t) (x b)] at htri
  exact htri.trans_lt (by
    change dist (x a) (x t) < ε / 2 at ha'
    change dist (x b) (x t) < ε / 2 at hb'
    linarith)

/-- A half-line càdlàg path has at most countably many discontinuities. -/
theorem IsCadlag.countable_discontinuities (hx : IsCadlag x) :
    {t | ¬ ContinuousAt x t}.Countable := by
  have hc : (⋃ n : ℕ, oscillationSet x (1 / (n + 1 : ℝ))).Countable :=
    countable_iUnion fun n => hx.countable_oscillationSet (by positivity)
  apply hc.mono
  intro t ht
  by_contra hnot
  apply ht
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hgood : t ∉ oscillationSet x (1 / (n + 1 : ℝ)) := by
    intro hbad
    exact hnot (mem_iUnion.mpr ⟨n, hbad⟩)
  obtain ⟨U, hU, htU, hdiam⟩ := not_not.mp hgood
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds htU)
  exact ⟨δ, hδ, fun s hs => (hdiam s (hball hs) t htU).trans hn⟩

/-- Two right-continuous paths agreeing on a dense set agree everywhere. -/
theorem IsCadlag.eq_of_eqOn_dense (hx : IsCadlag x) (hy : IsCadlag y)
    {S : Set Time} (hS : Dense S) (h : ∀ t ∈ S, x t = y t) : x = y := by
  funext t
  have hn : NeBot (𝓝[S ∩ Ioi t] t) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [mem_closure_iff]
    intro U hU htU
    have hne : (U ∩ Ioi t).Nonempty := by
      have hm : U ∩ Ioi t ∈ 𝓝[>] t :=
        inter_mem (mem_inf_of_left (hU.mem_nhds htU)) self_mem_nhdsWithin
      exact Filter.nonempty_of_mem hm
    obtain ⟨s, hs⟩ := hS.inter_open_nonempty (U ∩ Ioi t) (hU.inter isOpen_Ioi) hne
    exact ⟨s, hs.1.1, hs.2, hs.1.2⟩
  letI := hn
  have hsub : S ∩ Ioi t ⊆ Ici t := by
    intro s hs
    exact (show t < s from hs.2).le
  exact tendsto_nhds_unique ((hx.1 t).mono hsub)
    (((hy.1 t).mono hsub).congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (h s hs.1).symm))

/-- The continuity points of a half-line càdlàg path are dense. -/
theorem IsCadlag.dense_continuity_points (hx : IsCadlag x) :
    Dense {t | ContinuousAt x t} := by
  apply dense_iff_exists_between.mpr
  intro a b hab
  by_contra hnone
  have hbad : Ioo a b ⊆ {t | ¬ ContinuousAt x t} := by
    intro t ht hct
    exact hnone ⟨t, hct, ht.1, ht.2⟩
  have hc := (hx.countable_discontinuities.mono hbad).image (fun t : Time => (t : ℝ))
  have hr : (Ioo (a : ℝ) (b : ℝ)).Countable := hc.mono (by
    intro r hr
    refine ⟨⟨r, (show (0 : ℝ) ≤ a from a.2).trans hr.1.le⟩, ?_, rfl⟩
    exact hr)
  exact (not_le_of_gt hab) (Cardinal.Real.Ioo_countable_iff.mp hr)

end LatticeProb.Cadlag.HalfLine
