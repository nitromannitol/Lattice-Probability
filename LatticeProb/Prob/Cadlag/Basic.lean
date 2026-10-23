import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# Càdlàg paths on a compact time interval

The time domain is the closed real interval. Right continuity is required before the
terminal time, and left limits are required after the initial time. These conditions
imply boundedness without a completeness assumption on the range.
-/

namespace LatticeProb.Cadlag

open Set Filter
open scoped Topology

variable {T : ℝ} {E : Type*} [NormedAddCommGroup E]

/-- Right-continuous with left limits on `[0,T]`. -/
def IsCadlag (T : ℝ) (x : Icc (0 : ℝ) T → E) : Prop :=
  (∀ t : Icc (0 : ℝ) T, (t : ℝ) < T → ContinuousWithinAt x {s | t ≤ s} t) ∧
  (∀ t : Icc (0 : ℝ) T, 0 < (t : ℝ) →
    ∃ l : E, Tendsto x (nhdsWithin t {s | s < t}) (𝓝 l))

/-- The space `D([0,T]; E)` of càdlàg paths, before equipping it with its metric. -/
def D (T : ℝ) (E : Type*) [NormedAddCommGroup E] : Type _ :=
  {x : Icc (0 : ℝ) T → E // IsCadlag T x}

/-- Continuous paths are càdlàg, with their value as each left limit. -/
theorem isCadlag_of_continuous {x : Icc (0 : ℝ) T → E} (hx : Continuous x) :
    IsCadlag T x :=
  ⟨fun _ _ => hx.continuousAt.continuousWithinAt,
    fun t _ => ⟨x t, hx.continuousAt.mono_left nhdsWithin_le_nhds⟩⟩

/-- A càdlàg path has an eventual norm bound on each side of every time. -/
theorem IsCadlag.eventually_norm_le {x : Icc (0 : ℝ) T → E} (hx : IsCadlag T x)
    (t : Icc (0 : ℝ) T) : ∃ M : ℝ, ∀ᶠ s in 𝓝 t, ‖x s‖ ≤ M := by
  have hleft : ∃ M : ℝ, ∀ᶠ s in 𝓝[<] t, ‖x s‖ ≤ M := by
    by_cases ht : 0 < (t : ℝ)
    · obtain ⟨l, hl⟩ := hx.2 t ht
      exact hl.norm.isBoundedUnder_le
    · refine ⟨0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact False.elim (ht (lt_of_le_of_lt s.property.1 hs))
  have hright : ∃ M : ℝ, ∀ᶠ s in 𝓝[≥] t, ‖x s‖ ≤ M := by
    by_cases ht : (t : ℝ) < T
    · exact (hx.1 t ht).norm.isBoundedUnder_le
    · refine ⟨‖x t‖, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      have heq : s = t := Subtype.ext (le_antisymm
        (le_trans s.property.2 (le_of_not_gt ht)) hs)
      exact heq ▸ le_rfl
  obtain ⟨L, hL⟩ := hleft
  obtain ⟨R, hR⟩ := hright
  refine ⟨max L R, ?_⟩
  rw [← nhdsLT_sup_nhdsGE t, eventually_sup]
  exact ⟨hL.mono fun _ h => h.trans (le_max_left _ _),
    hR.mono fun _ h => h.trans (le_max_right _ _)⟩

/-- Càdlàg paths on a compact interval are bounded in norm. -/
theorem IsCadlag.exists_norm_le {x : Icc (0 : ℝ) T → E} (hx : IsCadlag T x) :
    ∃ M : ℝ, ∀ t, ‖x t‖ ≤ M := by
  have hb : Bornology.IsBounded (x '' univ) := by
    apply Bornology.isBounded_image_of_isLocallyBounded_of_isCompact isCompact_univ
    intro t
    obtain ⟨M, hM⟩ := hx.eventually_norm_le t
    refine ⟨{s | ‖x s‖ ≤ M}, hM, isBounded_iff_forall_norm_le.mpr ⟨M, ?_⟩⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  exact ⟨M, fun t => hM _ (mem_image_of_mem _ (mem_univ t))⟩

/-- A constant path is càdlàg. -/
theorem isCadlag_const (a : E) : IsCadlag T (fun _ => a) :=
  isCadlag_of_continuous continuous_const

/-- The constant càdlàg path with value `a`. -/
def const (T : ℝ) (a : E) : D T E := ⟨fun _ => a, isCadlag_const a⟩

/-- The constant path evaluates to its defining value. -/
@[simp] theorem const_apply (a : E) (t : Icc (0 : ℝ) T) : (const T a).1 t = a := rfl

/-- A continuous path regarded as a càdlàg path. -/
def ofContinuous (x : C(Icc (0 : ℝ) T, E)) : D T E :=
  ⟨x, isCadlag_of_continuous x.continuous⟩

/-- The continuous-path inclusion does not change evaluations. -/
@[simp] theorem ofContinuous_apply (x : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    (ofContinuous x).1 t = x t := rfl

/-- A path constant on either side of one jump, taking its right value at the jump. -/
noncomputable def jumpPath (a : ℝ) (u v : E) (t : Icc (0 : ℝ) T) : E :=
  if (t : ℝ) < a then u else v

/-- A single-jump path is càdlàg, including when the jump is at an endpoint. -/
theorem isCadlag_jumpPath (a : ℝ) (u v : E) : IsCadlag T (jumpPath a u v) := by
  constructor
  · intro t _
    by_cases ht : (t : ℝ) < a
    · have he : jumpPath a u v =ᶠ[𝓝[{s | t ≤ s}] t] fun _ => u := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
          ((continuous_subtype_val.tendsto t).eventually (Iio_mem_nhds ht))] with s hs
        exact if_pos hs
      change Tendsto (jumpPath a u v) _ (𝓝 (jumpPath a u v t))
      rw [show jumpPath a u v t = u from if_pos ht]
      exact he.tendsto
    · have he : jumpPath a u v =ᶠ[𝓝[{s | t ≤ s}] t] fun _ => v := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact if_neg (not_lt.mpr ((le_of_not_gt ht).trans hs))
      change Tendsto (jumpPath a u v) _ (𝓝 (jumpPath a u v t))
      rw [show jumpPath a u v t = v from if_neg ht]
      exact he.tendsto
  · intro t _
    by_cases ht : (t : ℝ) ≤ a
    · refine ⟨u, Filter.EventuallyEq.tendsto ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact if_pos (lt_of_lt_of_le (show (s : ℝ) < (t : ℝ) from hs) ht)
    · refine ⟨v, Filter.EventuallyEq.tendsto ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((continuous_subtype_val.tendsto t).eventually
          (Ioi_mem_nhds (lt_of_not_ge ht)))] with s hs
      exact if_neg (not_lt.mpr hs.le)

/-- The càdlàg path with a single jump at `a`. -/
noncomputable def jump (T a : ℝ) (u v : E) : D T E :=
  ⟨jumpPath a u v, isCadlag_jumpPath a u v⟩

/-- The single-jump constructor has the specified values. -/
@[simp] theorem jump_apply (a : ℝ) (u v : E) (t : Icc (0 : ℝ) T) :
    (jump T a u v).1 t = if (t : ℝ) < a then u else v := rfl

/-- Values on a dense time set containing the terminal time determine a càdlàg path. -/
theorem eq_of_eval_eq_on_dense {S : Set (Icc (0 : ℝ) T)} (hS : Dense S)
    (hterminal : ∀ t : Icc (0 : ℝ) T, (t : ℝ) = T → t ∈ S)
    {x y : D T E} (hxy : ∀ t ∈ S, x.1 t = y.1 t) : x = y := by
  apply Subtype.ext
  funext t
  by_cases ht : (t : ℝ) < T
  · apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δx, hδx, hx⟩ := (Metric.continuousWithinAt_iff.mp (x.2.1 t ht))
      (ε / 2) (half_pos hε)
    obtain ⟨δy, hδy, hy⟩ := (Metric.continuousWithinAt_iff.mp (y.2.1 t ht))
      (ε / 2) (half_pos hε)
    have hgap : 0 < T - (t : ℝ) := sub_pos.mpr ht
    let δ := min δx (min δy (T - t)) / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδx' : δ < δx := by
      have := min_le_left δx (min δy (T - t))
      dsimp [δ] at *
      linarith
    have hδy' : δ < δy := by
      have := (min_le_right δx (min δy (T - t))).trans (min_le_left _ _)
      dsimp [δ] at *
      linarith
    have hδT : δ < T - t := by
      have := (min_le_right δx (min δy (T - t))).trans (min_le_right _ _)
      dsimp [δ] at *
      linarith
    let u : Icc (0 : ℝ) T := ⟨t + δ, by constructor <;> linarith [t.property.1]⟩
    have htu : t < u := by change (t : ℝ) < t + δ; linarith
    obtain ⟨s, hs, hts, hsu⟩ := hS.exists_between htu
    have hdist : dist s t < δ := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr (show (t : ℝ) < (s : ℝ) from hts))]
      change (s : ℝ) < (u : ℝ) at hsu
      dsimp [u] at hsu
      linarith
    have hxs := hx hts.le (hdist.trans hδx')
    have hys := hy hts.le (hdist.trans hδy')
    rw [← hxy s hs] at hys
    have htriangle := dist_triangle (x.1 t) (x.1 s) (y.1 t)
    rw [dist_comm (x.1 s) (x.1 t)] at hxs
    linarith
  · exact hxy t (hterminal t (le_antisymm t.property.2 (le_of_not_gt ht)))

end LatticeProb.Cadlag
