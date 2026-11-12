/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P2F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P2E
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Measurable continuous extension from a countable dense set (tool for the glued metric)

A function on `ℂ × ℂ` given only through its values at the points `Q a` of the dense sequence
`Q = denseSeq (ℂ × ℂ)` is turned into an element of `C(ℂ × ℂ, ℝ)`: `extQ u p` is the limit of
`u a` as `Q a → p`; if `u` is locally uniformly continuous on `Q` (`IsLUCQ`, a countable
condition) this is continuous (`continuous_extQ`), otherwise the junk value `0` is used
(`contQ`). For a continuous `F`, `contQ (F ∘ Q) = F` (`contQ_comp`), and `x ↦ contQ (u x)` is
measurable whenever each `x ↦ u x a` is (`measurable_contQ`). This replaces `toCMap`, whose
composition with a pointwise-defined family need not be measurable. Own elementary argument
(measurability is implicit in the paper, T:1349 "a measurable function `h ↦ D_h`"; DEVIATIONS).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.DFGPS.T12

/-- the dense sequence of `ℂ × ℂ` -/
abbrev Qd : ℕ → ℂ × ℂ := denseSeq (ℂ × ℂ)

/-- the limit of `u a` as `Q a → p` -/
def extQ (u : ℕ → ℝ) (p : ℂ × ℂ) : ℝ := limUnder (comap Qd (𝓝 p)) u

/-- local uniform continuity of `u` along the dense sequence (countably many conditions) -/
def IsLUCQ (u : ℕ → ℝ) : Prop :=
  ∀ R m : ℕ, ∃ j : ℕ, ∀ a b : ℕ, ‖Qd a‖ ≤ R → ‖Qd b‖ ≤ R → dist (Qd a) (Qd b) < 1 / (j + 1) →
    |u a - u b| ≤ 1 / (m + 1)

instance comap_Qd_neBot (p : ℂ × ℂ) : (comap Qd (𝓝 p)).NeBot :=
  comap_neBot fun t ht => by
    obtain ⟨_, ⟨a, rfl⟩, hz⟩ := Dense.inter_nhds_nonempty (denseRange_denseSeq (ℂ × ℂ)) ht
    exact ⟨a, hz⟩

theorem one_div_succ_pos (m : ℕ) : (0 : ℝ) < 1 / (m + 1) := by positivity

theorem exists_one_div_lt {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, 1 / ((m : ℝ) + 1) < ε := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact ⟨m, hm⟩

theorem tendsto_extQ {u : ℕ → ℝ} (hu : IsLUCQ u) (p : ℂ × ℂ) :
    Tendsto u (comap Qd (𝓝 p)) (𝓝 (extQ u p)) := by
  have hc : Cauchy (map u (comap Qd (𝓝 p))) := by
    rw [Metric.cauchy_iff]
    refine ⟨map_neBot, fun ε hε => ?_⟩
    obtain ⟨m, hm⟩ := exists_one_div_lt hε
    obtain ⟨j, hj⟩ := hu (⌈‖p‖⌉₊ + 1) m
    set r := min 1 (1 / (2 * ((j : ℝ) + 1))) with hr
    have hr0 : 0 < r := lt_min one_pos (by positivity)
    refine ⟨u '' (Qd ⁻¹' ball p r), image_mem_map (preimage_mem_comap (ball_mem_nhds p hr0)), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hR : ∀ c, Qd c ∈ ball p r → ‖Qd c‖ ≤ (⌈‖p‖⌉₊ + 1 : ℕ) := fun c hc => by
      have h1 : dist (Qd c) p < 1 := hc.trans_le (min_le_left _ _)
      have h2 := norm_le_of_mem_closedBall (mem_closedBall.2 h1.le)
      push_cast
      linarith [Nat.le_ceil ‖p‖]
    have hab : dist (Qd a) (Qd b) < 1 / ((j : ℝ) + 1) := by
      have h1 : dist (Qd a) p < 1 / (2 * ((j : ℝ) + 1)) := (mem_ball.1 ha).trans_le (min_le_right _ _)
      have h2 : dist (Qd b) p < 1 / (2 * ((j : ℝ) + 1)) := (mem_ball.1 hb).trans_le (min_le_right _ _)
      have h3 := dist_triangle_right (Qd a) (Qd b) p
      have h4 : 1 / (2 * ((j : ℝ) + 1)) + 1 / (2 * ((j : ℝ) + 1)) = 1 / ((j : ℝ) + 1) := by
        field_simp; ring
      linarith
    rw [Real.dist_eq]
    exact (hj a b (hR a ha) (hR b hb) hab).trans_lt hm
  obtain ⟨c, hc'⟩ := cauchy_iff_exists_le_nhds.1 hc
  exact tendsto_nhds_limUnder ⟨c, hc'⟩

theorem continuous_extQ {u : ℕ → ℝ} (hu : IsLUCQ u) : Continuous (extQ u) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_one_div_lt (show 0 < ε / 2 by positivity)
  obtain ⟨j, hj⟩ := hu (⌈‖p‖⌉₊ + 2) m
  set r := min 1 (1 / (3 * ((j : ℝ) + 1))) with hr
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  filter_upwards [ball_mem_nhds p hr0] with q hq
  have hη : 0 < ε / 8 := by positivity
  -- points of the sequence close to `q` and `p` with values close to the limits
  have hq' := (tendsto_extQ hu q).eventually (ball_mem_nhds (extQ u q) hη)
  have hp' := (tendsto_extQ hu p).eventually (ball_mem_nhds (extQ u p) hη)
  have hq2 : ∀ᶠ a in comap Qd (𝓝 q), Qd a ∈ ball q (r - dist q p) :=
    preimage_mem_comap (ball_mem_nhds q (by have := mem_ball.1 hq; linarith))
  have hp2 : ∀ᶠ a in comap Qd (𝓝 p), Qd a ∈ ball p r := preimage_mem_comap (ball_mem_nhds p hr0)
  obtain ⟨a, ha1, ha2⟩ := (hq'.and hq2).exists
  obtain ⟨b, hb1, hb2⟩ := (hp'.and hp2).exists
  have hap : dist (Qd a) p < r := by
    have := dist_triangle (Qd a) q p; rw [mem_ball] at ha2; linarith
  have hbp : dist (Qd b) p < r := hb2
  have hR : ∀ c, dist (Qd c) p < r → ‖Qd c‖ ≤ (⌈‖p‖⌉₊ + 2 : ℕ) := fun c hc => by
    have h1 : dist (Qd c) p < 1 := hc.trans_le (min_le_left _ _)
    have h2 := norm_le_of_mem_closedBall (mem_closedBall.2 h1.le)
    push_cast
    linarith [Nat.le_ceil ‖p‖]
  have hab : dist (Qd a) (Qd b) < 1 / ((j : ℝ) + 1) := by
    have h1 : dist (Qd a) p < 1 / (3 * ((j : ℝ) + 1)) := hap.trans_le (min_le_right _ _)
    have h2 : dist (Qd b) p < 1 / (3 * ((j : ℝ) + 1)) := hbp.trans_le (min_le_right _ _)
    have h3 := dist_triangle_right (Qd a) (Qd b) p
    have e : 1 / (3 * ((j : ℝ) + 1)) = 1 / ((j : ℝ) + 1) / 3 := by rw [div_div, mul_comm]
    have hc : 0 < 1 / ((j : ℝ) + 1) := by positivity
    rw [e] at h1 h2
    linarith
  have hu' := hj a b (hR a hap) (hR b hbp) hab
  simp only [mem_ball, Real.dist_eq] at ha1 hb1 ⊢
  rw [abs_lt] at ha1 hb1 ⊢
  rw [abs_le] at hu'
  constructor <;> linarith

open Classical in
/-- the continuous function with values `u` on the dense sequence (junk `0` if `¬ IsLUCQ u`) -/
def contQ (u : ℕ → ℝ) : C(ℂ × ℂ, ℝ) :=
  if hu : IsLUCQ u then ⟨extQ u, continuous_extQ hu⟩ else 0

theorem isLUCQ_comp {F : ℂ × ℂ → ℝ} (hF : Continuous F) : IsLUCQ (F ∘ Qd) := by
  intro R m
  have hK := (isCompact_closedBall (0 : ℂ × ℂ) R).uniformContinuousOn_of_continuous
    hF.continuousOn
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.1 hK _ (one_div_succ_pos m)
  obtain ⟨j, hj⟩ := exists_one_div_lt hδ
  refine ⟨j, fun a b ha hb hab => ?_⟩
  have := hδF (Qd a) (by simpa using ha) (Qd b) (by simpa using hb) (hab.trans hj)
  rw [Real.dist_eq] at this
  exact this.le

theorem contQ_comp {F : C(ℂ × ℂ, ℝ)} : contQ (F ∘ Qd) = F := by
  have hu := isLUCQ_comp F.continuous
  ext p
  simp only [contQ, hu, ↓reduceDIte, ContinuousMap.coe_mk]
  exact ((F.continuous.tendsto p).comp tendsto_comap).limUnder_eq

theorem measurable_contQ {X : Type*} [MeasurableSpace X] {u : X → ℕ → ℝ}
    (hu : ∀ a, Measurable fun x => u x a) : Measurable fun x => contQ (u x) := by
  classical
  have hS : MeasurableSet {x | IsLUCQ (u x)} := by
    have e : {x | IsLUCQ (u x)} = ⋂ R : ℕ, ⋂ m : ℕ, ⋃ j : ℕ, ⋂ a : ℕ, ⋂ b : ℕ,
        {x | (‖Qd a‖ ≤ R ∧ ‖Qd b‖ ≤ R ∧ dist (Qd a) (Qd b) < 1 / (j + 1)) →
          |u x a - u x b| ≤ 1 / (m + 1)} := by
      ext x; simp only [IsLUCQ, mem_setOf_eq, mem_iInter, mem_iUnion, and_imp]
    rw [e]
    refine .iInter fun R => .iInter fun m => .iUnion fun j => .iInter fun a => .iInter fun b => ?_
    by_cases hP : (‖Qd a‖ ≤ R ∧ ‖Qd b‖ ≤ R ∧ dist (Qd a) (Qd b) < 1 / (j + 1))
    · have e2 : {x | (‖Qd a‖ ≤ R ∧ ‖Qd b‖ ≤ R ∧ dist (Qd a) (Qd b) < 1 / (j + 1)) →
          |u x a - u x b| ≤ 1 / (m + 1)} = {x | |u x a - u x b| ≤ 1 / (m + 1)} := by
        ext x; simp only [mem_setOf_eq]; exact ⟨fun h => h hP, fun h _ => h⟩
      rw [e2]
      exact measurableSet_le (continuous_abs.measurable.comp ((hu a).sub (hu b))) measurable_const
    · simp only [hP, false_implies, Set.ofPred_true]
      exact .univ
  refine ContinuousMap.measurable_iff_eval.2 fun p => ?_
  have he : Measurable fun x => extQ (u x) p :=
    (StronglyMeasurable.limUnder (l := comap Qd (𝓝 p))
      (f := fun a x => u x a) fun a => (hu a).stronglyMeasurable).measurable
  have : (fun x => contQ (u x) p) = fun x => if IsLUCQ (u x) then extQ (u x) p else 0 := by
    funext x
    by_cases h : IsLUCQ (u x)
    · simp [contQ, h]
    · simp [contQ, h]
  rw [this]
  exact Measurable.ite hS he measurable_const

end LQGMetric.DFGPS.T12
