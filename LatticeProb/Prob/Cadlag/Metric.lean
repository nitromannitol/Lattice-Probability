import LatticeProb.Prob.Cadlag.Basic

/-!
# Skorokhod's J1 metric

The distance is the infimum of simultaneous bounds on the uniform time displacement
and on the spatial discrepancy after an increasing time change. This is Billingsley's
metric from §12, with the interval rescaled to `[0,T]`.
-/

namespace LatticeProb.Cadlag

open Set Filter
open scoped Topology

noncomputable section

variable {T : ℝ} {E : Type*} [NormedAddCommGroup E]

/-- Bounds realized by an increasing bijection of the time interval. -/
def admissibleBounds (x y : D T E) : Set ℝ :=
  {r : ℝ | 0 ≤ r ∧ ∃ l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T,
    (∀ t, |((l t : Icc (0 : ℝ) T) : ℝ) - t| ≤ r) ∧
      ∀ t, ‖x.1 (l t) - y.1 t‖ ≤ r}

/-- Skorokhod's J1 distance, expressed as the infimum of admissible bounds. -/
def skorokhodDist (x y : D T E) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T,
    (∀ t, |((l t : Icc (0 : ℝ) T) : ℝ) - t| ≤ r) ∧
      ∀ t, ‖x.1 (l t) - y.1 t‖ ≤ r}

/-- The identity time change realizes any nonnegative uniform spatial bound. -/
theorem mem_admissibleBounds_of_uniform {x y : D T E} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, ‖x.1 t - y.1 t‖ ≤ r) : r ∈ admissibleBounds x y :=
  ⟨hr, OrderIso.refl _, by simpa only [OrderIso.refl_apply, sub_self, abs_zero] using
    (fun _ : Icc (0 : ℝ) T => hr), h⟩

/-- Boundedness of the two paths makes the admissible set nonempty. -/
theorem admissibleBounds_nonempty (x y : D T E) : (admissibleBounds x y).Nonempty := by
  obtain ⟨M, hM⟩ := x.2.exists_norm_le
  obtain ⟨N, hN⟩ := y.2.exists_norm_le
  refine ⟨max 0 (M + N), mem_admissibleBounds_of_uniform (le_max_left _ _) ?_⟩
  intro t
  exact (norm_sub_le _ _).trans ((add_le_add (hM t) (hN t)).trans (le_max_right _ _))

/-- Zero is a lower bound of the admissible set. -/
theorem admissibleBounds_bddBelow (x y : D T E) : BddBelow (admissibleBounds x y) :=
  ⟨0, fun _ h => h.1⟩

/-- The infimum used in the distance is a genuine greatest lower bound. -/
theorem isGLB_skorokhodDist (x y : D T E) :
    IsGLB (admissibleBounds x y) (skorokhodDist x y) :=
  isGLB_csInf (admissibleBounds_nonempty x y) (admissibleBounds_bddBelow x y)

/-- The J1 distance is nonnegative. -/
theorem skorokhodDist_nonneg (x y : D T E) : 0 ≤ skorokhodDist x y :=
  le_csInf (admissibleBounds_nonempty x y) (fun _ h => h.1)

/-- Every realized bound bounds the J1 distance. -/
theorem skorokhodDist_le_of_mem {x y : D T E} {r : ℝ}
    (h : r ∈ admissibleBounds x y) : skorokhodDist x y ≤ r :=
  csInf_le (admissibleBounds_bddBelow x y) h

/-- A strict upper bound on distance admits a time change with a smaller realized bound. -/
theorem exists_admissibleBounds_lt {x y : D T E} {r : ℝ} (h : skorokhodDist x y < r) :
    ∃ a ∈ admissibleBounds x y, a < r :=
  exists_lt_of_csInf_lt (admissibleBounds_nonempty x y) h

/-- A path has zero J1 distance from itself. -/
@[simp] theorem skorokhodDist_self (x : D T E) : skorokhodDist x x = 0 := by
  apply le_antisymm _ (skorokhodDist_nonneg x x)
  exact skorokhodDist_le_of_mem (mem_admissibleBounds_of_uniform le_rfl
    (fun _ => by rw [sub_self, norm_zero]))

/-- Inverting a time change preserves both of its uniform bounds. -/
theorem mem_admissibleBounds_symm {x y : D T E} {r : ℝ}
    (h : r ∈ admissibleBounds x y) : r ∈ admissibleBounds y x := by
  obtain ⟨hr, l, hl, hxy⟩ := h
  refine ⟨hr, l.symm, ?_, ?_⟩
  · intro t
    simpa only [l.apply_symm_apply, abs_sub_comm] using hl (l.symm t)
  · intro t
    simpa only [l.apply_symm_apply, norm_sub_rev] using hxy (l.symm t)

/-- J1 distance is symmetric. -/
theorem skorokhodDist_comm (x y : D T E) : skorokhodDist x y = skorokhodDist y x := by
  apply le_antisymm
  · apply le_csInf (admissibleBounds_nonempty y x)
    intro r hr
    exact skorokhodDist_le_of_mem (mem_admissibleBounds_symm hr)
  · apply le_csInf (admissibleBounds_nonempty x y)
    intro r hr
    exact skorokhodDist_le_of_mem (mem_admissibleBounds_symm hr)

/-- Composing time changes adds their time and spatial bounds. -/
theorem add_mem_admissibleBounds {x y z : D T E} {a b : ℝ}
    (ha : a ∈ admissibleBounds x y) (hb : b ∈ admissibleBounds y z) :
    a + b ∈ admissibleBounds x z := by
  obtain ⟨ha, l, hl, hxy⟩ := ha
  obtain ⟨hb, m, hm, hyz⟩ := hb
  refine ⟨add_nonneg ha hb, m.trans l, ?_, ?_⟩
  · intro t
    calc
      |((l (m t) : Icc (0 : ℝ) T) : ℝ) - t| ≤
          |((l (m t) : Icc (0 : ℝ) T) : ℝ) - (m t : ℝ)| + |(m t : ℝ) - t| :=
        abs_sub_le _ _ _
      _ ≤ a + b := add_le_add (hl (m t)) (hm t)
  · intro t
    calc
      ‖x.1 (l (m t)) - z.1 t‖ ≤ ‖x.1 (l (m t)) - y.1 (m t)‖ +
          ‖y.1 (m t) - z.1 t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ a + b := add_le_add (hxy (m t)) (hyz t)

/-- The J1 distance satisfies the triangle inequality. -/
theorem skorokhodDist_triangle (x y z : D T E) :
    skorokhodDist x z ≤ skorokhodDist x y + skorokhodDist y z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, haε⟩ := exists_admissibleBounds_lt
    (lt_add_of_pos_right (skorokhodDist x y) (half_pos hε))
  obtain ⟨b, hb, hbε⟩ := exists_admissibleBounds_lt
    (lt_add_of_pos_right (skorokhodDist y z) (half_pos hε))
  have hab := skorokhodDist_le_of_mem (add_mem_admissibleBounds ha hb)
  linarith

/-- Uniform spatial error controls J1 distance using the identity time change. -/
theorem skorokhodDist_le_uniform {x y : D T E} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, ‖x.1 t - y.1 t‖ ≤ r) : skorokhodDist x y ≤ r :=
  skorokhodDist_le_of_mem (mem_admissibleBounds_of_uniform hr h)

/-- An increasing bijection fixes the terminal time. -/
theorem timeChange_apply_terminal (l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T)
    (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = T) : l t = t := by
  obtain ⟨s, hs⟩ := l.surjective t
  have hst : s ≤ t := by change (s : ℝ) ≤ t; rw [ht]; exact s.property.2
  apply le_antisymm
  · change (l t : ℝ) ≤ t
    rw [ht]
    exact (l t).property.2
  · simpa only [hs] using l.monotone hst

/-- An increasing bijection fixes the initial time. -/
theorem timeChange_apply_initial (l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T)
    (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = 0) : l t = t := by
  obtain ⟨s, hs⟩ := l.surjective t
  have hts : t ≤ s := by change (t : ℝ) ≤ s; rw [ht]; exact s.property.1
  apply le_antisymm
  · simpa only [hs] using l.monotone hts
  · change (t : ℝ) ≤ l t
    rw [ht]
    exact (l t).property.1

/-- Zero J1 distance forces equality, by right continuity and the fixed terminal time. -/
theorem eq_of_skorokhodDist_eq_zero {x y : D T E} (h : skorokhodDist x y = 0) :
    x = y := by
  apply Subtype.ext
  funext t
  apply eq_of_forall_dist_le
  intro ε hε
  by_cases ht : (t : ℝ) < T
  · obtain ⟨δx, hδx, hx⟩ := (Metric.continuousWithinAt_iff.mp (x.2.1 t ht))
      (ε / 4) (by positivity)
    obtain ⟨δy, hδy, hy⟩ := (Metric.continuousWithinAt_iff.mp (y.2.1 t ht))
      (ε / 4) (by positivity)
    have hgap : 0 < T - (t : ℝ) := sub_pos.mpr ht
    let η := min δx (min δy (min (T - t) (ε / 4))) / 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hηx : η < δx := by
      have := min_le_left δx (min δy (min (T - t) (ε / 4)))
      dsimp [η] at *
      linarith
    have hηy : η < δy := by
      have := (min_le_right δx (min δy (min (T - t) (ε / 4)))).trans
        (min_le_left δy (min (T - t) (ε / 4)))
      dsimp [η] at *
      linarith
    have hηT : η < T - t := by
      have := (min_le_right δx (min δy (min (T - t) (ε / 4)))).trans
        ((min_le_right δy (min (T - t) (ε / 4))).trans (min_le_left _ _))
      dsimp [η] at *
      linarith
    have hηε : η < ε / 4 := by
      have := (min_le_right δx (min δy (min (T - t) (ε / 4)))).trans
        ((min_le_right δy (min (T - t) (ε / 4))).trans (min_le_right _ _))
      dsimp [η] at *
      linarith
    let s : Icc (0 : ℝ) T := ⟨t + η / 2,
      ⟨by linarith [t.property.1], by linarith⟩⟩
    obtain ⟨r, ⟨_, l, hl, hxy⟩, hr⟩ := exists_admissibleBounds_lt
      (x := x) (y := y) (r := η / 2) (by rw [h]; positivity)
    have hls := abs_le.mp (hl s)
    have hlt : (t : ℝ) ≤ (l s : ℝ) := by dsimp [s] at hls; linarith
    have hlδ : dist (l s) t < δx := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlt)]
      dsimp [s] at hls
      linarith
    have hsδ : dist s t < δy := by
      rw [Subtype.dist_eq, Real.dist_eq]
      dsimp [s]
      rw [add_sub_cancel_left, abs_of_pos (half_pos hη)]
      linarith
    have hxt := hx hlt hlδ
    have hyt := hy (show t ≤ s by change (t : ℝ) ≤ t + η / 2; linarith) hsδ
    have hsp : dist (x.1 (l s)) (y.1 s) ≤ r := by
      rw [dist_eq_norm]
      exact hxy s
    have htriangle := dist_triangle (x.1 t) (x.1 (l s)) (y.1 t)
    have htriangle' := dist_triangle (x.1 (l s)) (y.1 s) (y.1 t)
    rw [dist_comm (x.1 (l s)) (x.1 t)] at hxt
    linarith
  · have htT : (t : ℝ) = T := le_antisymm t.property.2 (le_of_not_gt ht)
    obtain ⟨r, ⟨_, l, _, hxy⟩, hr⟩ := exists_admissibleBounds_lt
      (x := x) (y := y) (r := ε) (by rw [h]; exact hε)
    have hsp := hxy t
    rw [timeChange_apply_terminal l t htT] at hsp
    exact (by rw [dist_eq_norm]; exact hsp.trans hr.le)

/-- The metric on càdlàg paths is the J1 metric. -/
instance instMetricSpace : MetricSpace (D T E) where
  dist := skorokhodDist
  dist_self := skorokhodDist_self
  dist_comm := skorokhodDist_comm
  dist_triangle := skorokhodDist_triangle
  eq_of_dist_eq_zero := eq_of_skorokhodDist_eq_zero

/-- The metric distance is definitionally the specified infimum. -/
theorem dist_eq_skorokhodDist (x y : D T E) : dist x y = skorokhodDist x y := rfl

/-- The J1 distance is bounded by the uniform supremum of spatial discrepancies. -/
theorem skorokhodDist_le_iSup (hT : 0 ≤ T) (x y : D T E) :
    skorokhodDist x y ≤ ⨆ t, ‖x.1 t - y.1 t‖ := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  letI : Nonempty (Icc (0 : ℝ) T) := ⟨t₀⟩
  obtain ⟨M, hM⟩ := x.2.exists_norm_le
  obtain ⟨N, hN⟩ := y.2.exists_norm_le
  have hb : BddAbove (range (fun t => ‖x.1 t - y.1 t‖)) := by
    refine ⟨M + N, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hM t) (hN t))
  apply skorokhodDist_le_uniform
  · exact (norm_nonneg (x.1 t₀ - y.1 t₀)).trans (le_ciSup hb t₀)
  · exact fun t => le_ciSup hb t

/-- The inclusion of continuous paths into càdlàg paths is 1-Lipschitz. -/
theorem lipschitzWith_ofContinuous :
    LipschitzWith 1 (ofContinuous : C(Icc (0 : ℝ) T, E) → D T E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply skorokhodDist_le_uniform dist_nonneg
  intro t
  simpa only [ofContinuous_apply, ← dist_eq_norm] using ContinuousMap.dist_apply_le_dist t

/-- The inclusion of continuous paths is continuous for the uniform and J1 topologies. -/
theorem continuous_ofContinuous :
    Continuous (ofContinuous : C(Icc (0 : ℝ) T, E) → D T E) :=
  lipschitzWith_ofContinuous.continuous

/-- The inclusion of continuous paths is injective. -/
theorem ofContinuous_injective :
    Function.Injective (ofContinuous : C(Icc (0 : ℝ) T, E) → D T E) := by
  intro x y h
  ext t
  exact congrFun (congrArg Subtype.val h) t

/-- At a continuous path, small J1 distance controls the uniform distance. -/
theorem exists_uniform_dist_control (x : C(Icc (0 : ℝ) T, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : C(Icc (0 : ℝ) T, E),
      skorokhodDist (ofContinuous y) (ofContinuous x) < δ → dist y x < ε := by
  obtain ⟨η, hη, hx⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous x.continuous)
    (ε / 2) (half_pos hε)
  let δ := min η (ε / 4) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := by
    have := min_le_left η (ε / 4)
    dsimp [δ]
    linarith
  have hδε : δ < ε / 4 := by
    have := min_le_right η (ε / 4)
    dsimp [δ]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  obtain ⟨r, ⟨_, l, hl, hyx⟩, hr⟩ := exists_admissibleBounds_lt hy
  have huniform : dist y x ≤ 3 * ε / 4 := by
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro s
    have ht : dist (l.symm s) s < η := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      have htime := hl (l.symm s)
      rw [l.apply_symm_apply] at htime
      exact htime.trans_lt (hr.trans hδη)
    have hsp : dist (y s) (x (l.symm s)) ≤ r := by
      simpa only [ofContinuous_apply, l.apply_symm_apply, dist_eq_norm] using
        hyx (l.symm s)
    have hc := hx ht
    have htriangle := dist_triangle (y s) (x (l.symm s)) (x s)
    linarith
  linarith

/-- The topology on continuous paths induced by J1 agrees with the uniform topology. -/
theorem isEmbedding_ofContinuous :
    Topology.IsEmbedding (ofContinuous : C(Icc (0 : ℝ) T, E) → D T E) := by
  apply Topology.IsEmbedding.mk' _ ofContinuous_injective
  intro x
  apply le_antisymm
  · apply ((Metric.nhds_basis_ball.comap _).le_basis_iff Metric.nhds_basis_ball).mpr
    intro ε hε
    obtain ⟨δ, hδ, hcontrol⟩ := exists_uniform_dist_control x hε
    exact ⟨δ, hδ, fun y hy => hcontrol y hy⟩
  · exact (continuous_ofContinuous.tendsto x).le_comap

/-- Terminal spatial discrepancy is bounded by J1 distance. -/
theorem norm_eval_terminal_sub_le (x y : D T E) (t : Icc (0 : ℝ) T)
    (ht : (t : ℝ) = T) : ‖x.1 t - y.1 t‖ ≤ skorokhodDist x y := by
  apply le_csInf (admissibleBounds_nonempty x y)
  rintro r ⟨_, l, _, hxy⟩
  simpa only [timeChange_apply_terminal l t ht] using hxy t

/-- Initial spatial discrepancy is bounded by J1 distance. -/
theorem norm_eval_initial_sub_le (x y : D T E) (t : Icc (0 : ℝ) T)
    (ht : (t : ℝ) = 0) : ‖x.1 t - y.1 t‖ ≤ skorokhodDist x y := by
  apply le_csInf (admissibleBounds_nonempty x y)
  rintro r ⟨_, l, _, hxy⟩
  simpa only [timeChange_apply_initial l t ht] using hxy t

/-- The distance between constant paths is the distance between their values. -/
theorem skorokhodDist_const (hT : 0 ≤ T) (u v : E) :
    skorokhodDist (const T u) (const T v) = ‖u - v‖ := by
  apply le_antisymm
  · exact skorokhodDist_le_uniform (norm_nonneg _) (fun _ => le_rfl)
  · exact norm_eval_terminal_sub_le (const T u) (const T v) ⟨T, hT, le_rfl⟩ rfl

/-- A single-jump path has exactly its jump size as distance from its initial constant path. -/
theorem skorokhodDist_jump_const (hT : 0 ≤ T) {a : ℝ} (ha : a ≤ T) (u v : E) :
    skorokhodDist (jump T a u v) (const T u) = ‖v - u‖ := by
  apply le_antisymm
  · apply skorokhodDist_le_uniform (norm_nonneg _)
    intro t
    simp only [jump_apply, const_apply]
    split_ifs
    · simpa only [sub_self, norm_zero] using norm_nonneg (v - u)
    · exact le_rfl
  · have hbound := norm_eval_terminal_sub_le (jump T a u v) (const T u)
      ⟨T, hT, le_rfl⟩ rfl
    simpa only [jump_apply, const_apply, not_lt.mpr ha, if_false] using hbound

/-- Distinct jump values give positive distance from the constant path; this needs no
completeness or finite-dimensionality assumption. -/
theorem skorokhodDist_midpoint_jump_pos (hT : 0 < T) {u v : E} (huv : u ≠ v) :
    0 < skorokhodDist (jump T (T / 2) u v) (const T u) := by
  rw [skorokhodDist_jump_const hT.le (by linarith)]
  exact norm_pos_iff.mpr (sub_ne_zero.mpr huv.symm)

/-- The midpoint-jump path has its initial value at time zero. -/
theorem midpoint_jump_initial (hT : 0 < T) (u v : E) :
    (jump T (T / 2) u v).1 ⟨0, le_rfl, hT.le⟩ = u := by
  simp only [jump_apply, half_pos hT, if_true]

/-- The midpoint-jump path takes its new value at the jump time. -/
theorem midpoint_jump_at_jump (hT : 0 < T) (u v : E) :
    (jump T (T / 2) u v).1 ⟨T / 2, by constructor <;> linarith⟩ = v := by
  simp only [jump_apply, lt_self_iff_false, if_false]

/-- A nontrivial range admits a midpoint jump at positive distance from a constant path. -/
theorem exists_midpoint_jump_pos [Nontrivial E] (hT : 0 < T) :
    ∃ u v : E, 0 < skorokhodDist (jump T (T / 2) u v) (const T u) := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne E
  exact ⟨u, v, skorokhodDist_midpoint_jump_pos hT huv⟩

end

end LatticeProb.Cadlag
