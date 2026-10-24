import LatticeProb.Prob.JumpChain.Position
import LatticeProb.Prob.Cadlag.Measurable

/-!
# Càdlàg realizations of regular jump histories

Positive holding intervals and nonexplosion give right continuity and left limits after
any embedding of the states in a normed group. Each evaluation of the resulting path
is measurable for a countable discrete measurable state space.
-/

namespace LatticeProb.JumpChain

open MeasureTheory Set Filter Topology Cadlag

noncomputable section

variable {S E : Type*} [NormedAddCommGroup E]

namespace RegularHistory

/-- Every regular history gives a càdlàg path after an arbitrary state embedding. -/
theorem isCadlag_position (h : RegularHistory S) (ι : S → E) (T : ℝ) :
    IsCadlag T (fun t : Icc (0 : ℝ) T => ι (h.position (Real.toNNReal t))) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := discreteTopology_bot S
  have hι : Continuous ι := continuous_of_discreteTopology
  have hc : Continuous (fun t : Icc (0 : ℝ) T => Real.toNNReal (t : ℝ)) :=
    continuous_real_toNNReal.comp continuous_subtype_val
  constructor
  · intro t _
    have ht : Tendsto (fun s : Icc (0 : ℝ) T => Real.toNNReal (s : ℝ))
        (𝓝[{s | t ≤ s}] t) (𝓝[≥] (Real.toNNReal (t : ℝ))) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hc.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.toNNReal_le_toNNReal hs
    have hp : Tendsto h.position (𝓝[≥] (Real.toNNReal (t : ℝ)))
        (𝓝 (h.position (Real.toNNReal (t : ℝ)))) :=
      h.continuousWithinAt_position_right _
    exact (hι.tendsto _).comp (hp.comp ht)
  · intro t hpos
    obtain ⟨z, hz⟩ := h.exists_leftLimit_position (Real.toNNReal (t : ℝ))
    refine ⟨ι z, (hι.tendsto _).comp (hz.comp ?_)⟩
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hc.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Real.toNNReal_lt_toNNReal_iff hpos).mpr hs

/-- A regular history as a càdlàg path on the specified closed time interval. -/
def path (h : RegularHistory S) (ι : S → E) (T : ℝ) : D T E :=
  ⟨_, h.isCadlag_position ι T⟩

/-- The path constructor preserves the actual embedded position at each time. -/
@[simp] theorem path_apply (h : RegularHistory S) (ι : S → E) (T : ℝ)
    (t : Icc (0 : ℝ) T) :
    (h.path ι T).1 t = ι (h.position (Real.toNNReal (t : ℝ))) := rfl

/-- At time zero the constructed path takes the embedded initial state. -/
theorem path_initial (h : RegularHistory S) (ι : S → E) (T : ℝ) (hT : 0 ≤ T) :
    (h.path ι T).1 ⟨0, le_rfl, hT⟩ = ι (h.val 0).1 := by
  simp only [path_apply, Real.toNNReal_zero, h.position_zero]

/-- Every evaluation of the constructed path is measurable. -/
theorem measurable_path_eval [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace E]
    (ι : S → E) (T : ℝ) (t : Icc (0 : ℝ) T) :
    Measurable (fun h : RegularHistory S => (h.path ι T).1 t) :=
  (measurable_of_countable ι).comp (measurable_position (Real.toNNReal (t : ℝ)))

/-- Moving a terminal jump into the interior costs its full jump size in J1 distance.
Thus jump-time continuity cannot include perturbations off the terminal face. -/
theorem skorokhodDist_terminal_jump (T a : ℝ) (ha : 0 ≤ a) (haT : a < T)
    (u v : E) :
    skorokhodDist (jump T T u v) (jump T a u v) = ‖u - v‖ := by
  apply le_antisymm
  · apply skorokhodDist_le_uniform (norm_nonneg _)
    intro t
    simp only [jump_apply]
    split_ifs <;> first
      | exact le_rfl
      | exact (norm_sub_rev _ _).le
      | simpa only [sub_self, norm_zero] using norm_nonneg (u - v)
  · apply le_csInf (admissibleBounds_nonempty _ _)
    rintro r ⟨_, l, _, hspace⟩
    let t : Icc (0 : ℝ) T := ⟨a, ha, haT.le⟩
    let e : Icc (0 : ℝ) T := ⟨T, ha.trans haT.le, le_rfl⟩
    have hte : t < e := haT
    have hle : l e = e := timeChange_apply_terminal l e rfl
    have hlt : (l t : ℝ) < T := by
      have := l.strictMono hte
      rw [hle] at this
      exact this
    have hb := hspace t
    change ‖(jump T T u v).1 (l t) - (if a < a then u else v)‖ ≤ r at hb
    simpa only [jump_apply, hlt, if_true, lt_self_iff_false, if_false] using hb

end RegularHistory

end

end LatticeProb.JumpChain
