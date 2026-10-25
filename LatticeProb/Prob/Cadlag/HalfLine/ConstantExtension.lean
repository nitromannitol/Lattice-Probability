import LatticeProb.Prob.Cadlag.HalfLine.RestrictionMeasurable

/-!
# Constant extension retaining the terminal value

A finite càdlàg path extends to the half-line by clamping time to its horizon.
The extension retains the terminal value, including a possible jump there, and is
Borel measurable as a map of path spaces. Restriction recovers the original path.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

variable {T : ℝ} {E : Type*} [NormedAddCommGroup E]

/-- Clamping a finite time embedded in the half-line fixes that time. -/
@[simp] theorem clampTime_intervalTime (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) :
    clampTime hT (intervalTime t) = t :=
  Subtype.ext (min_eq_left t.2.2)

/-- Clamping a time at or after the horizon gives the terminal time. -/
theorem clampTime_eq_terminal (hT : 0 ≤ T) {t : Time} (ht : T ≤ (t : ℝ)) :
    clampTime hT t = ⟨T, hT, le_rfl⟩ :=
  Subtype.ext (min_eq_right ht)

/-- Literal clamping preserves càdlàg paths, allowing a genuine jump at the horizon. -/
theorem isCadlag_comp_clampTime (hT : 0 < T) (x : Cadlag.D T E) :
    IsCadlag (fun t : Time => x.1 (clampTime hT.le t)) := by
  constructor
  · intro t
    by_cases ht : (t : ℝ) < T
    · apply (x.2.1 (clampTime hT.le t) (by
        change min (t : ℝ) T < T
        exact min_lt_of_left_lt ht)).comp
        (continuous_clampTime hT.le).continuousAt.continuousWithinAt
      intro s hs
      exact min_le_min (show (t : ℝ) ≤ s from hs) le_rfl
    · apply (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : Time => x.1 ⟨T, hT.le, le_rfl⟩) (Ici t) t).congr_of_eventuallyEq_of_mem
        (hx := mem_Ici.mpr (le_refl t))
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact congrArg x.1 (clampTime_eq_terminal hT.le
        ((le_of_not_gt ht).trans (show (t : ℝ) ≤ s from hs)))
  · intro t htzero
    by_cases ht : (t : ℝ) ≤ T
    · obtain ⟨l, hl⟩ := x.2.2 (clampTime hT.le t) (by
        change 0 < min (t : ℝ) T
        exact lt_min htzero hT)
      refine ⟨l, hl.comp ?_⟩
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_clampTime hT.le).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      change min (s : ℝ) T < min (t : ℝ) T
      rw [min_eq_left ht]
      exact (min_le_left (s : ℝ) T).trans_lt (show (s : ℝ) < t from hs)
    · refine ⟨x.1 ⟨T, hT.le, le_rfl⟩, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [mem_inf_of_left
        ((continuous_subtype_val.isOpen_preimage _ isOpen_Ioi).mem_nhds
          (lt_of_not_ge ht))] with s hs
      exact (congrArg x.1 (clampTime_eq_terminal hT.le hs.le)).symm

/-- Extend a finite path constantly after its horizon, retaining its terminal value. -/
def constantExtension (hT : 0 < T) (x : Cadlag.D T E) : D E :=
  ⟨fun t => x.1 (clampTime hT.le t), isCadlag_comp_clampTime hT x⟩

/-- Every extension evaluation is the original evaluation at the clamped time. -/
@[simp] theorem constantExtension_apply (hT : 0 < T) (x : Cadlag.D T E) (t : Time) :
    (constantExtension hT x).1 t = x.1 (clampTime hT.le t) := rfl

/-- At or after the horizon the extension takes the actual terminal value. -/
theorem constantExtension_apply_of_le (hT : 0 < T) (x : Cadlag.D T E)
    {t : Time} (ht : T ≤ (t : ℝ)) :
    (constantExtension hT x).1 t = x.1 ⟨T, hT.le, le_rfl⟩ := by
  rw [constantExtension_apply, clampTime_eq_terminal hT.le ht]

/-- At the horizon the extension retains the value rather than the left limit. -/
@[simp] theorem constantExtension_apply_terminal (hT : 0 < T) (x : Cadlag.D T E) :
    (constantExtension hT x).1 ⟨T, hT.le⟩ = x.1 ⟨T, hT.le, le_rfl⟩ :=
  constantExtension_apply_of_le hT x le_rfl

/-- Before the horizon the extension agrees with the original finite evaluation. -/
theorem constantExtension_apply_of_lt (hT : 0 < T) (x : Cadlag.D T E)
    {t : Time} (ht : (t : ℝ) < T) :
    (constantExtension hT x).1 t = x.1 ⟨t, t.2, ht.le⟩ := by
  apply congrArg x.1
  exact Subtype.ext (min_eq_left ht.le)

/-- The extension agrees with the finite path at every embedded finite time. -/
@[simp] theorem constantExtension_apply_intervalTime (hT : 0 < T)
    (x : Cadlag.D T E) (t : Icc (0 : ℝ) T) :
    (constantExtension hT x).1 (intervalTime t) = x.1 t := by
  rw [constantExtension_apply, clampTime_intervalTime]

/-- Restriction of the constant extension recovers the entire original finite path. -/
@[simp] theorem restrict_constantExtension (hT : 0 < T) (x : Cadlag.D T E) :
    restrict T (constantExtension hT x) = x := by
  apply Subtype.ext
  funext t
  exact constantExtension_apply_intervalTime hT x t

/-- Constant extension is measurable for the genuine path-space Borel structures. -/
theorem measurable_constantExtension [SeparableSpace E] (hT : 0 < T) :
    Measurable (constantExtension (E := E) hT) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  apply measurable_of_measurable_eval
  intro t
  exact Cadlag.measurable_eval (clampTime hT.le t)

/-- Extending an actual finite constant path gives the same half-line constant path. -/
@[simp] theorem constantExtension_const (hT : 0 < T) (a : E) :
    constantExtension hT (Cadlag.const T a) = const a := rfl

/-- A finite jump at the terminal time keeps its right value after extension. -/
theorem constantExtension_jump_terminal (hT : 0 < T) (u v : E) :
    (constantExtension hT (Cadlag.jump T T u v)).1 ⟨T, hT.le⟩ = v := by
  rw [constantExtension_apply_terminal, Cadlag.jump_apply, if_neg (lt_irrefl T)]

end

end LatticeProb.Cadlag.HalfLine
