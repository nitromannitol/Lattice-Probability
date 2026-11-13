/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ActualThresholdArrayShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.WindowModulusGridTransfer

/-!
# The centering trap of `ThresholdArrayInputs`, and the linear time change

Two obstructions sit between the walk's harmonic-coordinate martingale and the `harray` slot of
`Limit/WindowModulusGridTransfer.rescaledWindowModulusTail_of_localized_arrays`.  Both are
structural — no probability estimate about the reflected walk is proved or assumed here.

## 1. The centering trap

`LocalizedArrayProducer.ThresholdArrayInputs` carries `start_martingale : ∀ᵐ ω, M n 0 ω = 0`,
but the actual rows are `εₙ · M((εₙ)⁻¹² u) ω k` with `M` a spatial extension of the walk, and
`Process/SpatialEnds.IsSpatialExtension` forces `M 0 ω = Φ start` at the a.s. starting state.
So the field is *false* at the actual rows whenever the harmonic coordinate of the start point is
nonzero.

Feeding the centered extension `M − p` to the producer instead does **not** repair this: the
target rows of `LocalizedMartingaleArray` enter only through `agree`, which compares them to the
array's own rows by **exact equality**, and a deterministic nonzero offset makes that event all of
`Ω` at every index.

`localizedMartingaleArray_add_const` is the repair.  A deterministic shift of the rows by a
bounded sequence of constants keeps the **same** compensator, because

`(Y + c)² − B = (Y² − B) + 2c·Y + c²`

is a sum of three martingales; so `B`, `R`, `v` and all three error fields are untouched, `agree`
is literally the same event, and only the terminal second moment moves, by the pointwise bound
`(y + c)² ≤ 2y² + 2c²`.  Applying the producer to the centered rows and shifting back by
`cₙ := εₙ · p k` therefore lands an array **for the actual, uncentered rows**.

## 2. The linear time change

The rows are also reparametrised by `u ↦ (εₙ)⁻¹² u`.  `Mathlib/Topology/Order/Cadlag` has only
*post*-composition (`IsCadlag.continuous_comp`); precomposition by a nonnegative linear map is
`isCadlag_comp_const_mul` below.  The degenerate scale `c = 0` is handled explicitly (the path is
then constant), so no positivity hypothesis on the scale is needed anywhere downstream.

**This is structure algebra, not a discharge.**  Nothing here certifies the martingale,
compensator, integrability or bracket fields at the walk, and nothing here produces a
`LocalizedMartingaleArray` from scratch: the input of `localizedMartingaleArray_add_const` is an
array, and `LocalizedArrayProducer.thresholdArrayInputs_zero` already shows that lane is
inhabited, so no statement below is vacuous.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal Topology

namespace ReflectedGMS.ActualThresholdArray

open ReflectedGMS.WindowModulusGridTransfer

/-! ## The linear time change -/

/-- **Multiplication by a nonnegative constant maps the right-neighbourhood filter of `a` into
the right-neighbourhood filter of `c * a`**, when `c ≠ 0`.  (At `c = 0` the statement is false and
the consumers below branch on that case instead.) -/
theorem tendsto_nhdsGT_const_mul {c : ℝ≥0} (hc : c ≠ 0) (a : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => c * t) (𝓝[>] a) (𝓝[>] (c * a)) := by
  have hcpos : 0 < c := lt_of_le_of_ne zero_le (Ne.symm hc)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (show Continuous (fun t : ℝ≥0 => c * t) by fun_prop).continuousWithinAt ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact mul_lt_mul_of_pos_left ht hcpos

/-- The left-neighbourhood mirror of `tendsto_nhdsGT_const_mul`. -/
theorem tendsto_nhdsLT_const_mul {c : ℝ≥0} (hc : c ≠ 0) (a : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => c * t) (𝓝[<] a) (𝓝[<] (c * a)) := by
  have hcpos : 0 < c := lt_of_le_of_ne zero_le (Ne.symm hc)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (show Continuous (fun t : ℝ≥0 => c * t) by fun_prop).continuousWithinAt ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact mul_lt_mul_of_pos_left ht hcpos

/-- **Right continuity survives precomposition with a nonnegative linear time change.**  Mathlib's
càdlàg file has only post-composition; this is the missing precomposition, with the degenerate
scale `c = 0` handled (the reparametrised path is then constant). -/
theorem isRightContinuous_comp_const_mul {Y : Type*} [TopologicalSpace Y] {f : ℝ≥0 → Y}
    (hf : IsRightContinuous f) (c : ℝ≥0) :
    IsRightContinuous (fun t : ℝ≥0 => f (c * t)) := by
  intro a
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simp only [zero_mul]
    exact continuousWithinAt_const
  · exact Filter.Tendsto.comp (hf (c * a)) (tendsto_nhdsGT_const_mul hc a)

/-- **The càdlàg property survives precomposition with a nonnegative linear time change.** -/
theorem isCadlag_comp_const_mul {Y : Type*} [TopologicalSpace Y] {f : ℝ≥0 → Y}
    (hf : IsCadlag f) (c : ℝ≥0) :
    IsCadlag (fun t : ℝ≥0 => f (c * t)) where
  isRightContinuous := isRightContinuous_comp_const_mul hf.isRightContinuous c
  tendsto_nhdsLT := by
    intro x
    rcases eq_or_ne c 0 with hc | hc
    · refine ⟨f 0, ?_⟩
      subst hc
      simp only [zero_mul]
      exact tendsto_const_nhds
    · obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (c * x)
      exact ⟨l, hl.comp (tendsto_nhdsLT_const_mul hc x)⟩

/-! ## The deterministic shift -/

/-- **A localized martingale array for shifted target rows.**

If `A` is a `LocalizedMartingaleArray` for the target rows `X` on `[0, H]` and `c : ℕ → ℝ` is a
uniformly bounded sequence of deterministic constants, then `A`'s rows shifted by `c` form a
localized martingale array for the shifted target rows `X n t ω + c n`, with the **same**
filtrations, compensators, error envelopes and bracket slope.

This is what repairs the centering trap: the producer
`LocalizedArrayProducer.nonempty_localizedMartingaleArray_of_thresholdInputs` requires rows
starting at `0`, so it can only be applied to the centered coordinates
`εₙ (M((εₙ)⁻¹² u) k − p k)`; the shift by `cₙ := εₙ · p k` — bounded because a convergent scale
sequence is bounded — converts its output into an array for the actual rows.

The only field that moves is `terminal`, by `(y + c)² ≤ 2y² + 2c²`. -/
noncomputable def localizedMartingaleArray_add_const {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : @Measure Ω mΩ} [IsProbabilityMeasure P] {X : ℕ → ℝ≥0 → Ω → ℝ} {H : ℝ≥0}
    (A : LocalizedMartingaleArray P X H) (c : ℕ → ℝ) (b : ℝ) (hb : ∀ n, |c n| ≤ b) :
    LocalizedMartingaleArray P (fun n t ω => X n t ω + c n) H where
  F := A.F
  Y := fun n t ω => A.Y n t ω + c n
  B := A.B
  R := A.R
  C := 2 * A.C + 2 * b ^ 2
  v := A.v
  martingale := by
    intro n
    have heq : (fun (t : ℝ≥0) (ω : Ω) => A.Y n t ω + c n) = A.Y n + (fun _ _ => c n) := by
      funext t ω
      simp only [Pi.add_apply]
    rw [heq]
    exact (A.martingale n).add (martingale_const (A.F n) P (c n))
  compensated := by
    intro n
    have heq : (fun (t : ℝ≥0) (ω : Ω) =>
          (A.Y n t ω + c n) * (A.Y n t ω + c n) - A.B n t ω)
        = ((fun (t : ℝ≥0) (ω : Ω) => A.Y n t ω * A.Y n t ω - A.B n t ω)
            + (2 * c n) • A.Y n) + (fun _ _ => c n ^ 2) := by
      funext t ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact ((A.compensated n).add ((A.martingale n).smul (2 * c n))).add
      (martingale_const (A.F n) P (c n ^ 2))
  cadlag := by
    intro n
    filter_upwards [A.cadlag n] with ω hω
    have heq : (fun t : ℝ≥0 => A.Y n t ω + c n)
        = (fun t : ℝ≥0 => A.Y n t ω) + (fun _ : ℝ≥0 => c n) := by
      funext t
      simp only [Pi.add_apply]
    rw [heq]
    exact hω.add IsCadlag.const
  rightContinuous_compensated := by
    intro n
    filter_upwards [A.cadlag n, A.rightContinuous_compensated n] with ω hcad hrc
    have hY : IsRightContinuous (fun t : ℝ≥0 => A.Y n t ω) := hcad.isRightContinuous
    have hc1 : IsRightContinuous (fun _ : ℝ≥0 => 2 * c n) := IsRightContinuous.const
    have hc2 : IsRightContinuous (fun _ : ℝ≥0 => c n ^ 2) := IsRightContinuous.const
    have hfun : (fun t : ℝ≥0 => (A.Y n t ω + c n) * (A.Y n t ω + c n) - A.B n t ω)
        = ((fun t : ℝ≥0 => A.Y n t ω * A.Y n t ω - A.B n t ω)
            + (fun _ : ℝ≥0 => 2 * c n) * (fun t : ℝ≥0 => A.Y n t ω))
          + (fun _ : ℝ≥0 => c n ^ 2) := by
      funext t
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [hfun]
    exact (hrc.add (hc1.mul hY)).add hc2
  memLp := by
    intro n t
    have heq : (fun ω : Ω => A.Y n t ω + c n) = A.Y n t + (fun _ : Ω => c n) := by
      funext ω
      simp only [Pi.add_apply]
    rw [heq]
    exact (A.memLp n t).add (memLp_const (c n))
  terminal := by
    intro n
    have hb0 : (0 : ℝ) ≤ b := le_trans (abs_nonneg _) (hb n)
    have hmem : MemLp (fun ω : Ω => A.Y n H ω + c n) 2 P := by
      have heq : (fun ω : Ω => A.Y n H ω + c n) = A.Y n H + (fun _ : Ω => c n) := by
        funext ω
        simp only [Pi.add_apply]
      rw [heq]
      exact (A.memLp n H).add (memLp_const (c n))
    have hi1 : Integrable (fun ω => (A.Y n H ω + c n) ^ 2) P := hmem.integrable_sq
    have hi0 : Integrable (fun ω => A.Y n H ω ^ 2) P := (A.memLp n H).integrable_sq
    have hi2 : Integrable (fun ω => 2 * A.Y n H ω ^ 2 + 2 * c n ^ 2) P :=
      (hi0.const_mul 2).add (integrable_const _)
    have hpt : ∀ ω, (A.Y n H ω + c n) ^ 2 ≤ 2 * A.Y n H ω ^ 2 + 2 * c n ^ 2 := by
      intro ω
      nlinarith [sq_nonneg (A.Y n H ω - c n)]
    have hcb : c n ^ 2 ≤ b ^ 2 := sq_le_sq' (abs_le.mp (hb n)).1 (abs_le.mp (hb n)).2
    have hstep : ∫ ω, (A.Y n H ω + c n) ^ 2 ∂P
        ≤ ∫ ω, (2 * A.Y n H ω ^ 2 + 2 * c n ^ 2) ∂P :=
      integral_mono hi1 hi2 hpt
    have hsplit : ∫ ω, (2 * A.Y n H ω ^ 2 + 2 * c n ^ 2) ∂P
        = 2 * ∫ ω, A.Y n H ω ^ 2 ∂P + 2 * c n ^ 2 := by
      rw [integral_add (hi0.const_mul 2) (integrable_const _), integral_const_mul,
        integral_const]
      simp
    have hterm : ∫ ω, A.Y n H ω ^ 2 ∂P ≤ A.C := A.terminal n
    rw [hsplit] at hstep
    linarith
  v_nonneg := A.v_nonneg
  integrable_error := A.integrable_error
  error := A.error
  error_mean := A.error_mean
  agree := by
    have hset : ∀ n, {ω | ∃ t ≤ H, A.Y n t ω + c n ≠ X n t ω + c n}
        = {ω | ∃ t ≤ H, A.Y n t ω ≠ X n t ω} := by
      intro n
      ext ω
      simp only [Set.mem_setOf_eq, ne_eq, add_left_inj]
    simpa only [hset] using A.agree

/-- **A convergent scale sequence is bounded.**  This is the side condition of the shift at the
walk: the shift constants are `cₙ = εₙ · p k`, and `harray`'s binder gives only
`Tendsto ε atTop (𝓝 0)`. -/
theorem exists_bound_of_tendsto_zero {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ B : ℝ≥0, ∀ n, ε n ≤ B := by
  have h1 : ∀ᶠ n in atTop, ε n ≤ 1 := by
    have hmem := hε (Iio_mem_nhds (show (0 : ℝ≥0) < 1 by norm_num))
    exact Filter.Eventually.mono hmem fun n hn => le_of_lt hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp h1
  refine ⟨max 1 ((Finset.range N).sup ε), fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact le_trans (Finset.le_sup (Finset.mem_range.mpr hn)) (le_max_right _ _)
  · exact le_trans (hN n hn) (le_max_left _ _)

end ReflectedGMS.ActualThresholdArray
