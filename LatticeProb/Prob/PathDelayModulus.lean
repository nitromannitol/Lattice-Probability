/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.PathSpaceDUnif
import LatticeProb.Prob.MarkovStepShiftedPath

/-!
# Delay and advance moduli of continuous paths

For a path `y : C(ℝ≥0, E)` and a time `c ≥ 0` let `pathDelay c y t = y (t - c)` (truncated subtraction: the path
is held at `y 0` on `[0, c]` and then run with delay `c`), and let `pathShift y c = y (c + ·)` be the path advanced
by `c`. For the local uniform metric `dUnif` put

* `delayModulus a y = sup_{s ∈ [0, a]} dUnif (pathDelay s y) y`,
* `advanceModulus c y = sup_{s ∈ [0, c]} dUnif (pathShift y s) y`.

Main results:

* `LatticeProb.continuous_pathDelay_uncurry`: `(c, y) ↦ pathDelay c y` is jointly continuous for the
  compact-open topology.
* `LatticeProb.continuous_dUnif`: `dUnif` is jointly continuous for the compact-open topology.
* `LatticeProb.dUnif_le_dUnif_of_forall_exists_le`: `dUnif X Y ≤ dUnif X' Y'` as soon as every distance
  `dist (X t) (Y t)` is dominated by some `dist (X' u) (Y' u)` with `u ≤ t`.
* `LatticeProb.continuous_delayModulus`, `LatticeProb.continuous_advanceModulus`: both moduli are jointly
  continuous in the time and the path; they vanish at time `0` and are monotone in time.
* `LatticeProb.delayModulus_pathShift_le`:
  `delayModulus a (pathShift y c) ≤ delayModulus a y + 2 * advanceModulus c y`.
-/

open Filter Topology Set

open scoped NNReal

noncomputable section

namespace LatticeProb

variable {E : Type*} [MetricSpace E]

/-! ### The delayed path -/

/-- The path delayed by `c`: `t ↦ y (t - c)`, with truncated subtraction, so that it is held at `y 0` on
`[0, c]`. -/
def pathDelay (c : ℝ≥0) (y : C(ℝ≥0, E)) : C(ℝ≥0, E) :=
  y.comp ⟨fun t => t - c, continuous_id.sub continuous_const⟩

@[simp] lemma pathDelay_apply (c : ℝ≥0) (y : C(ℝ≥0, E)) (t : ℝ≥0) : pathDelay c y t = y (t - c) := rfl

@[simp] lemma pathDelay_zero (y : C(ℝ≥0, E)) : pathDelay 0 y = y := by
  ext t; simp

/-- The path advanced by `0` is the path itself. -/
lemma pathShift_zero_right (y : C(ℝ≥0, E)) : pathShift y 0 = y := by
  ext t; simp

/-- The map `c ↦ (t ↦ t - c)` into the continuous self-maps of `ℝ≥0` is continuous. -/
theorem continuous_timeDelayCM : Continuous fun c : ℝ≥0 =>
    (⟨fun t => t - c, continuous_id.sub continuous_const⟩ : C(ℝ≥0, ℝ≥0)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)

/-- The delayed path `(c, y) ↦ y (· - c)` is jointly continuous for the compact-open topology. -/
theorem continuous_pathDelay_uncurry :
    Continuous fun p : ℝ≥0 × C(ℝ≥0, E) => pathDelay p.1 p.2 :=
  ContinuousMap.continuous_comp'.comp ((continuous_timeDelayCM.comp continuous_fst).prodMk continuous_snd)

/-! ### Two facts on the local uniform metric -/

/-- The local uniform metric `dUnif` is jointly continuous for the compact-open topology. -/
theorem continuous_dUnif : Continuous fun p : C(ℝ≥0, E) × C(ℝ≥0, E) => dUnif p.1 p.2 := by
  let := dUnifMetricSpace (E := E)
  exact continuous_dist

/-- `dUnif` is monotone in the window suprema `pathSupDist`. -/
theorem dUnif_le_dUnif_of_pathSupDist_le {X Y X' Y' : C(ℝ≥0, E)}
    (h : ∀ T, pathSupDist T X Y ≤ pathSupDist T X' Y') : dUnif X Y ≤ dUnif X' Y' :=
  MeasureTheory.setIntegral_mono (integrableOn_dUnifIntegrand X Y) (integrableOn_dUnifIntegrand X' Y')
    fun T => by unfold dUnifIntegrand; exact min_le_min le_rfl (h _)

/-- If every distance `dist (X t) (Y t)` is dominated by a distance `dist (X' u) (Y' u)` at an earlier time
`u ≤ t`, then `dUnif X Y ≤ dUnif X' Y'`. -/
theorem dUnif_le_dUnif_of_forall_exists_le {X Y X' Y' : C(ℝ≥0, E)}
    (h : ∀ t, ∃ u ≤ t, dist (X t) (Y t) ≤ dist (X' u) (Y' u)) : dUnif X Y ≤ dUnif X' Y' :=
  dUnif_le_dUnif_of_pathSupDist_le fun _ => pathSupDist_le fun t ht => by
    obtain ⟨u, hu, hle⟩ := h t
    exact hle.trans (dist_le_pathSupDist X' Y' (hu.trans ht))

/-! ### Suprema over a time interval -/

lemma bddAbove_image_dUnif (g : ℝ≥0 → C(ℝ≥0, E)) (y : C(ℝ≥0, E)) (S : Set ℝ≥0) :
    BddAbove ((fun s => dUnif (g s) y) '' S) :=
  ⟨1, by rintro _ ⟨s, -, rfl⟩; exact dUnif_le_one _ _⟩

lemma image_mul_right_Icc_zero_one (a : ℝ≥0) : (fun u : ℝ≥0 => u * a) '' Icc 0 1 = Icc 0 a := by
  ext s
  constructor
  · rintro ⟨u, ⟨-, hu⟩, rfl⟩
    exact ⟨zero_le, mul_le_of_le_one_left zero_le hu⟩
  · rintro ⟨-, hs⟩
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, ⟨le_rfl, zero_le⟩, by simp [le_antisymm hs zero_le]⟩
    · exact ⟨s / a, ⟨zero_le, div_le_one_of_le₀ hs zero_le⟩, div_mul_cancel₀ s ha⟩

lemma sSup_image_Icc_eq_sSup_image_mul (g : ℝ≥0 → ℝ) (a : ℝ≥0) :
    sSup (g '' Icc 0 a) = sSup ((fun u => g (u * a)) '' Icc 0 1) := by
  rw [← image_mul_right_Icc_zero_one a, Set.image_image]

/-! ### The delay modulus -/

/-- The *delay modulus* `sup_{s ∈ [0, a]} dUnif (pathDelay s y) y` of a path `y`. -/
def delayModulus (a : ℝ≥0) (y : C(ℝ≥0, E)) : ℝ :=
  sSup ((fun s => dUnif (pathDelay s y) y) '' Icc 0 a)

theorem dUnif_pathDelay_le_delayModulus {s a : ℝ≥0} (hs : s ≤ a) (y : C(ℝ≥0, E)) :
    dUnif (pathDelay s y) y ≤ delayModulus a y :=
  le_csSup (bddAbove_image_dUnif _ y _) (mem_image_of_mem _ ⟨zero_le, hs⟩)

theorem delayModulus_nonneg (a : ℝ≥0) (y : C(ℝ≥0, E)) : 0 ≤ delayModulus a y :=
  (dUnif_nonneg _ _).trans (dUnif_pathDelay_le_delayModulus zero_le y)

theorem delayModulus_mono {a a' : ℝ≥0} (h : a ≤ a') (y : C(ℝ≥0, E)) :
    delayModulus a y ≤ delayModulus a' y :=
  csSup_le_csSup (bddAbove_image_dUnif _ y _) ((nonempty_Icc.2 zero_le).image _)
    (image_mono (Icc_subset_Icc le_rfl h))

@[simp] theorem delayModulus_zero (y : C(ℝ≥0, E)) : delayModulus 0 y = 0 := by
  simp [delayModulus, dUnif_self]

/-- The delay modulus is jointly continuous in the time and the path. -/
theorem continuous_delayModulus :
    Continuous fun p : ℝ≥0 × C(ℝ≥0, E) => delayModulus p.1 p.2 := by
  have h : (fun p : ℝ≥0 × C(ℝ≥0, E) => delayModulus p.1 p.2) =
      fun p => sSup ((fun u : ℝ≥0 => dUnif (pathDelay (u * p.1) p.2) p.2) '' Icc 0 1) := by
    funext p
    exact sSup_image_Icc_eq_sSup_image_mul (fun s => dUnif (pathDelay s p.2) p.2) p.1
  rw [h]
  refine isCompact_Icc.continuous_sSup ?_
  exact (continuous_dUnif (E := E)).comp ((continuous_pathDelay_uncurry.comp
    ((continuous_snd.mul (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp continuous_fst))).prodMk (continuous_snd.comp continuous_fst))

theorem tendsto_delayModulus_zero (y : C(ℝ≥0, E)) :
    Tendsto (fun a => delayModulus a y) (𝓝 0) (𝓝 0) := by
  have h : Continuous fun a : ℝ≥0 => delayModulus a y :=
    continuous_delayModulus.comp (continuous_id.prodMk continuous_const)
  simpa using h.tendsto 0

/-! ### The advance modulus -/

/-- The *advance modulus* `sup_{s ∈ [0, c]} dUnif (pathShift y s) y` of a path `y`. -/
def advanceModulus (c : ℝ≥0) (y : C(ℝ≥0, E)) : ℝ :=
  sSup ((fun s => dUnif (pathShift y s) y) '' Icc 0 c)

theorem dUnif_pathShift_le_advanceModulus {s c : ℝ≥0} (hs : s ≤ c) (y : C(ℝ≥0, E)) :
    dUnif (pathShift y s) y ≤ advanceModulus c y :=
  le_csSup (bddAbove_image_dUnif _ y _) (mem_image_of_mem _ ⟨zero_le, hs⟩)

theorem advanceModulus_nonneg (c : ℝ≥0) (y : C(ℝ≥0, E)) : 0 ≤ advanceModulus c y :=
  (dUnif_nonneg _ _).trans (dUnif_pathShift_le_advanceModulus zero_le y)

theorem advanceModulus_mono {c c' : ℝ≥0} (h : c ≤ c') (y : C(ℝ≥0, E)) :
    advanceModulus c y ≤ advanceModulus c' y :=
  csSup_le_csSup (bddAbove_image_dUnif _ y _) ((nonempty_Icc.2 zero_le).image _)
    (image_mono (Icc_subset_Icc le_rfl h))

@[simp] theorem advanceModulus_zero (y : C(ℝ≥0, E)) : advanceModulus 0 y = 0 := by
  simp [advanceModulus, pathShift_zero_right, dUnif_self]

/-- The advance modulus is jointly continuous in the time and the path. -/
theorem continuous_advanceModulus :
    Continuous fun p : ℝ≥0 × C(ℝ≥0, E) => advanceModulus p.1 p.2 := by
  have h : (fun p : ℝ≥0 × C(ℝ≥0, E) => advanceModulus p.1 p.2) =
      fun p => sSup ((fun u : ℝ≥0 => dUnif (pathShift p.2 (u * p.1)) p.2) '' Icc 0 1) := by
    funext p
    exact sSup_image_Icc_eq_sSup_image_mul (fun s => dUnif (pathShift p.2 s) p.2) p.1
  rw [h]
  refine isCompact_Icc.continuous_sSup ?_
  exact (continuous_dUnif (E := E)).comp ((continuous_pathShift_uncurry.comp
    ((continuous_snd.comp continuous_fst).prodMk
      (continuous_snd.mul (continuous_fst.comp continuous_fst)))).prodMk
        (continuous_snd.comp continuous_fst))

theorem tendsto_advanceModulus_zero (y : C(ℝ≥0, E)) :
    Tendsto (fun c => advanceModulus c y) (𝓝 0) (𝓝 0) := by
  have h : Continuous fun c : ℝ≥0 => advanceModulus c y :=
    continuous_advanceModulus.comp (continuous_id.prodMk continuous_const)
  simpa using h.tendsto 0

/-! ### The delay modulus of an advanced path -/

/-- Delaying commutes with the advance up to the advance modulus:
`dUnif (pathDelay s (pathShift y c)) (pathDelay s y) ≤ dUnif (pathShift y c) y`. -/
theorem dUnif_pathDelay_pathShift_le (s c : ℝ≥0) (y : C(ℝ≥0, E)) :
    dUnif (pathDelay s (pathShift y c)) (pathDelay s y) ≤ dUnif (pathShift y c) y :=
  dUnif_le_dUnif_of_forall_exists_le fun t => ⟨t - s, tsub_le_self, le_of_eq (by simp)⟩

/-- **The delay modulus of an advanced path.**
`delayModulus a (pathShift y c) ≤ delayModulus a y + 2 * advanceModulus c y`. -/
theorem delayModulus_pathShift_le (a c : ℝ≥0) (y : C(ℝ≥0, E)) :
    delayModulus a (pathShift y c) ≤ delayModulus a y + 2 * advanceModulus c y := by
  refine csSup_le ((nonempty_Icc.2 zero_le).image _) ?_
  rintro _ ⟨s, hs, rfl⟩
  have h1 : dUnif (pathDelay s (pathShift y c)) (pathDelay s y) ≤ advanceModulus c y :=
    (dUnif_pathDelay_pathShift_le s c y).trans (dUnif_pathShift_le_advanceModulus le_rfl y)
  have h2 : dUnif (pathDelay s y) y ≤ delayModulus a y := dUnif_pathDelay_le_delayModulus hs.2 y
  have h3 : dUnif y (pathShift y c) ≤ advanceModulus c y := by
    rw [dUnif_comm]; exact dUnif_pathShift_le_advanceModulus le_rfl y
  have t1 := dUnif_triangle (pathDelay s (pathShift y c)) y (pathShift y c)
  have t2 := dUnif_triangle (pathDelay s (pathShift y c)) (pathDelay s y) y
  show dUnif (pathDelay s (pathShift y c)) (pathShift y c) ≤ _
  linarith

end LatticeProb
