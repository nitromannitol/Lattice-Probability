/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.WaypointProofTemplate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RGeometry

/-!
# Metric facts about the moved polar template for the scaled-grid estimate waypoints

the waypoint construction, "Itinerary for x", steps 1–2 (the template construction): the moved template
`T(t) = z + r e^{iϑ} polarTemplate(t)` starts at the chosen boundary point `y₀` when `ϑ = arg (y₀ - z)`, stays in
`0.9r ≤ |T(t) - z| ≤ 1.1r`, and is `29r`-Lipschitz. In the unnormalised time `u ∈ [0,4]` the radius is
`1/5`-Lipschitz and the angle is `(2π - 1/10)`-Lipschitz, so the speed is at most
`1/5 + (11/10)(2π - 1/10) < 29/4`. All statements are for the clamped template
`CellularEmbedding.movedTemplate`, hence hold for every real parameter.
-/

set_option autoImplicit false

noncomputable section

open Set Real
open MatedCRTHarmonic.Topology

namespace MatedCRTHarmonic.CellFamily

/-- The increment of a kink `max (· - k) 0` over `[u, u']` is in `[0, u' - u]` and decreases in `k`. -/
theorem waypointProof_kink_mono {u u' k k' : ℝ} (huu : u ≤ u') (hkk : k ≤ k') :
    0 ≤ max (u' - k') 0 - max (u - k') 0 ∧
      max (u' - k') 0 - max (u - k') 0 ≤ max (u' - k) 0 - max (u - k) 0 ∧
      max (u' - k) 0 - max (u - k) 0 ≤ u' - u := by
  refine ⟨?_, ?_, ?_⟩
  · have := max_le_max_right 0 (show u - k' ≤ u' - k' by linarith)
    linarith
  · rcases le_total u' k' with h1 | h1
    · rw [max_eq_right (show u' - k' ≤ 0 by linarith), max_eq_right (show u - k' ≤ 0 by linarith)]
      have := max_le_max_right 0 (show u - k ≤ u' - k by linarith)
      linarith
    · rw [max_eq_left (show 0 ≤ u' - k' by linarith), max_eq_left (show 0 ≤ u' - k by linarith)]
      rcases le_total u k with h2 | h2
      · rw [max_eq_right (show u - k ≤ 0 by linarith)]
        have := le_max_right (u - k') 0
        linarith
      · rw [max_eq_left (show 0 ≤ u - k by linarith)]
        have := le_max_left (u - k') 0
        linarith
  · have := max_le (show u' - k ≤ max (u - k) 0 + (u' - u) by linarith [le_max_left (u - k) 0])
      (show (0 : ℝ) ≤ max (u - k) 0 + (u' - u) by linarith [le_max_right (u - k) 0])
    linarith

/-- One-sided radius increment bound: the radius of the polar template has slopes in `[-1/10, 1/5]`. -/
theorem waypointProof_polarRadius_sub_le {u u' : ℝ} (huu : u ≤ u') :
    |polarRadius u' - polarRadius u| ≤ (1 / 5) * (u' - u) := by
  obtain ⟨h10, h12, h1Δ⟩ := waypointProof_kink_mono (k := 1) (k' := 2) huu (by norm_num)
  obtain ⟨h20, h23, -⟩ := waypointProof_kink_mono (k := 2) (k' := 3) huu (by norm_num)
  have hdiff : polarRadius u' - polarRadius u = -(u' - u) / 10 +
      (3 / 10) * ((max (u' - 1) 0 - max (u - 1) 0) - (max (u' - 2) 0 - max (u - 2) 0)) +
      (1 / 10) * (max (u' - 3) 0 - max (u - 3) 0) := by
    unfold polarRadius
    ring
  rw [hdiff, abs_le]
  constructor <;> nlinarith

/-- The angle of the polar template has slopes in `[0, 2π - 1/10]`. -/
theorem waypointProof_polarAngle_sub_le {u u' : ℝ} (huu : u ≤ u') :
    |polarAngle u' - polarAngle u| ≤ (2 * π - 1 / 10) * (u' - u) := by
  have hpi := Real.pi_gt_three
  obtain ⟨h30, h32, -⟩ := waypointProof_kink_mono (k := 2) (k' := 3) huu (by norm_num)
  obtain ⟨-, -, h2Δ⟩ := waypointProof_kink_mono (k := 2) (k' := 2) huu le_rfl
  have hdiff : polarAngle u' - polarAngle u =
      (2 * π - 1 / 10) * ((max (u' - 2) 0 - max (u - 2) 0) - (max (u' - 3) 0 - max (u - 3) 0)) +
        (1 / 5) * (max (u' - 3) 0 - max (u - 3) 0) := by
    unfold polarAngle
    ring
  rw [hdiff, abs_le]
  have hA : 0 ≤ (2 * π - 1 / 10) *
      ((max (u' - 2) 0 - max (u - 2) 0) - (max (u' - 3) 0 - max (u - 3) 0)) :=
    mul_nonneg (by linarith) (by linarith)
  have hB : (1 / 5) * (max (u' - 3) 0 - max (u - 3) 0) ≤
      (2 * π - 1 / 10) * (max (u' - 3) 0 - max (u - 3) 0) :=
    mul_le_mul_of_nonneg_right (by linarith) h30
  have hC : (2 * π - 1 / 10) * (max (u' - 2) 0 - max (u - 2) 0) ≤ (2 * π - 1 / 10) * (u' - u) :=
    mul_le_mul_of_nonneg_left h2Δ (by linarith)
  constructor <;> nlinarith

/-- Unit-circle chord bound `|e^{ia} - e^{ib}| ≤ |a - b|`. -/
theorem waypointProof_exp_chord_bound (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have he : Complex.exp ((a : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) * Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  have hfactor : Complex.exp ((b : ℂ) * Complex.I) * Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) -
      Complex.exp ((b : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsin := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  have hrewrite : Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) =
      Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) := by
    congr 1
    ring
  rw [hrewrite] at hsin
  simpa [Real.norm_eq_abs] using hsin

/-- The polar template on `[0,1]` in polar form. -/
theorem waypointProof_polarTemplate_apply (t : unitInterval) :
    polarTemplate t = ((polarRadius (4 * (t : ℝ)) : ℝ) : ℂ) *
      Complex.exp (((polarAngle (4 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) := rfl

/-- **The polar template is `29`-Lipschitz in its normalised time.** -/
theorem waypointProof_polarTemplate_lipschitz (s t : unitInterval) :
    ‖polarTemplate s - polarTemplate t‖ ≤ 29 * |(s : ℝ) - t| := by
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  rw [waypointProof_polarTemplate_apply, waypointProof_polarTemplate_apply]
  set a := polarRadius (4 * (s : ℝ)) with ha
  set b := polarRadius (4 * (t : ℝ)) with hb
  set α := polarAngle (4 * (s : ℝ)) with hα
  set β := polarAngle (4 * (t : ℝ)) with hβ
  have hb0 : 0 ≤ b ∧ b ≤ 11 / 10 := by
    have h := polarRadius_bounds (u := 4 * (t : ℝ)) (by nlinarith [t.2.1]) (by nlinarith [t.2.2])
    exact ⟨by linarith [h.1], h.2⟩
  have hrad : |a - b| ≤ (1 / 5) * (4 * |(s : ℝ) - t|) := by
    rcases le_total (s : ℝ) t with hst | hst
    · have h := waypointProof_polarRadius_sub_le (u := 4 * (s : ℝ)) (u' := 4 * (t : ℝ))
        (by linarith)
      rw [abs_sub_comm (s : ℝ), abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s), abs_sub_comm]
      linarith
    · have h := waypointProof_polarRadius_sub_le (u := 4 * (t : ℝ)) (u' := 4 * (s : ℝ))
        (by linarith)
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t)]
      linarith
  have hang : |α - β| ≤ (2 * π - 1 / 10) * (4 * |(s : ℝ) - t|) := by
    rcases le_total (s : ℝ) t with hst | hst
    · have h := waypointProof_polarAngle_sub_le (u := 4 * (s : ℝ)) (u' := 4 * (t : ℝ))
        (by linarith)
      rw [abs_sub_comm (s : ℝ), abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s), abs_sub_comm]
      linarith
    · have h := waypointProof_polarAngle_sub_le (u := 4 * (t : ℝ)) (u' := 4 * (s : ℝ))
        (by linarith)
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t)]
      linarith
  have hsplit : (a : ℂ) * Complex.exp ((α : ℂ) * Complex.I) - (b : ℂ) * Complex.exp ((β : ℂ) * Complex.I) =
      ((a - b : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I) +
        (b : ℂ) * (Complex.exp ((α : ℂ) * Complex.I) - Complex.exp ((β : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [hsplit]
  have hchord := waypointProof_exp_chord_bound α β
  have h1 : ‖((a - b : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I)‖ = |a - b| := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(b : ℂ) * (Complex.exp ((α : ℂ) * Complex.I) - Complex.exp ((β : ℂ) * Complex.I))‖ ≤
      (11 / 10) * |α - β| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0.1]
    exact mul_le_mul hb0.2 hchord (norm_nonneg _) (by norm_num)
  have hst0 : 0 ≤ |(s : ℝ) - t| := abs_nonneg _
  calc
    _ ≤ ‖((a - b : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I)‖ +
        ‖(b : ℂ) * (Complex.exp ((α : ℂ) * Complex.I) - Complex.exp ((β : ℂ) * Complex.I))‖ :=
      norm_add_le _ _
    _ ≤ (1 / 5) * (4 * |(s : ℝ) - t|) + (11 / 10) * ((2 * π - 1 / 10) * (4 * |(s : ℝ) - t|)) := by
      rw [h1]
      have h3 : (11 / 10) * |α - β| ≤ (11 / 10) * ((2 * π - 1 / 10) * (4 * |(s : ℝ) - t|)) :=
        mul_le_mul_of_nonneg_left hang (by norm_num)
      linarith
    _ ≤ 29 * |(s : ℝ) - t| := by nlinarith

/-- **The moved (clamped) template is `29r`-Lipschitz on all of `ℝ`** (the waypoint construction, step 2). -/
theorem waypointProof_movedTemplate_lipschitz (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (ϑ s t : ℝ) :
    ‖CellularEmbedding.movedTemplate z r ϑ s - CellularEmbedding.movedTemplate z r ϑ t‖ ≤
      29 * r * |s - t| := by
  unfold CellularEmbedding.movedTemplate
  have hsub : z + (r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) *
        polarTemplate (Set.projIcc 0 1 zero_le_one s) -
      (z + (r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I) *
        polarTemplate (Set.projIcc 0 1 zero_le_one t)) =
      ((r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)) *
        (polarTemplate (Set.projIcc 0 1 zero_le_one s) -
          polarTemplate (Set.projIcc 0 1 zero_le_one t)) := by ring
  rw [hsub, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr]
  have hlip := waypointProof_polarTemplate_lipschitz (Set.projIcc 0 1 zero_le_one s)
    (Set.projIcc 0 1 zero_le_one t)
  have hproj : |((Set.projIcc 0 1 zero_le_one s : unitInterval) : ℝ) -
      (Set.projIcc 0 1 zero_le_one t : unitInterval)| ≤ |s - t| :=
    Set.abs_projIcc_sub_projIcc zero_le_one
  calc
    r * ‖polarTemplate (Set.projIcc 0 1 zero_le_one s) -
        polarTemplate (Set.projIcc 0 1 zero_le_one t)‖ ≤
        r * (29 * |s - t|) := by
      apply mul_le_mul_of_nonneg_left _ hr
      exact hlip.trans (mul_le_mul_of_nonneg_left hproj (by norm_num))
    _ = 29 * r * |s - t| := by ring

/-- The moved template stays in the annulus `0.9r ≤ |· - z| ≤ 1.1r` (the waypoint construction, step 1). -/
theorem waypointProof_movedTemplate_norm_bounds (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (ϑ s : ℝ) :
    (9 / 10) * r ≤ ‖CellularEmbedding.movedTemplate z r ϑ s - z‖ ∧
      ‖CellularEmbedding.movedTemplate z r ϑ s - z‖ ≤ (11 / 10) * r := by
  unfold CellularEmbedding.movedTemplate
  rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, polarTemplate_norm]
  set u : unitInterval := Set.projIcc 0 1 zero_le_one s
  have h := polarRadius_bounds (u := 4 * (u : ℝ)) (by nlinarith [u.2.1]) (by nlinarith [u.2.2])
  constructor
  · have := mul_le_mul_of_nonneg_left h.1 hr
    linarith
  · have := mul_le_mul_of_nonneg_left h.2 hr
    linarith

/-- The polar template starts at `1`. -/
theorem waypointProof_polarTemplate_zero : polarTemplate 0 = 1 := by
  norm_num [polarTemplate, polarRadius, polarAngle]

/-- With `ϑ = arg (y₀ - z)` and `|y₀ - z| = r`, the moved template starts at `y₀` (the waypoint construction, step 1). -/
theorem waypointProof_movedTemplate_zero {z y₀ : ℂ} {r : ℝ} (hy : ‖y₀ - z‖ = r) :
    CellularEmbedding.movedTemplate z r (Complex.arg (y₀ - z)) 0 = y₀ := by
  unfold CellularEmbedding.movedTemplate
  have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := by
    rw [Set.projIcc_left]
    rfl
  rw [hproj, waypointProof_polarTemplate_zero, mul_one, ← hy, Complex.norm_mul_exp_arg_mul_I]
  ring

end MatedCRTHarmonic.CellFamily
