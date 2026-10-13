import LatticeProb.Euclidean.Lattice
import LatticeProb.Euclidean.Cube
import LatticeProb.Euclidean.Shell
import LatticeProb.Euclidean.Summability

/-!
# Integrals of the critical radial integrand over lattice cube unions

The critical integrand `|x|^{-d}` is integrable on the unit cubes centered at integer points away
from the origin, and on closed Euclidean annuli.  The module compares the lattice sum of
`|w|^{-d}` over the points with `2√d ≤ |w| ≤ R` with the integral over the union of their unit
cubes, with error `comparisonConstant d · radialErrorConstant d`.  It evaluates the integral
over a Euclidean annulus in polar coordinates as `d · unitBallVolume d · log (b/a)`, and it
sandwiches the cube union between two annuli.
-/

noncomputable section

open scoped BigOperators
open scoped ENNReal
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Cube LatticeProb.Euclidean.Shell LatticeProb.Euclidean.Summability MeasureTheory Set

namespace LatticeProb.Euclidean.Integral

/-- The critical radial integrand `|x|^{-d}` on `Fin d → ℝ`, with the Euclidean radius. -/
def criticalIntegrand (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  Real.rpow (radius x) (-(d : ℝ))

/-- The integer points `w` with `2√d ≤ |w| ≤ R` (physical radius), enumerated in a box. -/
def latticeAnnulus (d : ℕ) (R : ℝ) : Finset (Site d) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌈R⌉) ⌈R⌉)).filter
    (fun w => 2 * Real.sqrt d ≤ radius (physical 1 w) ∧ radius (physical 1 w) ≤ R)

/-- The union of the unit cubes centered at the points of `latticeAnnulus d R`. -/
def cubeUnion (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  ⋃ w ∈ latticeAnnulus d R, cube w

/-- Membership in `latticeAnnulus d R`. -/
lemma mem_latticeAnnulus (d : ℕ) (R : ℝ) (w : Site d) :
    w ∈ latticeAnnulus d R ↔
      2 * Real.sqrt d ≤ radius (physical 1 w) ∧ radius (physical 1 w) ≤ R := by
  classical
  rw [latticeAnnulus, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro k
    have hc := (abs_coord_le_radius (physical 1 w) k).trans h.2
    simp only [physical, one_mul] at hc
    have hi : |w k| ≤ ⌈R⌉ := by
      have hr := hc.trans (Int.le_ceil R)
      rw [← Int.cast_abs] at hr
      exact_mod_cast hr
    exact Finset.mem_Icc.mpr (abs_le.mp hi)

/-- The closure of a unit cube is compact. -/
lemma cube_closure_compact {d : ℕ} (w : Site d) : IsCompact (closure (cube w)) := by
  let a : Fin d → ℝ := fun k => (w k : ℝ)-1/2
  let b : Fin d → ℝ := fun k => (w k : ℝ)+1/2
  have hs : cube w ⊆ Icc a b := by
    intro x hx
    exact ⟨fun k => (hx k).1, fun k => (hx k).2.le⟩
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (isClosed_Icc.closure_subset_iff.mpr hs)

/-- On the closure of a unit cube centered at `w` with `2√d ≤ |w|`, the radius is at least `3|w|/4`. -/
lemma cube_closure_radius_lower {d : ℕ} (w : Site d)
    (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) :
    ∀ x ∈ closure (cube w), 3 * radius (physical 1 w) / 4 ≤ radius x := by
  have hs : cube w ⊆ {x | 3 * radius (physical 1 w) / 4 ≤ radius x} :=
    fun x hx => cube_radius_lower w hw hx
  exact (isClosed_le continuous_const (radius_continuous d)).closure_subset_iff.mpr hs

/-- A unit cube centered at `w` with `2√d ≤ |w|` has a center of positive radius, for `d ≥ 1`. -/
lemma cube_center_radius_pos {d : ℕ} (hd : 1 ≤ d) (w : Site d)
    (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) : 0 < radius (physical 1 w) := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  exact lt_of_lt_of_le (mul_pos (by norm_num) hs) hw

/-- The critical integrand is integrable on the closure of a unit cube centered at `w` with `2√d ≤ |w|`. -/
theorem criticalIntegrand_integrableOn_cube_closure (d : ℕ) (hd : 1 ≤ d)
    (w : Site d) (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) :
    IntegrableOn (criticalIntegrand d) (closure (cube w)) volume := by
  have hb := cube_center_radius_pos hd w hw
  have hc : ContinuousOn (criticalIntegrand d) (closure (cube w)) := by
    apply (radius_continuous d).continuousOn.rpow_const
    intro x hx
    left
    exact ne_of_gt (lt_of_lt_of_le (by positivity) (cube_closure_radius_lower w hw x hx))
  exact hc.integrableOn_compact (cube_closure_compact w)

/-- The critical integrand is integrable on a unit cube centered at `w` with `2√d ≤ |w|`. -/
theorem criticalIntegrand_integrableOn_cube (d : ℕ) (hd : 1 ≤ d)
    (w : Site d) (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) :
    IntegrableOn (criticalIntegrand d) (cube w) volume :=
  (criticalIntegrand_integrableOn_cube_closure d hd w hw).mono_set subset_closure

/-- A unit cube has real volume one. -/
lemma cube_real_volume {d : ℕ} (w : Site d) : volume.real (cube w) = 1 := by
  rw [Measure.real, cube_volume, ENNReal.toReal_one]

/-- Integrating the pointwise comparison over a unit cube of volume one bounds the integral error by `comparisonConstant d · |w|^(-(d+1))`. -/
theorem cube_integral_error (d : ℕ) (hd : 1 ≤ d) (w : Site d)
    (hw : 2 * Real.sqrt d ≤ radius (physical 1 w)) :
    |criticalIntegrand d (physical 1 w) - ∫ x in cube w, criticalIntegrand d x| ≤
      comparisonConstant d * Real.rpow (radius (physical 1 w)) (-(d : ℝ)-1) := by
  have hf := criticalIntegrand_integrableOn_cube d hd w hw
  have hm : volume (cube w) ≠ ∞ := by rw [cube_volume]; exact ENNReal.one_ne_top
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => criticalIntegrand d (physical 1 w))
      (cube w) volume := integrableOn_const hm
  have he : criticalIntegrand d (physical 1 w) - ∫ x in cube w, criticalIntegrand d x =
      ∫ x in cube w, (criticalIntegrand d (physical 1 w) - criticalIntegrand d x) := by
    rw [integral_sub hconst hf, setIntegral_const, cube_real_volume, one_smul]
  rw [he, ← Real.norm_eq_abs]
  have h := norm_setIntegral_le_of_norm_le_const (s := cube w) (μ := volume)
    (f := fun x => criticalIntegrand d (physical 1 w) - criticalIntegrand d x)
    (lt_top_iff_ne_top.mpr hm) (fun x hx => by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact cube_radius_rpow_comparison d hd w hw x hx)
  rwa [cube_real_volume, mul_one] at h

/-- The union of the unit cubes over `latticeAnnulus d R` is measurable. -/
lemma cubeUnion_measurable (d : ℕ) (R : ℝ) : MeasurableSet (cubeUnion d R) :=
  Finset.measurableSet_biUnion _ (fun w _ => cube_measurable w)

/-- The critical integrand is integrable on the union of the unit cubes over `latticeAnnulus d R`. -/
theorem criticalIntegrand_integrableOn_cubeUnion (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    IntegrableOn (criticalIntegrand d) (cubeUnion d R) volume := by
  apply integrableOn_finset_iUnion.mpr
  intro w hw
  exact criticalIntegrand_integrableOn_cube d hd w ((mem_latticeAnnulus d R w).mp hw).1

/-- The integral over the cube union is the sum of the integrals over its cubes. -/
theorem cubeUnion_integral (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    ∫ x in cubeUnion d R, criticalIntegrand d x =
      ∑ w ∈ latticeAnnulus d R, ∫ x in cube w, criticalIntegrand d x := by
  exact integral_biUnion_finset _ (fun w _ => cube_measurable w)
    (fun _ _ _ _ h => cubes_disjoint h)
    (fun w hw => criticalIntegrand_integrableOn_cube d hd w
      ((mem_latticeAnnulus d R w).mp hw).1)

/-- Finite disjoint-cube error, retaining the precise finite radial error sum. -/
theorem finite_cube_integral_error (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    |(∑ w ∈ latticeAnnulus d R, Real.rpow (radius (physical 1 w)) (-(d : ℝ))) -
      ∫ x in cubeUnion d R, Real.rpow (radius x) (-(d : ℝ))| ≤
    comparisonConstant d * ∑ w ∈ latticeAnnulus d R,
      Real.rpow (radius (physical 1 w)) (-(d : ℝ)-1) := by
  change |(∑ w ∈ latticeAnnulus d R, criticalIntegrand d (physical 1 w)) -
    ∫ x in cubeUnion d R, criticalIntegrand d x| ≤ _
  rw [cubeUnion_integral d hd R, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w ∈ latticeAnnulus d R,
        |criticalIntegrand d (physical 1 w) - ∫ x in cube w, criticalIntegrand d x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ latticeAnnulus d R,
        comparisonConstant d * Real.rpow (radius (physical 1 w)) (-(d : ℝ)-1) :=
      Finset.sum_le_sum (fun w hw => cube_integral_error d hd w
        ((mem_latticeAnnulus d R w).mp hw).1)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Every point of `latticeAnnulus d R` is nonzero, for `d ≥ 1`. -/
lemma latticeAnnulus_nonzero (d : ℕ) (hd : 1 ≤ d) (R : ℝ) (w : Site d)
    (hw : w ∈ latticeAnnulus d R) : w ≠ 0 := by
  have hp := cube_center_radius_pos hd w ((mem_latticeAnnulus d R w).mp hw).1
  intro hz
  subst w
  have hzrad : radius (physical 1 (0 : Site d)) = 0 := by simp [radius, physical]
  rw [hzrad] at hp
  exact (lt_irrefl 0) hp

/-- The finite radial error sum over `latticeAnnulus d R` is at most `radialErrorConstant d`. -/
lemma finite_radial_error_le_global (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    ∑ w ∈ latticeAnnulus d R, Real.rpow (radius (physical 1 w)) (-(d : ℝ)-1) ≤
      radialErrorConstant d := by
  classical
  let s := (latticeAnnulus d R).subtype (fun w => w ≠ 0)
  have he : (∑ w ∈ latticeAnnulus d R,
      Real.rpow (radius (physical 1 w)) (-(d : ℝ)-1)) =
      ∑ w ∈ s, Real.rpow (radius (physical 1 w.val)) (-(d : ℝ)-1) := by
    apply Finset.sum_bij (fun w hw => ⟨w, latticeAnnulus_nonzero d hd R w hw⟩)
    · intro w hw
      exact Finset.mem_subtype.mpr hw
    · intro w hw z hz he
      exact congrArg Subtype.val he
    · intro w hw
      exact ⟨w.val, Finset.mem_subtype.mp hw, rfl⟩
    · intro w hw
      rfl
  rw [he]
  exact (nonzero_radial_error_summable_real d hd).sum_le_tsum s
    (fun w _ => Real.rpow_nonneg (radius_nonneg _) _)

/-- The finite cube-sum error bound, and its uniform bound by `comparisonConstant d * radialErrorConstant d`; the only hypothesis is `1 ≤ d`. -/
theorem disjoint_cube_integral_inequality (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    (|(∑ w ∈ latticeAnnulus d R, Real.rpow (radius (physical 1 w)) (-(d : ℝ))) -
      ∫ x in cubeUnion d R, Real.rpow (radius x) (-(d : ℝ))| ≤
      comparisonConstant d * ∑ w ∈ latticeAnnulus d R,
        Real.rpow (radius (physical 1 w)) (-(d : ℝ)-1)) ∧
    (comparisonConstant d * ∑ w ∈ latticeAnnulus d R,
        Real.rpow (radius (physical 1 w)) (-(d : ℝ)-1) ≤
      comparisonConstant d * radialErrorConstant d) := by
  constructor
  · exact finite_cube_integral_error d hd R
  · exact mul_le_mul_of_nonneg_left (finite_radial_error_le_global d hd R)
      (by unfold comparisonConstant; positivity)

/-- The radial profile `r ↦ r^{-d}` restricted to `[a,b]`. -/
def profile (d : ℕ) (a b : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc a b) (fun r => Real.rpow r (-(d : ℝ)))

/-- The polar integral of `|x|^{-d}` over the Euclidean annulus `a ≤ |x| ≤ b` is `d · unitBallVolume d · log (b/a)`. -/
lemma annulus_rpow_integral {d : ℕ} (hd : 1 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b}, Real.rpow (radius x) (-(d : ℝ))
      = (d : ℝ) * unitBallVolume d * Real.log (b / a) := by
  have hSm : MeasurableSet {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b} := by
    have hr : Measurable (fun x : Fin d → ℝ => radius x) := by
      unfold radius
      fun_prop
    exact (measurableSet_Icc.preimage hr : MeasurableSet ((fun x : Fin d → ℝ => radius x) ⁻¹' Icc a b))
  have h1 : ∫ x in {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b}, Real.rpow (radius x) (-(d : ℝ))
      = ∫ x : Fin d → ℝ,
          profile d a b ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
    rw [← integral_indicator hSm]
    congr 1
    funext x
    rw [← radius_norm x, profile]
    by_cases h : a ≤ radius x ∧ radius x ≤ b
    · have hx : radius x ∈ Icc a b := ⟨h.1, h.2⟩
      rw [Set.indicator_of_mem (show x ∈ {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b} from h),
        Set.indicator_of_mem hx]
    · have hx : radius x ∉ Icc a b := fun hm => h ⟨hm.1, hm.2⟩
      rw [Set.indicator_of_notMem (show x ∉ {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b} from h),
        Set.indicator_of_notMem hx]
  have h2 : ∫ x : Fin d → ℝ, profile d a b ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖
      = ∫ y : EuclideanSpace ℝ (Fin d), profile d a b ‖y‖ :=
    (PiLp.volume_preserving_toLp (Fin d)).integral_comp (MeasurableEquiv.toLp 2 _).measurableEmbedding
      (fun y : EuclideanSpace ℝ (Fin d) => profile d a b ‖y‖)
  rw [h1, h2]
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  rw [MeasureTheory.integral_fun_norm_addHaar volume (profile d a b)]
  rw [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  have hvol : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) = unitBallVolume d := by
    rw [Measure.real, volume_unit_ball d hd, ENNReal.toReal_ofReal]
    unfold unitBallVolume
    positivity
  rw [hvol]
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • profile d a b y = Real.log (b / a) := by
    have hc : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) • profile d a b y
        = Set.indicator (Icc a b) (fun y : ℝ => y⁻¹) y := by
      intro y hy
      have hy0 : 0 < y := hy
      by_cases hyI : y ∈ Icc a b
      · have hexp : ((d - 1 : ℕ) : ℝ) + (-(d : ℝ)) = -1 := by
          rw [Nat.cast_sub hd]
          push_cast
          ring
        have hpow : y ^ (d - 1) * y ^ (-(d : ℝ)) = y⁻¹ := by
          rw [← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy0, hexp, Real.rpow_neg_one]
        rw [Set.indicator_of_mem hyI, smul_eq_mul, profile, Set.indicator_of_mem hyI]
        exact hpow
      · rw [Set.indicator_of_notMem hyI, smul_eq_mul, profile, Set.indicator_of_notMem hyI,
          mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hc, setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.mpr hsub, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      integral_inv_of_pos ha (ha.trans_le hab)]
  rw [hint]
  ring

/-- The cube union lies in the outer annulus `3√d/2 ≤ |x| ≤ R + √d/2`. -/
lemma cubeUnion_subset_outer (d : ℕ) (R : ℝ) :
    cubeUnion d R ⊆
      {x : Fin d → ℝ | 3 * Real.sqrt d / 2 ≤ radius x ∧ radius x ≤ R + Real.sqrt d / 2} := by
  intro x hx
  have hx' : x ∈ ⋃ w ∈ latticeAnnulus d R, cube w := hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx'
  obtain ⟨hw1, hw2⟩ := (mem_latticeAnnulus d R w).mp hw
  obtain ⟨he1, he2⟩ := abs_le.mp (cube_radius_error w hxw)
  show 3 * Real.sqrt d / 2 ≤ radius x ∧ radius x ≤ R + Real.sqrt d / 2
  constructor <;> linarith

/-- The inner annulus `5√d/2 ≤ |x| ≤ R - √d/2` lies in the cube union: the integer point
`w_k = ⌊x_k + 1/2⌋` has the unit cube of `w` containing `x`. -/
lemma inner_annulus_subset_cubeUnion (d : ℕ) (R : ℝ) :
    {x : Fin d → ℝ | 5 * Real.sqrt d / 2 ≤ radius x ∧ radius x ≤ R - Real.sqrt d / 2} ⊆
      cubeUnion d R := by
  intro x hx
  have hx' : 5 * Real.sqrt d / 2 ≤ radius x ∧ radius x ≤ R - Real.sqrt d / 2 := hx
  have hxcube : x ∈ cube (fun k => ⌊x k + 1 / 2⌋) := by
    simp only [cube, Set.mem_setOf_eq]
    intro k
    have h1 := Int.floor_le (x k + 1 / 2)
    have h2 := Int.lt_floor_add_one (x k + 1 / 2)
    constructor <;> linarith
  obtain ⟨he1, he2⟩ := abs_le.mp (cube_radius_error _ hxcube)
  have hw : (fun k => ⌊x k + 1 / 2⌋) ∈ latticeAnnulus d R := by
    rw [mem_latticeAnnulus]
    constructor <;> linarith [hx'.1, hx'.2]
  unfold cubeUnion
  exact Set.mem_iUnion₂.mpr ⟨_, hw, hxcube⟩

/-- The critical integrand is integrable on each closed Euclidean annulus with inner radius
`a > 0`, being continuous on a compact set. -/
lemma criticalIntegrand_integrableOn_annulus (d : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : Fin d → ℝ => Real.rpow (radius x) (-(d : ℝ)))
      {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b} volume := by
  have hclosed : IsClosed {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b} :=
    (isClosed_le continuous_const (radius_continuous d)).inter
      (isClosed_le (radius_continuous d) continuous_const)
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-b) b)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hcpt : IsCompact {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b} := by
    refine IsCompact.of_isClosed_subset hK hclosed ?_
    intro x hx
    have hx' : a ≤ radius x ∧ radius x ≤ b := hx
    rw [Set.mem_pi]
    intro k _
    exact abs_le.mp ((abs_coord_le_radius x k).trans hx'.2)
  have hc : ContinuousOn (fun x : Fin d → ℝ => Real.rpow (radius x) (-(d : ℝ)))
      {x : Fin d → ℝ | a ≤ radius x ∧ radius x ≤ b} := by
    apply (radius_continuous d).continuousOn.rpow_const
    intro x hx
    left
    have hx' : a ≤ radius x ∧ radius x ≤ b := hx
    exact ne_of_gt (lt_of_lt_of_le ha hx'.1)
  exact hc.integrableOn_compact hcpt

/-- The critical integrand is almost everywhere nonnegative on any set. -/
lemma criticalIntegrand_nonneg_ae (d : ℕ) (s : Set (Fin d → ℝ)) :
    0 ≤ᵐ[volume.restrict s] (fun x : Fin d → ℝ => Real.rpow (radius x) (-(d : ℝ))) :=
  Filter.Eventually.of_forall fun x => Real.rpow_nonneg (radius_nonneg x) _

/-- Outer comparison: the critical integral over the cube union is at most `d V_d` times the log of
the radius ratio of the outer annulus. -/
lemma integral_cubeUnion_le {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : Real.sqrt d ≤ R) :
    ∫ x in cubeUnion d R, Real.rpow (radius x) (-(d : ℝ)) ≤
      (d : ℝ) * unitBallVolume d * Real.log ((R + Real.sqrt d / 2) / (3 * Real.sqrt d / 2)) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have ha : 0 < 3 * Real.sqrt d / 2 := by linarith
  have hab : 3 * Real.sqrt d / 2 ≤ R + Real.sqrt d / 2 := by linarith
  have hmono : ∫ x in cubeUnion d R, Real.rpow (radius x) (-(d : ℝ)) ≤
      ∫ x in {x : Fin d → ℝ | 3 * Real.sqrt d / 2 ≤ radius x ∧ radius x ≤ R + Real.sqrt d / 2},
        Real.rpow (radius x) (-(d : ℝ)) :=
    setIntegral_mono_set
      (criticalIntegrand_integrableOn_annulus d (b := R + Real.sqrt d / 2) ha)
      (criticalIntegrand_nonneg_ae d _)
      (Filter.Eventually.of_forall fun x hx => cubeUnion_subset_outer d R hx)
  rw [annulus_rpow_integral hd ha hab] at hmono
  exact hmono

/-- Inner comparison: the critical integral over the cube union is at least `d V_d` times the log
of the radius ratio of the inner annulus, which is nonempty for `R ≥ 3√d`. -/
lemma integral_cubeUnion_ge {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 3 * Real.sqrt d ≤ R) :
    (d : ℝ) * unitBallVolume d * Real.log ((R - Real.sqrt d / 2) / (5 * Real.sqrt d / 2)) ≤
      ∫ x in cubeUnion d R, Real.rpow (radius x) (-(d : ℝ)) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have ha : 0 < 5 * Real.sqrt d / 2 := by linarith
  have hab : 5 * Real.sqrt d / 2 ≤ R - Real.sqrt d / 2 := by linarith
  have hmono : ∫ x in {x : Fin d → ℝ | 5 * Real.sqrt d / 2 ≤ radius x ∧
        radius x ≤ R - Real.sqrt d / 2}, Real.rpow (radius x) (-(d : ℝ)) ≤
      ∫ x in cubeUnion d R, Real.rpow (radius x) (-(d : ℝ)) :=
    setIntegral_mono_set (criticalIntegrand_integrableOn_cubeUnion d hd R)
      (criticalIntegrand_nonneg_ae d _)
      (Filter.Eventually.of_forall fun x hx => inner_annulus_subset_cubeUnion d R hx)
  rw [annulus_rpow_integral hd ha hab] at hmono
  exact hmono

end LatticeProb.Euclidean.Integral
