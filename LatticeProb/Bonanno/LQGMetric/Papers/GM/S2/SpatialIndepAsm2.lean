/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepAsm2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm1
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# GM Lemma 2.7, assembly: the Markov domain `U = ⋃_z B_{1+s}(z)` after translation

Source: GM arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, l. 974
("Let `U = ⋃_{z ∈ Z} B_{1+s}(z)`"). Own elementary geometry: the balls `B_R(z − a)` (`z ∈ Z`,
`|z − w| ≥ 2R`) are disjoint, each is relatively clopen in `U`, their boundary circles lie in
`ℂ ∖ U`, `U` is bounded, and for `a` large `U` misses `∂𝔻`; translating and normalizing a
whole-plane GFF gives a normalized one (needed for `Blueprint.LMLem2_1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric

namespace LQGMetric.GM

open Blueprint

/-- `U = ⋃_{z ∈ Z} B_R(z − a)` -/
def unionO (Z : Finset ℂ) (a : ℂ) (R : ℝ) : Opens ℂ :=
  ⟨⋃ z ∈ Z, ball (z - a) R, isOpen_biUnion fun _ _ => isOpen_ball⟩

section Geom

variable {Z : Finset ℂ} {a : ℂ} {R : ℝ}

lemma coe_unionO : (unionO Z a R : Set ℂ) = ⋃ z ∈ Z, ball (z - a) R := rfl

lemma ballO_le_unionO {z : ℂ} (hz : z ∈ Z) : ballO (z - a) R ≤ unionO Z a R := by
  intro y hy
  show y ∈ (unionO Z a R : Set ℂ)
  rw [coe_unionO]
  exact mem_biUnion hz hy

lemma disjoint_ball_shift (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * R ≤ ‖z - w‖) {z w : ℂ}
    (hz : z ∈ Z) (hw : w ∈ Z) (hzw : z ≠ w) : Disjoint (ball (z - a) R) (ball (w - a) R) := by
  refine ball_disjoint_ball ?_
  rw [dist_eq_norm, sub_sub_sub_cancel_right]
  linarith [hsep z hz w hw hzw]

lemma unionO_diff_ball (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * R ≤ ‖z - w‖) {z : ℂ}
    (hz : z ∈ Z) : (unionO Z a R : Set ℂ) \ ball (z - a) R = ⋃ w ∈ Z.erase z, ball (w - a) R := by
  ext y
  simp only [coe_unionO, Set.mem_sdiff, mem_iUnion, Finset.mem_erase, exists_prop]
  constructor
  · rintro ⟨⟨w, hw, hy⟩, hyz⟩
    exact ⟨w, ⟨fun h => hyz (h ▸ hy), hw⟩, hy⟩
  · rintro ⟨w, ⟨hwz, hw⟩, hy⟩
    exact ⟨⟨w, hw, hy⟩, fun hy' =>
      (disjoint_ball_shift hsep hw hz hwz).ne_of_mem hy hy' rfl⟩

lemma isOpen_unionO_diff (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * R ≤ ‖z - w‖) {z : ℂ}
    (hz : z ∈ Z) : IsOpen ((unionO Z a R : Set ℂ) \ (ballO (z - a) R : Set ℂ)) := by
  show IsOpen ((unionO Z a R : Set ℂ) \ ball (z - a) R)
  rw [unionO_diff_ball hsep hz]
  exact isOpen_biUnion fun _ _ => isOpen_ball

lemma sphere_subset_compl_unionO (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * R ≤ ‖z - w‖)
    (hR : 0 < R) {z : ℂ} (hz : z ∈ Z) : sphere (z - a) |R| ⊆ (unionO Z a R : Set ℂ)ᶜ := by
  intro y hy hyU
  rw [coe_unionO, mem_iUnion₂] at hyU
  obtain ⟨w, hw, hyw⟩ := hyU
  rw [mem_sphere, abs_of_pos hR] at hy
  by_cases hzw : z = w
  · subst hzw; rw [mem_ball] at hyw; linarith
  · have h1 := hsep z hz w hw hzw
    have h2 : ‖z - w‖ ≤ dist y (z - a) + dist y (w - a) := by
      have := dist_triangle_left (z - a) (w - a) y
      rwa [dist_eq_norm (z - a), sub_sub_sub_cancel_right] at this
    rw [mem_ball] at hyw
    linarith

lemma isBounded_unionO : Bornology.IsBounded (unionO Z a R : Set ℂ) := by
  rw [coe_unionO, Bornology.isBounded_biUnion_finset]
  exact fun _ _ => isBounded_ball

/-- for `a` real and large, `U` misses the unit circle -/
lemma disjoint_unionO_sphere (hR : 0 < R) :
    Disjoint (unionO Z (((∑ z ∈ Z, ‖z‖) + R + 2 : ℝ) : ℂ) R : Set ℂ) (sphere (0 : ℂ) 1) := by
  rw [coe_unionO, Set.disjoint_iUnion₂_left]
  intro z hz
  rw [Set.disjoint_left]
  intro y hy hy1
  rw [mem_sphere_zero_iff_norm] at hy1
  rw [mem_ball, dist_eq_norm] at hy
  have hzs : ‖z‖ ≤ ∑ z ∈ Z, ‖z‖ :=
    Finset.single_le_sum (f := fun z => ‖z‖) (fun _ _ => norm_nonneg _) hz
  have hs0 : 0 ≤ ∑ z ∈ Z, ‖z‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set A : ℝ := (∑ z ∈ Z, ‖z‖) + R + 2
  have hA : ‖(A : ℂ)‖ = A := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 : ‖(A : ℂ)‖ ≤ ‖y - (z - (A : ℂ))‖ + ‖y‖ + ‖z‖ := by
    calc ‖(A : ℂ)‖ = ‖(y - (z - (A : ℂ))) - y + z‖ := by congr 1; ring
      _ ≤ ‖(y - (z - (A : ℂ))) - y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  rw [hA] at h3
  linarith

end Geom

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- the translated, normalized field `h(· + a) − h(· + a)_1(0)` is a normalized whole-plane GFF -/
theorem isNormalized_shift {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (a : ℂ) :
    IsNormalizedWPGFF (fun ω => addConst (affineComp 1 a (h ω))
      (-circleAvg (affineComp 1 a (h ω)) 1 0)) P := by
  have h1 := hh.affineComp one_pos a
  refine ⟨h1.addConst ((measurable_circleAvg_left 1 0).comp h1.measurable).neg, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero h1] with ω hω
  rw [hω]; ring

end LQGMetric.GM
