import LatticeProb.Network.RandomPathFlow
import LatticeProb.Analysis.SegmentHittingAngle
import LatticeProb.Analysis.RayHittingAngle

/-!
# Unit flows from paths through the cells met by a random segment

Fix a point `z ∈ ℂ`, a length `ρ`, and cells `H y ⊆ ℂ` indexed by a finite set `Y`. For a
direction `θ`, the segment `[z, z + ρ e^{iθ}]` meets the cells indexed by the finite set
`hitFinset Y (fun y => segmentDirections z ρ (H y)) θ`. A rule `F` choosing a path from every
finite set of indices gives the random path `segmentPath z ρ H Y F θ`, and with `θ` uniform on
`(0, 2π]` (`uniformDirection`) its expected net crossing flow `segmentPathFlow z ρ H Y F`. This is
the flow of the method of random paths for the upper bound of an effective resistance by a
straight segment from `z` (Berestycki-Gwynne, upper bound for effective resistances, step 1):

* `sum_segmentPathFlow_eq_ite`, `sum_segmentPathFlow_eq_ite_of_path`: if every realization is a
  path from `x` leaving `A`, the expected flow is a unit flow from `x` out of `A`;
* `abs_segmentPathFlow_le_one`: `|θ(a, b)| ≤ 1` for self-avoiding realizations;
* `abs_segmentPathFlow_le_diam_div_infDist`: if the path only visits cells met by the segment,
  `|θ(a, b)| ≤ diam H_a / dist(z, H_a)`.

The cells must be closed, so that the direction sets are Borel; no measurable selection is needed
since the path is a function of the finite set of cells met.
-/

namespace LatticeProb

open Complex Metric MeasureTheory Set

/-- The uniform distribution of a direction `θ ∈ (0, 2π]`. -/
noncomputable def uniformDirection : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ • volume.restrict (Ioc 0 (2 * Real.pi))

instance isProbabilityMeasure_uniformDirection : IsProbabilityMeasure uniformDirection := by
  constructor
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [uniformDirection, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hπ.le),
    inv_mul_cancel₀ hπ.ne', ENNReal.ofReal_one]

theorem uniformDirection_apply (s : Set ℝ) :
    uniformDirection s = ENNReal.ofReal (2 * Real.pi)⁻¹ * volume (s ∩ Ioc 0 (2 * Real.pi)) := by
  rw [uniformDirection, Measure.smul_apply, Measure.restrict_apply' measurableSet_Ioc, smul_eq_mul]

/-- The directions `θ` in which the segment `[z, z + ρ e^{iθ}]` meets `H`. -/
def segmentDirections (z : ℂ) (ρ : ℝ) (H : Set ℂ) : Set ℝ :=
  {θ : ℝ | ∃ t ∈ Icc (0 : ℝ) ρ, z + t * exp (θ * I) ∈ H}

theorem measurableSet_segmentDirections (z : ℂ) (ρ : ℝ) {H : Set ℂ} (hH : IsClosed H) :
    MeasurableSet (segmentDirections z ρ H) :=
  measurableSet_setOf_exists_segment_mem z ρ hH

/-- **A uniformly random segment from `z` meets a far set with probability at most
`diam H / dist(z, H)`.** -/
theorem uniformDirection_segmentDirections_le (z : ℂ) (ρ : ℝ) {H : Set ℂ}
    (hb : Bornology.IsBounded H) (hpos : 0 < infDist z H) :
    uniformDirection (segmentDirections z ρ H) ≤ ENNReal.ofReal (diam H / infDist z H) := by
  rw [uniformDirection_apply]
  refine le_trans ?_ (uniformDirection_ray_meets_le z hb hpos)
  gcongr
  intro θ hθ
  exact ⟨hθ.2, setOf_exists_segment_mem_subset z ρ H hθ.1⟩

variable {ι : Type*} [DecidableEq ι]

/-- The path chosen by the rule `F` through the cells met by the segment in direction `θ`. -/
noncomputable def segmentPath (z : ℂ) (ρ : ℝ) (H : ι → Set ℂ) (Y : Finset ι)
    (F : Finset ι → List ι) (θ : ℝ) : List ι :=
  F (hitFinset Y (fun y => segmentDirections z ρ (H y)) θ)

/-- The expected net crossing flow of `segmentPath` for a uniformly random direction. -/
noncomputable def segmentPathFlow (z : ℂ) (ρ : ℝ) (H : ι → Set ℂ) (Y : Finset ι)
    (F : Finset ι → List ι) (a b : ι) : ℝ :=
  expectedWalkFlow uniformDirection (segmentPath z ρ H Y F) (Y.powerset.image F) a b

variable {z : ℂ} {ρ : ℝ} {H : ι → Set ℂ} {Y : Finset ι} {F : Finset ι → List ι}

theorem segmentPath_mem_image (θ : ℝ) : segmentPath z ρ H Y F θ ∈ Y.powerset.image F :=
  comp_hitFinset_mem_image Y _ F θ

omit [DecidableEq ι] in
theorem measurableSet_segmentPath_preimage (hH : ∀ y ∈ Y, IsClosed (H y)) (p : List ι) :
    MeasurableSet (segmentPath z ρ H Y F ⁻¹' {p}) :=
  measurableSet_preimage_comp_hitFinset
    (fun y hy => measurableSet_segmentDirections z ρ (hH y hy)) F p

omit [DecidableEq ι] in
/-- A rule choosing paths inside the given set visits only cells met by the segment. -/
theorem mem_segmentDirections_of_mem_segmentPath (hF : ∀ T : Finset ι, ∀ a ∈ F T, a ∈ T)
    {θ : ℝ} {a : ι} (ha : a ∈ segmentPath z ρ H Y F θ) : θ ∈ segmentDirections z ρ (H a) := by
  classical
  have := hF _ a ha
  exact (mem_hitFinset.1 this).2

theorem segmentPathFlow_antisymm (a b : ι) :
    segmentPathFlow z ρ H Y F a b = -segmentPathFlow z ρ H Y F b a :=
  expectedWalkFlow_antisymm _ _ _ a b

/-- The expected flow is carried by the edges used by the realizations. -/
theorem segmentPathFlow_eq_zero_of_not_rel {R' : ι → ι → Prop} (hR' : ∀ u v, R' u v → R' v u)
    (hP : ∀ θ, (segmentPath z ρ H Y F θ).IsChain R') {a b : ι} (hab : ¬ R' a b) :
    segmentPathFlow z ρ H Y F a b = 0 :=
  expectedWalkFlow_eq_zero_of_not_rel hR' _ _ hP hab

/-- **Unit flow.** If every realization has divergence `1{a = x}` on `A`, so has the expected
flow. -/
theorem sum_segmentPathFlow_eq_ite (hH : ∀ y ∈ Y, IsClosed (H y)) {S A : Finset ι} {x : ι}
    (hdiv : ∀ θ, ∀ a ∈ A,
      ∑ b ∈ S, walkFlow (segmentPath z ρ H Y F θ) a b = if a = x then 1 else 0) :
    ∀ a ∈ A, ∑ b ∈ S, segmentPathFlow z ρ H Y F a b = if a = x then 1 else 0 :=
  sum_expectedWalkFlow_eq_ite uniformDirection segmentPath_mem_image
    (fun p _ => measurableSet_segmentPath_preimage hH p) hdiv

/-- **Unit flow from paths.** If in every direction the chosen path starts at `x`, stays in `S`
and ends outside `A`, the expected flow is a unit flow from `x` out of `A`. -/
theorem sum_segmentPathFlow_eq_ite_of_path (hH : ∀ y ∈ Y, IsClosed (H y)) {S A : Finset ι}
    {x : ι} (hpath : ∀ θ, ∃ p, segmentPath z ρ H Y F θ = x :: p ∧ (∀ v ∈ x :: p, v ∈ S) ∧
      (x :: p).getLast (List.cons_ne_nil x p) ∉ A) :
    ∀ a ∈ A, ∑ b ∈ S, segmentPathFlow z ρ H Y F a b = if a = x then 1 else 0 := by
  refine sum_segmentPathFlow_eq_ite hH fun θ => ?_
  obtain ⟨p, hp, hS, hlast⟩ := hpath θ
  rw [hp]
  exact sum_walkFlow_eq_ite_of_getLast_notMem hS hlast

/-- The expected flow of self-avoiding paths is at most `1` on every edge. -/
theorem abs_segmentPathFlow_le_one (hH : ∀ y ∈ Y, IsClosed (H y))
    (hnd : ∀ θ, (segmentPath z ρ H Y F θ).Nodup) (a b : ι) :
    |segmentPathFlow z ρ H Y F a b| ≤ 1 :=
  (abs_expectedWalkFlow_le uniformDirection segmentPath_mem_image
    (fun p _ => measurableSet_segmentPath_preimage hH p) hnd a b).trans measureReal_le_one

/-- **Flow bound by the angle subtended by a cell.** If the self-avoiding paths only visit cells
met by the segment, the expected flow through an edge at `a` is at most
`diam H_a / dist(z, H_a)`. -/
theorem abs_segmentPathFlow_le_diam_div_infDist (hH : ∀ y ∈ Y, IsClosed (H y))
    (hnd : ∀ θ, (segmentPath z ρ H Y F θ).Nodup)
    (hvis : ∀ θ, ∀ a ∈ segmentPath z ρ H Y F θ, θ ∈ segmentDirections z ρ (H a))
    {a : ι} (hb : Bornology.IsBounded (H a)) (hpos : 0 < infDist z (H a)) (b : ι) :
    |segmentPathFlow z ρ H Y F a b| ≤ diam (H a) / infDist z (H a) := by
  refine (abs_expectedWalkFlow_le_of_subset uniformDirection segmentPath_mem_image
    (fun p _ => measurableSet_segmentPath_preimage hH p) hnd (fun θ h => hvis θ a h) b).trans ?_
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg diam_nonneg hpos.le)
    (uniformDirection_segmentDirections_le z ρ hb hpos)

end LatticeProb
