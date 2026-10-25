module

/-
# Finite generic directions in a radial cone

Perturb a unit vector by a small multiple of its quarter turn. Each forbidden
nonzero vector excludes at most one perturbation parameter. A finite exclusion
therefore leaves a parameter in every open interval. Positive normalization
preserves the strict inward and outward forward inequalities.
-/
public import LatticeProb.Topology.DiskEndpointGeometry
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section



open Set Metric
namespace LatticeProb.Topology.PolygonalParity

/-- The forward coordinate varies continuously with the direction. -/
theorem continuous_fwd_left (z : Plane) : Continuous (fun u => fwd u z) :=
  continuous_const.inner continuous_id

/-- The forward coordinate varies continuously with the point. -/
theorem continuous_fwd_right (u : Plane) : Continuous (fwd u) :=
  continuous_id.inner continuous_const

/-- The transverse coordinate varies continuously with the point. -/
theorem continuous_hgt_right (u : Plane) : Continuous (hgt u) := by
  change Continuous (fun z : Plane => u 0 * z 1 - u 1 * z 0)
  fun_prop

/-- Every open neighborhood of a unit vector contains a nonzero vector
parallel to none of a prescribed finite collection of nonzero vectors. -/
theorem exists_generic_vector_in_open {a : Plane} (ha : Plane.IsDirection a)
    {S : Set Plane} (hS : S.Finite) {U : Set Plane} (hU : IsOpen U) (haU : a ∈ U) :
    ∃ d ∈ U, d ≠ 0 ∧ ∀ v ∈ S, v ≠ 0 → Plane.det d v ≠ 0 := by
  let d : ℝ → Plane := fun t => a + t • Plane.perp a
  have hd : Continuous d := continuous_const.add (continuous_id.smul continuous_const)
  have h0U : (0 : ℝ) ∈ d ⁻¹' U := by
    change a + (0 : ℝ) • Plane.perp a ∈ U
    rw [zero_smul, add_zero]
    exact haU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hd) 0 h0U
  have hbad : {t : ℝ | ∃ v ∈ S, v ≠ 0 ∧ Plane.det (d t) v = 0}.Finite := by
    refine (hS.image (fun v => -Plane.det a v / Plane.det (Plane.perp a) v)).subset ?_
    rintro t ⟨v, hv, hv0, hdet⟩
    have hid : Plane.det a v + t * Plane.det (Plane.perp a) v = 0 := by
      simpa only [d, Plane.det_add_left, Plane.det_smul_left] using hdet
    have hden : Plane.det (Plane.perp a) v ≠ 0 := by
      intro hz
      have hgt : hgt a v = 0 := by
        change Plane.det a v = 0
        simpa only [hz, mul_zero, add_zero] using hid
      have hfw : fwd a v = 0 := by
        rw [Plane.det_perp_left, neg_eq_zero] at hz
        exact (real_inner_comm a v).trans hz
      exact hv0 (by rw [decomp ha v, hfw, hgt, zero_smul, zero_smul, add_zero])
    refine ⟨v, hv, ?_⟩
    symm
    apply (eq_div_iff hden).mpr
    linarith only [hid]
  obtain ⟨t, ht, htbad⟩ := (Ioo_infinite (neg_lt_self hε)).exists_notMem_finite hbad
  have htball : t ∈ ball (0 : ℝ) ε := by
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
    exact ht
  refine ⟨d t, hball htball, ?_, fun v hv hv0 hdet => htbad ⟨v, hv, hv0, hdet⟩⟩
  intro hz
  have hfw : fwd a (d t) = 1 := by
    change fwd a (a + t • Plane.perp a) = 1
    rw [fwd_add_smul, fwd_perp, mul_zero, add_zero, fwd_self ha]
  rw [hz] at hfw
  have hzero : fwd a (0 : Plane) = 0 := by rw [fwd, inner_zero_left]
  exact zero_ne_one (hzero.symm.trans hfw)

/-- **A generic ray in a radial cone.** Strict inward and outward pairings
at a unit endpoint produce a unit ray direction with the same strict forward
inequalities, avoiding every prescribed finite nonzero direction. The ray
still points outward at the endpoint itself. -/
theorem exists_generic_direction_radial {a b c : Plane}
    (ha : Plane.IsDirection a) (hb : fwd a b < fwd a a)
    (hc : fwd a a < fwd a c) {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, Plane.IsDirection u ∧ fwd u b < fwd u a ∧
      fwd u a < fwd u c ∧ 0 < fwd u a ∧
      ∀ v ∈ S, v ≠ 0 → Plane.det u v ≠ 0 := by
  let U := {d : Plane | fwd d b < fwd d a ∧ fwd d a < fwd d c ∧ 0 < fwd d a}
  have hU : IsOpen U :=
    (isOpen_lt (continuous_fwd_left b) (continuous_fwd_left a)).inter
      ((isOpen_lt (continuous_fwd_left a) (continuous_fwd_left c)).inter
        (isOpen_lt continuous_const (continuous_fwd_left a)))
  have haU : a ∈ U := ⟨hb, hc, by rw [fwd_self ha]; exact zero_lt_one⟩
  obtain ⟨d, hdU, hd0, hdet⟩ := exists_generic_vector_in_open ha hS hU haU
  obtain ⟨r, hr, hdir⟩ := Plane.dir_eq_smul hd0
  have hscale : ∀ z : Plane, fwd (Plane.dir d) z = r * fwd d z := by
    intro z
    rw [hdir, fwd, real_inner_smul_right, fwd]
  refine ⟨Plane.dir d, Plane.isDirection_dir hd0, ?_, ?_, ?_, ?_⟩
  · rw [hscale b, hscale a]
    exact mul_lt_mul_of_pos_left hdU.1 hr
  · rw [hscale a, hscale c]
    exact mul_lt_mul_of_pos_left hdU.2.1 hr
  · rw [hscale a]
    exact mul_pos hr hdU.2.2
  · intro v hv hv0
    rw [hdir, Plane.det_smul_left]
    exact mul_ne_zero hr.ne' (hdet v hv hv0)

end LatticeProb.Topology.PolygonalParity
