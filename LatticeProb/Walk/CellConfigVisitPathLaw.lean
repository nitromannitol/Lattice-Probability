import LatticeProb.Walk.CellConfigVisitRange
import LatticeProb.Walk.LineConnectedCellWalkRange
import LatticeProb.Walk.ConstantStepContinuous
import LatticeProb.Prob.ContinuousMapUnboundedRange
import LatticeProb.Topology.ContinuousMapBorel

/-! # Continuous path laws for cell walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Constant-step interpolation is continuous, including at its knots. -/
theorem continuous_plane_path (m : ℝ) (p : ℕ → Plane) : Continuous (path m p) := by
  by_cases hm : 0 < m
  · let a : ℝ≥0 := ⟨m, hm.le⟩
    have ha : 0 < a := hm
    let τ := knot a
    have hmono : StrictMono τ := knot_strictMono ha
    have hzero : τ 0 = 0 := knot_zero a
    have hunb : ∀ b, ∃ n, b < τ n := knot_unbounded ha
    have hloc : LocallyFinite (fun n : ℕ => Icc (τ n) (τ (n + 1))) := by
      intro t
      obtain ⟨N, hN⟩ := hunb t
      refine ⟨Iio (τ N), Iio_mem_nhds hN, (finite_lt_nat N).subset ?_⟩
      intro n hn
      obtain ⟨x, hx, hx'⟩ := hn
      change n < N
      by_contra h
      have hle := hmono.monotone (Nat.le_of_not_gt h)
      exact (not_lt_of_ge (hle.trans hx.1)) hx'
    have hcover : (⋃ n : ℕ, Icc (τ n) (τ (n + 1))) = univ := by
      apply eq_univ_of_forall
      intro t
      obtain ⟨n, hn, hn'⟩ := LatticeProb.KnotReparam.exists_knot_bracket hzero hunb t
      exact mem_iUnion.mpr ⟨n, hn, hn'.le⟩
    apply hloc.continuous hcover (fun _ => isClosed_Icc)
    intro n
    let f : ℝ≥0 → Plane := fun t => AffineMap.lineMap (p n) (p (n + 1))
      (((t : ℝ) - τ n) / ((τ (n + 1) : ℝ) - τ n))
    have hf : Continuous f := by
      dsimp [f, AffineMap.lineMap_apply_module']
      fun_prop
    apply hf.continuousOn.congr
    intro t ht
    change path (a : ℝ) p t = f t
    rcases ht.2.lt_or_eq with ht' | ht'
    · exact path_eq_lineMap ha p n t ht.1 ht'
    · subst t
      change path (a : ℝ) p (knot a (n + 1)) = f (τ (n + 1))
      rw [path_knot ha p (n + 1)]
      dsimp [f]
      have hne : ((τ (n + 1) : ℝ) - τ n) ≠ 0 := by
        have h := NNReal.coe_lt_coe.mpr (hmono (Nat.lt_succ_self n))
        linarith
      simp [hne]
  · have hm' : m ≤ 0 := le_of_not_gt hm
    have heq : path m p = fun t : ℝ≥0 => AffineMap.lineMap (p 0) (p 1) (m * (t : ℝ)) := by
      funext t
      change AffineMap.lineMap (p ⌊m * (t : ℝ)⌋₊) (p (⌊m * (t : ℝ)⌋₊ + 1))
        (m * (t : ℝ) - (⌊m * (t : ℝ)⌋₊ : ℝ)) = _
      have hfloor : ⌊m * (t : ℝ)⌋₊ = 0 :=
        Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hm' t.2)
      rw [hfloor]
      simp only [Nat.cast_zero, sub_zero, zero_add]
    rw [heq]
    simp only [AffineMap.lineMap_apply_module']
    fun_prop

/-- Interpolation is jointly measurable in the anchors, speed, and time. -/
theorem measurable_plane_path :
    Measurable (fun q : (ℕ → Plane) × ℝ × ℝ≥0 => path q.2.1 q.1 q.2.2) := by
  let S := (ℕ → Plane) × ℝ × ℝ≥0
  have hs : Measurable (fun q : S => q.2.1 * (q.2.2 : ℝ)) :=
    (measurable_fst.comp measurable_snd).mul
      (NNReal.continuous_coe.measurable.comp (measurable_snd.comp measurable_snd))
  have hn : Measurable (fun q : S => ⌊q.2.1 * (q.2.2 : ℝ)⌋₊) := hs.nat_floor
  have heval : Measurable (fun z : (ℕ → Plane) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  have hp : Measurable (fun q : S => q.1 ⌊q.2.1 * (q.2.2 : ℝ)⌋₊) :=
    heval.comp (measurable_fst.prodMk hn)
  have hp' : Measurable (fun q : S => q.1 (⌊q.2.1 * (q.2.2 : ℝ)⌋₊ + 1)) :=
    heval.comp (measurable_fst.prodMk (hn.add measurable_const))
  have hcast : Measurable (fun q : S => (⌊q.2.1 * (q.2.2 : ℝ)⌋₊ : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn
  have ha := hs.sub hcast
  unfold path
  simp only [AffineMap.lineMap_apply_module']
  exact (ha.smul (hp'.sub hp)).add hp

/-- Constant-step interpolation of points in the plane as a continuous path. -/
def continuousPlanePath (m : ℝ) (p : ℕ → Plane) : C(ℝ≥0, Plane) :=
  ⟨path m p, continuous_plane_path m p⟩

end LatticeProb.ConstantStepInterpolation

namespace LatticeProb.CellConfigWalk

/-- Measurable sequences of points give measurable constant-step continuous paths. -/
theorem measurable_constantStepPath {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → ℕ → Plane) (hp : Measurable p) (m : ℝ) :
    Measurable (fun ω => ConstantStepInterpolation.continuousPlanePath m (p ω)) := by
  apply ContinuousMapBorel.ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun ω => ConstantStepInterpolation.path m (p ω) t)
  let n : ℕ := ⌊m * (t : ℝ)⌋₊
  have hn : Measurable (fun ω => p ω n) := (measurable_pi_apply n).comp hp
  have hn1 : Measurable (fun ω => p ω (n + 1)) :=
    (measurable_pi_apply (n + 1)).comp hp
  change Measurable (fun ω => AffineMap.lineMap (p ω n) (p ω (n + 1))
    (m * (t : ℝ) - n))
  simp only [AffineMap.lineMap_apply_module']
  exact ((measurable_const : Measurable (fun _ : Ω => m * (t : ℝ) - (n : ℝ))).smul
    (hn1.sub hn)).add hn

/-- Every positive-speed interpolation through measurable points of visited cells has
an unbounded path law, including when the point chosen depends on the visit. -/
theorem ae_unbounded_range_map_constantStepPath
    (H : CellConfig) (hH : H.IsCellConfiguration) (hL : H.LineConnected)
    {K : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K Q)
    (p : (ℕ → H.cells) → ℕ → Plane) (hp : Measurable p)
    (hmem : ∀ᵐ ω ∂Q, ∀ n, p ω n ∈ ((ω n).1 : Set Plane))
    {m : ℝ≥0} (hm : 0 < m) :
    ∀ᵐ (f : C(ℝ≥0, Plane)) ∂(Q.map (fun ω => ConstantStepInterpolation.continuousPlanePath m (p ω))),
      ¬ Bornology.IsBounded (Set.range f) := by
  apply (ae_map_iff (measurable_constantStepPath p hp m).aemeasurable
    (LatticeProb.measurableSet_continuousMap_unbounded_range (0 : Plane))).2
  filter_upwards [ae_infinite_range_of_lineConnected H hH hL hQ, hmem] with ω hω hpω
  exact unbounded_range_constantStep_of_infinite_range_cells H hH ω (p ω) hpω hω hm

/-- The interpolated path law of a simple random walk is a probability measure. -/
theorem constantStepPath_map_isProbability
    (H : CellConfig) {K : H.cells} {Q : Measure (ℕ → H.cells)}
    (hQ : H.IsSRWLaw K Q) (p : (ℕ → H.cells) → ℕ → Plane)
    (hp : Measurable p) (m : ℝ) :
    IsProbabilityMeasure (Q.map (fun ω => ConstantStepInterpolation.continuousPlanePath m (p ω))) := by
  let : IsProbabilityMeasure Q := hQ.1
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_constantStepPath p hp m).aemeasurable).2 inferInstance

end LatticeProb.CellConfigWalk
end
