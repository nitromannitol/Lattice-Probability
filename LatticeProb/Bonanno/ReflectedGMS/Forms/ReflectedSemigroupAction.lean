/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ReflectedSemigroupAction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIdentification
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Full `L²(m)` action of the actual reflected transition law

The full-form semigroup acts pointwise by integration against its probability
kernel on every weighted `L²(m)` vector.  The required `L¹` summability follows
directly from coordinatewise summability of the `L²` inner product, detailed
balance, and self-adjointness.  The checked equality of the actual one-time law
with the semigroup probability kernel then transfers both integrability and the
integral identity to the reflected path process.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace NNReal ENNReal

open MeasureTheory

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

namespace FullNetworkForm

private theorem semigroup_indic_apply_eq_sqrt_mul_kernel
    (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    fullFormSemigroup G m t
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x =
      Real.sqrt (m x) * semigroupKernel G m t x y := by
  simp only [semigroupKernel, unweight]
  have hs : Real.sqrt (m x) ≠ 0 := (Real.sqrt_pos.2 (hm x)).ne'
  field_simp [hs]

private theorem inner_indic_eq_mass_mul_unweight [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (u : ValueSpace V) (x : V) :
    ⟪u, weightedValue m (G.indic x)
      (VertexTest.indic_hasSpeedL2 G m x)⟫_ℝ = m x * unweight m u x := by
  rw [weightedValue_indic_eq_single G m x, lp.inner_single_right]
  simp only [Real.inner_apply, unweight]
  have hs : Real.sqrt (m x) ≠ 0 := (Real.sqrt_pos.2 (hm x)).ne'
  field_simp [hs]
  rw [Real.sq_sqrt (hm x).le]

/-- A full weighted `L²(m)` vector is absolutely summable against every row
of the semigroup kernel. -/
theorem summable_semigroupKernel_mul_unweight [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (t : ℝ≥0) (x : V) (f : ValueSpace V) :
    Summable (fun z ↦ semigroupKernel G m t x z * unweight m f z) := by
  let dx := weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)
  let ux := fullFormSemigroup G m t dx
  have hinner : Summable (fun z ↦ ⟪f z, ux z⟫_ℝ) := lp.summable_inner f ux
  have hscaled : Summable (fun z ↦ m x *
      (semigroupKernel G m t x z * unweight m f z)) := by
    refine hinner.congr (fun z ↦ ?_)
    simp only [ux, dx, Real.inner_apply, unweight]
    rw [semigroup_indic_apply_eq_sqrt_mul_kernel G m hm t z x]
    have hbalance := semigroupKernel_detailedBalance G m hm t x z
    have hs : Real.sqrt (m z) ≠ 0 := (Real.sqrt_pos.2 (hm z)).ne'
    calc
      f z * (Real.sqrt (m z) * semigroupKernel G m t z x) =
          (f z / Real.sqrt (m z)) *
            (m z * semigroupKernel G m t z x) := by
              field_simp [hs]
              rw [Real.sq_sqrt (hm z).le]
              ring
      _ = (f z / Real.sqrt (m z)) *
            (m x * semigroupKernel G m t x z) := by rw [hbalance]
      _ = m x * (semigroupKernel G m t x z *
            (f z / Real.sqrt (m z))) := by ring
  exact (summable_mul_left_iff (hm x).ne').mp hscaled

/-- Pointwise kernel action equals the decoded full-form semigroup action on
the entire weighted `L²(m)` space. -/
theorem tsum_semigroupKernel_mul_unweight_eq [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (t : ℝ≥0) (x : V) (f : ValueSpace V) :
    ∑' z, semigroupKernel G m t x z * unweight m f z =
      unweight m (fullFormSemigroup G m t f) x := by
  let dx := weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)
  let ux := fullFormSemigroup G m t dx
  have hsummable := summable_semigroupKernel_mul_unweight G m hm t x f
  have hseries : ⟪f, ux⟫_ℝ = m x *
      ∑' z, semigroupKernel G m t x z * unweight m f z := by
    rw [lp.inner_eq_tsum, ← hsummable.tsum_mul_left (m x)]
    apply tsum_congr
    intro z
    simp only [ux, dx, Real.inner_apply, unweight]
    rw [semigroup_indic_apply_eq_sqrt_mul_kernel G m hm t z x]
    have hbalance := semigroupKernel_detailedBalance G m hm t x z
    have hs : Real.sqrt (m z) ≠ 0 := (Real.sqrt_pos.2 (hm z)).ne'
    calc
      f z * (Real.sqrt (m z) * semigroupKernel G m t z x) =
          (f z / Real.sqrt (m z)) *
            (m z * semigroupKernel G m t z x) := by
              field_simp [hs]
              rw [Real.sq_sqrt (hm z).le]
              ring
      _ = (f z / Real.sqrt (m z)) *
            (m x * semigroupKernel G m t x z) := by rw [hbalance]
      _ = m x * (semigroupKernel G m t x z *
            (f z / Real.sqrt (m z))) := by ring
  have hsemigroup : ⟪f, ux⟫_ℝ =
      m x * unweight m (fullFormSemigroup G m t f) x := by
    calc
      ⟪f, ux⟫_ℝ = ⟪fullFormSemigroup G m t f, dx⟫_ℝ :=
        (fullFormSemigroup_isSelfAdjoint G m t).isSymmetric f dx |>.symm
      _ = m x * unweight m (fullFormSemigroup G m t f) x :=
        inner_indic_eq_mass_mul_unweight G m hm _ x
  exact (mul_left_cancel₀ (hm x).ne' (hseries.symm.trans hsemigroup))

/-- Every full weighted `L²(m)` vector is integrable against a semigroup
probability-kernel row. -/
theorem integrable_unweight_semigroupProbabilityKernel [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x : V) (f : ValueSpace V) :
    Integrable (unweight m f) (semigroupProbabilityKernel G m hm hmsum t x) := by
  let μ := semigroupProbabilityKernel G m hm hmsum t x
  have hnorm : Summable (fun z ↦
      semigroupKernel G m t x z * ‖unweight m f z‖) := by
    refine (summable_semigroupKernel_mul_unweight G m hm t x f).norm.congr
      (fun z ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (semigroupKernel_nonneg G m hm t x z)]
  change Integrable (unweight m f) μ
  rw [show μ = Measure.sum (fun z ↦ μ {z} • Measure.dirac z) by
    exact (Measure.sum_smul_dirac μ).symm]
  apply integrable_sum_dirac (fun z ↦ measure_ne_top _ _)
  simpa only [μ, semigroupProbabilityKernel_apply_singleton,
    ENNReal.toReal_ofReal (semigroupKernel_nonneg G m hm t x _)] using hnorm

/-- Integration against a semigroup probability-kernel row is the decoded
full-form semigroup action. -/
theorem integral_unweight_semigroupProbabilityKernel [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x : V) (f : ValueSpace V) :
    (∫ z, unweight m f z ∂semigroupProbabilityKernel G m hm hmsum t x) =
      unweight m (fullFormSemigroup G m t f) x := by
  rw [integral_countable
    (integrable_unweight_semigroupProbabilityKernel G m hm hmsum t x f)]
  simpa only [measureReal_def, semigroupProbabilityKernel_apply_singleton,
    ENNReal.toReal_ofReal (semigroupKernel_nonneg G m hm t x _), smul_eq_mul]
    using tsum_semigroupKernel_mul_unweight_eq G m hm t x f

end FullNetworkForm

/-- The decoded value of every full weighted `L²(m)` vector is integrable
along the actual reflected walk at every nonnegative time. -/
theorem integrable_reflected_unweight_at_time [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x : V) (f : ValueSpace V) :
    Integrable (fun ω ↦ (PF.X t ω).elim 0 (unweight m f)) (PF.P x) := by
  let g : Option V → ℝ := fun z ↦ z.elim 0 (unweight m f)
  have hg : Measurable g := measurable_of_countable _
  have hsome : Measurable (some : V → Option V) := measurable_of_countable _
  have hk : Integrable g
      ((semigroupProbabilityKernel G m hm hmsum t x).map (some : V → Option V)) :=
    (integrable_map_measure hg.aestronglyMeasurable hsome.aemeasurable).2 (by
      change Integrable (unweight m f)
        (semigroupProbabilityKernel G m hm hmsum t x)
      exact integrable_unweight_semigroupProbabilityKernel G m hm hmsum t x f)
  have hmap : Integrable g ((PF.P x).map (PF.X t)) := by
    rw [reflected_transitionLaw_eq_semigroupProbabilityKernel h hG hm hmsum t x]
    exact hk
  exact (integrable_map_measure hg.aestronglyMeasurable
    (PF.measurable_X t).aemeasurable).1 hmap

/-- The actual reflected one-time expectation realizes the full weighted
`L²(m)` semigroup action, with no boundedness restriction on the vector. -/
theorem integral_reflected_unweight_at_time [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x : V) (f : ValueSpace V) :
    (∫ ω, (PF.X t ω).elim 0 (unweight m f) ∂PF.P x) =
      unweight m (fullFormSemigroup G m t f) x := by
  let g : Option V → ℝ := fun z ↦ z.elim 0 (unweight m f)
  have hg : Measurable g := measurable_of_countable _
  have hsome : Measurable (some : V → Option V) := measurable_of_countable _
  calc
    (∫ ω, (PF.X t ω).elim 0 (unweight m f) ∂PF.P x) =
        ∫ z, g z ∂(PF.P x).map (PF.X t) := by
          simpa only [g, Function.comp_apply] using
            (integral_map (PF.measurable_X t).aemeasurable
              hg.aestronglyMeasurable).symm
    _ = ∫ z, g z ∂(semigroupProbabilityKernel G m hm hmsum t x).map
          (some : V → Option V) := by
        exact congrArg (fun μ : Measure (Option V) ↦ ∫ z, g z ∂μ)
          (reflected_transitionLaw_eq_semigroupProbabilityKernel
            h hG hm hmsum t x)
    _ = ∫ z, unweight m f z ∂semigroupProbabilityKernel G m hm hmsum t x := by
      simpa only [g, Function.comp_apply, Option.elim_some] using
        integral_map hsome.aemeasurable hg.aestronglyMeasurable
    _ = unweight m (fullFormSemigroup G m t f) x :=
      integral_unweight_semigroupProbabilityKernel G m hm hmsum t x f

end ReflectedGMS
