/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CountableResolventCore
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactVertexDynkin

/-!
# Dynkin martingales on the countable resolvent core

The discount-one vertex Dynkin martingales extend to every finite rational
combination in the existing countable full-form core by finite linearity.  The
resulting raw process is represented by the decoded core potential minus the
canonical occupation of its finite-sum drift.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The raw Dynkin martingale attached to a countable-resolvent-core
coordinate, formed without repeating the semigroup argument. -/
noncomputable def rawResolventCoreMartingale
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : ℝ≥0 → PF.Ω → ℝ :=
  q.sum fun y a ↦ (a : ℝ) • vertexDynkinMartingale PF G m 1 y

/-- The state-space drift of a countable-resolvent-core coordinate. -/
noncomputable def resolventCoreDrift
    (G : ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : Option V → ℝ :=
  fun p ↦ p.elim 0 fun x ↦ countableResolventCoreFeature G m q x - (q x : ℝ)

/-- The raw core potential, extended by zero at the cemetery state. -/
noncomputable def rawResolventCorePotential
    (G : ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : Option V → ℝ :=
  fun p ↦ p.elim 0 (countableResolventCoreFeature G m q)

theorem resolventCoreDrift_eq_sum
    (G : ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) (p : Option V) :
    resolventCoreDrift G m q p =
      q.sum fun y a ↦ (a : ℝ) * vertexDynkinIntegrand G m 1 y p := by
  classical
  cases p with
  | none => simp [resolventCoreDrift, vertexDynkinIntegrand]
  | some x =>
      rw [resolventCoreDrift, Option.elim_some,
        countableResolventCoreFeature_eq_sum]
      simp only [vertexDynkinIntegrand, Option.elim_some, one_mul]
      unfold Finsupp.sum
      simp only [mul_sub]
      change (∑ y ∈ q.support,
          (q y : ℝ) * vertexOccupationPotential G m 1 x y) - (q x : ℝ) =
        ∑ y ∈ q.support,
          ((q y : ℝ) * vertexOccupationPotential G m 1 x y -
            (q y : ℝ) * G.indic y x)
      rw [Finset.sum_sub_distrib]
      congr 1
      simp [ConductanceGraph.indic]

theorem integrable_dyadic_state_on_Icc
    (PF : ProcessFamily V) (f : Option V → ℝ) (t : ℝ≥0)
    {C : ℝ} (hf : ∀ p, ‖f p‖ ≤ C) (omega : PF.Ω) :
    Integrable (fun r : ℝ ↦ f (dyadicLimit PF.X (Real.toNNReal r) omega))
      (volume.restrict (Icc 0 (t : ℝ))) := by
  apply Integrable.of_bound
    (((measurable_of_countable f).comp
      (measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) omega)).aestronglyMeasurable.restrict)
    C
  filter_upwards [] with r
  exact hf _

theorem boundedStateOccupationVersion_resolventCoreDrift
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) (omega : PF.Ω) :
    boundedStateOccupationVersion PF (resolventCoreDrift G m q) t omega =
      q.sum fun y a ↦ (a : ℝ) *
        boundedStateOccupationVersion PF (vertexDynkinIntegrand G m 1 y) t omega := by
  classical
  rw [boundedStateOccupationVersion_eq_dyadicIntegral]
  simp_rw [resolventCoreDrift_eq_sum]
  change (∫ r : ℝ in Icc 0 (t : ℝ),
      ∑ y ∈ q.support, (q y : ℝ) *
        vertexDynkinIntegrand G m 1 y (dyadicLimit PF.X (Real.toNNReal r) omega)) =
    ∑ y ∈ q.support, (q y : ℝ) *
      boundedStateOccupationVersion PF (vertexDynkinIntegrand G m 1 y) t omega
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [boundedStateOccupationVersion_eq_dyadicIntegral, integral_const_mul]
  · intro y hy
    apply (integrable_dyadic_state_on_Icc PF
      (vertexDynkinIntegrand G m 1 y) t
      (vertexDynkinIntegrand_bound G m hm (by norm_num : (0 : ℝ) < 1) y) omega).const_mul

/-- Every finite rational countable-core combination is a martingale, by
linearity of the already proved vertex Dynkin martingales. -/
theorem rawResolventCoreMartingale_isMartingale
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V) (z : V) :
    Martingale (rawResolventCoreMartingale PF G m q)
      PF.naturalFiltration (PF.P z) := by
  classical
  unfold rawResolventCoreMartingale Finsupp.sum
  induction q.support using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact martingale_zero ℝ PF.naturalFiltration (PF.P z)
  | @insert y s hy ih =>
      rw [Finset.sum_insert hy]
      exact ((vertexDynkinMartingale_isMartingale h hG hm hmsum
        (by norm_num : (0 : ℝ) < 1) y z).smul (q y : ℝ)).add ih

/-- Exact all-sample, all-time representation of the finite core combination
by its raw potential and the canonical occupation of its drift. -/
theorem rawResolventCoreMartingale_eq_potential_sub_occupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) (omega : PF.Ω) :
    rawResolventCoreMartingale PF G m q t omega =
      rawResolventCorePotential G m q (PF.X t omega) -
        boundedStateOccupationVersion PF (resolventCoreDrift G m q) t omega := by
  classical
  rw [boundedStateOccupationVersion_resolventCoreDrift PF G m hm q t omega]
  unfold rawResolventCoreMartingale vertexDynkinMartingale Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ y ∈ q.support, (q y : ℝ) *
      ((PF.X t omega).elim 0 (vertexOccupationPotential G m 1 · y) -
        boundedStateOccupationVersion PF (vertexDynkinIntegrand G m 1 y) t omega)) =
    rawResolventCorePotential G m q (PF.X t omega) -
      ∑ y ∈ q.support, (q y : ℝ) *
        boundedStateOccupationVersion PF (vertexDynkinIntegrand G m 1 y) t omega
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  cases hx : PF.X t omega with
  | none => simp [rawResolventCorePotential, hx]
  | some x =>
      simp only [rawResolventCorePotential, hx, Option.elim_some]
      exact (countableResolventCoreFeature_eq_sum G m q x).symm

/-- The compact realization of a finite countable-core Dynkin combination. -/
noncomputable def compactResolventCoreMartingale
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V) :
    ℝ≥0 → PF.Ω → ℝ :=
  q.sum fun y a ↦ (a : ℝ) •
    compactVertexDynkinMartingale G m hm PF default y

/-- The compact finite combination is a martingale in the right-continuous
natural filtration. -/
theorem compactResolventCoreMartingale_isMartingale
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default : V) (q : CountableResolventCoreIndex V)
    (z : V) :
    Martingale (compactResolventCoreMartingale G m hm PF default q)
      PF.naturalFiltration.rightCont (PF.P z) := by
  classical
  unfold compactResolventCoreMartingale Finsupp.sum
  induction q.support using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact martingale_zero ℝ PF.naturalFiltration.rightCont (PF.P z)
  | @insert y s hy ih =>
      rw [Finset.sum_insert hy]
      exact ((compactVertexDynkinMartingale_isMartingale
        h hG hm hmsum default y z).smul (q y : ℝ)).add ih

/-- At each fixed time, the compact finite combination is a modification of
the raw countable-core martingale. -/
theorem compactResolventCoreMartingale_ae_eq
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default : V) (q : CountableResolventCoreIndex V)
    (z : V) (t : ℝ≥0) :
    compactResolventCoreMartingale G m hm PF default q t =ᵐ[PF.P z]
      rawResolventCoreMartingale PF G m q t := by
  classical
  filter_upwards [ae_all_iff.2 fun y : V ↦
    compactVertexDynkinMartingale_ae_eq h hG hm hmsum default y z t] with omega homega
  unfold compactResolventCoreMartingale rawResolventCoreMartingale Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [homega y]

/-- The compact finite combination has càdlàg paths almost surely. -/
theorem compactResolventCoreMartingale_ae_isCadlag
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default : V) (q : CountableResolventCoreIndex V)
    (z : V) :
    ∀ᵐ omega ∂PF.P z,
      IsCadlag (fun t ↦ compactResolventCoreMartingale G m hm PF default q t omega) := by
  classical
  filter_upwards [ae_all_iff.2 fun y : V ↦
    compactVertexDynkinMartingale_ae_isCadlag h hG hm hmsum default y z] with omega homega
  unfold compactResolventCoreMartingale Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  induction q.support using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (IsCadlag.const (c := (0 : ℝ)))
  | @insert y s hy ih =>
      have hadd := ((homega y).const_smul (q y : ℝ)).add ih
      convert hadd using 1
      funext t
      rw [Finset.sum_insert hy]
      rfl

end ReflectedGMS
