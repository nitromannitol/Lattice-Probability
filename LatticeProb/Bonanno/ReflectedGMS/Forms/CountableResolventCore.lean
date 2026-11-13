/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CountableResolventCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedDomainDensity
import Mathlib.Topology.Algebra.Module.Basic
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# A countable core made from vertex resolvent potentials

Finite rational combinations of the weighted vertex indicators form a dense
countable family in atomic `L²`. Applying the adjoint value inclusion gives
full-form vectors whose decoded functions are the corresponding finite rational
combinations of the actual discount-one vertex occupation potentials.
-/

set_option autoImplicit false

open Set Topology
open scoped BigOperators ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- Countable coordinates for finite rational combinations of vertices. -/
abbrev CountableResolventCoreIndex (V : Type*) := V →₀ ℚ

noncomputable instance countableResolventCoreIndex_countable [Countable V] :
    Countable (CountableResolventCoreIndex V) := inferInstance

/-- The weighted `L²` input represented by a finite rational vertex combination. -/
noncomputable def countableResolventCoreInput [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : ValueSpace V :=
  q.sum fun y a => (a : ℝ) •
    weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)

@[simp] theorem countableResolventCoreInput_zero [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) :
    countableResolventCoreInput G m (0 : CountableResolventCoreIndex V) = 0 := by
  simp [countableResolventCoreInput]

theorem countableResolventCoreInput_add [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (q r : CountableResolventCoreIndex V) :
    countableResolventCoreInput G m (q + r) =
      countableResolventCoreInput G m q + countableResolventCoreInput G m r := by
  classical
  unfold countableResolventCoreInput
  apply Finsupp.sum_add_index
  · intro y _
    simp
  · intro y _ a b
    rw [Rat.cast_add, add_smul]

/-- The rational vertex-combination map as an additive homomorphism. -/
noncomputable def countableResolventCoreInputAddHom [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) :
    CountableResolventCoreIndex V →+ ValueSpace V where
  toFun := countableResolventCoreInput G m
  map_zero' := countableResolventCoreInput_zero G m
  map_add' := countableResolventCoreInput_add G m

@[simp] theorem countableResolventCoreInput_single [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (y : V) (a : ℚ) :
    countableResolventCoreInput G m (Finsupp.single y a) =
      (a : ℝ) • weightedValue m (G.indic y)
        (VertexTest.indic_hasSpeedL2 G m y) := by
  classical
  simp [countableResolventCoreInput]

/-- Finite rational combinations of weighted vertex indicators are dense in
the actual atomic `L²` value space. -/
theorem denseRange_countableResolventCoreInput [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    DenseRange (countableResolventCoreInput G m) := by
  let A : AddSubgroup (ValueSpace V) :=
    AddMonoidHom.range (countableResolventCoreInputAddHom G m)
  have hscalar (y : V) (a : ℝ) :
      a • weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y) ∈
        A.topologicalClosure := by
    have ha : a ∈ closure (Set.range fun r : ℚ => (r : ℝ)) :=
      Rat.denseRange_cast a
    have hmaps : Set.MapsTo
        (fun r : ℝ => r • weightedValue m (G.indic y)
          (VertexTest.indic_hasSpeedL2 G m y))
        (Set.range fun r : ℚ => (r : ℝ)) (A.topologicalClosure : Set (ValueSpace V)) := by
      rintro _ ⟨r, rfl⟩
      apply AddSubgroup.le_topologicalClosure
      exact ⟨Finsupp.single y r, countableResolventCoreInput_single G m y r⟩
    exact Set.MapsTo.closure_left hmaps
      (continuous_id.smul continuous_const)
      (AddSubgroup.isClosed_topologicalClosure A) ha
  have hall_single (u : ValueSpace V) (y : V) :
      lp.single 2 y (u y) ∈ A.topologicalClosure := by
    have hs := hscalar y (u y / Real.sqrt (m y))
    rw [weightedValue_indic_eq_single G m y] at hs
    have hcoeff : u y = (u y / Real.sqrt (m y)) * Real.sqrt (m y) :=
      (div_mul_cancel₀ _ (Real.sqrt_pos.2 (hm y)).ne').symm
    have hsingle_eq : lp.single 2 y (u y) =
        (u y / Real.sqrt (m y)) •
          (lp.single 2 y (Real.sqrt (m y)) : ValueSpace V) := by
      calc
        lp.single 2 y (u y) =
            lp.single 2 y ((u y / Real.sqrt (m y)) * Real.sqrt (m y)) :=
          congrArg (lp.single 2 y) hcoeff
        _ = _ := by
          simpa only [smul_eq_mul] using
            (lp.single_smul (E := fun _ : V => ℝ) (𝕜 := ℝ)
              2 y (u y / Real.sqrt (m y)) (Real.sqrt (m y)))
    rw [hsingle_eq]
    exact hs
  intro u
  change u ∈ closure (A : Set (ValueSpace V))
  rw [← AddSubgroup.topologicalClosure_coe]
  apply (AddSubgroup.isClosed_topologicalClosure A).mem_of_tendsto
    (lp.hasSum_single (by norm_num) u)
  filter_upwards [] with s
  exact A.topologicalClosure.sum_mem fun y _ => hall_single u y

/-- The full-domain vector obtained by applying the checked `1`-resolvent lift. -/
noncomputable def countableResolventCoreVector [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : hilbertDomain G m :=
  oneResolventLift G m (countableResolventCoreInput G m q)

/-- The vertex function decoded from one rational resolvent-core vector. -/
noncomputable def countableResolventCoreFeature [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) : V → ℝ :=
  oneResolventFunction G m (countableResolventCoreInput G m q)

theorem countableResolventCoreFeature_hasFiniteEnergy [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) :
    G.HasFiniteEnergy (countableResolventCoreFeature G m q) :=
  oneResolventFunction_hasFiniteEnergy G m _

theorem countableResolventCoreFeature_hasSpeedL2 [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (q : CountableResolventCoreIndex V) :
    HasSpeedL2 m (countableResolventCoreFeature G m q) :=
  oneResolventFunction_hasSpeedL2 G m hm _

/-- The abstract resolvent-core vector is represented by its decoded full-domain
vertex function. -/
theorem countableResolventCoreVector_eq_inHilbertDomain [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (q : CountableResolventCoreIndex V) :
    countableResolventCoreVector G m q =
      inHilbertDomain G m hm (countableResolventCoreFeature G m q)
        (countableResolventCoreFeature_hasSpeedL2 G m hm q)
        (countableResolventCoreFeature_hasFiniteEnergy G m q) := by
  apply valueInclusion_injective G m
  rw [valueInclusion_inHilbertDomain]
  exact (weightedValue_unweight m hm (oneResolvent G m
    (countableResolventCoreInput G m q))).symm

/-- The rational vertex resolvent vectors are dense in the entire full form
domain, with no finite-support closure replacing that domain. -/
theorem denseRange_countableResolventCoreVector [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    DenseRange (countableResolventCoreVector G m) := by
  change DenseRange ((oneResolventLift G m) ∘ countableResolventCoreInput G m)
  exact (denseRange_oneResolventLift G m).comp
    (denseRange_countableResolventCoreInput G m hm)
    (oneResolventLift G m).continuous

private theorem parameterizedResolvent_one
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) :
    parameterizedResolvent G m 1 = oneResolvent G m := by
  have hden : resolventDenominator G m 1 =
      (1 : ValueSpace V →L[ℝ] ValueSpace V) := by
    apply ContinuousLinearMap.ext
    intro f
    simp [resolventDenominator]
  rw [parameterizedResolvent, hden, Ring.inverse_one, mul_one]

theorem oneResolventFunction_weightedIndic_eq_vertexOccupationPotential
    [DecidableEq V] (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (x y : V) :
    oneResolventFunction G m
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x =
      vertexOccupationPotential G m 1 x y := by
  rw [vertexOccupationPotential_eq_resolvent G m (by norm_num : (0 : ℝ) < 1)]
  simp only [one_div, inv_one, one_mul]
  rw [parameterizedResolvent_one]
  rfl

/-- Each coordinate is exactly a finite rational combination of the already
constructed discount-one vertex occupation potentials. -/
theorem countableResolventCoreFeature_eq_sum [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (q : CountableResolventCoreIndex V) (x : V) :
    countableResolventCoreFeature G m q x =
      q.sum fun y a => (a : ℝ) * vertexOccupationPotential G m 1 x y := by
  classical
  unfold countableResolventCoreFeature countableResolventCoreInput oneResolventFunction
  change unweight m (oneResolvent G m
      (∑ y ∈ q.support, ((q y : ℚ) : ℝ) •
        weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))) x =
    ∑ y ∈ q.support, ((q y : ℚ) : ℝ) * vertexOccupationPotential G m 1 x y
  rw [map_sum]
  simp only [map_smul, unweight, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  rw [mul_div_assoc]
  congr 1
  exact oneResolventFunction_weightedIndic_eq_vertexOccupationPotential G m x y

/-- A concrete uniform bound for one finite rational potential combination. -/
noncomputable def countableResolventCoreBound
    (q : CountableResolventCoreIndex V) : ℝ :=
  q.sum fun _ a => |(a : ℝ)|

theorem countableResolventCoreFeature_abs_le [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (q : CountableResolventCoreIndex V) (x : V) :
    |countableResolventCoreFeature G m q x| ≤ countableResolventCoreBound q := by
  rw [countableResolventCoreFeature_eq_sum]
  unfold countableResolventCoreBound
  calc
    |q.sum fun y a => (a : ℝ) * vertexOccupationPotential G m 1 x y| ≤
        q.sum fun y a => |(a : ℝ) * vertexOccupationPotential G m 1 x y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ q.sum fun _ a => |(a : ℝ)| := by
      apply Finset.sum_le_sum
      intro y hy
      change |((q y : ℚ) : ℝ) * vertexOccupationPotential G m 1 x y| ≤
        |((q y : ℚ) : ℝ)|
      rw [abs_mul]
      have hU0 := vertexOccupationPotential_nonneg G m hm
        (by norm_num : (0 : ℝ) < 1) x y
      have hU1 := vertexOccupationPotential_le_inv G m hm
        (by norm_num : (0 : ℝ) < 1) x y
      rw [abs_of_nonneg hU0]
      simp only [one_div, inv_one] at hU1
      exact mul_le_of_le_one_right (abs_nonneg _) hU1

end ReflectedGMS.FullNetworkForm
