/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreLinearity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreSquareAlgebra
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinEnergy

/-!
# Linearity and square integrability on the countable resolvent core

The feature and its raw and compact Dynkin martingales preserve addition and
subtraction of finite rational core coordinates exactly.  At every fixed time,
both martingale realizations belong to `L²` for any finite measure on path
space.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem countableResolventCoreFeature_sub
    (G : ConductanceGraph V) (m : V → ℝ)
    (q r : CountableResolventCoreIndex V) :
    countableResolventCoreFeature G m (q - r) =
      countableResolventCoreFeature G m q -
        countableResolventCoreFeature G m r := by
  classical
  funext x
  simp only [Pi.sub_apply, countableResolventCoreFeature_eq_sum]
  apply Finsupp.sum_sub_index
  intro y a b
  rw [Rat.cast_sub, sub_mul]

theorem compactResolventCoreMartingale_add
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V)
    (q r : CountableResolventCoreIndex V) :
    compactResolventCoreMartingale G m hm PF default (q + r) =
      compactResolventCoreMartingale G m hm PF default q +
        compactResolventCoreMartingale G m hm PF default r := by
  classical
  unfold compactResolventCoreMartingale
  apply Finsupp.sum_add_index
  · intro y
    simp
  · intro y _ a b
    rw [Rat.cast_add, add_smul]

theorem compactResolventCoreMartingale_sub
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V)
    (q r : CountableResolventCoreIndex V) :
    compactResolventCoreMartingale G m hm PF default (q - r) =
      compactResolventCoreMartingale G m hm PF default q -
        compactResolventCoreMartingale G m hm PF default r := by
  classical
  unfold compactResolventCoreMartingale
  apply Finsupp.sum_sub_index
  intro y a b
  rw [Rat.cast_sub, sub_smul]

theorem rawResolventCoreMartingale_memLp_two
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V)
    (nu : Measure PF.Ω) [IsFiniteMeasure nu] (t : ℝ≥0) :
    MemLp (rawResolventCoreMartingale PF G m q t) 2 nu := by
  classical
  unfold rawResolventCoreMartingale Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  induction q.support using Finset.induction_on with
  | empty => simp
  | @insert y s hy ih =>
      rw [Finset.sum_insert hy]
      exact ((vertexDynkinMartingale_memLp_two h hG hm hmsum
        (by norm_num : (0 : ℝ) < 1) y nu t).const_smul (q y : ℝ)).add ih

theorem norm_compactResolventCoreMartingale_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) (omega : PF.Ω) :
    ‖compactResolventCoreMartingale G m hm PF default q t omega‖ ≤
      countableResolventCoreBound q * (1 + 2 * (t : ℝ)) := by
  classical
  unfold compactResolventCoreMartingale countableResolventCoreBound Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  calc
    ‖∑ y ∈ q.support, (q y : ℝ) •
        compactVertexDynkinMartingale G m hm PF default y t omega‖ ≤
        ∑ y ∈ q.support, ‖(q y : ℝ) •
          compactVertexDynkinMartingale G m hm PF default y t omega‖ :=
      norm_sum_le _ _
    _ ≤ ∑ y ∈ q.support, |(q y : ℝ)| * (1 + 2 * (t : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_compactVertexDynkinMartingale_le G m hm PF default y t omega)
        (abs_nonneg _)
    _ = (∑ y ∈ q.support, |(q y : ℝ)|) * (1 + 2 * (t : ℝ)) := by
      rw [Finset.sum_mul]

theorem compactResolventCoreMartingale_memLp_two
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V)
    (nu : Measure PF.Ω) [IsFiniteMeasure nu] (t : ℝ≥0) :
    MemLp (compactResolventCoreMartingale G m hm PF default q t) 2 nu := by
  classical
  unfold compactResolventCoreMartingale Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  induction q.support using Finset.induction_on with
  | empty => simp
  | @insert y s hy ih =>
      rw [Finset.sum_insert hy]
      have hyLp : MemLp
          (compactVertexDynkinMartingale G m hm PF default y t) 2 nu := by
        apply MemLp.of_bound
          (((stronglyAdapted_compactVertexDynkinMartingale G m hm PF default y t).mono
            (PF.naturalFiltration.rightCont.le t)).aestronglyMeasurable)
          (1 + 2 * (t : ℝ))
        exact Filter.Eventually.of_forall
          (norm_compactVertexDynkinMartingale_le G m hm PF default y t)
      exact (hyLp.const_smul (q y : ℝ)).add ih

end ReflectedGMS
