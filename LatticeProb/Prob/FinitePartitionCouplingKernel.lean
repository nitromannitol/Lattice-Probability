module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/FinitePartitionCouplingKernel.lean.
-/
public import LatticeProb.Prob.FinitePartitionCoupling
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-!
# The explicit finite partition coupling is a measurable kernel

Parametrised by a point of `S`, the explicit finite partition coupling of the
laws `κ a` and `ν a` along fixed measurable cells is a Markov kernel from `S`
to `X × Y`. Its parameter dependence is proved measurable here, rather than
inferred from the pointwise existence of a coupling. At every parameter the
kernel has the marginals `κ a` and `ν a`, and the unmatched-mass bound of
`finitePartitionCoupling` holds.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace LatticeProb

variable {S X Y ι : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]

private noncomputable def weightedKernel (κ : Kernel S X) (c : S → ℝ≥0∞)
    (hc : Measurable c) : Kernel S X where
  toFun a := c a • κ a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hc.mul (κ.measurable_coe hA)

private noncomputable def cappedCellKernel (κ : Kernel S X) (ν : Kernel S Y)
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) : Kernel S X :=
  weightedKernel (κ.restrict hE) (fun a ↦ min (κ a E) (ν a F) / κ a E)
    (((κ.measurable_coe hE).min (ν.measurable_coe hF)).div (κ.measurable_coe hE))

private lemma cappedCellKernel_apply (κ : Kernel S X) (ν : Kernel S Y)
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) (a : S) :
    cappedCellKernel κ ν hE hF a = cappedRestrict (κ a) E (min (κ a E) (ν a F)) := rfl

private instance cappedCellKernel_isFinite (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] {E : Set X} {F : Set Y}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IsFiniteKernel (cappedCellKernel κ ν hE hF) := by
  apply isFiniteKernel_of_le (ν := κ)
  intro a A
  exact (cappedRestrict_le (κ a) E (min_le_left _ _) A).trans (Measure.restrict_le_self A)

private noncomputable def balancedProductKernel (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν] : Kernel S (X × Y) :=
  weightedKernel (κ ×ₖ ν) (fun a ↦ (κ a univ)⁻¹)
    (κ.measurable_coe MeasurableSet.univ).inv

private lemma balancedProductKernel_apply (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : S) :
    balancedProductKernel κ ν a = balancedProduct (κ a) (ν a) := by
  change (κ a univ)⁻¹ • (κ ×ₖ ν) a = _
  rw [Kernel.prod_apply]
  rfl

private noncomputable def matchedCellKernel (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) : Kernel S (X × Y) :=
  balancedProductKernel (cappedCellKernel κ ν hE hF) (cappedCellKernel ν κ hF hE)

private lemma matchedCellKernel_apply (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) (a : S) :
    matchedCellKernel κ ν hE hF a = matchedCellCoupling (κ a) (ν a) E F := by
  rw [matchedCellKernel, balancedProductKernel_apply, cappedCellKernel_apply,
    cappedCellKernel_apply]
  simp only [matchedCellCoupling, min_comm (ν a F) (κ a E)]

private noncomputable def finiteMatchedKernel [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) : Kernel S (X × Y) :=
  Kernel.sum (fun i ↦ matchedCellKernel κ ν (hE i) (hF i))

private lemma finiteMatchedKernel_apply [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) (a : S) :
    finiteMatchedKernel κ ν hE hF a = finiteMatchedCoupling (κ a) (ν a) E F := by
  simp only [finiteMatchedKernel, Kernel.sum_apply, matchedCellKernel_apply, finiteMatchedCoupling]

private instance finiteMatchedKernel_isFinite [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) :
    IsFiniteKernel (finiteMatchedKernel κ ν hE hF) := by
  refine ⟨⟨Fintype.card ι, ENNReal.natCast_lt_top _, fun a ↦ ?_⟩⟩
  rw [finiteMatchedKernel_apply, finiteMatchedCoupling_univ]
  calc
    ∑ i, min (κ a (E i)) (ν a (F i)) ≤ ∑ _i : ι, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum (fun i hi ↦ (min_le_left _ _).trans prob_le_one)
    _ = _ := by simp

private noncomputable def residualKernel (κ η : Kernel S X) [IsFiniteKernel η]
    (hle : ∀ a, η a ≤ κ a) : Kernel S X where
  toFun a := κ a - η a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.sub_apply hA (hle _)]
    exact (κ.measurable_coe hA).sub (η.measurable_coe hA)

private instance residualKernel_isFinite (κ η : Kernel S X)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hle : ∀ a, η a ≤ κ a) :
    IsFiniteKernel (residualKernel κ η hle) := by
  apply isFiniteKernel_of_le (ν := κ)
  intro a A
  exact Measure.sub_le A

/-- The explicit finite partition coupling as a kernel from `S`: at each parameter `a` it is
the measure `finitePartitionCoupling (κ a) (ν a) E F`. It is the sum over the cells of the
exact matched couplings, plus the balanced product of the two residual kernels, and its
measurability in the parameter is proved by construction. -/
noncomputable def finitePartitionCouplingKernel [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) : Kernel S (X × Y) := by
  let ρ := finiteMatchedKernel κ ν hE hF
  have hfst (a : S) : ρ.fst a ≤ κ a := by
    change (ρ a).fst ≤ κ a
    rw [finiteMatchedKernel_apply]
    exact finiteMatchedCoupling_fst_le (κ a) (ν a) F hE hdE
  have hsnd (a : S) : ρ.snd a ≤ ν a := by
    change (ρ a).snd ≤ ν a
    rw [finiteMatchedKernel_apply]
    exact finiteMatchedCoupling_snd_le (κ a) (ν a) E hF hdF
  exact ρ + balancedProductKernel (residualKernel κ ρ.fst hfst)
    (residualKernel ν ρ.snd hsnd)

/-- The kernel `finitePartitionCouplingKernel` evaluated at a parameter `a` is the explicit
finite partition coupling `finitePartitionCoupling (κ a) (ν a) E F`. -/
lemma finitePartitionCouplingKernel_apply [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (a : S) :
    finitePartitionCouplingKernel κ ν hE hF hdE hdF a =
      finitePartitionCoupling (κ a) (ν a) E F := by
  simp only [finitePartitionCouplingKernel, Kernel.add_apply, balancedProductKernel_apply,
    residualKernel, Kernel.coe_mk, Kernel.fst_apply, Kernel.snd_apply,
    finiteMatchedKernel_apply, finitePartitionCoupling, completeSubcoupling,
    Measure.fst, Measure.snd]

/-- The explicit finite partition coupling kernel is a Markov kernel: at every parameter it
is a probability measure. -/
instance finitePartitionCouplingKernel_isMarkov [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    IsMarkovKernel (finitePartitionCouplingKernel κ ν hE hF hdE hdF) where
  isProbabilityMeasure a := by
    rw [finitePartitionCouplingKernel_apply]
    exact (finitePartitionCoupling_spec (κ a) (ν a) hE hF hdE hdF).1

/-- At every parameter `a`, the two marginals of the explicit finite partition coupling kernel
are `κ a` and `ν a`, and every event `B` disjoint from all the paired cells `E i ×ˢ F i` has
probability at most the unmatched mass `1 - ∑ i, min (κ a (E i)) (ν a (F i))`. -/
theorem finitePartitionCouplingKernel_spec [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (a : S) :
    (finitePartitionCouplingKernel κ ν hE hF hdE hdF a).fst = κ a ∧
    (finitePartitionCouplingKernel κ ν hE hF hdE hdF a).snd = ν a ∧
    ∀ B : Set (X × Y), (∀ i, Disjoint B (E i ×ˢ F i)) →
      finitePartitionCouplingKernel κ ν hE hF hdE hdF a B ≤
        1 - ∑ i, min (κ a (E i)) (ν a (F i)) := by
  rw [finitePartitionCouplingKernel_apply]
  exact (finitePartitionCoupling_spec (κ a) (ν a) hE hF hdE hdF).2

/-! ### Nonvacuity examples -/

namespace FinitePartitionCouplingKernelExample

/-- The Markov kernel from `Bool` to `Bool` sending `a` to the Dirac mass at `a`. -/
noncomputable def idKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun a : Bool ↦ a) measurable_id

instance : IsMarkovKernel idKernel :=
  inferInstanceAs (IsMarkovKernel (Kernel.deterministic (fun a : Bool ↦ a) measurable_id))

/-- The Markov kernel from `Bool` to `Bool` sending `a` to the Dirac mass at `!a`. -/
noncomputable def negKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun a : Bool ↦ !a) Measurable.of_discrete

instance : IsMarkovKernel negKernel :=
  inferInstanceAs
    (IsMarkovKernel (Kernel.deterministic (fun a : Bool ↦ !a) Measurable.of_discrete))

/-- The cells `{false}` and `∅` on the first `Bool`. They do not cover `Bool`, since
`true` lies in neither. -/
def exampleE : Fin 2 → Set Bool := ![{false}, ∅]

/-- The cells `{true}` and `∅` on the second `Bool`. They do not cover `Bool`, since
`false` lies in neither. -/
def exampleF : Fin 2 → Set Bool := ![{true}, ∅]

/-- The cells `exampleE i` are measurable. -/
theorem exampleE_measurable : ∀ i, MeasurableSet (exampleE i) :=
  fun _ ↦ MeasurableSet.of_discrete

/-- The cells `exampleF i` are measurable. -/
theorem exampleF_measurable : ∀ i, MeasurableSet (exampleF i) :=
  fun _ ↦ MeasurableSet.of_discrete

/-- The cells `exampleE i` are pairwise disjoint. -/
theorem exampleE_pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (exampleE i) (exampleE j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [exampleE]

/-- The cells `exampleF i` are pairwise disjoint. -/
theorem exampleF_pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (exampleF i) (exampleF j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [exampleF]

/-- The point `(true, false)` avoids both paired cells `exampleE i ×ˢ exampleF i`. -/
theorem exampleEvent_disjoint :
    ∀ i, Disjoint ({((true : Bool), (false : Bool))} : Set (Bool × Bool))
      (exampleE i ×ˢ exampleF i) := by
  intro i
  fin_cases i <;> simp [exampleE, exampleF, Set.disjoint_singleton_left]

/-- At the parameter `false`, the kernel `idKernel` is the Dirac mass at `false`. -/
theorem idKernel_false : idKernel false = Measure.dirac false := rfl

/-- At the parameter `false`, the kernel `negKernel` is the Dirac mass at `true`. -/
theorem negKernel_false : negKernel false = Measure.dirac true := rfl

/-- At the parameter `false`, the first marginal of the explicit coupling kernel is the Dirac
mass at `false`. -/
theorem exampleKernel_fst_false :
    (finitePartitionCouplingKernel idKernel negKernel exampleE_measurable exampleF_measurable
      exampleE_pairwise_disjoint exampleF_pairwise_disjoint false).fst = Measure.dirac false := by
  rw [(finitePartitionCouplingKernel_spec idKernel negKernel exampleE_measurable
    exampleF_measurable exampleE_pairwise_disjoint exampleF_pairwise_disjoint false).1,
    idKernel_false]

/-- At the parameter `false`, the second marginal of the explicit coupling kernel is the Dirac
mass at `true`. -/
theorem exampleKernel_snd_false :
    (finitePartitionCouplingKernel idKernel negKernel exampleE_measurable exampleF_measurable
      exampleE_pairwise_disjoint exampleF_pairwise_disjoint false).snd = Measure.dirac true := by
  rw [(finitePartitionCouplingKernel_spec idKernel negKernel exampleE_measurable
    exampleF_measurable exampleE_pairwise_disjoint exampleF_pairwise_disjoint false).2.1,
    negKernel_false]

/-- At the parameter `false`, the unmatched mass is `0`: the common masses of the two cells are
`1` and `0`. -/
theorem exampleUnmatched_false :
    1 - ∑ i, min (idKernel false (exampleE i)) (negKernel false (exampleF i)) = 0 := by
  have h0 : idKernel false (exampleE 0) = 1 := by
    rw [idKernel_false]; exact Measure.dirac_apply_of_mem (mem_singleton _)
  have h1 : idKernel false (exampleE 1) = 0 := by
    rw [idKernel_false]
    exact (dirac_eq_zero_iff_not_mem MeasurableSet.of_discrete).2 (by simp [exampleE])
  have h2 : negKernel false (exampleF 0) = 1 := by
    rw [negKernel_false]; exact Measure.dirac_apply_of_mem (mem_singleton _)
  have h3 : negKernel false (exampleF 1) = 0 := by
    rw [negKernel_false]
    exact (dirac_eq_zero_iff_not_mem MeasurableSet.of_discrete).2 (by simp [exampleF])
  rw [Fin.sum_univ_two, h0, h1, h2, h3]
  simp

/-- At the parameter `false`, the explicit coupling kernel gives the event `{(true, false)}`,
which avoids both paired cells, probability at most `0`. -/
theorem exampleKernel_bad_event_false :
    finitePartitionCouplingKernel idKernel negKernel exampleE_measurable exampleF_measurable
      exampleE_pairwise_disjoint exampleF_pairwise_disjoint false
      {((true : Bool), (false : Bool))} ≤ 0 := by
  have h := (finitePartitionCouplingKernel_spec idKernel negKernel exampleE_measurable
    exampleF_measurable exampleE_pairwise_disjoint exampleF_pairwise_disjoint false).2.2 _
    exampleEvent_disjoint
  rw [exampleUnmatched_false] at h
  exact h

end FinitePartitionCouplingKernelExample

end LatticeProb
