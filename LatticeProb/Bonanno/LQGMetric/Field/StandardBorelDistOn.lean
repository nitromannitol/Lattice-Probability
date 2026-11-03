/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.StandardBorelDistOn at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelDist
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelExt
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Finsupp.Encodable

/-!
# `𝒟'(U)` is a standard Borel space (FOUNDATIONS §9 item 4)

Coordinates: `J = (ℕ × ℕ) →₀ ℤ` indexes the integer combinations `comb c = Σ c_j φ_j` of the
countable family `φ_j = distGen U j` (dense sequences in `𝓓_{K_n}`, `K_n` an exhaustion of `U`),
and `pairJ h = (⟨h, comb c⟩)_{c ∈ J} ∈ ℝ^J`.

The range of `pairJ` is the Borel set `rangeSet U` (`range_pairJ_eq`): `a ∈ ℝ^J` is in the range
iff `a` is additive, depends only on `comb c`, and for every `n` there are `C, N ∈ ℕ` with
`|a c| ≤ C ‖comb c‖_{C^N}` whenever `comb c` is supported in `K_n`. The converse direction
extends `a` by density to each `𝓓_{K_n}` (`exists_clm_extend`) and glues
(`TestFunction.mkCLM`); the forward direction uses that a continuous linear functional on `𝓓_K`
is bounded by finitely many seminorms (mathlib `Seminorm.bound_of_continuous`).
Since the σ-algebra is `comap pairJ` (`distOn_measurableSpace_eq_comap_pairJ`) and `pairJ` is
injective, `pairJ` is a measurable embedding onto a Borel subset of the Polish space `ℝ^J`, so
`DistOn U` is standard Borel (`standardBorelSpace_distOn`).

Published background: 𝒟' is a Lusin space (L. Schwartz, *Radon measures on arbitrary
topological spaces and cylindrical measures*, Part II); the coordinate argument here is an own
elementary proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions

namespace LQGMetric

section
variable (U : Opens ℂ)

lemma exhaustK_mono {n m : ℕ} (h : n ≤ m) : (exhaustK U n : Set ℂ) ⊆ exhaustK U m :=
  image_mono ((CompactExhaustion.choice U).subset h)

/-- `φ ∈ 𝓓(U)` supported in `K`, as an element of `𝓓_K` -/
def mkT {K : Compacts ℂ} (φ : TestOn U) (h : tsupport (φ : ℂ → ℝ) ⊆ K) : 𝓓^{⊤}_{K}(ℂ, ℝ) where
  toFun := φ
  contDiff' := φ.contDiff
  zero_on_compl' := fun _ hx => image_eq_zero_of_notMem_tsupport fun h' => hx (h h')

/-- the inclusion `𝓓_{K_n} → 𝓓(U)` -/
def iotaK (n : ℕ) : 𝓓^{⊤}_{exhaustK U n}(ℂ, ℝ) →L[ℝ] TestOn U :=
  TestFunction.ofSupportedInCLM ℝ (exhaustK_subset U n)

/-- coordinates `J = (ℕ × ℕ) →₀ ℤ` -/
abbrev CoordJ : Type := (ℕ × ℕ) →₀ ℤ

/-- `c ↦ Σ_j c_j φ_j` -/
def comb : CoordJ →+ TestOn U :=
  Finsupp.liftAddHom fun j => zmultiplesHom (TestOn U) (distGen U j)

lemma comb_single (j : ℕ × ℕ) : comb U (Finsupp.single j 1) = distGen U j := by
  simp [comb]

/-- `h ↦ (⟨h, comb c⟩)_c` -/
def pairJ (h : DistOn U) : CoordJ → ℝ := fun c => h (comb U c)

/-- the Borel set which is the range of `pairJ` -/
def rangeSet : Set (CoordJ → ℝ) :=
  {a | ∀ c c', a (c + c') = a c + a c'} ∩ {a | ∀ c c', comb U c = comb U c' → a c = a c'} ∩
    ⋂ n : ℕ, ⋃ C : ℕ, ⋃ N : ℕ, {a | ∀ c (hc : tsupport (comb U c : ℂ → ℝ) ⊆ exhaustK U n),
      |a c| ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK U n) N (mkT U _ hc)}

theorem measurableSet_rangeSet : MeasurableSet (rangeSet U) := by
  refine ((IsClosed.measurableSet ?_).inter (IsClosed.measurableSet ?_)).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun C => MeasurableSet.iUnion fun N =>
      IsClosed.measurableSet ?_)
  · simp only [ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun c' =>
      isClosed_eq (continuous_apply _) ((continuous_apply c).add (continuous_apply c'))
  · simp only [ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply _) (continuous_apply _)
  · simp only [ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply _).abs continuous_const

lemma supSeminorm_mono (K : Compacts ℂ) {i j : ℕ} (h : i ≤ j) :
    ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ K i ≤
      ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ K j :=
  Finset.sup_mono (Finset.Iic_subset_Iic.2 h)

/-- forward direction: every distribution satisfies the conditions -/
theorem range_pairJ_subset : range (pairJ U) ⊆ rangeSet U := by
  rintro _ ⟨h, rfl⟩
  refine ⟨⟨fun c c' => by simp [pairJ, map_add], fun c c' e => by simp [pairJ, e]⟩, ?_⟩
  refine mem_iInter.2 fun n => ?_
  let L : 𝓓^{⊤}_{exhaustK U n}(ℂ, ℝ) →L[ℝ] ℝ :=
    (h : TestOn U →L[ℝ] ℝ).comp (iotaK U n)
  let q : Seminorm ℝ 𝓓^{⊤}_{exhaustK U n}(ℂ, ℝ) := (normSeminorm ℝ ℝ).comp L.toLinearMap
  have hq : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms' ℝ ℂ ℝ ⊤ (exhaustK U n)) q hq
  refine mem_iUnion.2 ⟨⌈(C : ℝ)⌉₊, mem_iUnion.2 ⟨s.sup id, fun c hc => ?_⟩⟩
  set x := mkT U (comb U c) hc
  have h1 : |pairJ U h c| = q x := by
    have : iotaK U n x = comb U c := by ext; rfl
    simp only [q, L, pairJ, Seminorm.comp_apply, coe_normSeminorm, Real.norm_eq_abs]
    show |h (comb U c)| = |h (iotaK U n x)|
    rw [this]
  have h2 : q x ≤ C * (s.sup (ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK U n))) x :=
    hC x
  have h3 : (s.sup (ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK U n))) x ≤
      ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK U n) (s.sup id) x :=
    (Finset.sup_le fun i hi => supSeminorm_mono _ (Finset.le_sup (f := id) hi)) x
  have h4 : 0 ≤ ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK U n) (s.sup id) x :=
    apply_nonneg _ _
  rw [h1]
  calc q x ≤ C * _ := h2.trans (mul_le_mul_of_nonneg_left h3 C.2)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) h4

end

end LQGMetric
