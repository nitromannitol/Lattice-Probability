/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.RandomDistVersion at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.RandomDist
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistComplete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Versions: from a process indexed by test functions to a random distribution

Berestycki–Powell, arXiv:2404.16642, `definitionGFF.tex` l. 842–862: the GFF is first a
stochastic process `(h, ρ)` indexed by test functions, a.s. linear; a *version* of it is a random
variable in `𝒟'` whose pairings agree a.s. with the process.

`exists_version`: let `X : 𝓓(U) → Ω → ℝ` be a process with measurable coordinates such that
(i) a.s. the countably many values `(X (comb c) ω)_c` are admissible (`rangeSet U`: additive,
consistent, and of finite order on each `K_n`), and (ii) `X` is continuous in probability along
sequences converging in `𝓓(U)`. Then there is a random distribution `h : Ω → 𝒟'(U)`
(measurable for the cylinder = weak-* Borel σ-algebra) with `⟨h, φ⟩ = X φ` a.s. for every `φ`.
The random distribution is obtained by inverting the measurable embedding `pairJ`
(`measurableEmbedding_pairJ`), and (ii) transfers the identity from the countable family to all
test functions (limits in probability are a.s. unique, mathlib `tendstoInMeasure_ae_unique`).

Hypothesis (i) is where a published existence proof (BP's negative-Sobolev series, or the
Minlos/Itô regularization theorem for nuclear spaces) does its work; this file is the measurable
"version" step common to all of them. Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions

namespace LQGMetric

section
variable (U : Opens ℂ)

/-- a measurable left inverse of `pairJ` -/
def pairJInv : (CoordJ → ℝ) → DistOn U := Function.extend (pairJ U) id fun _ => 0

theorem measurable_pairJInv : Measurable (pairJInv U) :=
  (measurableEmbedding_pairJ U).measurable_extend measurable_id measurable_const

theorem pairJInv_pairJ (h : DistOn U) : pairJInv U (pairJ U h) = h :=
  (injective_pairJ U).extend_apply _ _ _

theorem exists_version {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : TestOn U → Ω → ℝ) (hX : ∀ φ, Measurable (X φ))
    (hadm : ∀ᵐ ω ∂P, (fun c => X (comb U c) ω) ∈ rangeSet U)
    (hcont : ∀ (φ : TestOn U) (ψ : ℕ → TestOn U), Tendsto ψ atTop (𝓝 φ) →
      TendstoInMeasure P (fun k => X (ψ k)) atTop (X φ)) :
    ∃ h : Ω → DistOn U, Measurable h ∧ ∀ φ, (fun ω => h ω φ) =ᵐ[P] X φ := by
  let a : Ω → CoordJ → ℝ := fun ω c => X (comb U c) ω
  have ha : Measurable a := Measurable.of_eval fun c => hX _
  refine ⟨fun ω => pairJInv U (a ω), (measurable_pairJInv U).comp ha, fun φ => ?_⟩
  have hgood : ∀ᵐ ω ∂P, ∀ c, pairJInv U (a ω) (comb U c) = X (comb U c) ω := by
    filter_upwards [hadm] with ω hω
    rw [← range_pairJ_eq] at hω
    obtain ⟨T, hT⟩ := hω
    intro c
    have : pairJInv U (a ω) = T := by
      show pairJInv U (fun c => X (comb U c) ω) = T
      rw [← hT]; exact pairJInv_pairJ U T
    rw [this]
    exact congrFun hT c
  obtain ⟨n, hn⟩ := exists_exhaustK_superset U φ.hasCompactSupport.isCompact φ.tsupport_subset
  set ψ := mkT U φ hn
  have hψφ : iotaK U n ψ = φ := by ext; rfl
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1
    (show ψ ∈ closure (combSub U n : Set _) by rw [(dense_combSub U n).closure_eq]; trivial)
  choose c hc using hs
  have hlim' : Tendsto (fun k => iotaK U n (s k)) atTop (𝓝 φ) := by
    rw [← hψφ]; exact ((iotaK U n).continuous.tendsto ψ).comp hlim
  have h1 := hcont φ _ hlim'
  have h2 : TendstoInMeasure P (fun k ω => pairJInv U (a ω) (iotaK U n (s k))) atTop
      (fun ω => pairJInv U (a ω) φ) := by
    refine tendstoInMeasure_of_tendsto_ae (fun k => ?_) (Eventually.of_forall fun ω =>
      ((map_continuous (pairJInv U (a ω))).tendsto φ).comp hlim')
    exact ((measurable_distOn_apply _).comp ((measurable_pairJInv U).comp ha)).aestronglyMeasurable
  have h3 : TendstoInMeasure P (fun k ω => pairJInv U (a ω) (iotaK U n (s k))) atTop (X φ) := by
    refine TendstoInMeasure.congr' (Eventually.of_forall fun k => ?_) EventuallyEq.rfl h1
    filter_upwards [hgood] with ω hω
    rw [← hc k, hω]
  exact tendstoInMeasure_ae_unique h2 h3

end

end LQGMetric
