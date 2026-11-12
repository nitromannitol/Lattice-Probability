/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentVer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Dyadic versions of random fields, measurable for a sub-σ-algebra (P2-GMCID, D67)

For a family `F : ℂ → Ω → ℝ` let `dyVer F z ω = lim_j F(d_j(z))(ω)` along the dyadic
approximations `d_j(z) = dyadicRoundC j z` (QZ's `avgReg` construction, `Field/Sample.lean`,
applied to a general family; junk `0` where the limit fails). Then:

* `measurable_dyVer` : if every `F z` is `m`-measurable, `(z, ω) ↦ dyVer F z ω` is measurable for
  `Borel(ℂ) ⊗ m` (countable range of `d_j`, as in QZ `measurable_eval_dyadic`);
* `ae_tendsto_of_summable` : `∑_j E|A_j − B| < ∞` implies `A_j → B` a.s. (Borel–Cantelli in its
  first-moment form, own elementary proof);
* `dyVer_ae_eq` : if `∑_j E|F(d_j z) − F z| < ∞` then `dyVer F z = F z` a.s.

Used to give DZZ's field `h̃_δ` (`LBM_LGDarXiv.tex` l. 430–433) a version that is jointly
measurable for `Borel ⊗ 𝓖_n`, `𝓖_n` the white-noise σ-algebra of the coarse scales; this is the
`𝓕_n`-measurability of `μ^n` in Berestycki arXiv:1506.09113 §4 (l. 649).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology QuantumZipper
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent

variable {Ω : Type*}

theorem measurable_dyadicRound' (n : ℕ) : Measurable (dyadicRound n) := by
  unfold dyadicRound
  exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
    (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))

theorem measurable_dyadicRoundC' (n : ℕ) : Measurable (dyadicRoundC n) := by
  have hrw : dyadicRoundC n
      = fun z : ℂ => (dyadicRound n z.re : ℂ) + (dyadicRound n z.im : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [dyadicRoundC]
  rw [hrw]
  exact (Complex.continuous_ofReal.measurable.comp
        ((measurable_dyadicRound' n).comp Complex.measurable_re)).add
    ((Complex.continuous_ofReal.measurable.comp
        ((measurable_dyadicRound' n).comp Complex.measurable_im)).mul_const Complex.I)

theorem countable_range_dyadicRoundC' (n : ℕ) : (Set.range (dyadicRoundC n)).Countable := by
  have hsub : Set.range (dyadicRoundC n) ⊆
      Set.range (fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
  exact (Set.countable_range _).mono hsub

/-- The dyadic version of a field. -/
def dyVer (F : ℂ → Ω → ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  limUnder atTop fun j => F (dyadicRoundC j z) ω

theorem measurable_eval_dyadicRoundC {m : MeasurableSpace Ω} {F : ℂ → Ω → ℝ}
    (hF : ∀ z, Measurable[m] (F z)) (n : ℕ) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω _ m] fun p : ℂ × Ω => F (dyadicRoundC n p.1) p.2 := by
  have : Countable (Set.range (dyadicRoundC n)) := (countable_range_dyadicRoundC' n).to_subtype
  intro T hT
  have key : (fun p : ℂ × Ω => F (dyadicRoundC n p.1) p.2) ⁻¹' T
      = ⋃ d : Set.range (dyadicRoundC n),
          (dyadicRoundC n ⁻¹' ({(d : ℂ)} : Set ℂ)) ×ˢ {ω | F (d : ℂ) ω ∈ T} := by
    ext ⟨z, ω⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hmem
      exact ⟨⟨dyadicRoundC n z, Set.mem_range_self z⟩, rfl, hmem⟩
    · rintro ⟨d, hdz, hmem⟩
      rwa [hdz]
  rw [key]
  refine MeasurableSet.iUnion fun d => MeasurableSet.prod ?_ ?_
  · exact (measurable_dyadicRoundC' n) (measurableSet_singleton _)
  · exact hF _ hT

/-- **`dyVer F` is `Borel ⊗ m`-measurable** when every `F z` is `m`-measurable. -/
theorem measurable_dyVer {m : MeasurableSpace Ω} {F : ℂ → Ω → ℝ}
    (hF : ∀ z, Measurable[m] (F z)) :
    Measurable[@Prod.instMeasurableSpace ℂ Ω _ m] fun p : ℂ × Ω => dyVer F p.1 p.2 := by
  let _ : MeasurableSpace Ω := m
  unfold dyVer
  exact (StronglyMeasurable.limUnder
    (fun n => (measurable_eval_dyadicRoundC hF n).stronglyMeasurable)).measurable

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- **First-moment Borel–Cantelli**: `∑_j E|A_j − B| < ∞` implies `A_j → B` a.s. -/
theorem ae_tendsto_of_summable {A : ℕ → Ω → ℝ} {B : Ω → ℝ} (hA : ∀ j, AEMeasurable (A j) P)
    (hB : AEMeasurable B P)
    (h : ∑' j, ∫⁻ ω, ENNReal.ofReal |A j ω - B ω| ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun j => A j ω) atTop (𝓝 (B ω)) := by
  have hm : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal |A j ω - B ω|) P := fun j =>
    (continuous_abs.measurable.comp_aemeasurable ((hA j).sub hB)).ennreal_ofReal
  have hfin : ∫⁻ ω, ∑' j, ENNReal.ofReal |A j ω - B ω| ∂P ≠ ∞ := by
    rwa [lintegral_tsum hm]
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hm) hfin] with ω hω
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h1 : Tendsto (fun j => |A j ω - B ω|) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    simpa [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using this
  have h2 : Tendsto (fun j => A j ω - B ω) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]; exact h1
  simpa using h2.add_const (B ω)

/-- **The dyadic version is a version**: if `∑_j E|F(d_j z) − F z| < ∞`, then
`dyVer F z = F z` a.s. -/
theorem dyVer_ae_eq {F : ℂ → Ω → ℝ} (hF : ∀ z, AEMeasurable (F z) P) (z : ℂ)
    (h : ∑' j, ∫⁻ ω, ENNReal.ofReal |F (dyadicRoundC j z) ω - F z ω| ∂P ≠ ∞) :
    dyVer F z =ᵐ[P] F z := by
  filter_upwards [ae_tendsto_of_summable (fun j => hF _) (hF z) h] with ω hω
  exact hω.limUnder_eq

end GMCIdent
end LQGMetric
