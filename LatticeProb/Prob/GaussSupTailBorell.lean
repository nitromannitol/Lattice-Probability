/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/SupTailBorell.lean.
-/
import LatticeProb.Prob.GaussBorellVector
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Running maxima and countable suprema of a Gaussian process

For a process `X : T → Ω → ℝ` and a sequence of indices `u : ℕ → T`, the running maximum
`seqMax X u n ω` is the largest of `X (u 0) ω, …, X (u n) ω`. This file proves that:

* the running maxima are monotone in `n`, dominate their terms, and converge to the supremum
  `⨆ k, X (u k) ω` whenever the sequence is bounded above;
* for a Gaussian process `X`, the running maxima are almost everywhere measurable and integrable,
  and any finite-dimensional subfamily `(X (t i))_i` is a Gaussian vector;
* if the expectations of the running maxima are bounded by a constant `C`, then the supremum
  `⨆ k, X (u k) ω` is integrable with expectation at most `C`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace LatticeProb.GaussConc.SupTail

variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The finite-dimensional vector `(X (t i))_i` of a Gaussian process is a Gaussian vector. -/
lemma hasGaussianLaw_finVec {X : T → Ω → ℝ} (hX : IsGaussianProcess X P) {n : ℕ}
    (t : Fin n → T) : HasGaussianLaw (fun ω i => X (t i) ω) P := by
  have hY : IsGaussianProcess (fun i : Fin n => X (t i)) P := hX.comp_right t
  let L : (↥(Finset.univ : Finset (Fin n)) → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj ⟨i, Finset.mem_univ i⟩
  exact (hY.hasGaussianLaw Finset.univ).map L

/-- Running maximum `max_{i ≤ n} X (u i)` of a process along a sequence of indices. -/
def seqMax (X : T → Ω → ℝ) (u : ℕ → T) (n : ℕ) (ω : Ω) : ℝ := ⨆ i : Fin (n + 1), X (u i) ω

variable {X : T → Ω → ℝ} {u : ℕ → T}

omit [MeasurableSpace Ω] in
/-- The running maximum is monotone in the number of indices. -/
lemma seqMax_mono (ω : Ω) : Monotone fun n => seqMax X u n ω := by
  intro m n hmn
  exact ciSup_le fun i => le_ciSup_of_le (Finite.bddAbove_range _)
    (Fin.castLE (by omega) i) le_rfl

omit [MeasurableSpace Ω] in
/-- Each term of the sequence is at most the running maximum over a longer initial segment. -/
lemma le_seqMax {k n : ℕ} (hk : k ≤ n) (ω : Ω) : X (u k) ω ≤ seqMax X u n ω :=
  le_ciSup (f := fun i : Fin (n + 1) => X (u i) ω) (Finite.bddAbove_range _) ⟨k, by omega⟩

omit [MeasurableSpace Ω] in
/-- The running maximum is at most the supremum of a sequence that is bounded above. -/
lemma seqMax_le_iSup {ω : Ω} (hb : BddAbove (range fun k => X (u k) ω)) (n : ℕ) :
    seqMax X u n ω ≤ ⨆ k, X (u k) ω :=
  ciSup_le fun i => le_ciSup hb (i : ℕ)

omit [MeasurableSpace Ω] in
/-- The running maxima converge to the supremum of a sequence that is bounded above. -/
lemma tendsto_seqMax {ω : Ω} (hb : BddAbove (range fun k => X (u k) ω)) :
    Tendsto (fun n => seqMax X u n ω) atTop (𝓝 (⨆ k, X (u k) ω)) := by
  refine tendsto_atTop_isLUB (seqMax_mono ω) ⟨?_, fun b hbub => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact seqMax_le_iSup hb n
  · exact ciSup_le fun k => (le_seqMax le_rfl ω).trans (hbub ⟨k, rfl⟩)

/-- The running maximum of a Gaussian process is almost everywhere measurable. -/
lemma aemeasurable_seqMax (hX : IsGaussianProcess X P) (n : ℕ) :
    AEMeasurable (seqMax X u n) P :=
  AEMeasurable.iSup fun i => hX.aemeasurable (u i)

/-- The running maximum of a Gaussian process is integrable. -/
lemma integrable_seqMax (hX : IsGaussianProcess X P) (n : ℕ) :
    Integrable (seqMax X u n) P := by
  have hi : ∀ i : Fin (n + 1), Integrable (X (u i)) P :=
    fun i => (hX.hasGaussianLaw_eval (u i)).integrable
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ => (hi i).abs)
    (aemeasurable_seqMax hX n).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have hs : ∀ j : Fin (n + 1), |X (u j) ω| ≤ ∑ i : Fin (n + 1), |X (u i) ω| := fun j =>
    Finset.single_le_sum (f := fun i : Fin (n + 1) => |X (u i) ω|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  constructor
  · have h0 := le_seqMax (X := X) (u := u) (Nat.zero_le n) ω
    have := hs 0
    have := neg_abs_le (X (u 0) ω)
    simp only [Fin.val_zero] at *
    linarith
  · exact ciSup_le fun j => (le_abs_self _).trans (hs j)

/-- **Monotone limits of expected maxima.** If the running maxima have `E max ≤ C` and the
sequence is bounded for every `ω`, the supremum is integrable with `E sup ≤ C`. -/
theorem integrable_iSup_of_seqMax (hX : IsGaussianProcess X P)
    (hb : ∀ ω, BddAbove (range fun k => X (u k) ω)) {C : ℝ}
    (hC : ∀ n, ∫ ω, seqMax X u n ω ∂P ≤ C) :
    Integrable (fun ω => ⨆ k, X (u k) ω) P ∧ ∫ ω, (⨆ k, X (u k) ω) ∂P ≤ C := by
  set F : Ω → ℝ := fun ω => ⨆ k, X (u k) ω
  have hFm : AEMeasurable F P := AEMeasurable.iSup fun k => hX.aemeasurable (u k)
  have h0 := integrable_seqMax (u := u) hX 0
  have hG : 0 ≤ᵐ[P] fun ω => F ω - seqMax X u 0 ω := Eventually.of_forall fun ω =>
    sub_nonneg.2 (seqMax_le_iSup (hb ω) 0)
  have hlim : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (seqMax X u n ω - seqMax X u 0 ω) ∂P)
      atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (F ω - seqMax X u 0 ω) ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((aemeasurable_seqMax hX n).sub (aemeasurable_seqMax hX 0)).ennreal_ofReal)
      (Eventually.of_forall fun ω m n hmn => ENNReal.ofReal_le_ofReal
        (sub_le_sub_right (seqMax_mono ω hmn) _))
      (Eventually.of_forall fun ω => ?_)
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_seqMax (hb ω)).sub tendsto_const_nhds)
  have hbd : ∀ n, ∫⁻ ω, ENNReal.ofReal (seqMax X u n ω - seqMax X u 0 ω) ∂P ≤
      ENNReal.ofReal (C - ∫ ω, seqMax X u 0 ω ∂P) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun ω => seqMax X u n ω - seqMax X u 0 ω)
      ((integrable_seqMax hX n).sub h0)
      (Eventually.of_forall fun ω => sub_nonneg.2 (seqMax_mono ω (Nat.zero_le n))),
      integral_sub (integrable_seqMax hX n) h0]
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (hC n) _)
  have hfin : ∫⁻ ω, ENNReal.ofReal (F ω - seqMax X u 0 ω) ∂P < ∞ :=
    (le_of_tendsto' hlim hbd).trans_lt ENNReal.ofReal_lt_top
  have hGi : Integrable (fun ω => F ω - seqMax X u 0 ω) P :=
    ⟨(hFm.sub (aemeasurable_seqMax hX 0)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hG).2 hfin⟩
  have hFi : Integrable F P := by
    have := hGi.add h0
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp
  refine ⟨hFi, ?_⟩
  have ht := integral_tendsto_of_tendsto_of_monotone (fun n => integrable_seqMax hX n) hFi
    (Eventually.of_forall fun ω => seqMax_mono ω)
    (Eventually.of_forall fun ω => tendsto_seqMax (hb ω))
  exact le_of_tendsto' ht hC

end LatticeProb.GaussConc.SupTail
