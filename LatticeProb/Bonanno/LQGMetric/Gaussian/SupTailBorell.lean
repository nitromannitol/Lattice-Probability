/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.SupTailBorell at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationVector
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
For a centered Gaussian process `X : T → Ω → ℝ` (`IsGaussianProcess X P`, `E X t = 0`) and a
sequence of indices `u : ℕ → T`:

* `seqMax X u n ω = max_{i ≤ n} X (u i) ω` (running maxima), monotone in `n`, integrable, and
  converging to `sup_k X (u k) ω` when the sequence is bounded;
* `integrable_iSup_of_seqMax`: `E max_{i ≤ n} ≤ C` for all `n` gives `sup_k X (u k)` integrable
  with `E sup ≤ C` (monotone convergence);
* `borellTIS_iSup_seq`: **Borell–TIS inequality** `P(sup - E sup ≥ t) ≤ exp (-t² / (2σ²))` for
  `σ² ≥ sup_k Var X (u k)`, `t ≥ 0`.

Source: R. J. Adler, J. E. Taylor, *Random Fields and Geometry*, Springer 2007, Thm 2.1.1
(p. 50) and its proof (pp. 56–57: the inequality for finite `T`, then monotone limits over
finite sets `T_n` increasing to a dense subset). The finite case is
`GaussConc.borellTIS_gaussianVector` of this library; the passage to the limit (Fatou-type
argument on the events and continuity in `t`) is written out here. Degenerate finite
subfamilies (all variances zero) are treated separately since the finite statement needs
`σ² = max Var` exactly. Unlike Adler–Taylor, `E sup < ∞` enters through the hypothesis
`E max_{i ≤ n} ≤ C` (in the applications it is supplied by the chaining bound,
`LQGMetric/Gaussian/FerniqueFinite.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric

namespace SupTail

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

lemma seqMax_mono (ω : Ω) : Monotone fun n => seqMax X u n ω := by
  intro m n hmn
  exact ciSup_le fun i => le_ciSup_of_le (Finite.bddAbove_range _)
    (Fin.castLE (by omega) i) le_rfl

omit [MeasurableSpace Ω] in
lemma le_seqMax {k n : ℕ} (hk : k ≤ n) (ω : Ω) : X (u k) ω ≤ seqMax X u n ω :=
  le_ciSup (f := fun i : Fin (n + 1) => X (u i) ω) (Finite.bddAbove_range _) ⟨k, by omega⟩

omit [MeasurableSpace Ω] in
lemma seqMax_le_iSup {ω : Ω} (hb : BddAbove (range fun k => X (u k) ω)) (n : ℕ) :
    seqMax X u n ω ≤ ⨆ k, X (u k) ω :=
  ciSup_le fun i => le_ciSup hb (i : ℕ)

omit [MeasurableSpace Ω] in
lemma tendsto_seqMax {ω : Ω} (hb : BddAbove (range fun k => X (u k) ω)) :
    Tendsto (fun n => seqMax X u n ω) atTop (𝓝 (⨆ k, X (u k) ω)) := by
  refine tendsto_atTop_isLUB (seqMax_mono ω) ⟨?_, fun b hbub => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact seqMax_le_iSup hb n
  · exact ciSup_le fun k => (le_seqMax le_rfl ω).trans (hbub ⟨k, rfl⟩)

lemma aemeasurable_seqMax (hX : IsGaussianProcess X P) (n : ℕ) :
    AEMeasurable (seqMax X u n) P :=
  AEMeasurable.iSup fun i => hX.aemeasurable (u i)

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

/-- Borell–TIS for the running maxima (from `GaussConc.borellTIS_gaussianVector`), with any
upper bound `σ² ≥ max_{i ≤ n} Var X (u i)`. -/
lemma borellTIS_seqMax (hX : IsGaussianProcess X P) (h0 : ∀ s, ∫ ω, X s ω ∂P = 0) {σ : ℝ}
    (hvar : ∀ k, Var[X (u k); P] ≤ σ ^ 2) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    P.real {ω | t ≤ seqMax X u n ω - ∫ ω', seqMax X u n ω' ∂P} ≤
      exp (-t ^ 2 / (2 * σ ^ 2)) := by
  have hP := hX.isProbabilityMeasure
  have hY := hasGaussianLaw_finVec hX (fun i : Fin (n + 1) => u i)
  set V := ⨆ i : Fin (n + 1), Var[fun ω => X (u i) ω; P] with hVdef
  have hV0 : 0 ≤ V := le_ciSup_of_le (Finite.bddAbove_range _) 0 (variance_nonneg _ _)
  have hVσ : V ≤ σ ^ 2 := ciSup_le fun i => hvar i
  rcases hV0.eq_or_lt with hV | hV
  · rcases ht.eq_or_lt with rfl | htpos
    · calc _ ≤ 1 := measureReal_le_one
        _ = _ := by simp
    have hz : ∀ i : Fin (n + 1), X (u i) =ᵐ[P] 0 := by
      intro i
      have hvi : Var[X (u i); P] = 0 := le_antisymm
        (hV ▸ le_ciSup (f := fun i : Fin (n + 1) => Var[fun ω => X (u i) ω; P])
          (Finite.bddAbove_range _) i) (variance_nonneg _ _)
      have hm := (hX.hasGaussianLaw_eval (u i)).memLp_two
      have he : evariance (X (u i)) P = 0 := by
        rw [← hm.ofReal_variance_eq, hvi, ENNReal.ofReal_zero]
      have := (evariance_eq_zero_iff hm.aestronglyMeasurable.aemeasurable).1 he
      refine this.trans (Eventually.of_forall fun ω => ?_)
      simp [h0]
    have hz' : ∀ᵐ ω ∂P, ∀ i : Fin (n + 1), X (u i) ω = 0 := ae_all_iff.2 hz
    have hM : seqMax X u n =ᵐ[P] 0 := hz'.mono fun ω hω => by simp [seqMax, hω]
    have hint : ∫ ω, seqMax X u n ω ∂P = 0 := by
      rw [integral_congr_ae hM]; simp
    have hS : P {ω | t ≤ seqMax X u n ω - ∫ ω', seqMax X u n ω' ∂P} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hM] with ω hω
      simp only [not_le, hint, sub_zero]
      rw [hω]
      exact htpos
    rw [measureReal_def, hS, ENNReal.toReal_zero]
    exact (exp_pos _).le
  · have hσn2 : (√V) ^ 2 = V := sq_sqrt hV0
    have h := GaussConc.borellTIS_gaussianVector (Finset.univ_nonempty) hY (fun i => h0 _)
      (sqrt_nonneg V) hσn2 ht
    simp only [Finset.sup'_univ_eq_ciSup] at h
    refine h.trans (exp_le_exp.2 ?_)
    rw [hσn2, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith)

/-- **Borell–TIS inequality for the supremum of a centered Gaussian process over a countable
set** (Adler–Taylor, *Random Fields and Geometry*, Thm 2.1.1, p. 50; the reduction to finite
index sets by monotone convergence is that of Adler–Taylor's proof, p. 57). If
`E max_{i ≤ n} X (u i) ≤ C` for all `n`, the sequence is bounded for every `ω` and
`Var X (u k) ≤ σ²`, then `P(sup_k X (u k) - E sup_k X (u k) ≥ t) ≤ exp (-t² / (2σ²))`. -/
theorem borellTIS_iSup_seq (hX : IsGaussianProcess X P) (h0 : ∀ s, ∫ ω, X s ω ∂P = 0)
    (hb : ∀ ω, BddAbove (range fun k => X (u k) ω)) {C : ℝ}
    (hC : ∀ n, ∫ ω, seqMax X u n ω ∂P ≤ C) {σ : ℝ}
    (hvar : ∀ k, Var[X (u k); P] ≤ σ ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ (⨆ k, X (u k) ω) - ∫ ω', (⨆ k, X (u k) ω') ∂P} ≤
      exp (-t ^ 2 / (2 * σ ^ 2)) := by
  have hP := hX.isProbabilityMeasure
  obtain ⟨hFi, -⟩ := integrable_iSup_of_seqMax hX hb hC
  set F : Ω → ℝ := fun ω => ⨆ k, X (u k) ω with hF
  set m := ∫ ω, F ω ∂P
  have hm : Tendsto (fun n => ∫ ω, seqMax X u n ω ∂P) atTop (𝓝 m) :=
    integral_tendsto_of_tendsto_of_monotone (fun n => integrable_seqMax hX n) hFi
      (Eventually.of_forall fun ω => seqMax_mono ω)
      (Eventually.of_forall fun ω => tendsto_seqMax (hb ω))
  -- strict tails
  have hstrict : ∀ s : ℝ, 0 ≤ s → P {ω | s < F ω - m} ≤ ENNReal.ofReal
      (exp (-s ^ 2 / (2 * σ ^ 2))) := by
    intro s hs
    set B : ℕ → Set Ω := fun N => {ω | ∀ n ≥ N, s < seqMax X u n ω - ∫ ω', seqMax X u n ω' ∂P}
    have hBm : Monotone B := fun N N' hNN' ω hω n hn => hω n (hNN'.trans hn)
    have hsub : {ω | s < F ω - m} ⊆ ⋃ N, B N := by
      intro ω hω
      have ht' : Tendsto (fun n => seqMax X u n ω - ∫ ω', seqMax X u n ω' ∂P) atTop
          (𝓝 (F ω - m)) := (tendsto_seqMax (hb ω)).sub hm
      obtain ⟨N, hN⟩ := eventually_atTop.1 (ht'.eventually (lt_mem_nhds hω))
      exact mem_iUnion.2 ⟨N, hN⟩
    refine (measure_mono hsub).trans ?_
    rw [hBm.measure_iUnion]
    refine iSup_le fun N => ?_
    have hsubN : B N ⊆ {ω | s ≤ seqMax X u N ω - ∫ ω', seqMax X u N ω' ∂P} :=
      fun ω hω => le_of_lt (hω N le_rfl)
    refine (measure_mono hsubN).trans ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (borellTIS_seqMax hX h0 hvar hs N)
  rcases ht.eq_or_lt with rfl | htpos
  · calc _ ≤ 1 := measureReal_le_one
      _ = _ := by simp
  set s : ℕ → ℝ := fun k => t * (1 - 1 / ((k : ℝ) + 1))
  have hs0 : ∀ k, 0 ≤ s k := fun k => mul_nonneg ht (sub_nonneg.2 (by
    rw [div_le_one (by positivity)]; simp))
  have hslt : ∀ k, s k < t := fun k => by
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    simp only [s]; nlinarith
  have hst : Tendsto s atTop (𝓝 t) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
    simpa [s] using this.const_mul t
  have hbound : ∀ k, P.real {ω | t ≤ F ω - m} ≤ exp (-s k ^ 2 / (2 * σ ^ 2)) := by
    intro k
    refine ENNReal.toReal_le_of_le_ofReal (exp_pos _).le ?_
    exact (measure_mono fun ω (hω : t ≤ F ω - m) => ((hslt k).trans_le hω : s k < F ω - m)).trans
      (hstrict (s k) (hs0 k))
  have hlim : Tendsto (fun k => exp (-s k ^ 2 / (2 * σ ^ 2))) atTop
      (𝓝 (exp (-t ^ 2 / (2 * σ ^ 2)))) :=
    ((continuous_exp.comp ((continuous_pow 2).neg.div_const _)).tendsto t).comp hst
  exact ge_of_tendsto' hlim hbound

end SupTail

end LQGMetric
