/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/SupTailBorell.lean.
-/
import LatticeProb.Prob.GaussSupTailBorell
import LatticeProb.Prob.GaussBorellVector

/-!
# Borell–TIS inequality for countable suprema of a Gaussian process

For a centred Gaussian process `X : T → Ω → ℝ` and a sequence of indices `u : ℕ → T`, this file
proves the upper tail bound `P(sup_k X (u k) − E sup_k X (u k) ≥ t) ≤ exp (−t² / (2σ²))`, where
`σ² ≥ Var X (u k)` for every `k`.

* `borellTIS_seqMax` is the bound for the running maxima `max_{i ≤ n} X (u i)`, obtained from the
  finite-index inequality `GaussConc.borellTIS_gaussianVector`.
* `borellTIS_iSup_seq` passes to the supremum by monotone limits. Its hypotheses are stated as in
  the source: `hb` requires the sequence to be bounded above for every `ω` (not almost surely), and
  `hC` assumes a uniform bound `C` on the expectations of the running maxima. The bound `C` is an
  input here, not derived from the boundedness, so this is weaker than the textbook statement that
  derives it.

The nonvacuity example instantiates all hypotheses with the identity process on `ℝ` under the
standard Gaussian law, repeated along `ℕ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace LatticeProb.GaussConc.SupTail

variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {X : T → Ω → ℝ} {u : ℕ → T}

/-- Borell–TIS for the running maxima `max_{i ≤ n} X (u i)`, with any upper bound
`σ² ≥ Var X (u k)` on the variances of the indices. -/
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

/-- Borell–TIS inequality for the supremum of a centred Gaussian process over a countable index
sequence. Assumptions:

* `hb` says the sequence `X (u k) ω` is bounded above for every `ω` (pointwise, not almost surely);
* `hC` says `E max_{i ≤ n} X (u i) ≤ C` for all `n`, a uniform bound on the expected running
  maxima, which is assumed here and not derived from `hb`;
* `hvar` bounds the variances `Var X (u k)` by `σ²`.

Conclusion: `P(sup_k X (u k) − E sup_k X (u k) ≥ t) ≤ exp (−t² / (2σ²))` for `t ≥ 0`. When `σ = 0`
and `t > 0` the right-hand side is `exp 0 = 1`, so the bound is trivial but still true. -/
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

namespace BorellSeqExample

/-- The identity process on `ℝ`, repeated at every index, is a Gaussian process under the standard
Gaussian law: each finite family is the image of one Gaussian variable under a continuous linear
map. -/
lemma isGaussianProcess_repeat :
    IsGaussianProcess (fun (_ : ℕ) (ω : ℝ) => ω) (gaussianReal 0 1) := by
  refine ⟨fun I => ?_⟩
  let L : ℝ →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ
  exact (IsGaussian.hasGaussianLaw_id.map L)

/-- Nonvacuity for `borellTIS_iSup_seq`: the repeated identity process under the standard Gaussian
law satisfies every hypothesis, with `σ = 1` and `C = 0`, and the bound applies. -/
example {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {ω : ℝ | t ≤ (⨆ _ : ℕ, ω) - ∫ ω', (⨆ _ : ℕ, ω') ∂(gaussianReal 0 1)} ≤
      exp (-t ^ 2 / (2 * 1 ^ 2)) := by
  have h0 : ∀ s : ℕ, ∫ ω, (fun (_ : ℕ) (ω : ℝ) => ω) s ω ∂(gaussianReal 0 1) = 0 :=
    fun _ => integral_id_gaussianReal
  have hb : ∀ ω : ℝ, BddAbove (range fun k : ℕ => (fun (_ : ℕ) (ω : ℝ) => ω) (id k) ω) :=
    fun ω => ⟨ω, by rintro _ ⟨k, rfl⟩; exact le_rfl⟩
  have hC : ∀ n : ℕ, ∫ ω, seqMax (fun (_ : ℕ) (ω : ℝ) => ω) id n ω ∂(gaussianReal 0 1) ≤ 0 := by
    intro n
    simp [seqMax, integral_id_gaussianReal]
  have hvar : ∀ k : ℕ, Var[(fun (_ : ℕ) (ω : ℝ) => ω) (id k); gaussianReal 0 1] ≤ 1 ^ 2 := by
    intro k
    simp
  exact borellTIS_iSup_seq (X := fun (_ : ℕ) (ω : ℝ) => ω) (u := id) isGaussianProcess_repeat
    h0 hb hC hvar ht

end BorellSeqExample

end LatticeProb.GaussConc.SupTail
