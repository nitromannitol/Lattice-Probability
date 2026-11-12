/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E1

/-!
# LM Theorem 1.7, packet P-VAR (c): Efron–Stein with the resampled metric `D^S`, per `g`

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, Step 1 (l. 1011–1026): "let `D^S` be sampled
from the conditional law of `D` given `{D(·,·;S') : S' ≠ S}` and `D̃(·,·;S)` … so that
`(h, θ, D^S) =d (h, θ, D)`" and "By the Efron–Stein inequality … `Var[D(z,w;V)|h,θ] ≤
∑_S E[(D^S(z,w;V) − D(z,w;V))_+² | h,θ]`" ((5.1), (5.4)).

We work under one probability measure `ν` (later `ν = κ_g`, the conditional law of `D` given
`h = g`), with finitely many coordinates `Y d : ι → E` (later the square metrics) whose joint law is
the product of the marginals (L5.4), and `F = Φ ∘ Y` `ν`-a.s. (L5.3).

* `t17v_update_law`: if `y, y'` are independent with law `⊗ μ_j`, so is `y` with its `i`-th
  coordinate replaced by `y'_i`.
* `t17v_es` (LM (5.1), (5.4)): `Var_ν(F) ≤ ∫ d, ∑_i ∫ d', (Φ(Y d with Y_i d' in slot i) − F d)_+²`.
* `t17v_resample_exists` (LM l. 1013–1016): for `ν`-a.e. `d`, every `i` and `ν`-a.e. `d'`, the
  value `Φ(Y d with Y_i d' in slot i)` is `F(D^S)` for a metric `D^S` with exactly these
  coordinates which satisfies every relation `R(d, D^S)` that holds a.s. for *all* couplings of
  `ν` with itself (later the bi-Lipschitz bound (5.11), `t17e_bilip_measure`). `D^S` is sampled from
  `condDistrib id Y ν` at the resampled coordinates; its law is `ν`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

/-- the resampled coordinates `update y i (y' i)` -/
lemma t17v_measurable_update (i : ι) :
    Measurable fun q : (ι → E) × (ι → E) => Function.update q.1 i (q.2 i) := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact (measurable_pi_apply j).comp measurable_snd
  · simp only [Function.update_of_ne hj]
    exact (measurable_pi_apply j).comp measurable_fst

/-- replacing one coordinate of a product-distributed vector by an independent copy keeps the law -/
theorem t17v_update_law (μ : ι → Measure E) [∀ j, IsProbabilityMeasure (μ j)] (i : ι) :
    ((Measure.pi μ).prod (Measure.pi μ)).map (fun q => Function.update q.1 i (q.2 i)) =
      Measure.pi μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (t17v_measurable_update i) (MeasurableSet.univ_pi hs)]
  set s1 : ι → Set E := Function.update s i univ
  set s2 : ι → Set E := Function.update (fun _ => univ) i (s i)
  have hpre : (fun q : (ι → E) × (ι → E) => Function.update q.1 i (q.2 i)) ⁻¹' univ.pi s =
      univ.pi s1 ×ˢ univ.pi s2 := by
    ext q
    simp only [mem_preimage, mem_univ_pi, mem_prod, s1, s2]
    constructor
    · intro h
      refine ⟨fun j => ?_, fun j => ?_⟩
      · by_cases hj : j = i
        · subst hj; simp
        · have := h j; rwa [Function.update_of_ne hj] at this ⊢
      · by_cases hj : j = i
        · subst hj; have := h j; rwa [Function.update_self] at this ⊢
        · simp [Function.update_of_ne hj]
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; have := h2 j; rwa [Function.update_self] at this ⊢
      · have := h1 j; rwa [Function.update_of_ne hj] at this ⊢
  have hs1 : ∀ j, MeasurableSet (s1 j) := fun j => by
    by_cases hj : j = i
    · subst hj; simp [s1]
    · simp only [s1, Function.update_of_ne hj]; exact hs j
  have hs2 : ∀ j, MeasurableSet (s2 j) := fun j => by
    by_cases hj : j = i
    · subst hj; simp only [s2, Function.update_self]; exact hs j
    · simp [s2, Function.update_of_ne hj]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (s1 j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (s2 j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (s j)) (Finset.mem_univ i)]
  have e1 : ∏ j ∈ Finset.univ.erase i, μ j (s1 j) = ∏ j ∈ Finset.univ.erase i, μ j (s j) :=
    Finset.prod_congr rfl fun j hj => by
      simp only [s1, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have e2 : ∏ j ∈ Finset.univ.erase i, μ j (s2 j) = 1 :=
    Finset.prod_eq_one fun j hj => by
      simp only [s2, Function.update_of_ne (Finset.ne_of_mem_erase hj), measure_univ]
  simp only [s1, s2, Function.update_self, measure_univ, one_mul] at e1 e2 ⊢
  rw [e1, e2, mul_one, mul_comm]

variable {β : Type*} [MeasurableSpace β]

/-- **Efron–Stein under `ν`** (LM (5.1), (5.4), l. 1017–1026): if the coordinates `Y` are
independent under `ν` and `F = Φ ∘ Y` `ν`-a.s., then
`Var_ν(F) ≤ ∫ d, ∑_i ∫ d', (Φ(Y d with Y_i d' in slot i) − F d)_+² dν(d') dν(d)`. -/
theorem t17v_es (ν : Measure β) [IsProbabilityMeasure ν] {Y : β → ι → E} (hY : Measurable Y)
    (hprod : ν.map Y = Measure.pi fun j => ν.map fun d => Y d j) {F : β → ℝ} {Φ : (ι → E) → ℝ}
    (hΦ : Measurable Φ) (hFm : Measurable F) (hF : F =ᵐ[ν] Φ ∘ Y) (hF2 : MemLp F 2 ν) :
    ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν) ≤
      ∫⁻ d, ∑ i, ∫⁻ d', ENNReal.ofReal
        (max (Φ (Function.update (Y d) i (Y d' i)) - F d) 0 ^ 2) ∂ν ∂ν := by
  set μ : ι → Measure E := fun j => ν.map fun d => Y d j with hμ
  have : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    (Measure.isProbabilityMeasure_map_iff ((measurable_pi_apply j).comp hY).aemeasurable).2 inferInstance
  have hvar : variance F ν = variance Φ (Measure.pi μ) := by
    rw [variance_congr hF, ← hprod, variance_map hΦ.aemeasurable hY.aemeasurable]
  have hL : MemLp Φ 2 (Measure.pi μ) := by
    rw [← hprod, memLp_map_measure_iff hΦ.aestronglyMeasurable hY.aemeasurable]
    exact hF2.ae_eq hF
  have hes := t17e_es_pi μ hΦ hL
  rw [← hvar, variance_eq_integral hF2.aemeasurable] at hes
  have hpp : (Measure.pi μ).prod (Measure.pi μ) = (ν.prod ν).map (Prod.map Y Y) := by
    rw [← hprod, Measure.map_prod_map _ _ hY hY]
  set G : ι → (ι → E) × (ι → E) → ℝ := fun i p =>
    max (Φ (Function.update p.1 i (p.2 i)) - Φ p.1) 0 ^ 2 with hG
  have hGm : ∀ i, Measurable (G i) := fun i =>
    ((hΦ.comp (t17v_measurable_update i)).sub (hΦ.comp measurable_fst)).max measurable_const
      |>.pow_const 2
  have hGn : ∀ i p, 0 ≤ G i p := fun i p => sq_nonneg _
  have hF1 : ∀ᵐ p ∂ν.prod ν, F p.1 = Φ (Y p.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hF
  have hmeasH : ∀ i, Measurable fun p : β × β => ENNReal.ofReal
      (max (Φ (Function.update (Y p.1) i (Y p.2 i)) - F p.1) 0 ^ 2) := fun i =>
    ENNReal.measurable_ofReal.comp ((((hΦ.comp (t17v_measurable_update i)).comp
      ((hY.comp measurable_fst).prodMk (hY.comp measurable_snd))).sub
      (hFm.comp measurable_fst)).max measurable_const |>.pow_const 2)
  have hstep : ∀ i, ENNReal.ofReal (∫ p, G i p ∂((Measure.pi μ).prod (Measure.pi μ))) ≤
      ∫⁻ d, ∫⁻ d', ENNReal.ofReal
        (max (Φ (Function.update (Y d) i (Y d' i)) - F d) 0 ^ 2) ∂ν ∂ν := by
    intro i
    refine (t17e_ofReal_integral_le (hGn i)).trans_eq ?_
    rw [hpp, lintegral_map (f := fun x => ENNReal.ofReal (G i x))
      (ENNReal.measurable_ofReal.comp (hGm i)) (hY.prodMap hY)]
    rw [← lintegral_prod _ (hmeasH i).aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hF1] with p hp
    simp only [hG, Prod.map_fst, Prod.map_snd, hp]
  calc ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν)
      ≤ ENNReal.ofReal (∑ i, ∫ p, G i p ∂((Measure.pi μ).prod (Measure.pi μ))) :=
        ENNReal.ofReal_le_ofReal hes
    _ ≤ ∑ i, ENNReal.ofReal (∫ p, G i p ∂((Measure.pi μ).prod (Measure.pi μ))) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg (hGn i)).le
    _ ≤ ∑ i, ∫⁻ d, ∫⁻ d', ENNReal.ofReal
          (max (Φ (Function.update (Y d) i (Y d' i)) - F d) 0 ^ 2) ∂ν ∂ν :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = _ := by
        rw [lintegral_finset_sum]
        intro i _
        exact (hmeasH i).lintegral_prod_right'

end LQGMetric.LM
