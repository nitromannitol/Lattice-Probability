/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.ResolventCoupling
import LatticeProb.Prob.MarkovPathKernelStrong

/-!
# The resolvent of a Markov path family, read at a stopping time

Let `K : E → Prob C(ℝ≥0, E)` be a continuous family of path laws with the Markov property at
deterministic times, and let `σ` be a stopping time of the filtration of stopped paths such that
stopping a path at `σ` does not change `σ`.  Write `R f (u) = ∫ ∫₀^∞ e^{-λ t} f (x_t) dt d(K u)(x)`
for the resolvent.  The strong Markov property at `σ` gives
`R f (v) ≈ ∫ R f (x_σ) d(K v)(x)`, with an error at most `2 M r + 2 (M/λ) K v (σ > r)` for
`|f| ≤ M`:

* `abs_discOcc_sub_exp_mul_le`: deterministic splitting of the discounted occupation at time `a`;
* `abs_pathResolvent_sub_exit_le`: the resolvent estimate.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The discounted occupation integral `∫₀^∞ e^{-λ t} f (x_t) dt` of a continuous path. -/
def pathDiscOcc (lam : ℝ) (f : E → ℝ) (x : C(ℝ≥0, E)) : ℝ := discOcc lam f (fun u => x u)

/-- The resolvent `u ↦ ∫ pathDiscOcc λ f d(K u)` of a family of path laws. -/
def pathResolvent (K : E → ProbabilityMeasure C(ℝ≥0, E)) (lam : ℝ) (f : E → ℝ) (u : E) : ℝ :=
  ∫ w, pathDiscOcc lam f w ∂(K u : Measure C(ℝ≥0, E))

omit [SecondCountableTopology E] in
theorem measurable_pathDiscOcc {f : E → ℝ} (hf : Measurable f) (lam : ℝ) :
    Measurable (pathDiscOcc lam f : C(ℝ≥0, E) → ℝ) := by
  have hev : Continuous fun q : C(ℝ≥0, E) × ℝ≥0 => q.1 q.2 := ContinuousEval.continuous_eval
  have h : Measurable fun q : C(ℝ≥0, E) × ℝ => Real.exp (-lam * q.2) * f (q.1 q.2.toNNReal) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (hf.comp (hev.measurable.comp (measurable_fst.prodMk
        (measurable_real_toNNReal.comp measurable_snd))))
  exact (h.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioi 0))).measurable

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem abs_pathDiscOcc_le {f : E → ℝ} {M lam : ℝ} (hlam : 0 < lam) (hM : ∀ e, |f e| ≤ M)
    (x : C(ℝ≥0, E)) : |pathDiscOcc lam f x| ≤ M / lam :=
  abs_discOcc_le hlam hM _

omit [SecondCountableTopology E] in
theorem measurable_pathResolvent {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    {f : E → ℝ} (hf : Measurable f) (lam : ℝ) : Measurable (pathResolvent K lam f) := by
  have hmeas : Measurable fun u : E => (K u : Measure C(ℝ≥0, E)) :=
    measurable_measure_comp_of_continuous hK measurable_id
  let κ : ProbabilityTheory.Kernel E C(ℝ≥0, E) := ⟨fun u => (K u : Measure C(ℝ≥0, E)), hmeas⟩
  exact ((measurable_pathDiscOcc hf lam).stronglyMeasurable.integral_kernel (κ := κ)).measurable

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem abs_pathResolvent_le {K : E → ProbabilityMeasure C(ℝ≥0, E)} {f : E → ℝ} {M lam : ℝ}
    (hlam : 0 < lam) (hM : ∀ e, |f e| ≤ M) (u : E) : |pathResolvent K lam f u| ≤ M / lam := by
  have h := norm_integral_le_of_norm_le_const (μ := (K u : Measure C(ℝ≥0, E)))
    (f := pathDiscOcc lam f) (C := M / lam)
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_pathDiscOcc_le hlam hM x)
  simpa [pathResolvent, Real.norm_eq_abs] using h

omit [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- Deterministic splitting of the discounted occupation at time `a`: the part before `a` is at most
`M a`. -/
theorem abs_discOcc_sub_exp_mul_le {f : E → ℝ} {M lam : ℝ} (hlam : 0 < lam)
    (hM : ∀ e, |f e| ≤ M) {x : ℝ≥0 → E} (hx : Measurable fun u : ℝ≥0 => f (x u)) (a : ℝ≥0) :
    |discOcc lam f x - Real.exp (-lam * a) * discOcc lam f (fun u => x (a + u))| ≤ M * a := by
  rw [discOcc_split hlam hM hx a, add_sub_cancel_right]
  have h1 := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun t : ℝ => Real.exp (-lam * t) * f (x t.toNNReal)) (C := M) measure_Ioc_lt_top
    (Filter.Eventually.of_forall fun t ht => by
      have hexp : Real.exp (-lam * t) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [ht.1])
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-lam * t) * |f (x t.toNNReal)| ≤ 1 * M :=
            mul_le_mul hexp (hM _) (abs_nonneg _) zero_le_one
        _ = M := one_mul M)
  rw [measureReal_def] at h1
  rw [show (volume (Ioc (0 : ℝ) a)).toReal = a by
    rw [← measureReal_def, Real.volume_real_Ioc_of_le a.coe_nonneg, sub_zero]] at h1
  simpa [Real.norm_eq_abs] using h1

/-- **The resolvent read at a stopping time.**  Let `K` be a continuous family of path laws with the
Markov property at deterministic times at `v`, and let `σ` be a stopping time of the filtration of
stopped paths with `σ (x (· ∧ σ x)) = σ x` when `σ x < ∞`.  For `|f| ≤ M` and `r ≥ 0`,
`|R f (v) - ∫ R f (x_σ) d(K v)(x)| ≤ 2 M r + 2 (M / λ) (K v) {σ > r}`. -/
theorem abs_pathResolvent_sub_exit_le {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    {v : E} (hMv : ∀ t, MarkovAt K v t) {σ : C(ℝ≥0, E) → ℝ≥0∞}
    (hσ : IsStoppingTime (stoppedPathFiltration (E := E)) σ)
    (hstop : ∀ x, σ x < ⊤ → σ (stopPath x (σ x).toNNReal) = σ x)
    {f : E → ℝ} (hf : Measurable f) {M lam : ℝ} (hlam : 0 < lam) (hM : ∀ e, |f e| ≤ M)
    (r : ℝ≥0) :
    |pathResolvent K lam f v - ∫ x, pathResolvent K lam f (x (σ x).toNNReal)
        ∂(K v : Measure C(ℝ≥0, E))| ≤
      2 * M * r + 2 * (M / lam) * ((K v : Measure C(ℝ≥0, E)) {x | (r : ℝ≥0∞) < σ x}).toReal := by
  classical
  have hσm : Measurable σ := measurable_of_isStoppingTime_stoppedPath hσ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM v)
  have hML : 0 ≤ M / lam := div_nonneg hM0 hlam.le
  have hev : Continuous fun q : C(ℝ≥0, E) × ℝ≥0 => q.1 q.2 := ContinuousEval.continuous_eval
  have ham : Measurable fun x : C(ℝ≥0, E) => (σ x).toNNReal := hσm.ennreal_toNNReal
  have hYm : Measurable fun x : C(ℝ≥0, E) => x (σ x).toNNReal :=
    hev.measurable.comp (measurable_id.prodMk ham)
  have hΦm : Measurable (pathDiscOcc lam f : C(ℝ≥0, E) → ℝ) := measurable_pathDiscOcc hf lam
  have hgm : Measurable (pathResolvent K lam f) := measurable_pathResolvent hK hf lam
  have hgY : Measurable fun x : C(ℝ≥0, E) => pathResolvent K lam f (x (σ x).toNNReal) :=
    hgm.comp hYm
  have hexpm : Measurable fun x : C(ℝ≥0, E) => Real.exp (-lam * ((σ x).toNNReal : ℝ)) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_coe_nnreal_real.comp ham))
  have hshm : Measurable fun x : C(ℝ≥0, E) => pathShift x (σ x).toNNReal :=
    continuous_pathShift_uncurry.measurable.comp (measurable_id.prodMk ham)
  have hT1m : Measurable fun x : C(ℝ≥0, E) =>
      Real.exp (-lam * ((σ x).toNNReal : ℝ)) * pathDiscOcc lam f (pathShift x (σ x).toNNReal) :=
    hexpm.mul (hΦm.comp hshm)
  have hT2m : Measurable fun x : C(ℝ≥0, E) =>
      Real.exp (-lam * ((σ x).toNNReal : ℝ)) * pathResolvent K lam f (x (σ x).toNNReal) :=
    hexpm.mul hgY
  have hΦb := abs_pathDiscOcc_le (E := E) (f := f) hlam hM
  have hgb := abs_pathResolvent_le (K := K) (f := f) hlam hM
  have hexp1 : ∀ x : C(ℝ≥0, E), Real.exp (-lam * ((σ x).toNNReal : ℝ)) ≤ 1 := fun x =>
    Real.exp_le_one_iff.2 (by
      have := mul_nonneg hlam.le (NNReal.coe_nonneg (σ x).toNNReal)
      linarith)
  have hexp0 : ∀ x : C(ℝ≥0, E), 0 ≤ Real.exp (-lam * ((σ x).toNNReal : ℝ)) := fun x =>
    (Real.exp_pos _).le
  have hint : ∀ {h : C(ℝ≥0, E) → ℝ} {B : ℝ}, Measurable h → (∀ x, |h x| ≤ B) →
      Integrable h (K v : Measure C(ℝ≥0, E)) := fun hm hb =>
    Integrable.of_bound hm.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
  have hT1b : ∀ x : C(ℝ≥0, E),
      |Real.exp (-lam * ((σ x).toNNReal : ℝ)) * pathDiscOcc lam f (pathShift x (σ x).toNNReal)| ≤
        M / lam := fun x => by
    rw [abs_mul, abs_of_nonneg (hexp0 x)]
    calc _ ≤ 1 * (M / lam) := mul_le_mul (hexp1 x) (hΦb _) (abs_nonneg _) zero_le_one
      _ = M / lam := one_mul _
  have hT2b : ∀ x : C(ℝ≥0, E),
      |Real.exp (-lam * ((σ x).toNNReal : ℝ)) * pathResolvent K lam f (x (σ x).toNNReal)| ≤
        M / lam := fun x => by
    rw [abs_mul, abs_of_nonneg (hexp0 x)]
    calc _ ≤ 1 * (M / lam) := mul_le_mul (hexp1 x) (hgb _) (abs_nonneg _) zero_le_one
      _ = M / lam := one_mul _
  have hPle : ∀ S : Set C(ℝ≥0, E), ((K v : Measure C(ℝ≥0, E)) S).toReal ≤ 1 := fun S => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one (μ := (K v : Measure C(ℝ≥0, E))) (s := S))
    simpa using this
  -- the event `{σ ≤ r}`
  set G : Set C(ℝ≥0, E) := {x | σ x ≤ (r : ℝ≥0∞)} with hG
  have hGm : MeasurableSet G := measurableSet_le hσm measurable_const
  have hGt : ∀ x ∈ G, σ x < ⊤ := fun x hx => lt_of_le_of_lt hx ENNReal.coe_lt_top
  have hGc : Gᶜ = {x | (r : ℝ≥0∞) < σ x} := by
    ext x
    simp [hG]
  have har : ∀ x ∈ G, ((σ x).toNNReal : ℝ) ≤ r := fun x hx => by
    have : (σ x).toNNReal ≤ r :=
      (ENNReal.toNNReal_mono ENNReal.coe_ne_top hx).trans_eq (ENNReal.toNNReal_coe r)
    exact_mod_cast this
  -- step 1: before the exit time
  have hE1 : |∫ x in G, pathDiscOcc lam f x ∂(K v : Measure C(ℝ≥0, E)) -
      ∫ x in G, Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
        pathDiscOcc lam f (pathShift x (σ x).toNNReal) ∂(K v : Measure C(ℝ≥0, E))| ≤ M * r := by
    rw [← integral_sub (hint hΦm hΦb).integrableOn (hint hT1m hT1b).integrableOn]
    have h1 := norm_setIntegral_le_of_norm_le_const_ae' (μ := (K v : Measure C(ℝ≥0, E))) (s := G)
      (f := fun x => pathDiscOcc lam f x - Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
        pathDiscOcc lam f (pathShift x (σ x).toNNReal)) (C := M * r) (measure_lt_top _ _)
      (Filter.Eventually.of_forall fun x hx => by
        have h2 := abs_discOcc_sub_exp_mul_le hlam hM
          (x := fun u => x u) (hf.comp x.continuous.measurable) (σ x).toNNReal
        rw [Real.norm_eq_abs]
        refine h2.trans ?_
        exact mul_le_mul_of_nonneg_left (har x hx) hM0)
    rw [measureReal_def] at h1
    rw [Real.norm_eq_abs] at h1
    calc _ ≤ M * r * ((K v : Measure C(ℝ≥0, E)) G).toReal := h1
      _ ≤ M * r * 1 := mul_le_mul_of_nonneg_left (hPle G) (mul_nonneg hM0 r.coe_nonneg)
      _ = M * r := mul_one _
  -- step 2: strong Markov property at `σ`
  have hE2 : ∫ x in G, Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
        pathDiscOcc lam f (pathShift x (σ x).toNNReal) ∂(K v : Measure C(ℝ≥0, E)) =
      ∫ x in G, Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
        pathResolvent K lam f (x (σ x).toNNReal) ∂(K v : Measure C(ℝ≥0, E)) := by
    let G2 : C(ℝ≥0, E) × C(ℝ≥0, E) → ℝ := fun q =>
      G.indicator (fun p => Real.exp (-lam * ((σ p).toNNReal : ℝ))) q.1 * pathDiscOcc lam f q.2
    have hG2m : Measurable G2 :=
      ((hexpm.indicator hGm).comp measurable_fst).mul (hΦm.comp measurable_snd)
    have hG2b : ∀ q, ‖G2 q‖ ≤ M / lam := fun q => by
      rw [Real.norm_eq_abs, abs_mul]
      have h0 : |G.indicator (fun p => Real.exp (-lam * ((σ p).toNNReal : ℝ))) q.1| ≤ 1 := by
        by_cases hq : q.1 ∈ G
        · rw [Set.indicator_of_mem hq, abs_of_nonneg (hexp0 _)]
          exact hexp1 _
        · rw [Set.indicator_of_notMem hq]
          simp
      calc _ ≤ 1 * (M / lam) := mul_le_mul h0 (hΦb _) (abs_nonneg _) zero_le_one
        _ = M / lam := one_mul _
    have hSM := strongMarkov_setIntegral_lt_top hK hMv hσ hG2m hG2b
    have hlt : MeasurableSet {x : C(ℝ≥0, E) | σ x < ⊤} := measurableSet_lt hσm measurable_const
    have hL : ∫ x in {x : C(ℝ≥0, E) | σ x < ⊤}, G2 (stopPath x (σ x).toNNReal,
        pathShift x (σ x).toNNReal) ∂(K v : Measure C(ℝ≥0, E)) =
        ∫ x in {x : C(ℝ≥0, E) | σ x < ⊤}, G.indicator (fun x => Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
          pathDiscOcc lam f (pathShift x (σ x).toNNReal)) x ∂(K v : Measure C(ℝ≥0, E)) := by
      refine setIntegral_congr_fun hlt fun x hx => ?_
      have hx' : σ x < ⊤ := hx
      have hmem : stopPath x (σ x).toNNReal ∈ G ↔ x ∈ G := by
        simp only [hG, Set.mem_ofPred_eq, hstop x hx']
      by_cases hxG : x ∈ G
      · rw [Set.indicator_of_mem hxG]
        simp only [G2]
        rw [Set.indicator_of_mem (hmem.2 hxG), hstop x hx']
      · rw [Set.indicator_of_notMem hxG]
        simp only [G2]
        rw [Set.indicator_of_notMem (fun h => hxG (hmem.1 h))]
        simp
    have hR : ∫ x in {x : C(ℝ≥0, E) | σ x < ⊤}, ∫ w, G2 (stopPath x (σ x).toNNReal, w)
        ∂(K (x (σ x).toNNReal) : Measure C(ℝ≥0, E)) ∂(K v : Measure C(ℝ≥0, E)) =
        ∫ x in {x : C(ℝ≥0, E) | σ x < ⊤}, G.indicator (fun x => Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
          pathResolvent K lam f (x (σ x).toNNReal)) x ∂(K v : Measure C(ℝ≥0, E)) := by
      refine setIntegral_congr_fun hlt fun x hx => ?_
      have hx' : σ x < ⊤ := hx
      have hmem : stopPath x (σ x).toNNReal ∈ G ↔ x ∈ G := by
        simp only [hG, Set.mem_ofPred_eq, hstop x hx']
      by_cases hxG : x ∈ G
      · rw [Set.indicator_of_mem hxG]
        simp only [G2]
        rw [Set.indicator_of_mem (hmem.2 hxG), hstop x hx', integral_const_mul]
        rfl
      · rw [Set.indicator_of_notMem hxG]
        simp only [G2]
        rw [Set.indicator_of_notMem (fun h => hxG (hmem.1 h))]
        simp
    rw [hL, hR] at hSM
    have hsub : {x : C(ℝ≥0, E) | σ x < ⊤} ∩ G = G := Set.inter_eq_right.2 hGt
    rw [setIntegral_indicator hGm, hsub, setIntegral_indicator hGm, hsub] at hSM
    exact hSM
  -- step 3: replacing the discount by one
  have hE3 : |∫ x in G, Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
        pathResolvent K lam f (x (σ x).toNNReal) ∂(K v : Measure C(ℝ≥0, E)) -
      ∫ x in G, pathResolvent K lam f (x (σ x).toNNReal) ∂(K v : Measure C(ℝ≥0, E))| ≤ M * r := by
    rw [← integral_sub (hint hT2m hT2b).integrableOn (hint hgY fun x => hgb _).integrableOn]
    have h1 := norm_setIntegral_le_of_norm_le_const_ae' (μ := (K v : Measure C(ℝ≥0, E))) (s := G)
      (f := fun x => Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
        pathResolvent K lam f (x (σ x).toNNReal) - pathResolvent K lam f (x (σ x).toNNReal))
      (C := M * r) (measure_lt_top _ _)
      (Filter.Eventually.of_forall fun x hx => by
        have h2 := abs_exp_neg_mul_sub_le hlam (NNReal.coe_nonneg (σ x).toNNReal) (le_refl (0 : ℝ))
        rw [mul_zero, Real.exp_zero, sub_zero] at h2
        have h3 : Real.exp (-lam * ((σ x).toNNReal : ℝ)) *
            pathResolvent K lam f (x (σ x).toNNReal) - pathResolvent K lam f (x (σ x).toNNReal) =
            (Real.exp (-lam * ((σ x).toNNReal : ℝ)) - 1) *
              pathResolvent K lam f (x (σ x).toNNReal) := by ring
        rw [Real.norm_eq_abs, h3, abs_mul]
        have h4 : lam * ((σ x).toNNReal : ℝ) * (M / lam) ≤ M * r := by
          have : lam * ((σ x).toNNReal : ℝ) * (M / lam) = M * ((σ x).toNNReal : ℝ) := by
            field_simp
          rw [this]
          exact mul_le_mul_of_nonneg_left (har x hx) hM0
        calc _ ≤ (lam * |((σ x).toNNReal : ℝ)|) * (M / lam) := by
              refine mul_le_mul (by simpa using h2) (hgb _) (abs_nonneg _) (by positivity)
          _ = lam * ((σ x).toNNReal : ℝ) * (M / lam) := by rw [abs_of_nonneg (NNReal.coe_nonneg _)]
          _ ≤ M * r := h4)
    rw [measureReal_def, Real.norm_eq_abs] at h1
    calc _ ≤ M * r * ((K v : Measure C(ℝ≥0, E)) G).toReal := h1
      _ ≤ M * r * 1 := mul_le_mul_of_nonneg_left (hPle G) (mul_nonneg hM0 r.coe_nonneg)
      _ = M * r := mul_one _
  -- step 4: the complement of `{σ ≤ r}`
  have htail : ∀ {h : C(ℝ≥0, E) → ℝ}, (∀ x, |h x| ≤ M / lam) →
      |∫ x in Gᶜ, h x ∂(K v : Measure C(ℝ≥0, E))| ≤
        M / lam * ((K v : Measure C(ℝ≥0, E)) {x | (r : ℝ≥0∞) < σ x}).toReal := fun {h} hb => by
    have h1 := norm_setIntegral_le_of_norm_le_const_ae' (μ := (K v : Measure C(ℝ≥0, E))) (s := Gᶜ)
      (f := h) (C := M / lam) (measure_lt_top _ _)
      (Filter.Eventually.of_forall fun x _ => by simpa [Real.norm_eq_abs] using hb x)
    rw [measureReal_def, Real.norm_eq_abs] at h1
    rw [← hGc]
    exact h1
  have hT := htail hΦb
  have hT' := htail (h := fun x => pathResolvent K lam f (x (σ x).toNNReal)) fun x => hgb _
  -- assembly
  have hsplitΦ := integral_add_compl hGm (hint hΦm hΦb) (μ := (K v : Measure C(ℝ≥0, E)))
  have hsplitg := integral_add_compl hGm (hint hgY fun x => hgb _) (μ := (K v : Measure C(ℝ≥0, E)))
  have hRdef : pathResolvent K lam f v =
      ∫ x, pathDiscOcc lam f x ∂(K v : Measure C(ℝ≥0, E)) := rfl
  rw [hRdef, ← hsplitΦ, ← hsplitg]
  rw [hE2] at hE1
  have a1 := abs_le.1 hE1
  have a2 := abs_le.1 hE3
  have a3 := abs_le.1 hT
  have a4 := abs_le.1 hT'
  rw [abs_le]
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

end LatticeProb

end
