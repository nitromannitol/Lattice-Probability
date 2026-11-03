/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaExistenceTRL at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadius
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# M4-A1, part 0: the two-radius lemma with a planar index set

Blueprint node M4-A1 (`blueprint/M4_BLUEPRINT.md`): the area analogue of M4-B2.

`TwoRadius.trl_core_bound` is stated for index sets `S ⊆ ℝ`. For the area measure the index set
is a region `S ⊆ ℂ`, and the decorrelation beyond distance `δ` holds for `‖t - u‖ ≥ δ`. The only
place where the dimension enters is the measure of the `δ`-neighbourhood of the diagonal:
in `ℂ` it is at most `π δ² |S|` (`measureReal_near_diag_le_C`), which is what makes the planar
lemma work for every `γ < 2`.

* `TRLHypC`: the Gaussian hypotheses (same as `TwoRadius.TRLHyp`, planar index).
* `trlC_core_bound`: `E|∫_S f D| ≤ √(Mg · D) + Mb |S|` for any bound `D` on the
  near-diagonal measure; the one-point estimates are reused from `TwoRadius` through the
  singleton reduction `TRLHypC.point`.
* `trlC_bound_area`: the area specialization (`γ ↦ 2γ`, truncation level `α = 2 + γ`), giving
  the exponents `e₁° = 2 - γ² + θ²/2` (`θ = max 0 ((3γ-2)/2)`) and `e₂° = (2-γ)²/8` of
  blueprint §4 once `L = ½ log (1/ε)` and `δ ≍ ε`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace TwoRadiusC

open TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Gaussian-level hypotheses of the planar two-radius lemma. -/
structure TRLHypC (P : Measure Ω) (S : Set ℂ) (δ K W : ℝ) (L : ℂ → ℝ) (v w : ℂ → ℝ≥0)
    (U Δ : ℂ → Ω → ℝ) : Prop where
  measU : Measurable (fun p : ℂ × Ω => U p.1 p.2)
  measΔ : Measurable (fun p : ℂ × Ω => Δ p.1 p.2)
  measL : Measurable L
  measw : Measurable w
  lawU : ∀ t ∈ S, HasLaw (U t) (gaussianReal 0 (v t)) P
  lawΔ : ∀ t ∈ S, HasLaw (Δ t) (gaussianReal 0 (w t)) P
  varU : ∀ t ∈ S, (v t : ℝ) ≤ 2 * L t + K
  varΔ : ∀ t ∈ S, (w t : ℝ) ≤ W
  indep : ∀ t ∈ S, IndepFun (Δ t) (U t) P
  decor : ∀ t ∈ S, ∀ u ∈ S, δ ≤ ‖t - u‖ →
    IndepFun (Δ t) (fun ω => (U t ω, U u ω, Δ u ω)) P

/-- The density difference `f t · A_t · (1 - Y_t)` at a point `t ∈ ℂ`. -/
noncomputable def dC (γ : ℝ) (f L : ℂ → ℝ) (w : ℂ → ℝ≥0) (U Δ : ℂ → Ω → ℝ) (t : ℂ)
    (ω : Ω) : ℝ :=
  f t * (exp (-(γ ^ 2 / 4) * L t + γ / 2 * U t ω) * tiltY γ (w t) (Δ t ω))

/-- Good part of `dC`. -/
noncomputable def gC (γ α : ℝ) (f L : ℂ → ℝ) (w : ℂ → ℝ≥0) (U Δ : ℂ → Ω → ℝ) (t : ℂ)
    (ω : Ω) : ℝ :=
  f t * goodA γ α (L t) (U t ω) * tiltY γ (w t) (Δ t ω)

/-- Bad part of `dC`. -/
noncomputable def bC (γ α : ℝ) (f L : ℂ → ℝ) (w : ℂ → ℝ≥0) (U Δ : ℂ → Ω → ℝ) (t : ℂ)
    (ω : Ω) : ℝ :=
  f t * badA γ α (L t) (U t ω) * tiltY γ (w t) (Δ t ω)

omit [MeasurableSpace Ω] in
lemma dC_eq (γ α : ℝ) (f L : ℂ → ℝ) (w : ℂ → ℝ≥0) (U Δ : ℂ → Ω → ℝ) (t : ℂ) (ω : Ω) :
    dC γ f L w U Δ t ω = gC γ α f L w U Δ t ω + bC γ α f L w U Δ t ω := by
  unfold dC gC bC
  rw [← goodA_add_badA γ α (L t) (U t ω)]
  ring

section Pointwise

variable {P : Measure Ω} {S : Set ℂ} {δ K W : ℝ} {L f : ℂ → ℝ} {v w : ℂ → ℝ≥0}
  {U Δ : ℂ → Ω → ℝ} {γ α : ℝ}

lemma TRLHypC.measurable_U (h : TRLHypC P S δ K W L v w U Δ) (t : ℂ) : Measurable (U t) :=
  h.measU.comp (measurable_const.prodMk measurable_id)

lemma TRLHypC.measurable_Δ (h : TRLHypC P S δ K W L v w U Δ) (t : ℂ) : Measurable (Δ t) :=
  h.measΔ.comp (measurable_const.prodMk measurable_id)

/-- Singleton reduction: at a point `t ∈ S`, the one-point data form a (real-indexed)
`TRLHyp` on `{0}`, so the one-point estimates of `TwoRadius` apply. -/
lemma TRLHypC.point (h : TRLHypC P S δ K W L v w U Δ) {t : ℂ} (ht : t ∈ S) :
    TRLHyp P {0} 1 K W (fun _ => L t) (fun _ => v t) (fun _ => w t) (fun _ => U t)
      (fun _ => Δ t) where
  measU := (h.measurable_U t).comp measurable_snd
  measΔ := (h.measurable_Δ t).comp measurable_snd
  measL := measurable_const
  measw := measurable_const
  lawU := fun _ _ => h.lawU t ht
  lawΔ := fun _ _ => h.lawΔ t ht
  varU := fun _ _ => h.varU t ht
  varΔ := fun _ _ => h.varΔ t ht
  indep := fun _ _ => h.indep t ht
  decor := by
    intro s hs u hu hsu
    rw [Set.mem_singleton_iff] at hs hu
    subst hs; subst hu
    norm_num at hsu

lemma measurable_gC (hf : Measurable f) (h : TRLHypC P S δ K W L v w U Δ) :
    Measurable (fun p : ℂ × Ω => gC γ α f L w U Δ p.1 p.2) := by
  unfold gC
  exact ((hf.comp measurable_fst).mul ((measurable_goodA₂ γ α).comp
    ((h.measL.comp measurable_fst).prodMk h.measU))).mul
    ((continuous_tiltY₂ γ).measurable.comp
      ((measurable_coe_nnreal_real.comp (h.measw.comp measurable_fst)).prodMk h.measΔ))

lemma measurable_bC (hf : Measurable f) (h : TRLHypC P S δ K W L v w U Δ) :
    Measurable (fun p : ℂ × Ω => bC γ α f L w U Δ p.1 p.2) := by
  unfold bC
  exact ((hf.comp measurable_fst).mul ((measurable_badA₂ γ α).comp
    ((h.measL.comp measurable_fst).prodMk h.measU))).mul
    ((continuous_tiltY₂ γ).measurable.comp
      ((measurable_coe_nnreal_real.comp (h.measw.comp measurable_fst)).prodMk h.measΔ))

lemma measurable_gC_t (hf : Measurable f) (h : TRLHypC P S δ K W L v w U Δ) (t : ℂ) :
    Measurable (gC γ α f L w U Δ t) :=
  (measurable_gC hf h).comp (measurable_const.prodMk measurable_id)

variable [IsProbabilityMeasure P]

lemma integral_gC_sq_le {θ M : ℝ} (hθ : 0 ≤ θ) (h : TRLHypC P S δ K W L v w U Δ)
    {t : ℂ} (ht : t ∈ S) (hM : |f t| ≤ M) :
    ∫ ω, gC γ α f L w U Δ t ω ^ 2 ∂P
      ≤ M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) * (exp ((γ - θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 2) + θ * α + (γ - θ) ^ 2) * L t))) :=
  integral_trlG_sq_le (f := fun _ => f t) hθ (h.point ht) (Set.mem_singleton 0) hM

lemma integral_abs_bC_le {θ M : ℝ} (hθ : 0 ≤ θ) (h : TRLHypC P S δ K W L v w U Δ)
    {t : ℂ} (ht : t ∈ S) (hM : |f t| ≤ M) :
    ∫ ω, |bC γ α f L w U Δ t ω| ∂P
      ≤ M * (2 * (exp ((γ / 2 + θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 4) - θ * α + (γ / 2 + θ) ^ 2) * L t))) :=
  integral_abs_trlB_le (f := fun _ => f t) hθ (h.point ht) (Set.mem_singleton 0) hM

lemma memLp_gC (hγ : 0 ≤ γ) (h : TRLHypC P S δ K W L v w U Δ) {t : ℂ} (ht : t ∈ S) :
    MemLp (gC γ α f L w U Δ t) 2 P :=
  memLp_trlG (f := fun _ => f t) hγ measurable_const (h.point ht) (Set.mem_singleton 0)

lemma integrable_bC (h : TRLHypC P S δ K W L v w U Δ) {t : ℂ} (ht : t ∈ S) :
    Integrable (bC γ α f L w U Δ t) P :=
  integrable_trlB (f := fun _ => f t) measurable_const (h.point ht) (Set.mem_singleton 0)

omit [IsProbabilityMeasure P] in
/-- Decorrelation of the good part beyond distance `δ` (planar index). -/
lemma integral_gC_mul_eq_zero (h : TRLHypC P S δ K W L v w U Δ)
    {t u : ℂ} (ht : t ∈ S) (hu : u ∈ S) (htu : δ ≤ ‖t - u‖) :
    ∫ ω, gC γ α f L w U Δ t ω * gC γ α f L w U Δ u ω ∂P = 0 := by
  let g : ℝ × ℝ × ℝ → ℝ := fun q =>
    f t * goodA γ α (L t) q.1 * (f u * goodA γ α (L u) q.2.1 * tiltY γ (w u) q.2.2)
  have hg : Measurable g := by
    exact (measurable_const.mul ((measurable_goodA γ α (L t)).comp measurable_fst)).mul
      ((measurable_const.mul ((measurable_goodA γ α (L u)).comp
        (measurable_fst.comp measurable_snd))).mul
        ((measurable_tiltY γ (w u)).comp (measurable_snd.comp measurable_snd)))
  have h1 := (h.decor t ht u hu htu).integral_fun_comp_mul_comp
    (h.measurable_Δ t).aemeasurable
    ((h.measurable_U t).prodMk ((h.measurable_U u).prodMk (h.measurable_Δ u))).aemeasurable
    (measurable_tiltY γ (w t)).aestronglyMeasurable hg.aestronglyMeasurable
  have hY : ∫ ω, tiltY γ (w t) (Δ t ω) ∂P = 0 := by
    rw [← integral_tiltY γ (w t)]
    exact (h.lawΔ t ht).integral_comp (f := fun d => tiltY γ (w t) d)
      (measurable_tiltY γ (w t)).aestronglyMeasurable
  calc ∫ ω, gC γ α f L w U Δ t ω * gC γ α f L w U Δ u ω ∂P
      = ∫ ω, tiltY γ (w t) (Δ t ω) * g (U t ω, U u ω, Δ u ω) ∂P := by
        congr 1 with ω; simp only [g, gC]; ring
    _ = (∫ ω, tiltY γ (w t) (Δ t ω) ∂P) * ∫ ω, g (U t ω, U u ω, Δ u ω) ∂P := h1
    _ = 0 := by rw [hY, zero_mul]

end Pointwise

/-- Lebesgue measure of the `δ`-neighbourhood of the diagonal inside `S × S`, `S ⊆ ℂ`. -/
lemma measureReal_near_diag_le_C {S : Set ℂ} (hSf : volume S < ∞) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((volume.restrict S).prod (volume.restrict S)).real {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}
      ≤ π * δ ^ 2 * volume.real S := by
  have hN : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} :=
    measurableSet_lt (continuous_fst.sub continuous_snd).norm.measurable measurable_const
  have hball : ∀ t : ℂ, volume (Metric.ball t δ) = ENNReal.ofReal (π * δ ^ 2) := by
    intro t
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  have hle : ((volume.restrict S).prod (volume.restrict S)) {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}
      ≤ ENNReal.ofReal (π * δ ^ 2) * volume S := by
    rw [Measure.prod_apply hN]
    calc ∫⁻ t, (volume.restrict S) (Prod.mk t ⁻¹' {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ})
          ∂(volume.restrict S)
        ≤ ∫⁻ _t, ENNReal.ofReal (π * δ ^ 2) ∂(volume.restrict S) := by
          refine lintegral_mono fun t => ?_
          calc (volume.restrict S) (Prod.mk t ⁻¹' {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ})
              ≤ volume (Prod.mk t ⁻¹' {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}) :=
                Measure.restrict_apply_le _ _
            _ ≤ volume (Metric.ball t δ) := by
                refine measure_mono fun u hu => ?_
                simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hu
                rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
                exact hu
            _ = ENNReal.ofReal (π * δ ^ 2) := hball t
      _ = ENNReal.ofReal (π * δ ^ 2) * volume S := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  calc ((volume.restrict S).prod (volume.restrict S)).real {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}
      ≤ (ENNReal.ofReal (π * δ ^ 2) * volume S).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf.ne) hle
    _ = π * δ ^ 2 * volume.real S := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), measureReal_def]

section Main

variable {P : Measure Ω} [IsProbabilityMeasure P] {S : Set ℂ} {δ K W : ℝ} {L f : ℂ → ℝ}
  {v w : ℂ → ℝ≥0} {U Δ : ℂ → Ω → ℝ} {γ α : ℝ}

/-- **Planar two-radius lemma, core form** (arbitrary truncation, near-diagonal bound `D`). -/
theorem trlC_core_bound (hγ : 0 ≤ γ) {θg θb δ Lmin Lmax M D : ℝ} (hθg : 0 ≤ θg)
    (hθb : 0 ≤ θb)
    (hcg : 0 ≤ -(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2)
    (hcb : -(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2 ≤ 0)
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hf : Measurable f) (hM : ∀ t, |f t| ≤ M)
    (h : TRLHypC P S δ K W L v w U Δ) (hLmin : ∀ t ∈ S, Lmin ≤ L t)
    (hLmax : ∀ t ∈ S, L t ≤ Lmax)
    (hD : ((volume.restrict S).prod (volume.restrict S)).real
      {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} ≤ D) :
    ∫ ω, |∫ t in S, dC γ f L w U Δ t ω| ∂P
      ≤ √(M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) * (exp ((γ - θg) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2) * Lmax))) * D)
        + M * (2 * (exp ((γ / 2 + θb) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2) * Lmin))) * volume.real S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  set Mg := M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) * (exp ((γ - θg) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2) * Lmax))) with hMg
  set Mb := M * (2 * (exp ((γ / 2 + θb) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2) * Lmin))) with hMb
  set G := gC γ α f L w U Δ with hG
  set B := bC γ α f L w U Δ with hB
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hMg0 : 0 ≤ Mg := by positivity
  have hG2 : ∀ t ∈ S, ∫ ω, G t ω ^ 2 ∂P ≤ Mg := by
    intro t ht
    refine (integral_gC_sq_le hθg h ht (hM t)).trans ?_
    rw [hMg]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonneg_left (hLmax t ht) hcg)) (exp_pos _).le)
      (by positivity)) (sq_nonneg _)
  have hB1 : ∀ t ∈ S, ∫ ω, |B t ω| ∂P ≤ Mb := by
    intro t ht
    refine (integral_abs_bC_le hθb h ht (hM t)).trans ?_
    rw [hMb]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonpos_left (hLmin t ht) hcb)) (exp_pos _).le)
      two_pos.le) hM0
  have hGL2 : ∀ t ∈ S, MemLp (G t) 2 P := fun t ht => memLp_gC hγ h ht
  have hGsq : ∀ t ∈ S, Integrable (fun ω => G t ω ^ 2) P := fun t ht =>
    (memLp_two_iff_integrable_sq (measurable_gC_t hf h t).aestronglyMeasurable).1 (hGL2 t ht)
  have hGGint1 : ∀ t ∈ S, ∀ u ∈ S, Integrable (fun ω => G t ω * G u ω) P := by
    intro t ht u hu
    refine Integrable.mono' (((hGsq t ht).add (hGsq u hu)).div_const 2)
      ((measurable_gC_t hf h t).mul (measurable_gC_t hf h u)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_mul_le_half_add_sq _ _
  have hcross : ∀ t ∈ S, ∀ u ∈ S, ∫ ω, |G t ω * G u ω| ∂P ≤ Mg := by
    intro t ht u hu
    calc ∫ ω, |G t ω * G u ω| ∂P ≤ ∫ ω, (G t ω ^ 2 + G u ω ^ 2) / 2 ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (((hGsq t ht).add (hGsq u hu)).div_const 2)
            (ae_of_all _ fun ω => abs_mul_le_half_add_sq _ _)
      _ = ((∫ ω, G t ω ^ 2 ∂P) + ∫ ω, G u ω ^ 2 ∂P) / 2 := by
          rw [integral_div, integral_add (hGsq t ht) (hGsq u hu)]
      _ ≤ Mg := by linarith [hG2 t ht, hG2 u hu]
  have hcross0 : ∀ t ∈ S, ∀ u ∈ S, δ ≤ ‖t - u‖ → ∫ ω, G t ω * G u ω ∂P = 0 :=
    fun t ht u hu htu => integral_gC_mul_eq_zero h ht hu htu
  have hSS : ∀ᵐ p ∂((volume.restrict S).prod (volume.restrict S)), p.1 ∈ S ∧ p.2 ∈ S := by
    rw [Measure.prod_restrict]
    exact (ae_restrict_mem (hS.prod hS)).mono fun p hp => hp
  have hGint : Integrable (fun p : ℂ × Ω => G p.1 p.2) ((volume.restrict S).prod P) := by
    rw [integrable_prod_iff (measurable_gC hf h).aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hS] with t ht
      exact (hGL2 t ht).integrable one_le_two
    · refine Integrable.mono' (integrable_const ((1 + Mg) / 2))
        (measurable_gC hf h).aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hS] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ ω, ‖G t ω‖ ∂P ≤ ∫ ω, (1 + G t ω ^ 2) / 2 ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (((integrable_const 1).add (hGsq t ht)).div_const 2)
              (ae_of_all _ fun ω => show ‖G t ω‖ ≤ (1 + G t ω ^ 2) / 2 by
                rw [Real.norm_eq_abs]; exact abs_le_half_one_add_sq _)
        _ = (1 + ∫ ω, G t ω ^ 2 ∂P) / 2 := by
            rw [integral_div, integral_add (integrable_const 1) (hGsq t ht)]; simp
        _ ≤ (1 + Mg) / 2 := by linarith [hG2 t ht]
  have hBint : Integrable (fun p : ℂ × Ω => B p.1 p.2) ((volume.restrict S).prod P) := by
    rw [integrable_prod_iff (measurable_bC hf h).aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hS] with t ht
      exact integrable_bC h ht
    · refine Integrable.mono' (integrable_const Mb)
        (measurable_bC hf h).aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hS] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Real.norm_eq_abs] using hB1 t ht
  have hGGmeas : Measurable (fun q : (ℂ × ℂ) × Ω => G q.1.1 q.2 * G q.1.2 q.2) :=
    ((measurable_gC hf h).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((measurable_gC hf h).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hGGint : Integrable (fun q : (ℂ × ℂ) × Ω => G q.1.1 q.2 * G q.1.2 q.2)
      (((volume.restrict S).prod (volume.restrict S)).prod P) := by
    rw [integrable_prod_iff hGGmeas.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hSS] with p hp
      exact hGGint1 p.1 hp.1 p.2 hp.2
    · refine Integrable.mono' (integrable_const Mg)
        hGGmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hSS] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Real.norm_eq_abs] using hcross p.1 hp.1 p.2 hp.2
  set X : Ω → ℝ := fun ω => ∫ t in S, G t ω with hX
  set Y : Ω → ℝ := fun ω => ∫ t in S, B t ω with hY
  have hsplit : ∀ᵐ ω ∂P, ∫ t in S, dC γ f L w U Δ t ω = X ω + Y ω := by
    filter_upwards [hGint.prod_left_ae, hBint.prod_left_ae] with ω h1 h2
    rw [hX, hY]
    simp only
    rw [← integral_add h1 h2]
    congr 1 with t
    exact dC_eq γ α f L w U Δ t ω
  have hXint : Integrable X P := hGint.integral_prod_right
  have hYint : Integrable Y P := hBint.integral_prod_right
  have hBabs : Integrable (fun p : ℂ × Ω => |B p.1 p.2|) ((volume.restrict S).prod P) :=
    hBint.abs
  have hYbound : ∫ ω, |Y ω| ∂P ≤ Mb * volume.real S := by
    calc ∫ ω, |Y ω| ∂P ≤ ∫ ω, (∫ t in S, |B t ω|) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            hBabs.integral_prod_right (ae_of_all _ fun ω => by
              simpa only [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (μ := volume.restrict S) (fun t => B t ω))
      _ = ∫ t in S, ∫ ω, |B t ω| ∂P := (integral_integral_swap hBabs).symm
      _ ≤ ∫ _t in S, Mb := by
          refine integral_mono_ae hBabs.integral_prod_left (integrable_const _) ?_
          filter_upwards [ae_restrict_mem hS] with t ht
          exact hB1 t ht
      _ = Mb * volume.real S := by
          rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
  have hX2eq : ∀ ω, X ω ^ 2 = ∫ p, G p.1 ω * G p.2 ω
      ∂((volume.restrict S).prod (volume.restrict S)) := by
    intro ω
    rw [sq, hX]
    exact (integral_prod_mul (fun t => G t ω) (fun t => G t ω)).symm
  have hX2int : Integrable (fun ω => X ω ^ 2) P :=
    hGGint.integral_prod_right.congr (ae_of_all _ fun ω => (hX2eq ω).symm)
  have hX2bound : ∫ ω, X ω ^ 2 ∂P ≤ Mg * D := by
    have hN : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} :=
      measurableSet_lt (continuous_fst.sub continuous_snd).norm.measurable measurable_const
    calc ∫ ω, X ω ^ 2 ∂P
        = ∫ ω, ∫ p, G p.1 ω * G p.2 ω ∂((volume.restrict S).prod (volume.restrict S)) ∂P := by
          congr 1 with ω; exact hX2eq ω
      _ = ∫ p, ∫ ω, G p.1 ω * G p.2 ω ∂P
            ∂((volume.restrict S).prod (volume.restrict S)) :=
          (integral_integral_swap hGGint).symm
      _ ≤ ∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}.indicator (fun _ => Mg) p
            ∂((volume.restrict S).prod (volume.restrict S)) := by
          refine integral_mono_ae hGGint.integral_prod_left
            ((integrable_const Mg).indicator hN) ?_
          filter_upwards [hSS] with p hp
          by_cases hpN : p ∈ {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}
          · rw [Set.indicator_of_mem hpN]
            have hn : |∫ ω, G p.1 ω * G p.2 ω ∂P| ≤ ∫ ω, |G p.1 ω * G p.2 ω| ∂P := by
              simpa only [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (μ := P) (fun ω => G p.1 ω * G p.2 ω)
            exact (le_abs_self _).trans (hn.trans (hcross p.1 hp.1 p.2 hp.2))
          · rw [Set.indicator_of_notMem hpN]
            simp only [Set.mem_ofPred_eq, not_lt] at hpN
            exact (hcross0 p.1 hp.1 p.2 hp.2 hpN).le
      _ = ((volume.restrict S).prod (volume.restrict S)).real
            {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} * Mg := by
          rw [integral_indicator_const _ hN, smul_eq_mul]
      _ ≤ D * Mg := mul_le_mul_of_nonneg_right hD hMg0
      _ = Mg * D := mul_comm _ _
  have hXbound : ∫ ω, |X ω| ∂P ≤ √(Mg * D) := by
    have hXL2 : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq hXint.aestronglyMeasurable).2 hX2int
    have hvar := variance_nonneg (fun ω => ‖X ω‖) P
    rw [variance_eq_sub hXL2.norm] at hvar
    have hsq : ∫ ω, ((fun ω => ‖X ω‖) ^ 2) ω ∂P = ∫ ω, X ω ^ 2 ∂P := by
      congr 1 with ω; try simp [Real.norm_eq_abs, sq_abs]
    rw [hsq] at hvar
    have h1 : (∫ ω, |X ω| ∂P) ^ 2 ≤ Mg * D := by
      have : (∫ ω, |X ω| ∂P) = ∫ ω, (fun ω => ‖X ω‖) ω ∂P := by
        congr 1 with ω; try simp [Real.norm_eq_abs]
      rw [this]; linarith
    exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
  calc ∫ ω, |∫ t in S, dC γ f L w U Δ t ω| ∂P
      ≤ ∫ ω, (|X ω| + |Y ω|) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hXint.abs.add hYint.abs)
          (hsplit.mono fun ω hω => by beta_reduce; rw [hω]; exact abs_add_le _ _)
    _ = ∫ ω, |X ω| ∂P + ∫ ω, |Y ω| ∂P := integral_add hXint.abs hYint.abs
    _ ≤ _ := add_le_add hXbound hYbound

/-- The truncation parameters for the area measure, in the variable `g = 2γ`: level
`α = 2 + γ`, good tilt `θ = max 0 ((3γ-2)/2)`, bad tilt `(2-γ)/2`. -/
lemma trlC_area_exponent_identities {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    -((2 * γ) ^ 2 / 2) + max 0 ((3 * γ - 2) / 2) * (2 + γ) + (2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2
        = 2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2 ∧
      0 ≤ 2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2 ∧
      -((2 * γ) ^ 2 / 4) - (2 - γ) / 2 * (2 + γ) + (2 * γ / 2 + (2 - γ) / 2) ^ 2
        = -((2 - γ) ^ 2 / 4) := by
  refine ⟨?_, ?_, by ring⟩
  · rcases le_total ((3 * γ - 2) / 2) 0 with h | h
    · rw [max_eq_left h]; ring
    · rw [max_eq_right h]; ring
  · rcases le_total ((3 * γ - 2) / 2) 0 with h | h
    · rw [max_eq_left h]; nlinarith [sq_nonneg γ]
    · rw [max_eq_right h]; nlinarith

/-- **Planar two-radius lemma, area form.** For the area densities
`ε^{γ²/2} e^{γ U}` one applies the core bound with `γ ↦ 2γ` and `L = ½ log (1/ε')`
(so that `Var U ≤ 2L + K` for interior circle averages). With `θ = max 0 ((3γ-2)/2)`:
`E|∫_S f D| ≤ √(Mg · π δ² |S|) + Mb |S|`, `Mg ∝ e^{(2γ² - θ²) Lc}`, `Mb ∝ e^{-((2-γ)²/4) Lc}`. -/
theorem trlC_bound_area {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ Lc M : ℝ} (hδ : 0 ≤ δ)
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hf : Measurable f) (hM : ∀ t, |f t| ≤ M)
    (h : TRLHypC P S δ K W (fun _ => Lc) v w U Δ) :
    ∫ ω, |∫ t in S, dC (2 * γ) f (fun _ => Lc) w U Δ t ω| ∂P
      ≤ √(M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * W)) *
            (exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 * K / 2) *
            exp ((2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) * Lc))) *
            (π * δ ^ 2 * volume.real S))
        + M * (2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
            exp (-((2 - γ) ^ 2 / 4) * Lc))) * volume.real S := by
  obtain ⟨e1, e2, e3⟩ := trlC_area_exponent_identities hγ hγ2
  have hcore := trlC_core_bound (α := 2 + γ) (by positivity : (0 : ℝ) ≤ 2 * γ)
    (le_max_left 0 _) (show (0 : ℝ) ≤ (2 - γ) / 2 by linarith) (by rw [e1]; exact e2)
    (by rw [e3]; nlinarith) hS hSf hf hM h (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (measureReal_near_diag_le_C hSf hδ)
  rwa [e1, e3] at hcore

end Main

end TwoRadiusC
end QuantumZipper
