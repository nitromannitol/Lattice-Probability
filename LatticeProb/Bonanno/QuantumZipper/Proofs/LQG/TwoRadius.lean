/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.TwoRadius at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadiusTilt
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# M4-B2: the (truncated) two-radius lemma at the Gaussian level

Blueprint node M4-B2 (`blueprint/M4_BLUEPRINT.md`), stated for an abstract Gaussian family.

At each `t ∈ S` we are given the coarse-radius coordinate `U t` (centered Gaussian, variance
`≤ 2 L t + K`, where `L t = log (1/ε'(t))`) and the increment `Δ t` to the finer radius
(centered Gaussian, variance `w t ≤ W`), with `Δ t ⊥ U t`, and, for `|t - u| ≥ δ`,
`Δ t ⊥ (U t, U u, Δ u)`.  These are exactly the properties that M4-R1/R2 provide for the
normalized free field. The density difference is
`f t · e^{-(γ²/4) L t + (γ/2) U t} · (1 - e^{(γ/2) Δ t - γ² w t / 8})`.

`trl_core_bound` proves, for arbitrary truncation parameters,
`E|∫_S f D| ≤ √(Mg · 2δ|S|) + Mb · |S|`, by splitting along the single-scale good event
`{U t ≤ α L t}`: the good part is uncorrelated beyond `δ` (second moment), the bad part is small in
`L¹` (one-point tilt, M4-B1).  `trl_bound` specializes to `α = (2+γ)/2` and gives the exponents
of blueprint §4 for **every** `γ ∈ (0,2)`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The density difference `f t · A_t · (1 - Y_t)` at a point `t`. -/
noncomputable def trlD (γ : ℝ) (f L : ℝ → ℝ) (w : ℝ → ℝ≥0) (U Δ : ℝ → Ω → ℝ) (t : ℝ)
    (ω : Ω) : ℝ :=
  f t * (exp (-(γ ^ 2 / 4) * L t + γ / 2 * U t ω) * tiltY γ (w t) (Δ t ω))

/-- Good part of `trlD` (on `{U t ≤ α L t}`). -/
noncomputable def trlG (γ α : ℝ) (f L : ℝ → ℝ) (w : ℝ → ℝ≥0) (U Δ : ℝ → Ω → ℝ) (t : ℝ)
    (ω : Ω) : ℝ :=
  f t * goodA γ α (L t) (U t ω) * tiltY γ (w t) (Δ t ω)

/-- Bad part of `trlD` (on `{U t > α L t}`). -/
noncomputable def trlB (γ α : ℝ) (f L : ℝ → ℝ) (w : ℝ → ℝ≥0) (U Δ : ℝ → Ω → ℝ) (t : ℝ)
    (ω : Ω) : ℝ :=
  f t * badA γ α (L t) (U t ω) * tiltY γ (w t) (Δ t ω)

lemma trlD_eq (γ α : ℝ) (f L : ℝ → ℝ) (w : ℝ → ℝ≥0) (U Δ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    trlD γ f L w U Δ t ω = trlG γ α f L w U Δ t ω + trlB γ α f L w U Δ t ω := by
  unfold trlD trlG trlB
  rw [← goodA_add_badA γ α (L t) (U t ω)]
  ring

/-- Gaussian-level hypotheses of the two-radius lemma (provided by M4-R1/R2 for the field). -/
structure TRLHyp (P : Measure Ω) (S : Set ℝ) (δ K W : ℝ) (L : ℝ → ℝ) (v w : ℝ → ℝ≥0)
    (U Δ : ℝ → Ω → ℝ) : Prop where
  measU : Measurable (fun p : ℝ × Ω => U p.1 p.2)
  measΔ : Measurable (fun p : ℝ × Ω => Δ p.1 p.2)
  measL : Measurable L
  measw : Measurable w
  lawU : ∀ t ∈ S, HasLaw (U t) (gaussianReal 0 (v t)) P
  lawΔ : ∀ t ∈ S, HasLaw (Δ t) (gaussianReal 0 (w t)) P
  varU : ∀ t ∈ S, (v t : ℝ) ≤ 2 * L t + K
  varΔ : ∀ t ∈ S, (w t : ℝ) ≤ W
  indep : ∀ t ∈ S, IndepFun (Δ t) (U t) P
  decor : ∀ t ∈ S, ∀ u ∈ S, δ ≤ |t - u| →
    IndepFun (Δ t) (fun ω => (U t ω, U u ω, Δ u ω)) P

section Pointwise

variable {P : Measure Ω} {S : Set ℝ} {δ K W : ℝ} {L f : ℝ → ℝ} {v w : ℝ → ℝ≥0}
  {U Δ : ℝ → Ω → ℝ} {γ α : ℝ}

lemma TRLHyp.measurable_U (h : TRLHyp P S δ K W L v w U Δ) (t : ℝ) : Measurable (U t) :=
  h.measU.comp (measurable_const.prodMk measurable_id)

lemma TRLHyp.measurable_Δ (h : TRLHyp P S δ K W L v w U Δ) (t : ℝ) : Measurable (Δ t) :=
  h.measΔ.comp (measurable_const.prodMk measurable_id)

lemma measurable_trlG (hf : Measurable f) (h : TRLHyp P S δ K W L v w U Δ) :
    Measurable (fun p : ℝ × Ω => trlG γ α f L w U Δ p.1 p.2) := by
  unfold trlG
  exact ((hf.comp measurable_fst).mul ((measurable_goodA₂ γ α).comp
    ((h.measL.comp measurable_fst).prodMk h.measU))).mul
    ((continuous_tiltY₂ γ).measurable.comp
      ((measurable_coe_nnreal_real.comp (h.measw.comp measurable_fst)).prodMk h.measΔ))

lemma measurable_trlB (hf : Measurable f) (h : TRLHyp P S δ K W L v w U Δ) :
    Measurable (fun p : ℝ × Ω => trlB γ α f L w U Δ p.1 p.2) := by
  unfold trlB
  exact ((hf.comp measurable_fst).mul ((measurable_badA₂ γ α).comp
    ((h.measL.comp measurable_fst).prodMk h.measU))).mul
    ((continuous_tiltY₂ γ).measurable.comp
      ((measurable_coe_nnreal_real.comp (h.measw.comp measurable_fst)).prodMk h.measΔ))

lemma measurable_trlG_t (hf : Measurable f) (h : TRLHyp P S δ K W L v w U Δ) (t : ℝ) :
    Measurable (trlG γ α f L w U Δ t) :=
  (measurable_trlG hf h).comp (measurable_const.prodMk measurable_id)

lemma abs_mul_le_half_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

lemma abs_le_half_one_add_sq (a : ℝ) : |a| ≤ (1 + a ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - 1), sq_abs a]

variable [IsProbabilityMeasure P]

/-- One-point second moment of the good part. -/
lemma integral_trlG_sq_le {θ M : ℝ} (hθ : 0 ≤ θ) (h : TRLHyp P S δ K W L v w U Δ)
    {t : ℝ} (ht : t ∈ S) (hM : |f t| ≤ M) :
    ∫ ω, trlG γ α f L w U Δ t ω ^ 2 ∂P
      ≤ M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) * (exp ((γ - θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 2) + θ * α + (γ - θ) ^ 2) * L t))) := by
  have h1 := (h.indep t ht).integral_fun_comp_mul_comp (h.measurable_Δ t).aemeasurable
    (h.measurable_U t).aemeasurable
    (((measurable_tiltY γ (w t)).pow_const 2).aestronglyMeasurable)
    (((measurable_goodA γ α (L t)).pow_const 2).aestronglyMeasurable)
    (f := fun d => tiltY γ (w t) d ^ 2) (g := fun x => goodA γ α (L t) x ^ 2)
  have hY : ∫ ω, tiltY γ (w t) (Δ t ω) ^ 2 ∂P = ∫ d, tiltY γ (w t) d ^ 2 ∂(gaussianReal 0 (w t)) :=
    (h.lawΔ t ht).integral_comp (f := fun d => tiltY γ (w t) d ^ 2)
      ((measurable_tiltY γ (w t)).pow_const 2).aestronglyMeasurable
  have hA : ∫ ω, goodA γ α (L t) (U t ω) ^ 2 ∂P
      = ∫ x, goodA γ α (L t) x ^ 2 ∂(gaussianReal 0 (v t)) :=
    (h.lawU t ht).integral_comp (f := fun x => goodA γ α (L t) x ^ 2)
      ((measurable_goodA γ α (L t)).pow_const 2).aestronglyMeasurable
  have hYb := integral_tiltY_sq_le γ (w t)
  have hYb' : 1 + exp (γ ^ 2 / 4 * (w t : ℝ)) ≤ 1 + exp (γ ^ 2 / 4 * W) := by
    have := h.varΔ t ht
    gcongr
  have hAb := integral_goodA_sq_le (γ := γ) (α := α) (L := L t) (K := K) hθ (h.varU t ht)
  have hf2 : f t ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
  calc ∫ ω, trlG γ α f L w U Δ t ω ^ 2 ∂P
      = ∫ ω, f t ^ 2 * (tiltY γ (w t) (Δ t ω) ^ 2 * goodA γ α (L t) (U t ω) ^ 2) ∂P := by
        congr 1 with ω; unfold trlG; ring
    _ = f t ^ 2 * ((∫ ω, tiltY γ (w t) (Δ t ω) ^ 2 ∂P) *
          ∫ ω, goodA γ α (L t) (U t ω) ^ 2 ∂P) := by
        rw [integral_const_mul]; congr 1
    _ ≤ M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) * (exp ((γ - θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 2) + θ * α + (γ - θ) ^ 2) * L t))) := by
        rw [hY, hA]
        have i1 : 0 ≤ ∫ d, tiltY γ (w t) d ^ 2 ∂(gaussianReal 0 (w t)) :=
          integral_nonneg fun _ => sq_nonneg _
        have i2 : 0 ≤ ∫ x, goodA γ α (L t) x ^ 2 ∂(gaussianReal 0 (v t)) :=
          integral_nonneg fun _ => sq_nonneg _
        exact mul_le_mul hf2 (mul_le_mul (hYb.trans hYb') hAb i2 (by positivity))
          (mul_nonneg i1 i2) (sq_nonneg _)

/-- Decorrelation of the good part beyond distance `δ`. -/
lemma integral_trlG_mul_eq_zero (hf : Measurable f) (h : TRLHyp P S δ K W L v w U Δ)
    {t u : ℝ} (ht : t ∈ S) (hu : u ∈ S) (htu : δ ≤ |t - u|) :
    ∫ ω, trlG γ α f L w U Δ t ω * trlG γ α f L w U Δ u ω ∂P = 0 := by
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
  calc ∫ ω, trlG γ α f L w U Δ t ω * trlG γ α f L w U Δ u ω ∂P
      = ∫ ω, tiltY γ (w t) (Δ t ω) * g (U t ω, U u ω, Δ u ω) ∂P := by
        congr 1 with ω; simp only [g, trlG]; ring
    _ = (∫ ω, tiltY γ (w t) (Δ t ω) ∂P) * ∫ ω, g (U t ω, U u ω, Δ u ω) ∂P := h1
    _ = 0 := by rw [hY, zero_mul]

/-- One-point `L¹` bound of the bad part. -/
lemma integral_abs_trlB_le {θ M : ℝ} (hθ : 0 ≤ θ) (h : TRLHyp P S δ K W L v w U Δ)
    {t : ℝ} (ht : t ∈ S) (hM : |f t| ≤ M) :
    ∫ ω, |trlB γ α f L w U Δ t ω| ∂P
      ≤ M * (2 * (exp ((γ / 2 + θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 4) - θ * α + (γ / 2 + θ) ^ 2) * L t))) := by
  have h1 := (h.indep t ht).integral_fun_comp_mul_comp (h.measurable_Δ t).aemeasurable
    (h.measurable_U t).aemeasurable
    ((continuous_abs.measurable.comp (measurable_tiltY γ (w t))).aestronglyMeasurable)
    ((measurable_badA γ α (L t)).aestronglyMeasurable)
    (f := fun d => |tiltY γ (w t) d|) (g := fun x => badA γ α (L t) x)
  have hY : ∫ ω, |tiltY γ (w t) (Δ t ω)| ∂P = ∫ d, |tiltY γ (w t) d| ∂(gaussianReal 0 (w t)) :=
    (h.lawΔ t ht).integral_comp (f := fun d => |tiltY γ (w t) d|)
      (continuous_abs.measurable.comp (measurable_tiltY γ (w t))).aestronglyMeasurable
  have hA : ∫ ω, badA γ α (L t) (U t ω) ∂P = ∫ x, badA γ α (L t) x ∂(gaussianReal 0 (v t)) :=
    (h.lawU t ht).integral_comp (f := fun x => badA γ α (L t) x)
      (measurable_badA γ α (L t)).aestronglyMeasurable
  have hAb := integral_badA_le (γ := γ) (α := α) (L := L t) (K := K) hθ (h.varU t ht)
  have hYb := integral_abs_tiltY_le γ (w t)
  calc ∫ ω, |trlB γ α f L w U Δ t ω| ∂P
      = ∫ ω, |f t| * (|tiltY γ (w t) (Δ t ω)| * badA γ α (L t) (U t ω)) ∂P := by
        congr 1 with ω; unfold trlB
        rw [abs_mul, abs_mul, abs_of_nonneg (badA_nonneg _ _ _ _)]; ring
    _ = |f t| * ((∫ ω, |tiltY γ (w t) (Δ t ω)| ∂P) * ∫ ω, badA γ α (L t) (U t ω) ∂P) := by
        rw [integral_const_mul]; congr 1
    _ ≤ M * (2 * (exp ((γ / 2 + θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 4) - θ * α + (γ / 2 + θ) ^ 2) * L t))) := by
        rw [hY, hA]
        have i1 : 0 ≤ ∫ d, |tiltY γ (w t) d| ∂(gaussianReal 0 (w t)) :=
          integral_nonneg fun _ => abs_nonneg _
        have i2 : 0 ≤ ∫ x, badA γ α (L t) x ∂(gaussianReal 0 (v t)) :=
          integral_nonneg fun _ => badA_nonneg _ _ _ _
        exact mul_le_mul hM (mul_le_mul hYb hAb i2 (by norm_num)) (mul_nonneg i1 i2)
          ((abs_nonneg _).trans hM)

lemma memLp_trlG (hγ : 0 ≤ γ) (hf : Measurable f) (h : TRLHyp P S δ K W L v w U Δ)
    {t : ℝ} (ht : t ∈ S) : MemLp (trlG γ α f L w U Δ t) 2 P := by
  rw [memLp_two_iff_integrable_sq (measurable_trlG_t hf h t).aestronglyMeasurable]
  set E := exp (γ / 2 * (α - γ / 2) * L t)
  have hint : Integrable (fun ω => tiltY γ (w t) (Δ t ω) ^ 2) P :=
    (h.lawΔ t ht).integrable_fun_comp (integrable_tiltY_sq γ (w t))
  refine Integrable.mono' (hint.const_mul (f t ^ 2 * E ^ 2))
    ((measurable_trlG_t hf h t).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 := goodA_nonneg γ α (L t) (U t ω)
  have h1 : goodA γ α (L t) (U t ω) ≤ E := goodA_le hγ
  calc trlG γ α f L w U Δ t ω ^ 2
      = f t ^ 2 * goodA γ α (L t) (U t ω) ^ 2 * tiltY γ (w t) (Δ t ω) ^ 2 := by
        unfold trlG; ring
    _ ≤ f t ^ 2 * E ^ 2 * tiltY γ (w t) (Δ t ω) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2)
          (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

lemma integrable_trlB (hf : Measurable f) (h : TRLHyp P S δ K W L v w U Δ)
    {t : ℝ} (ht : t ∈ S) : Integrable (trlB γ α f L w U Δ t) P := by
  have hind : IndepFun (badA γ α (L t) ∘ U t) (tiltY γ (w t) ∘ Δ t) P :=
    (h.indep t ht).symm.comp (measurable_badA γ α (L t)) (measurable_tiltY γ (w t))
  have hiA : Integrable (badA γ α (L t) ∘ U t) P :=
    (h.lawU t ht).integrable_comp (integrable_badA_gaussianReal γ α (L t) (v t))
  have hiY : Integrable (tiltY γ (w t) ∘ Δ t) P := by
    refine (h.lawΔ t ht).integrable_comp ?_
    unfold tiltY
    exact (integrable_const 1).sub (integrable_exp_mul_add_gaussianReal _ _ _)
  refine ((hind.integrable_mul hiA hiY).const_mul (f t)).congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply, Function.comp_apply, trlB]
  ring

end Pointwise

section Main

variable {P : Measure Ω} [IsProbabilityMeasure P] {S : Set ℝ} {δ K W : ℝ} {L f : ℝ → ℝ}
  {v w : ℝ → ℝ≥0} {U Δ : ℝ → Ω → ℝ} {γ α : ℝ}

/-- Lebesgue measure of the `δ`-neighbourhood of the diagonal inside `S × S`. -/
lemma measureReal_near_diag_le (hSf : volume S < ∞) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((volume.restrict S).prod (volume.restrict S)).real {p : ℝ × ℝ | |p.1 - p.2| < δ}
      ≤ 2 * δ * volume.real S := by
  have hN : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| < δ} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hle : ((volume.restrict S).prod (volume.restrict S)) {p : ℝ × ℝ | |p.1 - p.2| < δ}
      ≤ ENNReal.ofReal (2 * δ) * volume S := by
    rw [Measure.prod_apply hN]
    calc ∫⁻ t, (volume.restrict S) (Prod.mk t ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| < δ})
          ∂(volume.restrict S)
        ≤ ∫⁻ _t, ENNReal.ofReal (2 * δ) ∂(volume.restrict S) := by
          refine lintegral_mono fun t => ?_
          calc (volume.restrict S) (Prod.mk t ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| < δ})
              ≤ volume (Prod.mk t ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| < δ}) :=
                Measure.restrict_apply_le _ _
            _ ≤ volume (Set.Ioo (t - δ) (t + δ)) := by
                refine measure_mono fun u hu => ?_
                simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hu
                rw [abs_sub_lt_iff] at hu
                constructor <;> linarith
            _ = ENNReal.ofReal (2 * δ) := by
                rw [Real.volume_Ioo]; congr 1; ring
      _ = ENNReal.ofReal (2 * δ) * volume S := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  calc ((volume.restrict S).prod (volume.restrict S)).real {p : ℝ × ℝ | |p.1 - p.2| < δ}
      ≤ (ENNReal.ofReal (2 * δ) * volume S).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf.ne) hle
    _ = 2 * δ * volume.real S := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), measureReal_def]

/-- **Two-radius lemma, core form** (M4-B2 at the Gaussian level, arbitrary truncation). -/
theorem trl_core_bound (hγ : 0 ≤ γ) {θg θb δ Lmin Lmax M : ℝ} (hθg : 0 ≤ θg) (hθb : 0 ≤ θb)
    (hcg : 0 ≤ -(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2)
    (hcb : -(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2 ≤ 0) (hδ : 0 ≤ δ)
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hf : Measurable f) (hM : ∀ t, |f t| ≤ M)
    (h : TRLHyp P S δ K W L v w U Δ) (hLmin : ∀ t ∈ S, Lmin ≤ L t)
    (hLmax : ∀ t ∈ S, L t ≤ Lmax) :
    ∫ ω, |∫ t in S, trlD γ f L w U Δ t ω| ∂P
      ≤ √(M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) * (exp ((γ - θg) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2) * Lmax))) * (2 * δ * volume.real S))
        + M * (2 * (exp ((γ / 2 + θb) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2) * Lmin))) * volume.real S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  set Mg := M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) * (exp ((γ - θg) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2) * Lmax))) with hMg
  set Mb := M * (2 * (exp ((γ / 2 + θb) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2) * Lmin))) with hMb
  set G := trlG γ α f L w U Δ with hG
  set B := trlB γ α f L w U Δ with hB
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hMg0 : 0 ≤ Mg := by positivity
  -- one-point bounds, uniform in `t ∈ S`
  have hG2 : ∀ t ∈ S, ∫ ω, G t ω ^ 2 ∂P ≤ Mg := by
    intro t ht
    refine (integral_trlG_sq_le hθg h ht (hM t)).trans ?_
    rw [hMg]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonneg_left (hLmax t ht) hcg)) (exp_pos _).le)
      (by positivity)) (sq_nonneg _)
  have hB1 : ∀ t ∈ S, ∫ ω, |B t ω| ∂P ≤ Mb := by
    intro t ht
    refine (integral_abs_trlB_le hθb h ht (hM t)).trans ?_
    rw [hMb]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonpos_left (hLmin t ht) hcb)) (exp_pos _).le)
      two_pos.le) hM0
  have hGL2 : ∀ t ∈ S, MemLp (G t) 2 P := fun t ht => memLp_trlG hγ hf h ht
  have hGsq : ∀ t ∈ S, Integrable (fun ω => G t ω ^ 2) P := fun t ht =>
    (memLp_two_iff_integrable_sq (measurable_trlG_t hf h t).aestronglyMeasurable).1 (hGL2 t ht)
  have hGGint1 : ∀ t ∈ S, ∀ u ∈ S, Integrable (fun ω => G t ω * G u ω) P := by
    intro t ht u hu
    refine Integrable.mono' (((hGsq t ht).add (hGsq u hu)).div_const 2)
      ((measurable_trlG_t hf h t).mul (measurable_trlG_t hf h u)).aestronglyMeasurable
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
  have hcross0 : ∀ t ∈ S, ∀ u ∈ S, δ ≤ |t - u| → ∫ ω, G t ω * G u ω ∂P = 0 :=
    fun t ht u hu htu => integral_trlG_mul_eq_zero hf h ht hu htu
  -- integrability on product spaces
  have hSS : ∀ᵐ p ∂((volume.restrict S).prod (volume.restrict S)), p.1 ∈ S ∧ p.2 ∈ S := by
    rw [Measure.prod_restrict]
    exact (ae_restrict_mem (hS.prod hS)).mono fun p hp => hp
  have hGint : Integrable (fun p : ℝ × Ω => G p.1 p.2) ((volume.restrict S).prod P) := by
    rw [integrable_prod_iff (measurable_trlG hf h).aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hS] with t ht
      exact (hGL2 t ht).integrable one_le_two
    · refine Integrable.mono' (integrable_const ((1 + Mg) / 2))
        (measurable_trlG hf h).aestronglyMeasurable.norm.integral_prod_right' ?_
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
  have hBint : Integrable (fun p : ℝ × Ω => B p.1 p.2) ((volume.restrict S).prod P) := by
    rw [integrable_prod_iff (measurable_trlB hf h).aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hS] with t ht
      exact integrable_trlB hf h ht
    · refine Integrable.mono' (integrable_const Mb)
        (measurable_trlB hf h).aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hS] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Real.norm_eq_abs] using hB1 t ht
  have hGGmeas : Measurable (fun q : (ℝ × ℝ) × Ω => G q.1.1 q.2 * G q.1.2 q.2) :=
    ((measurable_trlG hf h).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((measurable_trlG hf h).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hGGint : Integrable (fun q : (ℝ × ℝ) × Ω => G q.1.1 q.2 * G q.1.2 q.2)
      (((volume.restrict S).prod (volume.restrict S)).prod P) := by
    rw [integrable_prod_iff hGGmeas.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hSS] with p hp
      exact hGGint1 p.1 hp.1 p.2 hp.2
    · refine Integrable.mono' (integrable_const Mg) hGGmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hSS] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Real.norm_eq_abs] using hcross p.1 hp.1 p.2 hp.2
  -- splitting
  set X : Ω → ℝ := fun ω => ∫ t in S, G t ω with hX
  set Y : Ω → ℝ := fun ω => ∫ t in S, B t ω with hY
  have hsplit : ∀ᵐ ω ∂P, ∫ t in S, trlD γ f L w U Δ t ω = X ω + Y ω := by
    filter_upwards [hGint.prod_left_ae, hBint.prod_left_ae] with ω h1 h2
    rw [hX, hY]
    simp only
    rw [← integral_add h1 h2]
    congr 1 with t
    exact trlD_eq γ α f L w U Δ t ω
  have hXint : Integrable X P := hGint.integral_prod_right
  have hYint : Integrable Y P := hBint.integral_prod_right
  -- the bad part
  have hBabs : Integrable (fun p : ℝ × Ω => |B p.1 p.2|) ((volume.restrict S).prod P) := hBint.abs
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
  -- the good part: second moment
  have hX2eq : ∀ ω, X ω ^ 2 = ∫ p, G p.1 ω * G p.2 ω
      ∂((volume.restrict S).prod (volume.restrict S)) := by
    intro ω
    rw [sq, hX]
    exact (integral_prod_mul (fun t => G t ω) (fun t => G t ω)).symm
  have hX2int : Integrable (fun ω => X ω ^ 2) P :=
    hGGint.integral_prod_right.congr (ae_of_all _ fun ω => (hX2eq ω).symm)
  have hX2bound : ∫ ω, X ω ^ 2 ∂P ≤ Mg * (2 * δ * volume.real S) := by
    have hN : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| < δ} :=
      measurableSet_lt (by fun_prop) measurable_const
    calc ∫ ω, X ω ^ 2 ∂P
        = ∫ ω, ∫ p, G p.1 ω * G p.2 ω ∂((volume.restrict S).prod (volume.restrict S)) ∂P := by
          congr 1 with ω; exact hX2eq ω
      _ = ∫ p, ∫ ω, G p.1 ω * G p.2 ω ∂P
            ∂((volume.restrict S).prod (volume.restrict S)) :=
          (integral_integral_swap hGGint).symm
      _ ≤ ∫ p, {p : ℝ × ℝ | |p.1 - p.2| < δ}.indicator (fun _ => Mg) p
            ∂((volume.restrict S).prod (volume.restrict S)) := by
          refine integral_mono_ae hGGint.integral_prod_left
            ((integrable_const Mg).indicator hN) ?_
          filter_upwards [hSS] with p hp
          by_cases hpN : p ∈ {p : ℝ × ℝ | |p.1 - p.2| < δ}
          · rw [Set.indicator_of_mem hpN]
            have hn : |∫ ω, G p.1 ω * G p.2 ω ∂P| ≤ ∫ ω, |G p.1 ω * G p.2 ω| ∂P := by
              simpa only [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (μ := P) (fun ω => G p.1 ω * G p.2 ω)
            exact (le_abs_self _).trans (hn.trans (hcross p.1 hp.1 p.2 hp.2))
          · rw [Set.indicator_of_notMem hpN]
            simp only [Set.mem_ofPred_eq, not_lt] at hpN
            exact (hcross0 p.1 hp.1 p.2 hp.2 hpN).le
      _ = ((volume.restrict S).prod (volume.restrict S)).real
            {p : ℝ × ℝ | |p.1 - p.2| < δ} * Mg := by
          rw [integral_indicator_const _ hN, smul_eq_mul]
      _ ≤ (2 * δ * volume.real S) * Mg :=
          mul_le_mul_of_nonneg_right (measureReal_near_diag_le hSf hδ) hMg0
      _ = Mg * (2 * δ * volume.real S) := mul_comm _ _
  have hXbound : ∫ ω, |X ω| ∂P ≤ √(Mg * (2 * δ * volume.real S)) := by
    have hXL2 : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq hXint.aestronglyMeasurable).2 hX2int
    have hvar := variance_nonneg (fun ω => ‖X ω‖) P
    rw [variance_eq_sub hXL2.norm] at hvar
    have hsq : ∫ ω, ((fun ω => ‖X ω‖) ^ 2) ω ∂P = ∫ ω, X ω ^ 2 ∂P := by
      congr 1 with ω; try simp [Real.norm_eq_abs, sq_abs]
    rw [hsq] at hvar
    have h1 : (∫ ω, |X ω| ∂P) ^ 2 ≤ Mg * (2 * δ * volume.real S) := by
      have : (∫ ω, |X ω| ∂P) = ∫ ω, (fun ω => ‖X ω‖) ω ∂P := by
        congr 1 with ω; try simp [Real.norm_eq_abs]
      rw [this]; linarith
    exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
  -- assembling
  calc ∫ ω, |∫ t in S, trlD γ f L w U Δ t ω| ∂P
      ≤ ∫ ω, (|X ω| + |Y ω|) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hXint.abs.add hYint.abs)
          (hsplit.mono fun ω hω => by beta_reduce; rw [hω]; exact abs_add_le _ _)
    _ = ∫ ω, |X ω| ∂P + ∫ ω, |Y ω| ∂P := integral_add hXint.abs hYint.abs
    _ ≤ _ := add_le_add hXbound hYbound

/-- The truncation parameters of blueprint §4: level `α = (2+γ)/2`, good tilt
`θg = max 0 ((3γ-2)/4)`, bad tilt `θb = (2-γ)/4`. -/
lemma trl_exponent_identities {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    -(γ ^ 2 / 2) + max 0 ((3 * γ - 2) / 4) * ((2 + γ) / 2) + (γ - max 0 ((3 * γ - 2) / 4)) ^ 2
        = γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2 ∧
      0 ≤ γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2 ∧
      -(γ ^ 2 / 4) - (2 - γ) / 4 * ((2 + γ) / 2) + (γ / 2 + (2 - γ) / 4) ^ 2
        = -((2 - γ) ^ 2 / 16) := by
  refine ⟨?_, ?_, by ring⟩
  · rcases le_total ((3 * γ - 2) / 4) 0 with h | h
    · rw [max_eq_left h]; ring
    · rw [max_eq_right h]; ring
  · rcases le_total ((3 * γ - 2) / 4) 0 with h | h
    · rw [max_eq_left h]; nlinarith [sq_nonneg γ]
    · rw [max_eq_right h]; nlinarith

/-- **Two-radius lemma** (M4-B2 at the Gaussian level), truncated at `α = (2+γ)/2`, valid for
every `γ ∈ (0,2)`. With `θg = max 0 ((3γ-2)/4)`:
`E|∫_S f D| ≤ √(Mg · 2δ|S|) + Mb |S|`, where `Mg ∝ e^{(γ²/2 - θg²) Lmax}` and
`Mb ∝ e^{-((2-γ)²/16) Lmin}`. -/
theorem trl_bound {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ Lmin Lmax M : ℝ} (hδ : 0 ≤ δ)
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hf : Measurable f) (hM : ∀ t, |f t| ≤ M)
    (h : TRLHyp P S δ K W L v w U Δ) (hLmin : ∀ t ∈ S, Lmin ≤ L t)
    (hLmax : ∀ t ∈ S, L t ≤ Lmax) :
    ∫ ω, |∫ t in S, trlD γ f L w U Δ t ω| ∂P
      ≤ √(M ^ 2 * ((1 + exp (γ ^ 2 / 4 * W)) *
            (exp ((γ - max 0 ((3 * γ - 2) / 4)) ^ 2 * K / 2) *
            exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * Lmax))) *
            (2 * δ * volume.real S))
        + M * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * K / 2) *
            exp (-((2 - γ) ^ 2 / 16) * Lmin))) * volume.real S := by
  obtain ⟨e1, e2, e3⟩ := trl_exponent_identities hγ hγ2
  have hcore := trl_core_bound (α := (2 + γ) / 2) hγ.le (le_max_left 0 _)
    (show (0 : ℝ) ≤ (2 - γ) / 4 by linarith) (by rw [e1]; exact e2) (by rw [e3]; nlinarith)
    hδ hS hSf hf hM h hLmin hLmax
  rwa [e1, e3] at hcore

/-- **Two-radius lemma, radius form** (the statement of M4-B2): at each `t ∈ S` the two radii
satisfy `ε ≤ r₂ t ≤ r₁ t ≤ Λε`, `U t` is the field coordinate at the larger radius
(variance `≤ 2 log (1/r₁ t) + K`, e.g. `K = 2 log R`) and `U t + Δ t` the one at the smaller
radius, with `Var Δ t = 2 log (r₁ t / r₂ t)`. Then, with `e₁ = 1 - γ²/2 + θg²` and
`e₂ = (2-γ)²/16`,
`E|∫_S f (d_{r₁} - d_{r₂})| ≤ M √(C₁ |S| ε^{e₁}) + M C₂ |S| ε^{e₂}`,
`C₁ = 4Λ(1 + Λ^{γ²/2}) e^{(γ-θg)²K/2}`, `C₂ = 2 e^{(γ/2+θb)²K/2} Λ^{e₂}`. -/
theorem trl_bound_radii {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ε Λ M : ℝ} (hε : 0 < ε)
    (hΛ : 1 ≤ Λ) {r₁ r₂ : ℝ → ℝ} (hr₁ : Measurable r₁)
    (hr : ∀ t ∈ S, ε ≤ r₂ t ∧ r₂ t ≤ r₁ t ∧ r₁ t ≤ Λ * ε)
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hf : Measurable f) (hM : ∀ t, |f t| ≤ M)
    (measU : Measurable (fun p : ℝ × Ω => U p.1 p.2))
    (measΔ : Measurable (fun p : ℝ × Ω => Δ p.1 p.2)) (measw : Measurable w)
    (lawU : ∀ t ∈ S, HasLaw (U t) (gaussianReal 0 (v t)) P)
    (lawΔ : ∀ t ∈ S, HasLaw (Δ t) (gaussianReal 0 (w t)) P)
    (varU : ∀ t ∈ S, (v t : ℝ) ≤ 2 * log (1 / r₁ t) + K)
    (varΔ : ∀ t ∈ S, (w t : ℝ) = 2 * log (r₁ t / r₂ t))
    (indep : ∀ t ∈ S, IndepFun (Δ t) (U t) P)
    (decor : ∀ t ∈ S, ∀ u ∈ S, 2 * Λ * ε ≤ |t - u| →
      IndepFun (Δ t) (fun ω => (U t ω, U u ω, Δ u ω)) P) :
    ∫ ω, |∫ t in S, f t * (r₁ t ^ (γ ^ 2 / 4) * exp (γ / 2 * U t ω)
        - r₂ t ^ (γ ^ 2 / 4) * exp (γ / 2 * (U t ω + Δ t ω)))| ∂P
      ≤ M * √((4 * Λ * (1 + Λ ^ (γ ^ 2 / 2)) *
              exp ((γ - max 0 ((3 * γ - 2) / 4)) ^ 2 * K / 2)) * volume.real S *
              ε ^ (1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2))
        + M * (2 * exp ((γ / 2 + (2 - γ) / 4) ^ 2 * K / 2) * Λ ^ ((2 - γ) ^ 2 / 16)) *
            volume.real S * ε ^ ((2 - γ) ^ 2 / 16) := by
  have hΛ0 : 0 < Λ := by linarith
  set θ := max 0 ((3 * γ - 2) / 4) with hθ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hpos : ∀ t ∈ S, 0 < r₂ t ∧ 0 < r₁ t := fun t ht =>
    ⟨hε.trans_le (hr t ht).1, hε.trans_le ((hr t ht).1.trans (hr t ht).2.1)⟩
  have h : TRLHyp P S (2 * Λ * ε) K (2 * log Λ) (fun t => log (1 / r₁ t)) v w U Δ :=
    { measU := measU, measΔ := measΔ, measL := (measurable_const.div hr₁).log,
      measw := measw, lawU := lawU, lawΔ := lawΔ, varU := varU
      varΔ := by
        intro t ht
        rw [varΔ t ht]
        obtain ⟨h1, h2, h3⟩ := hr t ht
        have : r₁ t / r₂ t ≤ Λ := by
          rw [div_le_iff₀ (hpos t ht).1]; nlinarith
        have := log_le_log (div_pos (hpos t ht).2 (hpos t ht).1) this
        linarith
      indep := indep, decor := decor }
  have hLmax : ∀ t ∈ S, log (1 / r₁ t) ≤ log (1 / ε) := fun t ht =>
    log_le_log (by have := (hpos t ht).2; positivity)
      (one_div_le_one_div_of_le hε ((hr t ht).1.trans (hr t ht).2.1))
  have hLmin : ∀ t ∈ S, log (1 / (Λ * ε)) ≤ log (1 / r₁ t) := fun t ht =>
    log_le_log (by positivity) (one_div_le_one_div_of_le (hpos t ht).2 (hr t ht).2.2)
  have hcore := trl_bound hγ hγ2 (by positivity) hS hSf hf hM h hLmin hLmax
  have hpt : ∀ ω, ∫ t in S, f t * (r₁ t ^ (γ ^ 2 / 4) * exp (γ / 2 * U t ω)
        - r₂ t ^ (γ ^ 2 / 4) * exp (γ / 2 * (U t ω + Δ t ω)))
      = ∫ t in S, trlD γ f (fun t => log (1 / r₁ t)) w U Δ t ω := by
    intro ω
    refine setIntegral_congr_fun hS (fun t ht => ?_)
    obtain ⟨h2, h1⟩ := hpos t ht
    have hXY : ∀ X Y : ℝ, exp X * (1 - exp Y) = exp X - exp (X + Y) := by
      intro X Y; rw [exp_add]; ring
    simp only [trlD, tiltY]
    rw [hXY, varΔ t ht, rpow_def_of_pos h1, rpow_def_of_pos h2, one_div, log_inv,
      log_div h1.ne' h2.ne', ← exp_add, ← exp_add]
    congr 1; congr 1 <;> (congr 1; ring)
  have hε1 : ε ^ (1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2)
      = exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * log (1 / ε)) * ε := by
    calc ε ^ (1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2)
        = exp (log ε * (1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2)) := rpow_def_of_pos hε _
      _ = exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * log (1 / ε)) * exp (log ε) := by
          rw [← exp_add, one_div, log_inv]; congr 1; ring
      _ = _ := by rw [exp_log hε]
  have hΛp : Λ ^ (γ ^ 2 / 2) = exp (γ ^ 2 / 4 * (2 * log Λ)) := by
    rw [rpow_def_of_pos hΛ0]; congr 1; ring
  have hε2 : Λ ^ ((2 - γ) ^ 2 / 16) * ε ^ ((2 - γ) ^ 2 / 16)
      = exp (-((2 - γ) ^ 2 / 16) * log (1 / (Λ * ε))) := by
    rw [rpow_def_of_pos hΛ0, rpow_def_of_pos hε, ← exp_add, one_div, log_inv,
      log_mul hΛ0.ne' hε.ne']
    congr 1; ring
  rw [hΛp, hε1, show M * (2 * exp ((γ / 2 + (2 - γ) / 4) ^ 2 * K / 2) * Λ ^ ((2 - γ) ^ 2 / 16)) *
      volume.real S * ε ^ ((2 - γ) ^ 2 / 16) = M * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * K / 2) *
      (Λ ^ ((2 - γ) ^ 2 / 16) * ε ^ ((2 - γ) ^ 2 / 16)))) * volume.real S by ring, hε2]
  simp_rw [hpt]
  refine hcore.trans (le_of_eq ?_)
  congr 1
  rw [mul_assoc (M ^ 2), Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]
  congr 1; congr 1
  ring

end Main

end TwoRadius
end QuantumZipper
