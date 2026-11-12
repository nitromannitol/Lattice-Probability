/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108L2 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# CONF Lemma 2.10: the conditioning and limit steps

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF), proof of Lemma 2.10
(C:719–742). CONF writes `h = h_{0,t} + h_{t,∞}`, applies Lemma 2.9 to the continuous coarse part
`h_{t,∞}` conditionally (C:735–738) and passes to the limit `t → 0` (C:740–741, backward martingale
and Kolmogorov 0-1 law). We use the variant proposed in handoff/P2-CONFFKG.md: condition on the
coarse σ-algebras `𝓕_n` (increasing to `σ(h)`), so that the limit is Lévy's upward theorem
(mathlib `MeasureTheory.tendsto_ae_condExp`); this avoids the 0-1 law and backward martingales.

* `integral_mul_ge_of_filtration` (the limit step): if `f, g` are bounded and
  `⨆ₙ 𝓕ₙ`-measurable and `E[f|𝓕ₙ]`, `E[g|𝓕ₙ]` are positively correlated for every `n`, then so are
  `f, g` (Lévy upward + dominated convergence);
* `condExp_comp_indep` (the conditioning step): for `S` `𝓖`-measurable and `R` independent of `𝓖`,
  `E[F(S, R) | 𝓖] = F̄(S)` with `F̄(s) = ∫ F(s, r) d(law R)` (freezing).

Both are standard measure theory (own proofs, `DEVIATIONS` DV-CONF210-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LQGMetric.CONF

section Limit

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrable_of_ae_bound {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, |f ω| ≤ C) : Integrable f P :=
  (MemLp.of_bound hf C (by simpa [Real.norm_eq_abs] using hb)).integrable le_top

/-- **Limit step (Lévy upward)**: positive correlation of the conditional expectations along a
filtration passes to bounded `⨆ₙ 𝓕ₙ`-measurable limits -/
theorem integral_mul_ge_of_filtration (ℱ : Filtration ℕ m0) {f g : Ω → ℝ} {Cf Cg : ℝ≥0}
    (hf : AEStronglyMeasurable[⨆ n, ℱ n] f P) (hg : AEStronglyMeasurable[⨆ n, ℱ n] g P)
    (hfb : ∀ᵐ ω ∂P, |f ω| ≤ Cf) (hgb : ∀ᵐ ω ∂P, |g ω| ≤ Cg)
    (h : ∀ n, (∫ ω, (P[f | ℱ n]) ω ∂P) * (∫ ω, (P[g | ℱ n]) ω ∂P) ≤
      ∫ ω, (P[f | ℱ n]) ω * (P[g | ℱ n]) ω ∂P) :
    (∫ ω, f ω ∂P) * (∫ ω, g ω ∂P) ≤ ∫ ω, f ω * g ω ∂P := by
  have hle : (⨆ n, ℱ n) ≤ m0 := iSup_le ℱ.le
  have hfi : Integrable f P := integrable_of_ae_bound (hf.mono hle) hfb
  have hgi : Integrable g P := integrable_of_ae_bound (hg.mono hle) hgb
  have hlim : ∀ {u : Ω → ℝ}, AEStronglyMeasurable[⨆ n, ℱ n] u P → Integrable u P →
      ∀ᵐ ω ∂P, Tendsto (fun n => (P[u | ℱ n]) ω) atTop (𝓝 (u ω)) := fun hu hui => by
    filter_upwards [tendsto_ae_condExp (μ := P) (ℱ := ℱ) _,
      condExp_of_aestronglyMeasurable' hle hu hui] with ω h1 h2
    rwa [h2] at h1
  have hF := hlim hf hfi
  have hG := hlim hg hgi
  have hbF : ∀ n, ∀ᵐ ω ∂P, |(P[f | ℱ n]) ω| ≤ Cf := fun n => ae_bdd_condExp_of_ae_bdd hfb
  have hbG : ∀ n, ∀ᵐ ω ∂P, |(P[g | ℱ n]) ω| ≤ Cg := fun n => ae_bdd_condExp_of_ae_bdd hgb
  have hmF : ∀ n, AEStronglyMeasurable (P[f | ℱ n]) P := fun n =>
    (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable
  have hmG : ∀ n, AEStronglyMeasurable (P[g | ℱ n]) P := fun n =>
    (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable
  have h1 := tendsto_integral_of_dominated_convergence (fun _ => (Cf : ℝ)) hmF
    (integrable_const _) (fun n => by simpa [Real.norm_eq_abs] using hbF n) hF
  have h2 := tendsto_integral_of_dominated_convergence (fun _ => (Cg : ℝ)) hmG
    (integrable_const _) (fun n => by simpa [Real.norm_eq_abs] using hbG n) hG
  have h3 := tendsto_integral_of_dominated_convergence (fun _ => (Cf : ℝ) * Cg)
    (fun n => (hmF n).mul (hmG n)) (integrable_const _)
    (fun n => by
      filter_upwards [hbF n, hbG n] with ω ha hb
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul ha hb (abs_nonneg _) Cf.2)
    (by filter_upwards [hF, hG] with ω ha hb using ha.mul hb)
  exact le_of_tendsto_of_tendsto' (h1.mul h2) h3 h

end Limit

section Freeze

variable {Ω α β : Type*} {𝓖 m0 : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Conditioning step (freezing)**: `E[F(S, R) | 𝓖] = F̄(S)`, `F̄(s) = ∫ F(s, r) d(law R)`, for
`S` `𝓖`-measurable and `R` independent of `𝓖`, `F` bounded measurable -/
theorem condExp_comp_indep (h𝓖 : 𝓖 ≤ m0) {S : Ω → α} {R : Ω → β}
    (hS : Measurable[𝓖] S) (hR : Measurable R)
    (hind : Indep 𝓖 (MeasurableSpace.comap R inferInstance) P) {F : α × β → ℝ}
    (hF : Measurable F) {C : ℝ} (hFb : ∀ p, |F p| ≤ C) :
    P[fun ω => F (S ω, R ω) | 𝓖] =ᵐ[P] fun ω => ∫ r, F (S ω, r) ∂(P.map R) := by
  have hR' : IsProbabilityMeasure (P.map R) :=
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 ‹_›
  have hSm : Measurable S := hS.mono h𝓖 le_rfl
  set Fb : α → ℝ := fun s => ∫ r, F (s, r) ∂(P.map R) with hFb_def
  have hFbm : Measurable Fb := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hFbb : ∀ s, |Fb s| ≤ C := fun s => by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C) (Eventually.of_forall fun r => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hFb _
    · simp
  have hfm : Measurable fun ω => F (S ω, R ω) := hF.comp (hSm.prodMk hR)
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝓖
    (integrable_of_ae_bound hfm.aestronglyMeasurable (Eventually.of_forall fun ω => hFb _))
    (fun s _ _ => (integrable_of_ae_bound (P := P) (hFbm.comp hSm).aestronglyMeasurable
      (Eventually.of_forall fun ω => hFbb _)).integrableOn) ?_
    ((hFbm.comp hS).stronglyMeasurable.aestronglyMeasurable)).symm
  intro s hs _
  -- `Z = (S, clip 1_s)` is `𝓖`-measurable, hence independent of `R`
  let cl : ℝ → ℝ := fun b => max (min b 1) 0
  have hcl : Measurable cl := (measurable_id.min measurable_const).max measurable_const
  let Z : Ω → α × ℝ := fun ω => (S ω, s.indicator (fun _ => (1 : ℝ)) ω)
  have hZ𝓖 : Measurable[𝓖] Z := hS.prodMk ((measurable_const (a := (1 : ℝ))).indicator hs)
  have hZ : Measurable Z := hZ𝓖.mono h𝓖 le_rfl
  have hZR : IndepFun Z R P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind hZ𝓖.comap_le
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hR.aemeasurable).1 hZR
  have hZ' : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 ‹_›
  let G : (α × ℝ) × β → ℝ := fun p => cl p.1.2 * F (p.1.1, p.2)
  have hGm : Measurable G := (hcl.comp (measurable_snd.comp measurable_fst)).mul
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hGb : ∀ p, |G p| ≤ C := fun p => by
    have h01 : |cl p.1.2| ≤ 1 := by
      simp only [cl]; rw [abs_le]; constructor <;> [exact (by linarith [le_max_right (min p.1.2 1) 0]);
        exact max_le (min_le_right _ _) zero_le_one]
    rw [abs_mul]
    calc |cl p.1.2| * |F (p.1.1, p.2)| ≤ 1 * C :=
          mul_le_mul h01 (hFb _) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have ecl : ∀ ω, cl (s.indicator (fun _ => (1 : ℝ)) ω) = s.indicator 1 ω := fun ω => by
    by_cases hω : ω ∈ s <;> simp [cl, hω]
  have e1 : ∫ ω in s, F (S ω, R ω) ∂P = ∫ ω, G (Z ω, R ω) ∂P := by
    rw [← integral_indicator (h𝓖 _ hs)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [G, Z, ecl]
    by_cases hω : ω ∈ s <;> simp [hω]
  have e2 : ∫ ω in s, (Fb ∘ S) ω ∂P = ∫ ω, cl (Z ω).2 * Fb (Z ω).1 ∂P := by
    rw [← integral_indicator (h𝓖 _ hs)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Z, ecl]
    by_cases hω : ω ∈ s <;> simp [hω]
  have hGi : Integrable G ((P.map Z).prod (P.map R)) :=
    integrable_of_ae_bound hGm.aestronglyMeasurable (Eventually.of_forall hGb)
  rw [e1, e2, ← integral_map (hZ.prodMk hR).aemeasurable hGm.aestronglyMeasurable, hmap,
    integral_prod G hGi,
    ← integral_map (f := fun z : α × ℝ => cl z.2 * Fb z.1) hZ.aemeasurable
      ((hcl.comp measurable_snd).mul (hFbm.comp measurable_fst)).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [G, Fb]
  exact (integral_const_mul (μ := P.map R) (cl z.2) fun r => F (z.1, r)).symm

end Freeze

end LQGMetric.CONF
