/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108L2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108L3
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-!
# CONF Lemma 2.10: the frozen functional (item (R1) of `handoff/P2-CONF210.md`)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, proof of Lemma 2.10 (C:733–738): conditionally on
the fine part `h_{0,t}`, the functional `Φ_{h_{0,t}}(f) := E[Φ(h_{0,t} + f)]` of the smooth part is
non-decreasing and a.s. continuous along (random) approximating sequences, so Lemma 2.9 applies to
it. Here `X = R + S` with `S : Ω → C(ℂ, ℝ)` (the smooth part) independent of `R : Ω → 𝒟'(ℂ)`, and
the frozen functional is `frozenFun (P.map R) Φ s = ∫ Φ(r + s) d(law R)(r)`.

* `frozenFun_mono`: `Φ̄` is monotone (CONF C:735: "`Φ_{h_{0,t}}` is non-decreasing"), from the
  a.s. monotonicity of `Φ` at the sample (no independence needed);
* **`frozen_isFKG`**: `Φ̄` is monotone and a.s. continuous along measurable approximating
  sequences **under the law of `S`** (`AeSeqContAt (P.map S) id Φ̄`; CONF C:736–737);
* **`cov_frozen_nonneg`**: CONF Lemma 2.9 applied to `Φ̄, Ψ̄` at the Gaussian `S` (C:737–738).

The continuity is proved on the canonical space `(C(ℂ, ℝ), law S)`. The hypotheses of
`IsFKGFunZB` hold at the sample `X ω` (a non-measurable predicate), and independence only transfers
measurable events to `law S ⊗ law R`. For a fixed measurable sequence `gₙ : C(ℂ, ℝ) → C(ℂ, ℝ)` the
event `{(s, r) : gₙ(s) → s ⇒ Φ(r + gₙ(s)) → Φ(r + s)}` is measurable, contains the sample-level
good set, and therefore has full `law S ⊗ law R` measure; Fubini and dominated convergence finish.
The form `AeSeqContAt P S Φ̄` (sequences `gₙ : Ω → C(ℂ, ℝ)` not functions of `S`) does not follow
this way, because `(gₙ(ω₀), S ω₀, R ω)` under `P ⊗ P` does not have the law of
`(gₙ(ω), S ω, R ω)` under `P`; the canonical form is what Lemma 2.9 needs
(`fkg_continuous_gaussian_seq` uses only sequences that are measurable functions of `S`).
Own elementary measure theory (Fubini plus independence), following CONF's sentence C:736–737.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.CONF

/-- the frozen functional `Φ̄(s) = ∫ Φ(r + s) dμ_R(r)` -/
def frozenFun (μR : Measure DistC) (Φ : DistC → ℝ) (s : C(ℂ, ℝ)) : ℝ :=
  ∫ r, Φ (addFun r s) ∂μR

lemma ofCont_add_m1 (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

/-- `(r + t) + (s − t) = r + s` -/
lemma addFun_addFun_sub_m1 (r : DistC) (t s : C(ℂ, ℝ)) :
    addFun (addFun r t) (s - t) = addFun r s := by
  simp only [addFun, add_assoc, ← ofCont_add_m1, add_sub_cancel]

lemma measurable_frozenFun_aux {Φ : DistC → ℝ} (hΦ : Measurable Φ) :
    Measurable fun p : C(ℂ, ℝ) × DistC => Φ (addFun p.2 p.1) :=
  hΦ.comp (measurable_addFun.comp (measurable_snd.prodMk measurable_fst))

lemma measurable_frozenFun (μR : Measure DistC) [SFinite μR] {Φ : DistC → ℝ}
    (hΦ : Measurable Φ) : Measurable (frozenFun μR Φ) :=
  (measurable_frozenFun_aux hΦ).stronglyMeasurable.integral_prod_right'.measurable

lemma abs_frozenFun_le (μR : Measure DistC) [IsProbabilityMeasure μR] {Φ : DistC → ℝ} {C : ℝ}
    (hC : ∀ x, |Φ x| ≤ C) (s : C(ℂ, ℝ)) : |frozenFun μR Φ s| ≤ C := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := C) (Eventually.of_forall fun r => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact hC _
  · simp

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `Φ̄` is non-decreasing (CONF C:735) -/
lemma frozenFun_mono {S : Ω → C(ℂ, ℝ)} {R : Ω → DistC} (hR : Measurable R) {Φ : DistC → ℝ}
    (hΦ : IsFKGFunZB P (fun ω => addFun (R ω) (S ω)) Φ) : Monotone (frozenFun (P.map R) Φ) := by
  obtain ⟨C, hC⟩ := hΦ.bdd
  intro s s' hss'
  have hm : ∀ s : C(ℂ, ℝ), Measurable fun r : DistC => Φ (addFun r s) := fun s =>
    hΦ.meas.comp (measurable_addFun_left s)
  have hi : ∀ s : C(ℂ, ℝ), Integrable (fun ω => Φ (addFun (R ω) s)) P := fun s =>
    integrable_of_ae_bound ((hm s).comp hR).aestronglyMeasurable
      (Eventually.of_forall fun ω => hC _)
  simp only [frozenFun]
  rw [integral_map hR.aemeasurable (hm s).aestronglyMeasurable,
    integral_map hR.aemeasurable (hm s').aestronglyMeasurable]
  refine integral_mono_ae (hi s) (hi s') ?_
  filter_upwards [hΦ.mono] with ω hω
  have := hω (s - S ω) (s' - S ω) (sub_le_sub_right hss' _)
  simpa only [addFun_addFun_sub_m1] using this

/-- **The frozen functional of CONF Lemma 2.10** (C:733–738; `handoff/P2-CONF210.md` (R1)): for
`S ⊥ R` and `Φ` as in `IsFKGFunZB` for `X = R + S`, `Φ̄(s) = ∫ Φ(r + s) d(law R)` is monotone and
a.s. continuous along measurable approximating sequences under the law of `S`. -/
theorem frozen_isFKG {S : Ω → C(ℂ, ℝ)} {R : Ω → DistC} (hS : Measurable S) (hR : Measurable R)
    (hind : IndepFun S R P) {Φ : DistC → ℝ}
    (hΦ : IsFKGFunZB P (fun ω => addFun (R ω) (S ω)) Φ) :
    Monotone (frozenFun (P.map R) Φ) ∧ AeSeqContAt (P.map S) id (frozenFun (P.map R) Φ) := by
  refine ⟨frozenFun_mono hR hΦ, fun gn hgn hconv => ?_⟩
  obtain ⟨C, hC⟩ := hΦ.bdd
  have hRp : IsProbabilityMeasure (P.map R) :=
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 ‹_›
  -- a measurable full-measure set `M` on which `gₙ(s) → s`
  set N := toMeasurable (P.map S) {s | ¬Tendsto (fun n => gn n s) atTop (𝓝 (id s))} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P.map S N = 0 := by rw [hN, measure_toMeasurable]; exact ae_iff.1 hconv
  have hMc : ∀ s, s ∉ N → Tendsto (fun n => gn n s) atTop (𝓝 s) := fun s hs => by
    by_contra h
    exact hs (subset_toMeasurable _ _ h)
  -- the measurable event `Q`
  set Q : Set (C(ℂ, ℝ) × DistC) := (Prod.fst ⁻¹' N) ∪
    {p | Tendsto (fun n => Φ (addFun p.2 (gn n p.1))) atTop (𝓝 (Φ (addFun p.2 p.1)))} with hQ
  have hQm : MeasurableSet Q := by
    refine (measurable_fst hNm).union ?_
    have hf : ∀ n, Measurable fun p : C(ℂ, ℝ) × DistC => Φ (addFun p.2 (gn n p.1)) - Φ (addFun p.2 p.1) :=
      fun n => (hΦ.meas.comp (measurable_addFun.comp
        (measurable_snd.prodMk ((hgn n).comp measurable_fst)))).sub
        (measurable_frozenFun_aux hΦ.meas)
    have e : {p : C(ℂ, ℝ) × DistC | Tendsto (fun n => Φ (addFun p.2 (gn n p.1))) atTop
        (𝓝 (Φ (addFun p.2 p.1)))} = {p | Tendsto (fun n => Φ (addFun p.2 (gn n p.1)) -
          Φ (addFun p.2 p.1)) atTop (𝓝 0)} := by
      ext p
      simp only [mem_ofPred_eq]
      exact tendsto_sub_nhds_zero_iff.symm
    rw [e]
    exact measurableSet_tendsto (𝓝 0) hf
  -- `Q` holds at the sample
  have hQω : ∀ᵐ ω ∂P, (S ω, R ω) ∈ Q := by
    filter_upwards [hΦ.cont] with ω hω
    by_cases hSN : S ω ∈ N
    · exact Or.inl hSN
    · right
      have ht : Tendsto (fun n => gn n (S ω) - S ω) atTop (𝓝 0) := by
        simpa only [sub_self] using (hMc _ hSN).sub_const (S ω)
      have := hω _ ht
      simpa only [mem_ofPred_eq, addFun_addFun_sub_m1] using this
  have hmap : P.map (fun ω => (S ω, R ω)) = (P.map S).prod (P.map R) :=
    (indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable hR.aemeasurable).1 hind
  have hQp : ∀ᵐ p ∂((P.map S).prod (P.map R)), p ∈ Q := by
    rw [← hmap]
    exact (ae_map_iff (hS.prodMk hR).aemeasurable hQm).2 hQω
  have hNae : ∀ᵐ s ∂(P.map S), s ∉ N := by
    rw [ae_iff]; simpa using hN0
  filter_upwards [Measure.ae_ae_of_ae_prod hQp, hNae] with s hs hsN
  simp only [id, frozenFun]
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
    (integrable_const C) (fun n => Eventually.of_forall fun r => ?_) ?_
  · exact (hΦ.meas.comp (measurable_addFun_left _)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hC _
  · filter_upwards [hs] with r hr
    rcases hr with hr | hr
    · exact absurd hr hsN
    · exact hr

/-- **CONF Lemma 2.9 for the frozen functionals** (C:737–738): for a continuous Gaussian `S` with
nonnegative covariances, independent of `R`, `Cov(Φ̄(S), Ψ̄(S)) ≥ 0`. -/
theorem cov_frozen_nonneg {S : Ω → C(ℂ, ℝ)} {R : Ω → DistC} (hS : Measurable S)
    (hR : Measurable R) (hind : IndepFun S R P)
    (hG : IsGaussianProcess (fun x ω => S ω x) P)
    (hcov : ∀ x y, 0 ≤ cov[fun ω => S ω x, fun ω => S ω y; P]) {Φ Ψ : DistC → ℝ}
    (hΦ : IsFKGFunZB P (fun ω => addFun (R ω) (S ω)) Φ)
    (hΨ : IsFKGFunZB P (fun ω => addFun (R ω) (S ω)) Ψ) :
    0 ≤ cov[fun ω => frozenFun (P.map R) Φ (S ω), fun ω => frozenFun (P.map R) Ψ (S ω); P] := by
  have hRp : IsProbabilityMeasure (P.map R) :=
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 ‹_›
  have hSp : IsProbabilityMeasure (P.map S) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 ‹_›
  obtain ⟨hΦm, hΦc⟩ := frozen_isFKG hS hR hind hΦ
  obtain ⟨hΨm, hΨc⟩ := frozen_isFKG hS hR hind hΨ
  obtain ⟨CΦ, hCΦ⟩ := hΦ.bdd
  obtain ⟨CΨ, hCΨ⟩ := hΨ.bdd
  have hmΦ := measurable_frozenFun (P.map R) hΦ.meas
  have hmΨ := measurable_frozenFun (P.map R) hΨ.meas
  have hev : ∀ x : ℂ, Measurable fun s : C(ℂ, ℝ) => s x := fun x =>
    (continuous_eval_const x).measurable
  -- the canonical process under the law of `S`
  have hG' : IsGaussianProcess (fun x (s : C(ℂ, ℝ)) => id s x) (P.map S) := by
    refine ⟨fun I => ?_⟩
    have hgm : Measurable fun s : C(ℂ, ℝ) => I.restrict fun x => id s x :=
      measurable_pi_iff.2 fun j => hev (j : ℂ)
    refine ⟨hgm.aemeasurable, ?_⟩
    rw [Measure.map_map hgm hS]
    exact (hG.hasGaussianLaw I).isGaussian_map
  have hcov' : ∀ x y, 0 ≤ cov[fun s : C(ℂ, ℝ) => id s x, fun s => id s y; P.map S] := by
    intro x y
    show 0 ≤ cov[fun s : C(ℂ, ℝ) => s x, fun s => s y; P.map S]
    rw [covariance_map_fun (X := fun s : C(ℂ, ℝ) => s x) (Y := fun s => s y)
      (hev x).aestronglyMeasurable (hev y).aestronglyMeasurable hS.aemeasurable]
    exact hcov x y
  have h := fkg_continuous_gaussian_seq (P := P.map S) measurable_id hG' hcov' hΦm hΨm hmΦ hmΨ
    (abs_frozenFun_le (P.map R) hCΦ) (abs_frozenFun_le (P.map R) hCΨ) hΦc hΨc
  have e := covariance_map_fun (X := frozenFun (P.map R) Φ) (Y := frozenFun (P.map R) Ψ)
    hmΦ.aestronglyMeasurable hmΨ.aestronglyMeasurable hS.aemeasurable (μ := P)
  simp only [id] at h
  rwa [e] at h

end LQGMetric.CONF
