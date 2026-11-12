/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108Q2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M1

/-!
# CONF Lemma 2.10 from a coarse/fine splitting along a filtration (assembly)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, proof of Lemma 2.10 (C:719–742).
CONF writes the zero-boundary GFF as `h = h_{0,t} + h_{t,∞}` (white noise, C:722–731), where the
coarse part `h_{t,∞}` is continuous, Gaussian with nonnegative covariances and independent of the
fine part `h_{0,t}`; it applies Lemma 2.9 conditionally (C:733–738) and lets `t → 0` (C:740–741).

Here the splitting is an abstract hypothesis `IsCoarseSplit P 𝓖 X S R` (`X = R + S` a.s.,
`S` coarse = `𝓖`-measurable continuous Gaussian with nonnegative covariances, `R` fine =
independent of `𝓖`), along an increasing filtration whose limit carries `X` (the limit step is
Lévy's upward theorem, DV-CONF210-2).

* `IsFKGFunZB.congr_ae`: the hypotheses of L2.10 only depend on `X` up to a.e. equality;
* **`cov_nonneg_of_coarseSplit`**: the assembly, from `condExp_comp_indep`, `cov_frozen_nonneg`
  (P2-CONF210, P2-CONFFKGB) and `integral_mul_ge_of_filtration`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace LQGMetric.CONF

variable {Ω : Type} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- the coarse/fine splitting of CONF C:722–738 at the σ-algebra `𝓖` (the coarse part
`h_{t,∞}` is `S`, the fine part `h_{0,t}` is `R`) -/
structure IsCoarseSplit (P : Measure Ω) (𝓖 : MeasurableSpace Ω) (X : Ω → DistC)
    (S : Ω → C(ℂ, ℝ)) (R : Ω → DistC) : Prop where
  measS : Measurable[𝓖] S
  measR : Measurable[m0] R
  indep : Indep 𝓖 (MeasurableSpace.comap R inferInstance) P
  gauss : IsGaussianProcess (fun x ω => S ω x) P
  cov_nonneg : ∀ x y, 0 ≤ cov[fun ω => S ω x, fun ω => S ω y; P]
  eq : ∀ᵐ ω ∂P, X ω = addFun (R ω) (S ω)

lemma IsFKGFunZB.congr_ae {X Y : Ω → DistC} {Φ : DistC → ℝ} (hXY : X =ᵐ[P] Y)
    (hΦ : IsFKGFunZB P X Φ) : IsFKGFunZB P Y Φ where
  meas := hΦ.meas
  bdd := hΦ.bdd
  mono := by
    filter_upwards [hΦ.mono, hXY] with ω h e
    rw [← e]; exact h
  cont := by
    filter_upwards [hΦ.cont, hXY] with ω h e
    rw [← e]; exact h

variable [IsProbabilityMeasure P]

lemma memLp_two_of_bound {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hb : ∀ ω, |f ω| ≤ C) : MemLp f 2 P :=
  MemLp.of_bound hf C (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)

/-- the frozen step at one level: `E[E[Φ(X)|𝓖] E[Ψ(X)|𝓖]] ≥ E[Φ(X)] E[Ψ(X)]` -/
lemma integral_condExp_mul_ge_of_split (ℱ : Filtration ℕ m0) (n : ℕ)
    {X : Ω → DistC} {S : Ω → C(ℂ, ℝ)} {R : Ω → DistC} (hs : IsCoarseSplit P (ℱ n) X S R)
    {Φ Ψ : DistC → ℝ} (hΦ : IsFKGFunZB P X Φ) (hΨ : IsFKGFunZB P X Ψ) :
    (∫ ω, (P[fun ω => Φ (X ω) | ℱ n]) ω ∂P) * (∫ ω, (P[fun ω => Ψ (X ω) | ℱ n]) ω ∂P) ≤
      ∫ ω, (P[fun ω => Φ (X ω) | ℱ n]) ω * (P[fun ω => Ψ (X ω) | ℱ n]) ω ∂P := by
  haveI hRp : IsProbabilityMeasure (P.map R) :=
    (Measure.isProbabilityMeasure_map_iff hs.measR.aemeasurable).2 ‹_›
  have hSm : Measurable S := hs.measS.mono (ℱ.le n) le_rfl
  have hind : IndepFun S R P :=
    (IndepFun_iff_Indep S R P).2 (indep_of_indep_of_le_left hs.indep hs.measS.comap_le)
  have hΦY := hΦ.congr_ae hs.eq
  have hΨY := hΨ.congr_ae hs.eq
  -- freezing: `E[Φ(X)|ℱ n] = Φ̄(S)`
  have freeze : ∀ {Θ : DistC → ℝ}, IsFKGFunZB P X Θ →
      P[fun ω => Θ (X ω) | ℱ n] =ᵐ[P] fun ω => frozenFun (P.map R) Θ (S ω) := by
    intro Θ hΘ
    obtain ⟨C, hC⟩ := hΘ.bdd
    have e1 : (fun ω => Θ (X ω)) =ᵐ[P] fun ω => (fun p : C(ℂ, ℝ) × DistC => Θ (addFun p.2 p.1))
        (S ω, R ω) := by
      filter_upwards [hs.eq] with ω e
      rw [e]
    refine (condExp_congr_ae e1).trans ?_
    exact condExp_comp_indep (ℱ.le n) hs.measS hs.measR hs.indep (measurable_frozenFun_aux hΘ.meas)
      (fun p => hC _)
  have hfa := freeze hΦ
  have hga := freeze hΨ
  have e3 : ∫ ω, (P[fun ω => Φ (X ω) | ℱ n]) ω * (P[fun ω => Ψ (X ω) | ℱ n]) ω ∂P =
      ∫ ω, frozenFun (P.map R) Φ (S ω) * frozenFun (P.map R) Ψ (S ω) ∂P :=
    integral_congr_ae (by filter_upwards [hfa, hga] with ω h1 h2; rw [h1, h2])
  rw [integral_congr_ae hfa, integral_congr_ae hga, e3]
  obtain ⟨CΦ, hCΦ⟩ := hΦ.bdd
  obtain ⟨CΨ, hCΨ⟩ := hΨ.bdd
  have hcov := cov_frozen_nonneg hSm hs.measR hind hs.gauss hs.cov_nonneg hΦY hΨY
  rw [covariance_eq_sub
    (memLp_two_of_bound (f := fun ω => frozenFun (P.map R) Φ (S ω))
      ((measurable_frozenFun _ hΦ.meas).comp hSm).aestronglyMeasurable
      (fun ω => abs_frozenFun_le _ hCΦ _))
    (memLp_two_of_bound (f := fun ω => frozenFun (P.map R) Ψ (S ω))
      ((measurable_frozenFun _ hΨ.meas).comp hSm).aestronglyMeasurable
      (fun ω => abs_frozenFun_le _ hCΨ _))] at hcov
  have := sub_nonneg.1 hcov
  simpa only [Pi.mul_apply] using this

/-- **CONF Lemma 2.10, assembly** (C:733–741): if along an increasing filtration `ℱ` whose
limit carries `X` (up to a.e. equality) the field splits at every level into a coarse continuous
positively correlated Gaussian part and an independent fine part, then `Cov(Φ(X), Ψ(X)) ≥ 0`
for all `Φ, Ψ` as in `IsFKGFunZB`. -/
theorem cov_nonneg_of_coarseSplit (ℱ : Filtration ℕ m0) {X X' : Ω → DistC}
    (hXm : Measurable X) (hX' : Measurable[⨆ n, ℱ n] X') (hXX' : X =ᵐ[P] X')
    (hsplit : ∀ n, ∃ S : Ω → C(ℂ, ℝ), ∃ R : Ω → DistC, IsCoarseSplit P (ℱ n) X S R)
    {Φ Ψ : DistC → ℝ} (hΦ : IsFKGFunZB P X Φ) (hΨ : IsFKGFunZB P X Ψ) :
    0 ≤ cov[fun ω => Φ (X ω), fun ω => Ψ (X ω); P] := by
  obtain ⟨CΦ, hCΦ⟩ := hΦ.bdd
  obtain ⟨CΨ, hCΨ⟩ := hΨ.bdd
  rw [covariance_eq_sub
    (memLp_two_of_bound (f := fun ω => Φ (X ω)) (hΦ.meas.comp hXm).aestronglyMeasurable (fun ω => hCΦ _))
    (memLp_two_of_bound (f := fun ω => Ψ (X ω)) (hΨ.meas.comp hXm).aestronglyMeasurable (fun ω => hCΨ _))]
  refine sub_nonneg.2 ?_
  have hsm : ∀ {Θ : DistC → ℝ}, Measurable Θ →
      AEStronglyMeasurable[⨆ n, ℱ n] (fun ω => Θ (X ω)) P := by
    intro Θ hΘ
    refine ⟨fun ω => Θ (X' ω), (hΘ.comp hX').stronglyMeasurable, ?_⟩
    filter_upwards [hXX'] with ω e
    rw [e]
  have key := integral_mul_ge_of_filtration ℱ (Cf := CΦ.toNNReal) (Cg := CΨ.toNNReal)
    (hsm hΦ.meas) (hsm hΨ.meas)
    (Eventually.of_forall fun ω => (hCΦ _).trans (Real.le_coe_toNNReal _))
    (Eventually.of_forall fun ω => (hCΨ _).trans (Real.le_coe_toNNReal _))
    (fun n => by
      obtain ⟨S, R, hs⟩ := hsplit n
      exact integral_condExp_mul_ge_of_split ℱ n hs hΦ hΨ)
  simpa only [Pi.mul_apply] using key

end LQGMetric.CONF
