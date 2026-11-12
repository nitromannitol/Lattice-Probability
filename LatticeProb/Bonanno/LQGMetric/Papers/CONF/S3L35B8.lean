/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B7
import LatticeProb.Bonanno.LQGMetric.Field.HarmExistB

/-!
# The Markov harmonic part with its decomposition (task P2-CONF35b)

`markov_harmPart_dec`: the proof of `HarmExist.exists_isHarmPartRaw_of_normAt`
(Field/HarmExistA.lean, P2-D110c; CONF C:1187–1190, LM Lemma 2.1 via `DFGPS.markov_normAt`),
copied verbatim, with the conclusion extended by the decomposition `g = G + h̊` it uses (`G`
measurable, `G ⫫ h̊`, `h̊|_U` a zero-boundary GFF, `H` the harmonic representative of `G|_U`), so
that the Gaussian tail `dg_tail_unif` (DG Lemma 2.2) applies to the harmonic part itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint HarmExist

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- the raw harmonic part of the Markov decomposition, with the decomposition -/
theorem markov_harmPart_dec {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {ρ : ℝ}
    (hρ : 0 < ρ) (w : ℂ) (hn : ∀ᵐ ω ∂P, circleAvg (g ω) ρ w = 0) {U : Set ℂ} (hU : IsOpen U)
    (hUw : Disjoint U (sphere w ρ)) :
    ∃ (H : Ω → ℂ → ℝ) (G hz : Ω → DistC), HarmLoc.IsHarmPartRaw P g U H ∧ Measurable G ∧
      (∀ᵐ ω ∂P, g ω = G ω + hz ω) ∧ IndepFun G hz P ∧
      IsZeroBoundaryGFF (toOpens U hU) (fun ω => restrictTo (toOpens U hU) (hz ω)) P ∧
      ∀ᵐ ω ∂P, ∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (G ω) φ = ∫ x, H ω x * φ x := by
  classical
  obtain ⟨hh₀, hz, hdec, hharm, ⟨G, hGm, hhG⟩, hind0, hzb, hvan, hind⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P g hg hρ w hn (toOpens U hU) hUw
  set V := toOpens U hU
  have hm : fieldSigmaClosed g Uᶜ ≤ mΩ := MarkovZBIndep.fieldSigmaClosed_le hg _
  have hGm' : Measurable G := hGm.mono hm le_rfl
  -- a measurable version of `h̊`
  set X : Ω → DistC := fun ω => g ω - G ω with hX_def
  have hXm : Measurable X := by
    refine GFFInv.measurable_distC_iff.2 fun φ => ?_
    exact ((GFFInv.measurable_pair φ).comp hg.measurable).sub
      ((GFFInv.measurable_pair φ).comp hGm')
  have hXz : X =ᵐ[P] hz := by
    filter_upwards [hhG] with ω hω
    simp only [hX_def, hdec ω, ← hω, add_sub_cancel_left]
  have hindX : Indep (MeasurableSpace.comap X inferInstance) (fieldSigmaClosed g Uᶜ) P :=
    MarkovAsm.indep_comap_congr hm hind hXz.symm
  set Hf : Ω → ℂ → ℝ := fun ω =>
    if hω : ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f U ∧
      ∀ φ : TestOn V, restrictTo V (hh₀ ω) φ = ∫ x, f x * φ x then hω.choose else 0 with hHf
  have hraw : HarmLoc.IsHarmPartRaw P g U Hf := by
    refine ⟨fun ω => ?_, fun φ ψ hφ hψ hψ1 => ?_⟩
    · by_cases hω : ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f U ∧
        ∀ φ : TestOn V, restrictTo V (hh₀ ω) φ = ∫ x, f x * φ x
      · simp only [hHf, dif_pos hω]
        exact hω.choose_spec.1
      · simp only [hHf, dif_neg hω]
        exact InnerProductSpace.harmonicOnNhd_const (s := U) (0 : ℝ)
    set χ : TestC := φ - (∫ x, φ x) • ψ
    have hzψ : ∀ ω, hz ω ψ = 0 := fun ω => by
      have := DFunLike.congr_fun (hvan ω) (testOnHE _ ψ hψ)
      exact (restrictTo_testOnHE _ (hz ω) ψ hψ).symm.trans this
    have hint : ∫ x, χ x = 0 := by
      have e : (χ : ℂ → ℝ) = fun x => φ x - (∫ x, φ x) * ψ x := by ext x; simp [χ]
      rw [e, integral_sub (GM.gm_integrable_testC φ) ((GM.gm_integrable_testC ψ).const_mul _),
        integral_const_mul, hψ1, mul_one, sub_self]
    -- integrability
    have hgχ : Integrable (fun ω => g ω χ) P :=
      (MarkovZB.memLp_pair hg ⟨χ, hint⟩).integrable one_le_two
    have hzφ : Integrable (fun ω => hz ω φ) P := by
      have := ((hzb.process.gaussian.hasGaussianLaw_eval (testOnHE V φ hφ)).memLp_two).integrable one_le_two
      refine this.congr (Eventually.of_forall fun ω => ?_)
      exact restrictTo_testOnHE V (hz ω) φ hφ
    have hXφ : Integrable (fun ω => X ω φ) P :=
      hzφ.congr (hXz.mono fun ω hω => by simp only [hω])
    have hdecχ : ∀ ω, g ω χ = hh₀ ω χ + hz ω φ := fun ω => by
      rw [hdec ω]
      show hh₀ ω χ + hz ω χ = _
      simp only [χ, map_sub, map_smul, hzψ ω, smul_zero, sub_zero]
    have hGχ : (fun ω => G ω χ) =ᵐ[P] fun ω => g ω χ - X ω φ := by
      filter_upwards [hhG, hXz] with ω h1 h2
      rw [h2, hdecχ ω, ← h1]; ring
    have hGχi : Integrable (fun ω => G ω χ) P := (hgχ.sub hXφ).congr hGχ.symm
    -- the conditional expectation
    have hsplit : (fun ω => g ω χ) =ᵐ[P] fun ω => G ω χ + X ω φ := by
      filter_upwards [hGχ] with ω h1
      rw [h1]; ring
    have hc1 : P[fun ω => G ω χ | fieldSigmaClosed g Uᶜ] = fun ω => G ω χ :=
      condExp_of_stronglyMeasurable hm ((GFFInv.measurable_pair χ).comp hGm).stronglyMeasurable
        hGχi
    have hc2 : P[fun ω => X ω φ | fieldSigmaClosed g Uᶜ] =ᵐ[P] fun _ => ∫ ω, X ω φ ∂P :=
      condExp_indep_eq hXm.comap_le hm
        ((GFFInv.measurable_pair φ).comp (comap_measurable X)).stronglyMeasurable hindX
    have hmean : ∫ ω, X ω φ ∂P = 0 := by
      rw [integral_congr_ae (hXz.mono fun ω hω => show X ω φ = hz ω φ by rw [hω])]
      refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans
        (hzb.process.centered (testOnHE V φ hφ))
      exact (restrictTo_testOnHE V (hz ω) φ hφ).symm
    have hRHS : (fun ω => (∫ x, Hf ω x * φ x) - (∫ x, φ x) * g ω ψ) =ᵐ[P]
        fun ω => G ω χ := by
      filter_upwards [hharm, hhG] with ω hω h1
      have hrep : hh₀ ω φ = ∫ x, hω.choose x * φ x :=
        (restrictTo_testOnHE V _ φ hφ).symm.trans (hω.choose_spec.2 _)
      have e : Hf ω = hω.choose := dif_pos hω
      rw [e, ← h1, ← hrep, hdec ω]
      show hh₀ ω φ - (∫ x, φ x) * (hh₀ ω ψ + hz ω ψ) = hh₀ ω χ
      simp only [χ, map_sub, map_smul, hzψ ω, add_zero, smul_eq_mul]
    refine (condExp_congr_ae hsplit).trans ?_
    refine (condExp_add hGχi hXφ (fieldSigmaClosed g Uᶜ)).trans ?_
    rw [hc1]
    filter_upwards [hc2, hRHS] with ω h2 h3
    rw [Pi.add_apply, h2, hmean, add_zero, h3]
  refine ⟨Hf, G, hz, hraw, hGm', ?_, hind0.congr hhG (ae_eq_refl _), hzb, ?_⟩
  · filter_upwards [hhG] with ω hω
    rw [hdec ω, hω]
  · filter_upwards [hharm, hhG] with ω hω h1
    intro φ
    have e : Hf ω = hω.choose := dif_pos hω
    rw [e, ← h1]
    exact hω.choose_spec.2 φ

end LQGMetric.CONF
