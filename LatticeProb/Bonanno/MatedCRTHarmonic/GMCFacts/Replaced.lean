/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.Replaced at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedDefs

/-!
# Replacing the radial part of a whole-plane GFF by an independent two-sided Brownian motion

**Theorem** (`isWholePlaneGFF_replField`). Let `X` be a whole-plane GFF and `W` a continuous centred Gaussian process
with the covariance `radCov` of a two-sided Brownian motion, independent of `X`. Then

  `X̃ = lateral(X) + W(−log|·|)`

is again a whole-plane GFF (LQGMetric's `IsWholePlaneGFF`: its mean-zero pairings form a centred Gaussian process with
covariance `logCov`).

This is the decomposition of the whole-plane GFF into its radial part (a two-sided Brownian motion in `−log|·|`) and
its lateral part, independent of each other (DMS §4.1, Lemmas 4.2–4.4; used in the cone-to-whole-plane comparison and
in [18]'s proof of Lemma 2.8, , and [16]'s proof of Lemma A.3).

**Proof.** For a mean-zero test function `φ`, a.s. `⟨X̃, φ⟩ = U_φ + V_φ` with `U_φ = ⟨X, φ − φ̄⟩` and
`V_φ = ⟨W(−log|·|), φ̄⟩` (`ae_replField_apply`, `φ̄` the rotation average). The `U`'s are a Gaussian process (pairings
of `X`), the `V`'s are measurable functions of `W`, independent of `X`; since `W` has the law of the radial process `ρ`
of `X` (`map_eq_of_radCov`), the `V`'s have the joint law of `(⟨X, φ̄⟩)_φ` (`ae_pairW_radialProcess`), a Gaussian
process. So `(U, V)` is Gaussian and `⟨X̃, ·⟩` is a centred Gaussian process. Its covariance is
`logCov(φ − φ̄, ψ − ψ̄) + logCov(φ̄, ψ̄) = logCov(φ, ψ)`, because `logCov(φ − φ̄, ψ̄) = 0`
(`logCov_sub_symmTest_symmTest`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMCFacts

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma hasGaussianLaw_congr {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [MeasurableSpace E] {Y Y' : Ω → E} (h : HasGaussianLaw Y P) (hYY : Y =ᵐ[P] Y') :
    HasGaussianLaw Y' P :=
  ⟨h.aemeasurable.congr hYY, by rw [← Measure.map_congr hYY]; exact h.isGaussian_map⟩

lemma hasGaussianLaw_of_map_eq {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [MeasurableSpace E] {Y Y' : Ω → E} (h : HasGaussianLaw Y P) (hY' : AEMeasurable Y' P)
    (hmap : P.map Y' = P.map Y) : HasGaussianLaw Y' P :=
  ⟨hY', by rw [hmap]; exact h.isGaussian_map⟩

/-- The covariance of two random variables only depends on their joint law. -/
lemma covariance_eq_of_map_eq {f g f' g' : Ω → ℝ} (hfg : AEMeasurable (fun ω => (f ω, g ω)) P)
    (hfg' : AEMeasurable (fun ω => (f' ω, g' ω)) P)
    (h : P.map (fun ω => (f ω, g ω)) = P.map (fun ω => (f' ω, g' ω))) :
    cov[f, g; P] = cov[f', g'; P] := by
  have e1 := covariance_map (μ := P) (X := Prod.fst) (Y := Prod.snd) (Z := fun ω => (f ω, g ω))
    measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable hfg
  have e2 := covariance_map (μ := P) (X := Prod.fst) (Y := Prod.snd) (Z := fun ω => (f' ω, g' ω))
    measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable hfg'
  rw [h] at e1
  exact e1.symm.trans e2

/-- The mean of a random variable only depends on its law. -/
lemma integral_eq_of_map_eq {f f' : Ω → ℝ} (hf : AEMeasurable f P) (hf' : AEMeasurable f' P)
    (h : P.map f = P.map f') : ∫ ω, f ω ∂P = ∫ ω, f' ω ∂P := by
  rw [← integral_map (f := fun y => y) hf aestronglyMeasurable_id,
    ← integral_map (f := fun y => y) hf' aestronglyMeasurable_id, h]

variable {X : Ω → DistC}

/-- The symmetrized mean-zero test function. -/
def sT (φ : TestC0) : TestC0 := ⟨symmTest φ.1, by rw [integral_symmTest]; exact φ.2⟩

/-- The lateral part `φ − φ̄` of a mean-zero test function. -/
def dT (φ : TestC0) : TestC0 := ⟨φ.1 - symmTest φ.1, integral_sub_symmTest φ.1⟩

/-- **The replaced field is a whole-plane GFF.** -/
theorem isWholePlaneGFF_replField (hX : IsWholePlaneGFF X P) {W : Ω → C(ℝ, ℝ)}
    (hWm : Measurable W) (hWg : IsGaussianProcess (fun t ω => W ω t) P)
    (hW0 : ∀ t, ∫ ω, W ω t ∂P = 0)
    (hWc : ∀ s t, cov[fun ω => W ω s, fun ω => W ω t; P] = radCov s t) (hind : IndepFun X W P) :
    IsWholePlaneGFF (replField X W) P := by
  have := hX.gaussian.isProbabilityMeasure
  obtain ⟨ρ, hρm, hρae, hρg, hρ0, hρc⟩ := exists_radialProcess hX
  have hlaw : P.map W = P.map ρ := map_eq_of_radCov hWm hρm hWg hρg hW0 hρ0 hWc hρc
  -- laws of measurable functionals of `W` and `ρ` agree
  have hlawF : ∀ {β : Type} [MeasurableSpace β] (F : C(ℝ, ℝ) → β), Measurable F →
      P.map (fun ω => F (W ω)) = P.map (fun ω => F (ρ ω)) := fun F hF => by
    show P.map (F ∘ W) = P.map (F ∘ ρ)
    rw [← Measure.map_map hF hWm, ← Measure.map_map hF hρm, hlaw]
  -- the radial pairings of `ρ` are those of `X`
  have hradX : ∀ φ : TestC0, (fun ω => pairW (sT φ).1 (ρ ω)) =ᵐ[P] fun ω => X ω (sT φ).1 :=
    fun φ => ae_pairW_radialProcess hX hρm hρae φ.2
  set U : TestC0 → Ω → ℝ := fun φ ω => X ω (dT φ).1
  set V : TestC0 → Ω → ℝ := fun φ ω => pairW (sT φ).1 (W ω)
  have hUm : ∀ φ, Measurable (U φ) := fun φ => (GFFInv.measurable_pair _).comp hX.measurable
  have hVm : ∀ φ, Measurable (V φ) := fun φ => (measurable_pairW _).comp hWm
  have hdec : ∀ φ : TestC0, (fun ω => replField X W ω φ.1) =ᵐ[P] fun ω => U φ ω + V φ ω :=
    fun φ => ae_replField_apply hX W φ.1
  -- finite-dimensional laws of `V`
  have hlawV : ∀ (ι : Type) [Countable ι] (f : ι → TestC0),
      P.map (fun ω i => V (f i) ω) = P.map (fun ω i => X ω (sT (f i)).1) := by
    intro ι _ f
    have hF : Measurable fun w : C(ℝ, ℝ) => fun i => pairW (sT (f i)).1 w :=
      measurable_pi_iff.2 fun i => measurable_pairW _
    rw [hlawF _ hF]
    refine Measure.map_congr ?_
    filter_upwards [ae_all_iff.2 fun i => hradX (f i)] with ω hω
    funext i
    exact hω i
  have hV2 : ∀ φ ψ : TestC0, P.map (fun ω => (V φ ω, V ψ ω)) =
      P.map (fun ω => (X ω (sT φ).1, X ω (sT ψ).1)) := by
    intro φ ψ
    have hF : Measurable fun w : C(ℝ, ℝ) => (pairW (sT φ).1 w, pairW (sT ψ).1 w) :=
      (measurable_pairW _).prodMk (measurable_pairW _)
    rw [hlawF _ hF]
    refine Measure.map_congr ?_
    filter_upwards [hradX φ, hradX ψ] with ω h1 h2
    simp only [h1, h2]
  have hV1 : ∀ φ : TestC0, P.map (V φ) = P.map (fun ω => X ω (sT φ).1) := by
    intro φ
    have hF : Measurable fun w : C(ℝ, ℝ) => pairW (sT φ).1 w := measurable_pairW _
    rw [show V φ = fun ω => pairW (sT φ).1 (W ω) from rfl, hlawF _ hF]
    exact Measure.map_congr (hradX φ)
  -- Gaussianity of single coordinates
  have hXg : ∀ φ : TestC0, HasGaussianLaw (fun ω => X ω φ.1) P := fun φ =>
    hX.gaussian.hasGaussianLaw_eval φ
  have hVg : ∀ φ : TestC0, HasGaussianLaw (V φ) P := fun φ =>
    hasGaussianLaw_of_map_eq (hXg (sT φ)) (hVm φ).aemeasurable (hV1 φ)
  have hUL2 : ∀ φ, MemLp (U φ) 2 P := fun φ => (hXg (dT φ)).memLp_two
  have hVL2 : ∀ φ, MemLp (V φ) 2 P := fun φ => (hVg φ).memLp_two
  -- independence of the two parts
  have hindUV : ∀ φ ψ : TestC0, IndepFun (U φ) (V ψ) P := fun φ ψ =>
    hind.comp (GFFInv.measurable_pair _) (measurable_pairW _)
  refine ⟨measurable_replField hX.measurable hWm, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · -- Gaussian process
    classical
    have hUv : HasGaussianLaw (fun ω (i : I) => U i ω) P :=
      DGMC.hasGaussianLaw_fintype hX.gaussian (fun i : I => dT i)
    have hVv : HasGaussianLaw (fun ω (i : I) => V i ω) P :=
      hasGaussianLaw_of_map_eq (DGMC.hasGaussianLaw_fintype hX.gaussian (fun i : I => sT i))
        (measurable_pi_iff.2 fun i => hVm _).aemeasurable (hlawV I (fun i => (i : TestC0)))
    have hind' : IndepFun (fun ω (i : I) => U i ω) (fun ω (i : I) => V i ω) P :=
      hind.comp (measurable_pi_iff.2 fun i => GFFInv.measurable_pair _)
        (measurable_pi_iff.2 fun i => measurable_pairW _)
    have hsum : HasGaussianLaw (fun ω (i : I) => U i ω + V i ω) P := by
      have h := (hind'.hasGaussianLaw hUv hVv).map
        (ContinuousLinearMap.fst ℝ (I → ℝ) (I → ℝ) + ContinuousLinearMap.snd ℝ (I → ℝ) (I → ℝ))
      exact h
    refine hasGaussianLaw_congr hsum ?_
    filter_upwards [ae_all_iff.2 fun i : I => hdec i] with ω hω
    funext i
    exact (hω i).symm
  · -- centred
    rw [integral_congr_ae (hdec φ), integral_add (hUL2 φ |>.integrable one_le_two)
      (hVL2 φ |>.integrable one_le_two), hX.centered (dT φ),
      integral_eq_of_map_eq (hVm φ).aemeasurable (hXg (sT φ)).aemeasurable (hV1 φ),
      hX.centered (sT φ), add_zero]
  · -- covariance
    rw [covariance_congr_ae (hdec φ) (hdec ψ)]
    change cov[U φ + V φ, U ψ + V ψ; P] = _
    rw [covariance_add_left (hUL2 φ) (hVL2 φ) ((hUL2 ψ).add (hVL2 ψ)),
      covariance_add_right (hUL2 φ) (hUL2 ψ) (hVL2 ψ), covariance_add_right (hVL2 φ) (hUL2 ψ) (hVL2 ψ),
      (hindUV φ ψ).covariance_eq_zero (hUL2 φ) (hVL2 ψ),
      ((hindUV ψ φ).symm).covariance_eq_zero (hVL2 φ) (hUL2 ψ),
      covariance_eq_of_map_eq ((hVm φ).prodMk (hVm ψ)).aemeasurable
        (((GFFInv.measurable_pair _).comp hX.measurable).prodMk
          ((GFFInv.measurable_pair _).comp hX.measurable)).aemeasurable (hV2 φ ψ)]
    change cov[fun ω => X ω (dT φ).1, fun ω => X ω (dT ψ).1; P] + 0 + (0 +
      cov[fun ω => X ω (sT φ).1, fun ω => X ω (sT ψ).1; P]) = _
    rw [hX.covariance_eq, hX.covariance_eq]
    -- `logCov φ ψ` splits along `φ = (φ − φ̄) + φ̄`
    have hsplit : ∀ θ : TestC0, (fun ω => X ω θ.1) = fun ω => X ω (dT θ).1 + X ω (sT θ).1 := fun θ => by
      funext ω
      simp only [dT, sT, map_sub, sub_add_cancel]
    have hXL2 : ∀ θ : TestC0, MemLp (fun ω => X ω θ.1) 2 P := fun θ => (hXg θ).memLp_two
    have key : logCov φ.1 ψ.1 = logCov (dT φ).1 (dT ψ).1 + logCov (dT φ).1 (sT ψ).1 +
        (logCov (sT φ).1 (dT ψ).1 + logCov (sT φ).1 (sT ψ).1) := by
      rw [← hX.covariance_eq φ ψ, hsplit φ, hsplit ψ]
      change cov[(fun ω => X ω (dT φ).1) + fun ω => X ω (sT φ).1,
        (fun ω => X ω (dT ψ).1) + fun ω => X ω (sT ψ).1; P] = _
      rw [covariance_add_left (hXL2 _) (hXL2 _) ((hXL2 _).add (hXL2 _)),
        covariance_add_right (hXL2 _) (hXL2 _) (hXL2 _),
        covariance_add_right (hXL2 _) (hXL2 _) (hXL2 _),
        hX.covariance_eq, hX.covariance_eq, hX.covariance_eq, hX.covariance_eq]
    have h0 : logCov (dT φ).1 (sT ψ).1 = 0 := logCov_sub_symmTest_symmTest φ.1 ψ.1
    have h0' : logCov (sT φ).1 (dT ψ).1 = 0 := by
      rw [← hX.covariance_eq, covariance_comm, hX.covariance_eq]
      exact logCov_sub_symmTest_symmTest ψ.1 φ.1
    rw [key, h0, h0']

end MatedCRTHarmonic.GMCFacts
