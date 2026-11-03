/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.Existence at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.AdmissibleAux
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Non-vacuity of the GFF hypotheses

`exists_zeroGFF` and `exists_freeGFF`: the hypotheses `IsZeroBoundaryGFFH` and
`IsFreeGFFModConstH` are satisfiable.

Route (Gram representation + Gaussian series):

1. `HeatFeature`: for admissible measures, `kernelCov greenH μ ν` and
   `kernelCov2 neumannH p q` (balanced pairs) are `L²(dt ⊗ γ)` inner products of explicit
   heat-kernel features `hkFeat` (Fourier features, method of images, Frullani).
2. `GaussianSeries`: any family of vectors in a separable Hilbert space is the Gram
   representation of a Gaussian family on `(ℕ → ℝ, stdP)`.
3. The zero-boundary field uses the features of `(μ, 0)`; the free field uses the features of
   `(μ, μ(ℂ) • ρ₀)` for a fixed admissible probability measure `ρ₀`, whose contributions
   cancel in balanced differences. Non-admissible measures get the value `0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace ENNReal

namespace QuantumZipper

namespace GFFExist

open LQGDimension.ExistAsm

/-- The index set: admissible measures. -/
abbrev AdmT := {μ : Measure ℂ // IsAdmissibleH μ}

/-- The Hilbert space `L²(dt ⊗ γ)`. -/
abbrev HkE := Lp ℝ 2 hkM

instance : SFinite hkM := by unfold hkM; infer_instance

instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

instance : TopologicalSpace.SeparableSpace HkE := inferInstance

lemma hk_inner_toLp {F G : ℝ × ℂ → ℝ} (hF : MemLp F 2 hkM) (hG : MemLp G 2 hkM) :
    ⟪hF.toLp F, hG.toLp G⟫ = ∫ x, F x * G x ∂hkM := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Laws of four-term combinations, in a convenient form. -/
lemma gs_comb4 {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : T → E}
    {X : T → (ℕ → ℝ) → ℝ}
    (hX : ∀ {ι : Type} [Fintype ι] (τ : ι → T) (c : ι → ℝ),
      HasLaw (fun ω => ∑ i, c i * X (τ i) ω)
        (gaussianReal 0 (‖∑ i, c i • v (τ i)‖ ^ 2).toNNReal) stdP)
    (t : Fin 4 → T) (a : Fin 4 → ℝ) (Y : (ℕ → ℝ) → ℝ) (hY : ∀ ω, Y ω = ∑ i, a i * X (t i) ω)
    (u : E) (hu : u = ∑ i, a i • v (t i)) :
    HasLaw Y (gaussianReal 0 (‖u‖ ^ 2).toNNReal) stdP := by
  have e : Y = fun ω => ∑ i, a i * X (t i) ω := funext hY
  rw [e, hu]
  exact hX t a

/-! ### Zero-boundary features -/

theorem zeroMemLp (μ : AdmT) : MemLp (hkFeat (-1) (μ.1, 0)) 2 hkM :=
  hk_memLp (-1) (by norm_num) (μ.1, 0) (gffEx_hkGood μ.2 μ.2)
    (gffEx_hkGood μ.2 gffEx_admissible_zero) (gffEx_hkGood gffEx_admissible_zero μ.2)
    (gffEx_hkGood gffEx_admissible_zero gffEx_admissible_zero) (by ring)

/-- The zero-boundary feature vector of an admissible measure. -/
def zeroVec (μ : AdmT) : HkE := (zeroMemLp μ).toLp _

theorem zeroVec_inner (μ ν : AdmT) : ⟪zeroVec μ, zeroVec ν⟫ = kernelCov greenH μ.1 ν.1 := by
  rw [zeroVec, zeroVec, hk_inner_toLp,
    hk_integral_mul (-1) (by norm_num) (μ.1, 0) (ν.1, 0) (gffEx_hkGood μ.2 ν.2)
      (gffEx_hkGood μ.2 gffEx_admissible_zero) (gffEx_hkGood gffEx_admissible_zero ν.2)
      (gffEx_hkGood gffEx_admissible_zero gffEx_admissible_zero) (by ring)
      (zeroMemLp μ) (zeroMemLp ν), hkK_neg_one]
  simp [kernelCov2, kernelCov]

/-! ### Free-boundary features -/

/-- The reference measure with the mass of `μ`. -/
def freeRef (μ : Measure ℂ) : Measure ℂ := (μ Set.univ) • gffExRef

theorem freeRef_admissible {μ : Measure ℂ} (hμ : IsAdmissibleH μ) : IsAdmissibleH (freeRef μ) :=
  haveI := hμ.1
  gffEx_admissible_smul gffEx_admissible_ref (measure_ne_top μ _)

theorem freeRef_real_univ (μ : Measure ℂ) : (freeRef μ).real univ = μ.real univ := by
  simp [freeRef, measureReal_def, Measure.smul_apply]

theorem freeMemLp (μ : AdmT) : MemLp (hkFeat 1 (μ.1, freeRef μ.1)) 2 hkM :=
  hk_memLp 1 (by norm_num) (μ.1, freeRef μ.1) (gffEx_hkGood μ.2 μ.2)
    (gffEx_hkGood μ.2 (freeRef_admissible μ.2)) (gffEx_hkGood (freeRef_admissible μ.2) μ.2)
    (gffEx_hkGood (freeRef_admissible μ.2) (freeRef_admissible μ.2))
    (by simp only [freeRef_real_univ, sub_self, mul_zero])

/-- The free-boundary feature vector of an admissible measure. -/
def freeVec (μ : AdmT) : HkE := (freeMemLp μ).toLp _

theorem pairMemLp (μ ν : AdmT) (h : μ.1 univ = ν.1 univ) :
    MemLp (hkFeat 1 (μ.1, ν.1)) 2 hkM :=
  hk_memLp 1 (by norm_num) (μ.1, ν.1) (gffEx_hkGood μ.2 μ.2) (gffEx_hkGood μ.2 ν.2)
    (gffEx_hkGood ν.2 μ.2) (gffEx_hkGood ν.2 ν.2)
    (by simp only [measureReal_def, h, sub_self, mul_zero])

theorem freeVec_sub (μ ν : AdmT) (h : μ.1 univ = ν.1 univ) :
    freeVec μ - freeVec ν = (pairMemLp μ ν h).toLp _ := by
  rw [freeVec, freeVec, ← MemLp.toLp_sub]
  refine MemLp.toLp_congr _ _ (ae_of_all _ fun q => ?_)
  have hr : freeRef ν.1 = freeRef μ.1 := by simp only [freeRef, h]
  simp only [Pi.sub_apply, hkFeat, hr]
  ring

theorem freeVec_inner (μ ν μ' ν' : AdmT) (h : μ.1 univ = ν.1 univ)
    (h' : μ'.1 univ = ν'.1 univ) :
    ⟪freeVec μ - freeVec ν, freeVec μ' - freeVec ν'⟫ =
      kernelCov2 neumannH (μ.1, ν.1) (μ'.1, ν'.1) := by
  rw [freeVec_sub μ ν h, freeVec_sub μ' ν' h', hk_inner_toLp,
    hk_integral_mul 1 (by norm_num) (μ.1, ν.1) (μ'.1, ν'.1) (gffEx_hkGood μ.2 μ'.2)
      (gffEx_hkGood μ.2 ν'.2) (gffEx_hkGood ν.2 μ'.2) (gffEx_hkGood ν.2 ν'.2)
      (by simp only [measureReal_def, h, sub_self, mul_zero])
      (pairMemLp μ ν h) (pairMemLp μ' ν' h'), hkK_one]

/-! ### Linearity -/

theorem gffEx_admissible_add {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    IsAdmissibleH (μ + ν) := by
  obtain ⟨hf1, ⟨K₁, hK₁, hK₁H, hK₁0⟩, C₁, hC₁, hb₁⟩ := hμ
  obtain ⟨hf2, ⟨K₂, hK₂, hK₂H, hK₂0⟩, C₂, hC₂, hb₂⟩ := hν
  refine ⟨inferInstance, ⟨K₁ ∪ K₂, hK₁.union hK₂, union_subset hK₁H hK₂H, ?_⟩, C₁ + C₂,
    ENNReal.add_lt_top.2 ⟨hC₁, hC₂⟩, fun y => ?_⟩
  · rw [Measure.add_apply, compl_union, measure_mono_null inter_subset_left hK₁0,
      measure_mono_null inter_subset_right hK₂0, add_zero]
  · rw [lintegral_add_measure]
    exact add_le_add (hb₁ y) (hb₂ y)

theorem gffEx_admissible_comb {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν)
    (a b : NNReal) : IsAdmissibleH (a • μ + b • ν) := by
  have e1 : a • μ = (a : ℝ≥0∞) • μ := by ext s; simp
  have e2 : b • ν = (b : ℝ≥0∞) • ν := by ext s; simp
  rw [e1, e2]
  exact gffEx_admissible_add (gffEx_admissible_smul hμ ENNReal.coe_ne_top)
    (gffEx_admissible_smul hν ENNReal.coe_ne_top)

theorem freeVec_comb (μ ν : AdmT) (a b : NNReal) (w : AdmT) (hw : w.1 = a • μ.1 + b • ν.1) :
    freeVec w = (a : ℝ) • freeVec μ + (b : ℝ) • freeVec ν := by
  have := μ.2.1
  have := ν.2.1
  rw [freeVec, freeVec, freeVec, ← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul,
    ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ (ae_of_all _ fun q => ?_)
  have hm : ((a • μ.1 + b • ν.1) univ).toReal =
      (a : ℝ) * (μ.1 univ).toReal + (b : ℝ) * (ν.1 univ).toReal := by
    rw [Measure.add_apply, Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply,
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hkFeat, freeRef, hkA_smul, hw,
    hkA_comb, hm]
  ring

end GFFExist

open GFFExist LQGDimension.ExistAsm

/-- **Non-vacuity of the zero-boundary GFF hypothesis.** -/
theorem exists_zeroGFF : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (X : Ω → FieldSample), IsProbabilityMeasure P ∧ IsZeroBoundaryGFFH X P := by
  classical
  obtain ⟨X, hXm, hX⟩ := gs_process_hilbert AdmT zeroVec
  set F : (ℕ → ℝ) → FieldSample := fun ω μ => if h : IsAdmissibleH μ then X ⟨μ, h⟩ ω else 0
    with hF
  have hFX : ∀ (μ : Measure ℂ) (h : IsAdmissibleH μ), (fun ω => F ω μ) = X ⟨μ, h⟩ := by
    intro μ h; funext ω; simp only [hF, h, ↓reduceDIte]
  have hlaw1 : ∀ μ : AdmT, HasLaw (X μ) (gaussianReal 0 (‖zeroVec μ‖ ^ 2).toNNReal) stdP :=
    fun μ => gs_comb4 hX ![μ, μ, μ, μ] ![1, 0, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]) _ (by simp [Fin.sum_univ_four])
  refine ⟨ℕ → ℝ, inferInstance, stdP, F, inferInstance, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro μ
    by_cases h : IsAdmissibleH μ
    · rw [hFX μ h]; exact hXm _
    · have : (fun ω => F ω μ) = fun _ => 0 := by funext ω; simp only [hF, h, ↓reduceDIte]
      rw [this]; exact measurable_const
  · have e : (fun (μ : AdmT) (ω : ℕ → ℝ) => F ω μ.1) = X := by
      funext μ ω; exact congrFun (hFX μ.1 μ.2) ω
    rw [e]
    exact gs_isGaussianProcess (fun t => (hXm t).aemeasurable)
      fun I c => ⟨_, hX (fun i : I => (i : AdmT)) c⟩
  · intro μ hμ
    rw [hFX μ hμ]
    exact gs_integral_eq_zero (hlaw1 ⟨μ, hμ⟩)
  · intro μ ν hμ hν
    rw [hFX μ hμ, hFX ν hν, ← zeroVec_inner ⟨μ, hμ⟩ ⟨ν, hν⟩]
    refine gs_cov_eq (hlaw1 _) (hlaw1 _) ?_
    exact gs_comb4 hX ![⟨μ, hμ⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩, ⟨μ, hμ⟩] ![1, 1, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]) _ (by simp [Fin.sum_univ_four])

/-- **Non-vacuity of the free-boundary GFF hypothesis.** -/
theorem exists_freeGFF : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (X : Ω → FieldSample), IsProbabilityMeasure P ∧ IsFreeGFFModConstH X P := by
  classical
  obtain ⟨X, hXm, hX⟩ := gs_process_hilbert AdmT freeVec
  set F : (ℕ → ℝ) → FieldSample := fun ω μ => if h : IsAdmissibleH μ then X ⟨μ, h⟩ ω else 0
    with hF
  have hFX : ∀ (μ : Measure ℂ) (h : IsAdmissibleH μ) ω, F ω μ = X ⟨μ, h⟩ ω := by
    intro μ h ω; simp only [hF, h, ↓reduceDIte]
  have hdiff : ∀ (μ ν : Measure ℂ) (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν),
      (fun ω => F ω μ - F ω ν) = fun ω => X ⟨μ, hμ⟩ ω - X ⟨ν, hν⟩ ω := by
    intro μ ν hμ hν; funext ω; rw [hFX μ hμ, hFX ν hν]
  have hlaw2 : ∀ μ ν : AdmT, HasLaw (fun ω => X μ ω - X ν ω)
      (gaussianReal 0 (‖freeVec μ - freeVec ν‖ ^ 2).toNNReal) stdP :=
    fun μ ν => gs_comb4 hX ![μ, ν, μ, μ] ![1, -1, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four, sub_eq_add_neg])
  refine ⟨ℕ → ℝ, inferInstance, stdP, F, inferInstance, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro μ
    by_cases h : IsAdmissibleH μ
    · have : (fun ω => F ω μ) = X ⟨μ, h⟩ := funext (hFX μ h)
      rw [this]; exact hXm _
    · have : (fun ω => F ω μ) = fun _ => 0 := by funext ω; simp only [hF, h, ↓reduceDIte]
      rw [this]; exact measurable_const
  · refine gs_isGaussianProcess (fun p => ?_) fun I c => ?_
    · rw [hdiff _ _ p.2.1 p.2.2.1]
      exact ((hXm _).sub (hXm _)).aemeasurable
    · set τ : I ⊕ I → AdmT := Sum.elim (fun i => ⟨i.1.1.1, i.1.2.1⟩)
        (fun i => ⟨i.1.1.2, i.1.2.2.1⟩) with hτ
      set c' : I ⊕ I → ℝ := Sum.elim c (fun i => -c i) with hc'
      have e : (fun ω => ∑ i : I, c i * (F ω i.1.1.1 - F ω i.1.1.2)) =
          fun ω => ∑ j, c' j * X (τ j) ω := by
        funext ω
        rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hτ, hc', Sum.elim_inl, Sum.elim_inr]
        rw [hFX _ i.1.2.1 ω, hFX _ i.1.2.2.1 ω]
        ring
      exact ⟨_, e ▸ hX τ c'⟩
  · intro μ ν hμ hν _
    rw [hdiff μ ν hμ hν]
    exact gs_integral_eq_zero (hlaw2 ⟨μ, hμ⟩ ⟨ν, hν⟩)
  · intro p q hp1 hp2 hp hq1 hq2 hq
    rw [hdiff _ _ hp1 hp2, hdiff _ _ hq1 hq2]
    have hinner := freeVec_inner ⟨p.1, hp1⟩ ⟨p.2, hp2⟩ ⟨q.1, hq1⟩ ⟨q.2, hq2⟩ hp hq
    simp only [Prod.mk.eta] at hinner
    rw [← hinner]
    refine gs_cov_eq (hlaw2 _ _) (hlaw2 _ _) ?_
    exact gs_comb4 hX ![⟨p.1, hp1⟩, ⟨p.2, hp2⟩, ⟨q.1, hq1⟩, ⟨q.2, hq2⟩] ![1, -1, 1, -1] _
      (fun ω => by simp [Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four]; abel)
  · intro μ ν hμ hν a b
    have hw := gffEx_admissible_comb hμ hν a b
    have hlaw := gs_comb4 hX ![⟨_, hw⟩, ⟨μ, hμ⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩] ![1, -(a : ℝ), -(b : ℝ), 0]
      (fun ω => X ⟨_, hw⟩ ω - ((a : ℝ) * X ⟨μ, hμ⟩ ω + (b : ℝ) * X ⟨ν, hν⟩ ω))
      (fun ω => by simp [Fin.sum_univ_four]; ring) (0 : HkE)
      (by
        simp [Fin.sum_univ_four, freeVec_comb ⟨μ, hμ⟩ ⟨ν, hν⟩ a b ⟨_, hw⟩ rfl]
        try module)
    have h0 : (‖(0 : HkE)‖ ^ 2).toNNReal = 0 := by simp
    have hae : ∀ᵐ ω ∂stdP,
        X ⟨_, hw⟩ ω - ((a : ℝ) * X ⟨μ, hμ⟩ ω + (b : ℝ) * X ⟨ν, hν⟩ ω) = 0 := by
      refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
      rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
      exact Filter.eventually_pure.2 rfl
    filter_upwards [hae] with ω hω
    rw [hFX _ hw ω, hFX μ hμ ω, hFX ν hν ω]
    linarith

end QuantumZipper
