/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.DualNorm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# GFF-K3, nodes F2, F5, F6, E1: dual Dirichlet norms as Hilbert norms

* F2: `norm_sq_clm_complex`, `norm_fderiv_sq_eq_gradInner`.
* F6: elementary monotonicity / congruence lemmas for `dualNormSq`.
* E1: `isDNSpace_zeroSpace`, `isDNSpace_mixedSpace`.
* F5: the gradient space `GradSpace D = L²((vol|D) ⊗ count_{Fin 2})`, the gradient feature map
  `gradFeat`, the closure `gradClosure D V` of its range, Riesz vectors `rieszVec`, and the
  identities `dualNormSq = ‖rieszVec‖²`, `dualCov = ⟪rieszVec, rieszVec⟫`; the admissible cone is
  closed under `+` and `ℝ≥0`-scaling.

Route for the Riesz vector: `L_μ` factors through `gradFeat` (quotient by the kernel), is bounded
by `√(dualNormSq)` on the range, extends to the whole space by Hahn–Banach, and is represented in
the complete space `gradClosure` by `InnerProductSpace.toDual`. The identity
`dualNormSq = ‖v‖²` holds for *any* `v ∈ gradClosure` representing `L_μ` on `V`
(`dualNormSq_eq_of_pairing`), which gives additivity and polarization without uniqueness.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal NNReal

namespace QuantumZipper.K3

/-! ## F2 -/

/-- The operator norm of a real functional on `ℂ` is the Euclidean norm of its gradient. -/
theorem norm_sq_clm_complex (L : ℂ →L[ℝ] ℝ) : ‖L‖ ^ 2 = L 1 ^ 2 + L Complex.I ^ 2 := by
  set v : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm L with hv
  have hL : ‖L‖ = ‖v‖ := by rw [hv, LinearIsometryEquiv.norm_map]
  have h1 : L 1 = v.re := by
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℂ) (x := 1) (y := L), ← hv]
    simp [real_inner_eq_re_inner]
  have hI : L Complex.I = v.im := by
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℂ) (x := Complex.I) (y := L), ← hv]
    simp [real_inner_eq_re_inner]
  rw [hL, h1, hI, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- `⟪∇u, ∇φ⟫(z)` in coordinates. -/
def gradInner (u φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ u z 1 * fderiv ℝ φ z 1 + fderiv ℝ u z Complex.I * fderiv ℝ φ z Complex.I

theorem norm_fderiv_sq_eq_gradInner (f : ℂ → ℝ) (z : ℂ) :
    ‖fderiv ℝ f z‖ ^ 2 = gradInner f f z := by
  rw [norm_sq_clm_complex]; simp [gradInner, sq]

/-! ## F6 -/

section F6

variable {D D' : Set ℂ} {V V' : Set (ℂ → ℝ)} {μ : Measure ℂ}

theorem dualNormSq_mono_space (h : V ⊆ V') : dualNormSq D V μ ≤ dualNormSq D V' μ := by
  unfold dualNormSq
  exact biSup_mono fun f hf => ⟨h hf.1, hf.2⟩

theorem dualNormSq_congr_energy
    (h : ∀ f ∈ V, dirichletEnergyOn D f = dirichletEnergyOn D' f) :
    dualNormSq D V μ = dualNormSq D' V μ := by
  unfold dualNormSq
  refine iSup_congr fun f => ?_
  by_cases hf : f ∈ V
  · simp only [Set.mem_ofPred_eq, h f hf]
  · simp [hf]

lemma energy_eq_of_tsupport_subset {f : ℂ → ℝ} (h : tsupport f ⊆ D) :
    dirichletEnergyOn D f = (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ f z‖ ^ 2 := by
  unfold dirichletEnergyOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro z hz
  have : fderiv ℝ f z = 0 := by
    by_contra hne
    exact hz (h (support_fderiv_subset (𝕜 := ℝ) (f := f) hne))
  simp [this]

theorem dualNormSq_zeroSpace_mono {U U' : Set ℂ} (_hU : IsOpen U) (hUU' : U ⊆ U') :
    dualNormSq U (zeroSpace U) μ ≤ dualNormSq U' (zeroSpace U') μ := by
  rw [dualNormSq_congr_energy (D' := U') (fun f hf => by
    rw [energy_eq_of_tsupport_subset hf.2.2, energy_eq_of_tsupport_subset (hf.2.2.trans hUU')])]
  exact dualNormSq_mono_space fun f hf => ⟨hf.1, hf.2.1, hf.2.2.trans hUU'⟩

theorem dualNormSq_zeroSpace_restrict {U : Set ℂ} (_hU : IsOpen U) [IsFiniteMeasure μ] :
    dualNormSq U (zeroSpace U) μ = dualNormSq U (zeroSpace U) (μ.restrict U) := by
  unfold dualNormSq
  refine iSup_congr fun f => iSup_congr fun hf => ?_
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro z hz
  by_contra hne
  exact hz (hf.1.2.2 (subset_tsupport f hne))

end F6

/-! ## Test spaces (F5 structure, E1) -/

/-- A test space for dual Dirichlet norms on `D`: a real vector space of `C¹` finite-energy
functions. -/
structure IsDNSpace (D : Set ℂ) (V : Set (ℂ → ℝ)) : Prop where
  smooth : ∀ f ∈ V, ContDiff ℝ 1 f
  energy : ∀ f ∈ V, IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D
  zero_mem : (0 : ℂ → ℝ) ∈ V
  add_mem : ∀ f ∈ V, ∀ g ∈ V, f + g ∈ V
  smul_mem : ∀ (a : ℝ), ∀ f ∈ V, a • f ∈ V

lemma one_le_smooth : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)

lemma smooth_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp

theorem isDNSpace_zeroSpace (U : Set ℂ) : IsDNSpace U (zeroSpace U) where
  smooth f hf := hf.1.of_le one_le_smooth
  energy f hf := by
    have hc : Continuous fun z => ‖fderiv ℝ f z‖ ^ 2 :=
      ((hf.1.continuous_fderiv smooth_ne_zero).norm).pow 2
    have hs : HasCompactSupport fun z => ‖fderiv ℝ f z‖ ^ 2 :=
      (hf.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L => ‖L‖ ^ 2) (by simp)
    exact (hc.integrable_of_hasCompactSupport hs).integrableOn
  zero_mem := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem f hf g hg := ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem a f hf := ⟨contDiff_const.smul hf.1,
    hf.2.1.comp_left (g := fun x => a • x) (smul_zero a),
    (tsupport_smul_subset_right (fun _ => a) f).trans hf.2.2⟩

theorem isDNSpace_mixedSpace (D S : Set ℂ) : IsDNSpace D (mixedSpace D S) where
  smooth f hf := hf.1.of_le one_le_smooth
  energy f hf := hf.2.1
  zero_mem := ⟨contDiff_const, by simp, univ, isOpen_univ, subset_univ _, fun _ _ => rfl⟩
  add_mem f hf g hg := by
    obtain ⟨hfs, hfe, N₁, hN₁, hsN₁, hf0⟩ := hf
    obtain ⟨hgs, hge, N₂, hN₂, hsN₂, hg0⟩ := hg
    refine ⟨hfs.add hgs, ?_, N₁ ∩ N₂, hN₁.inter hN₂, subset_inter hsN₁ hsN₂,
      fun z hz => by simp [hf0 z hz.1, hg0 z hz.2]⟩
    refine ((hfe.const_mul 2).add (hge.const_mul 2)).mono'
      (((hfs.add hgs).continuous_fderiv smooth_ne_zero).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    rw [fderiv_add (hfs.differentiable smooth_ne_zero z) (hgs.differentiable smooth_ne_zero z),
      norm_pow, norm_norm]
    have h := norm_add_le (fderiv ℝ f z) (fderiv ℝ g z)
    have h0 := norm_nonneg (fderiv ℝ f z + fderiv ℝ g z)
    nlinarith [norm_nonneg (fderiv ℝ f z), norm_nonneg (fderiv ℝ g z),
      sq_nonneg (‖fderiv ℝ f z‖ - ‖fderiv ℝ g z‖)]
  smul_mem a f hf := by
    obtain ⟨hfs, hfe, N, hN, hsN, hf0⟩ := hf
    refine ⟨contDiff_const.smul hfs, ?_, N, hN, hsN, fun z hz => by simp [hf0 z hz]⟩
    refine (hfe.const_mul (a ^ 2)).congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [fderiv_const_smul (hfs.differentiable smooth_ne_zero z) a, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]

/-! ## F5: the gradient space -/

/-- The measure `(vol|D) ⊗ count` on `ℂ × Fin 2`. -/
abbrev gradMeasure (D : Set ℂ) : Measure (ℂ × Fin 2) := (volume.restrict D).prod Measure.count

/-- The gradient space `L²((vol|D) ⊗ count_{Fin 2})`. -/
abbrev GradSpace (D : Set ℂ) := Lp ℝ 2 (gradMeasure D)

instance fact_two_ne_top_K3 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

instance (D : Set ℂ) : SFinite (gradMeasure D) := by unfold gradMeasure; infer_instance

instance instSeparableGradSpace (D : Set ℂ) : TopologicalSpace.SeparableSpace (GradSpace D) :=
  inferInstance

/-- The coordinate directions `1, I`. -/
def gradVec (i : Fin 2) : ℂ := if i = 0 then 1 else Complex.I

/-- `(z, i) ↦ (2π)^{-1/2} ∂_i f(z)`. -/
def gradVal (f : ℂ → ℝ) (p : ℂ × Fin 2) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * fderiv ℝ f p.1 (gradVec p.2)

open Classical in
/-- The gradient feature `(2π)^{-1/2} ∇f ∈ GradSpace D` (`0` if not square integrable). -/
def gradFeat (D : Set ℂ) (f : ℂ → ℝ) : GradSpace D :=
  if h : MemLp (gradVal f) 2 (gradMeasure D) then h.toLp _ else 0

/-- The closure of the span of the gradient features of `V`. -/
def gradClosure (D : Set ℂ) (V : Set (ℂ → ℝ)) : Submodule ℝ (GradSpace D) :=
  (Submodule.span ℝ (gradFeat D '' V)).topologicalClosure

instance (D : Set ℂ) (V : Set (ℂ → ℝ)) : CompleteSpace (gradClosure D V) := by
  unfold gradClosure; infer_instance

instance (D : Set ℂ) (V : Set (ℂ → ℝ)) : TopologicalSpace.SeparableSpace (gradClosure D V) :=
  inferInstance

section GradFeat

variable {D : Set ℂ} {V : Set (ℂ → ℝ)} {μ ν : Measure ℂ}

lemma measurable_gradVal {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) : Measurable (gradVal f) := by
  have hc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have h1 : Measurable fun p : ℂ × Fin 2 => fderiv ℝ f p.1 1 :=
    (hc.clm_apply continuous_const).measurable.comp measurable_fst
  have hI : Measurable fun p : ℂ × Fin 2 => fderiv ℝ f p.1 Complex.I :=
    (hc.clm_apply continuous_const).measurable.comp measurable_fst
  have : gradVal f = fun p => (Real.sqrt (2 * Real.pi))⁻¹ *
      (if p.2 = 0 then fderiv ℝ f p.1 1 else fderiv ℝ f p.1 Complex.I) := by
    funext p; simp only [gradVal, gradVec]; split_ifs <;> rfl
  rw [this]
  exact measurable_const.mul
    (Measurable.ite (measurable_snd (measurableSet_singleton 0)) h1 hI)

lemma sum_gradVal_sq (f : ℂ → ℝ) (z : ℂ) :
    ∑ i : Fin 2, gradVal f (z, i) ^ 2 = (2 * Real.pi)⁻¹ * ‖fderiv ℝ f z‖ ^ 2 := by
  have hc : ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 = (2 * Real.pi)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [norm_sq_clm_complex, Fin.sum_univ_two]
  simp only [gradVal, gradVec, mul_pow, hc]
  simp
  ring

lemma memLp_gradVal {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D) :
    MemLp (gradVal f) 2 (gradMeasure D) := by
  rw [memLp_two_iff_integrable_sq (measurable_gradVal hf).aestronglyMeasurable]
  refine Integrable.mono' ((hE.const_mul (2 * Real.pi)⁻¹).comp_fst
    (Measure.count : Measure (Fin 2))) ((measurable_gradVal hf).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sum_gradVal_sq]
  exact Finset.single_le_sum (f := fun i => gradVal f (p.1, i) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ p.2)

lemma energy_nonneg (D : Set ℂ) (f : ℂ → ℝ) : 0 ≤ dirichletEnergyOn D f :=
  mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg fun _ => sq_nonneg _)

/-- F2 in `GradSpace`: `‖gradFeat D f‖² = E_D f`. -/
theorem norm_gradFeat_sq {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D) :
    ‖gradFeat D f‖ ^ 2 = dirichletEnergyOn D f := by
  have hL := memLp_gradVal hf hE
  rw [gradFeat, dif_pos hL, ← real_inner_self_eq_norm_sq, L2.inner_def]
  have h1 : ∫ p, ⟪hL.toLp _ p, hL.toLp _ p⟫ ∂gradMeasure D =
      ∫ p, gradVal f p ^ 2 ∂gradMeasure D := by
    refine integral_congr_ae ?_
    filter_upwards [hL.coeFn_toLp] with p hp
    rw [hp, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [h1, integral_prod _ hL.integrable_sq]
  simp only [integral_count, sum_gradVal_sq]
  rw [integral_const_mul]
  rfl

lemma gradVal_add {f g : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    gradVal (f + g) = gradVal f + gradVal g := by
  funext p
  simp only [gradVal, Pi.add_apply, fderiv_add (hf.differentiable one_ne_zero p.1)
    (hg.differentiable one_ne_zero p.1), ContinuousLinearMap.add_apply]
  ring

lemma gradVal_smul (a : ℝ) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) :
    gradVal (a • f) = a • gradVal f := by
  funext p
  simp only [gradVal, Pi.smul_apply, fderiv_const_smul (hf.differentiable one_ne_zero p.1) a,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma gradFeat_add (hV : IsDNSpace D V) {f g : ℂ → ℝ} (hf : f ∈ V) (hg : g ∈ V) :
    gradFeat D (f + g) = gradFeat D f + gradFeat D g := by
  have hLf := memLp_gradVal (hV.smooth f hf) (hV.energy f hf)
  have hLg := memLp_gradVal (hV.smooth g hg) (hV.energy g hg)
  have hLfg := memLp_gradVal (D := D) (hV.smooth _ (hV.add_mem f hf g hg))
    (hV.energy _ (hV.add_mem f hf g hg))
  rw [gradFeat, gradFeat, gradFeat, dif_pos hLf, dif_pos hLg, dif_pos hLfg, ← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p =>
    congrFun (gradVal_add (hV.smooth f hf) (hV.smooth g hg)) p)

lemma gradFeat_smul (hV : IsDNSpace D V) (a : ℝ) {f : ℂ → ℝ} (hf : f ∈ V) :
    gradFeat D (a • f) = a • gradFeat D f := by
  have hLf := memLp_gradVal (hV.smooth f hf) (hV.energy f hf)
  have hLaf := memLp_gradVal (D := D) (hV.smooth _ (hV.smul_mem a f hf))
    (hV.energy _ (hV.smul_mem a f hf))
  rw [gradFeat, gradFeat, dif_pos hLf, dif_pos hLaf, ← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p =>
    congrFun (gradVal_smul a (hV.smooth f hf)) p)

lemma gradFeat_zero (hV : IsDNSpace D V) : gradFeat D 0 = 0 := by
  have := gradFeat_smul hV 0 hV.zero_mem
  simpa using this

lemma gradFeat_eq_zero_of_energy (hV : IsDNSpace D V) {f : ℂ → ℝ} (hf : f ∈ V)
    (h : dirichletEnergyOn D f = 0) : gradFeat D f = 0 := by
  have : ‖gradFeat D f‖ ^ 2 = 0 := by
    rw [norm_gradFeat_sq (hV.smooth f hf) (hV.energy f hf), h]
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)

lemma gradFeat_mem_gradClosure {f : ℂ → ℝ} (hf : f ∈ V) : gradFeat D f ∈ gradClosure D V :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

/-- The range of `gradFeat` on `V`, as a submodule. -/
def featSub (hV : IsDNSpace D V) : Submodule ℝ (GradSpace D) where
  carrier := gradFeat D '' V
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hV.add_mem f hf g hg, gradFeat_add hV hf hg⟩
  zero_mem' := ⟨0, hV.zero_mem, gradFeat_zero hV⟩
  smul_mem' := by
    rintro a _ ⟨f, hf, rfl⟩
    exact ⟨a • f, hV.smul_mem a f hf, gradFeat_smul hV a hf⟩

lemma mem_image_of_mem_span (hV : IsDNSpace D V) {w : GradSpace D}
    (hw : w ∈ Submodule.span ℝ (gradFeat D '' V)) : w ∈ gradFeat D '' V := by
  have h : Submodule.span ℝ (gradFeat D '' V) = featSub hV := Submodule.span_eq (featSub hV)
  rw [h] at hw
  exact hw

lemma inner_sq_le (v w : GradSpace D) : ⟪v, w⟫ ^ 2 ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [← sq_abs, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm v w) 2

/-- The sup defining `dualNormSq` dominates each quotient. -/
lemma le_dualNormSq {f : ℂ → ℝ} (hf : f ∈ V) (hp : 0 < dirichletEnergyOn D f) :
    ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn D f) ≤ dualNormSq D V μ :=
  le_iSup₂ (f := fun g (_ : g ∈ {g ∈ V | 0 < dirichletEnergyOn D g}) =>
    ENNReal.ofReal ((∫ x, g x ∂μ) ^ 2 / dirichletEnergyOn D g)) f ⟨hf, hp⟩

/-- **Key identity.** Any `v ∈ gradClosure D V` representing `f ↦ ∫ f dμ` on `V` has
`‖v‖² = dualNormSq D V μ`. No hypothesis on `μ`. -/
theorem dualNormSq_eq_of_pairing (hV : IsDNSpace D V) {v : GradSpace D}
    (hv : v ∈ gradClosure D V) (hpair : ∀ f ∈ V, ⟪v, gradFeat D f⟫ = ∫ x, f x ∂μ) :
    dualNormSq D V μ = ENNReal.ofReal (‖v‖ ^ 2) := by
  have hE : ∀ f ∈ V, ‖gradFeat D f‖ ^ 2 = dirichletEnergyOn D f :=
    fun f hf => norm_gradFeat_sq (hV.smooth f hf) (hV.energy f hf)
  apply le_antisymm
  · refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hf.2, ← hpair f hf.1, ← hE f hf.1]
    exact inner_sq_le v _
  · by_cases htop : dualNormSq D V μ = ⊤
    · rw [htop]; exact le_top
    have hN0 : 0 ≤ (dualNormSq D V μ).toReal := ENNReal.toReal_nonneg
    have hsub : (Submodule.span ℝ (gradFeat D '' V) : Set (GradSpace D)) ⊆
        {w | ⟪v, w⟫ ≤ √(dualNormSq D V μ).toReal * ‖w‖} := by
      intro w hw
      obtain ⟨f, hf, rfl⟩ := mem_image_of_mem_span hV hw
      show ⟪v, gradFeat D f⟫ ≤ √(dualNormSq D V μ).toReal * ‖gradFeat D f‖
      rcases (energy_nonneg D f).lt_or_eq with hp | hz
      · have h1 := le_dualNormSq (μ := μ) hf hp
        rw [ENNReal.ofReal_le_iff_le_toReal htop, div_le_iff₀ hp, ← hpair f hf, ← hE f hf] at h1
        calc ⟪v, gradFeat D f⟫ ≤ |⟪v, gradFeat D f⟫| := le_abs_self _
          _ = √(⟪v, gradFeat D f⟫ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ √((dualNormSq D V μ).toReal * ‖gradFeat D f‖ ^ 2) := Real.sqrt_le_sqrt h1
          _ = √(dualNormSq D V μ).toReal * ‖gradFeat D f‖ := by
            rw [Real.sqrt_mul hN0, Real.sqrt_sq (norm_nonneg _)]
      · rw [gradFeat_eq_zero_of_energy hV hf hz.symm]; simp
    have hcl : IsClosed {w : GradSpace D | ⟪v, w⟫ ≤ √(dualNormSq D V μ).toReal * ‖w‖} :=
      isClosed_le (continuous_const.inner continuous_id) (continuous_const.mul continuous_norm)
    have hv' : v ∈ closure (Submodule.span ℝ (gradFeat D '' V) : Set (GradSpace D)) := by
      rw [← Submodule.topologicalClosure_coe]; exact hv
    have h := closure_minimal hsub hcl hv'
    simp only [Set.mem_ofPred_eq, real_inner_self_eq_norm_sq] at h
    have hv2 : ‖v‖ ≤ √(dualNormSq D V μ).toReal := by
      rcases (norm_nonneg v).lt_or_eq with hp | h0
      · nlinarith [Real.sqrt_nonneg (dualNormSq D V μ).toReal]
      · rw [← h0]; exact Real.sqrt_nonneg _
    have : ‖v‖ ^ 2 ≤ (dualNormSq D V μ).toReal := by
      calc ‖v‖ ^ 2 ≤ (√(dualNormSq D V μ).toReal) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv2 2
        _ = (dualNormSq D V μ).toReal := Real.sq_sqrt hN0
    calc ENNReal.ofReal (‖v‖ ^ 2) ≤ ENNReal.ofReal (dualNormSq D V μ).toReal :=
          ENNReal.ofReal_le_ofReal this
      _ = dualNormSq D V μ := ENNReal.ofReal_toReal htop

lemma dualNormSq_eq_zero_of_nopos (h : ¬ ∃ f ∈ V, 0 < dirichletEnergyOn D f) :
    dualNormSq D V μ = 0 := by
  unfold dualNormSq
  exact le_antisymm (iSup₂_le fun f hf => (h ⟨f, hf.1, hf.2⟩).elim) bot_le

lemma eq_zero_of_mem_gradClosure_of_nopos (hV : IsDNSpace D V)
    (h : ¬ ∃ f ∈ V, 0 < dirichletEnergyOn D f) {v : GradSpace D} (hv : v ∈ gradClosure D V) :
    v = 0 := by
  have hle : gradClosure D V ≤ ⊥ := by
    show (Submodule.span ℝ (gradFeat D '' V)).topologicalClosure ≤ ⊥
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      simp only [Submodule.bot_coe, Set.mem_singleton_iff]
      exact gradFeat_eq_zero_of_energy hV hf
        (le_antisymm (not_lt.mp fun hp => h ⟨f, hf, hp⟩) (energy_nonneg D f))
    · rw [Submodule.bot_coe]; exact isClosed_singleton
  exact (Submodule.mem_bot ℝ).mp (hle hv)

lemma integrable_of_mem (hV : IsDNSpace D V) [IsFiniteMeasure μ]
    (hsupp : ∃ K, IsCompact K ∧ μ Kᶜ = 0) {f : ℂ → ℝ} (hf : f ∈ V) : Integrable f μ := by
  obtain ⟨K, hK, hμK⟩ := hsupp
  have hμ : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμK)
  rw [← hμ]
  exact (hV.smooth f hf).continuous.continuousOn.integrableOn_compact hK

/-- A (finite) dual norm bounds the pairing, including on zero-energy functions. -/
lemma sq_integral_le (hV : IsDNSpace D V) [IsFiniteMeasure μ]
    (hsupp : ∃ K, IsCompact K ∧ μ Kᶜ = 0) (hfin : dualNormSq D V μ < ⊤)
    (hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g) {f : ℂ → ℝ} (hf : f ∈ V) :
    (∫ x, f x ∂μ) ^ 2 ≤ (dualNormSq D V μ).toReal * ‖gradFeat D f‖ ^ 2 := by
  have htop := hfin.ne
  have hE : ∀ f ∈ V, ‖gradFeat D f‖ ^ 2 = dirichletEnergyOn D f :=
    fun f hf => norm_gradFeat_sq (hV.smooth f hf) (hV.energy f hf)
  have key : ∀ h ∈ V, 0 < dirichletEnergyOn D h →
      (∫ x, h x ∂μ) ^ 2 ≤ (dualNormSq D V μ).toReal * dirichletEnergyOn D h := by
    intro h hh hp
    have h1 := le_dualNormSq (μ := μ) hh hp
    rwa [ENNReal.ofReal_le_iff_le_toReal htop, div_le_iff₀ hp] at h1
  rw [hE f hf]
  rcases (energy_nonneg D f).lt_or_eq with hp | h0
  · exact key f hf hp
  · rw [← h0, mul_zero]
    obtain ⟨g, hg, hgp⟩ := hpos
    have hf0 := gradFeat_eq_zero_of_energy hV hf h0.symm
    by_contra hne
    have hLf : ∫ x, f x ∂μ ≠ 0 := fun h => hne (by rw [h]; simp)
    have hNE : 0 ≤ (dualNormSq D V μ).toReal * dirichletEnergyOn D g :=
      mul_nonneg ENNReal.toReal_nonneg (energy_nonneg D g)
    have hmem : g + (((dualNormSq D V μ).toReal * dirichletEnergyOn D g + 1 -
        ∫ x, g x ∂μ) / ∫ x, f x ∂μ) • f ∈ V :=
      hV.add_mem g hg _ (hV.smul_mem _ f hf)
    have hEeq : dirichletEnergyOn D (g + (((dualNormSq D V μ).toReal * dirichletEnergyOn D g + 1 -
        ∫ x, g x ∂μ) / ∫ x, f x ∂μ) • f) = dirichletEnergyOn D g := by
      rw [← hE _ hmem, ← hE g hg, gradFeat_add hV hg (hV.smul_mem _ f hf), gradFeat_smul hV _ hf,
        hf0, smul_zero, add_zero]
    have hint : ∫ x, (g + (((dualNormSq D V μ).toReal * dirichletEnergyOn D g + 1 -
        ∫ x, g x ∂μ) / ∫ x, f x ∂μ) • f) x ∂μ =
        (dualNormSq D V μ).toReal * dirichletEnergyOn D g + 1 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_add (integrable_of_mem hV hsupp hg)
        ((integrable_of_mem hV hsupp hf).const_mul _), integral_const_mul,
        div_mul_cancel₀ _ hLf]
      ring
    have := key _ hmem (by rw [hEeq]; exact hgp)
    rw [hint, hEeq] at this
    nlinarith

/-- Existence of a Riesz vector (needs some positive-energy element of `V`). -/
theorem exists_riesz (hV : IsDNSpace D V) [IsFiniteMeasure μ]
    (hsupp : ∃ K, IsCompact K ∧ μ Kᶜ = 0) (hfin : dualNormSq D V μ < ⊤)
    (hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g) :
    ∃ v ∈ gradClosure D V, ∀ f ∈ V, ⟪v, gradFeat D f⟫ = ∫ x, f x ∂μ := by
  have hN0 : 0 ≤ (dualNormSq D V μ).toReal := ENNReal.toReal_nonneg
  let Vs : Submodule ℝ (ℂ → ℝ) :=
    { carrier := V
      add_mem' := fun {f g} hf hg => hV.add_mem f hf g hg
      zero_mem' := hV.zero_mem
      smul_mem' := fun a f hf => hV.smul_mem a f hf }
  let T : Vs →ₗ[ℝ] GradSpace D :=
    { toFun := fun x => gradFeat D x.1
      map_add' := fun x y => gradFeat_add hV x.2 y.2
      map_smul' := fun a x => gradFeat_smul hV a x.2 }
  let L : Vs →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∫ y, x.1 y ∂μ
      map_add' := fun x y => integral_add (integrable_of_mem hV hsupp x.2)
        (integrable_of_mem hV hsupp y.2)
      map_smul' := fun a x => integral_smul a x.1 }
  have hker : LinearMap.ker T ≤ LinearMap.ker L := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h := sq_integral_le hV hsupp hfin hpos x.2
    have hx' : gradFeat D x.1 = 0 := hx
    rw [hx', norm_zero] at h
    have h2 : (∫ y, x.1 y ∂μ) ^ 2 ≤ 0 := by simpa using h
    exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h2 (sq_nonneg _))
  let ℓ₀ : LinearMap.range T →ₗ[ℝ] ℝ :=
    ((LinearMap.ker T).liftQ L hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hℓ₀ : ∀ (x : Vs) (h : T x ∈ LinearMap.range T), ℓ₀ ⟨T x, h⟩ = L x := by
    intro x h
    simp only [ℓ₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hℓ₀bd : ∀ w, ‖ℓ₀ w‖ ≤ √(dualNormSq D V μ).toReal * ‖w‖ := by
    rintro ⟨w, x, rfl⟩
    have e : ℓ₀ ⟨T x, ⟨x, rfl⟩⟩ = ∫ y, x.1 y ∂μ := hℓ₀ x _
    rw [Real.norm_eq_abs]
    refine le_trans (le_of_eq (congrArg abs e)) ?_
    show |∫ y, x.1 y ∂μ| ≤ √(dualNormSq D V μ).toReal * ‖gradFeat D x.1‖
    calc |∫ y, x.1 y ∂μ| = √((∫ y, x.1 y ∂μ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √((dualNormSq D V μ).toReal * ‖gradFeat D x.1‖ ^ 2) :=
          Real.sqrt_le_sqrt (sq_integral_le hV hsupp hfin hpos x.2)
      _ = √(dualNormSq D V μ).toReal * ‖gradFeat D x.1‖ := by
          rw [Real.sqrt_mul hN0, Real.sqrt_sq (norm_nonneg _)]
  let ℓ : StrongDual ℝ (LinearMap.range T) := ℓ₀.mkContinuous _ hℓ₀bd
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range T) ℓ
  let gK : StrongDual ℝ (gradClosure D V) := g.comp (gradClosure D V).subtypeL
  let vK : gradClosure D V := (InnerProductSpace.toDual ℝ (gradClosure D V)).symm gK
  refine ⟨(vK : GradSpace D), vK.2, fun f hf => ?_⟩
  have hmem : gradFeat D f ∈ gradClosure D V := gradFeat_mem_gradClosure hf
  have h1 : ⟪(vK : GradSpace D), gradFeat D f⟫ =
      ⟪vK, (⟨gradFeat D f, hmem⟩ : gradClosure D V)⟫ := rfl
  rw [h1, InnerProductSpace.toDual_symm_apply]
  have h3 := hg ⟨T ⟨f, hf⟩, LinearMap.mem_range_self T _⟩
  have h4 : ℓ ⟨T ⟨f, hf⟩, LinearMap.mem_range_self T _⟩ = ∫ x, f x ∂μ :=
    hℓ₀ ⟨f, hf⟩ _
  exact h3.trans h4

open Classical in
/-- The Riesz vector of `f ↦ ∫ f dμ` in `gradClosure D V` (`0` if there is none). -/
def rieszVec (D : Set ℂ) (V : Set (ℂ → ℝ)) (μ : Measure ℂ) : GradSpace D :=
  if h : ∃ v ∈ gradClosure D V, ∀ f ∈ V, ⟪v, gradFeat D f⟫ = ∫ x, f x ∂μ then h.choose else 0

lemma rieszVec_mem : rieszVec D V μ ∈ gradClosure D V := by
  unfold rieszVec
  split_ifs with h
  · exact h.choose_spec.1
  · exact zero_mem _

lemma rieszVec_pair_of_exists
    (h : ∃ v ∈ gradClosure D V, ∀ f ∈ V, ⟪v, gradFeat D f⟫ = ∫ x, f x ∂μ) :
    ∀ f ∈ V, ⟪rieszVec D V μ, gradFeat D f⟫ = ∫ x, f x ∂μ := by
  unfold rieszVec
  rw [dif_pos h]
  exact h.choose_spec.2

theorem dualNormSq_eq_norm_rieszVec (hV : IsDNSpace D V) [IsFiniteMeasure μ]
    (hsupp : ∃ K, IsCompact K ∧ μ Kᶜ = 0) (hfin : dualNormSq D V μ < ⊤) :
    dualNormSq D V μ = ENNReal.ofReal (‖rieszVec D V μ‖ ^ 2) := by
  by_cases hpos : ∃ f ∈ V, 0 < dirichletEnergyOn D f
  · exact dualNormSq_eq_of_pairing hV rieszVec_mem
      (rieszVec_pair_of_exists (exists_riesz hV hsupp hfin hpos))
  · rw [dualNormSq_eq_zero_of_nopos hpos,
      eq_zero_of_mem_gradClosure_of_nopos hV hpos (rieszVec_mem (μ := μ))]
    simp

lemma integrable_of_admissible (hV : IsDNSpace D V) (hμ : IsAdmissibleDual D V μ)
    {f : ℂ → ℝ} (hf : f ∈ V) : Integrable f μ := by
  obtain ⟨hμf, ⟨K, hK, -, hKμ⟩, -⟩ := hμ
  have := hμf
  exact integrable_of_mem hV ⟨K, hK, hKμ⟩ hf

lemma pair_rieszVec (hV : IsDNSpace D V) (hμ : IsAdmissibleDual D V μ)
    (hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g) :
    ∀ f ∈ V, ⟪rieszVec D V μ, gradFeat D f⟫ = ∫ x, f x ∂μ := by
  obtain ⟨hμf, ⟨K, hK, -, hKμ⟩, hfin⟩ := hμ
  have := hμf
  exact rieszVec_pair_of_exists (exists_riesz hV ⟨K, hK, hKμ⟩ hfin hpos)

lemma pair_add (hV : IsDNSpace D V) (hμ : IsAdmissibleDual D V μ)
    (hν : IsAdmissibleDual D V ν) (hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g) :
    ∀ f ∈ V, ⟪rieszVec D V μ + rieszVec D V ν, gradFeat D f⟫ = ∫ x, f x ∂(μ + ν) := by
  intro f hf
  rw [inner_add_left, pair_rieszVec hV hμ hpos f hf, pair_rieszVec hV hν hpos f hf,
    integral_add_measure (integrable_of_admissible hV hμ hf) (integrable_of_admissible hV hν hf)]

theorem dualCov_eq_inner_rieszVec (hV : IsDNSpace D V) (hμ : IsAdmissibleDual D V μ)
    (hν : IsAdmissibleDual D V ν) :
    dualCov D V μ ν = ⟪rieszVec D V μ, rieszVec D V ν⟫ := by
  by_cases hpos : ∃ f ∈ V, 0 < dirichletEnergyOn D f
  · have hNμ := dualNormSq_eq_of_pairing hV rieszVec_mem (pair_rieszVec hV hμ hpos)
    have hNν := dualNormSq_eq_of_pairing hV rieszVec_mem (pair_rieszVec hV hν hpos)
    have hNμν := dualNormSq_eq_of_pairing hV (add_mem rieszVec_mem rieszVec_mem)
      (pair_add hV hμ hν hpos)
    unfold dualCov
    rw [hNμ, hNν, hNμν, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal (sq_nonneg _), norm_add_sq_real]
    ring
  · have h1 : rieszVec D V μ = 0 := eq_zero_of_mem_gradClosure_of_nopos hV hpos rieszVec_mem
    have h2 : rieszVec D V ν = 0 := eq_zero_of_mem_gradClosure_of_nopos hV hpos rieszVec_mem
    unfold dualCov
    rw [dualNormSq_eq_zero_of_nopos (μ := μ + ν) hpos, dualNormSq_eq_zero_of_nopos (μ := μ) hpos,
      dualNormSq_eq_zero_of_nopos (μ := ν) hpos, h1, h2]
    simp

theorem IsAdmissibleDual.add (hV : IsDNSpace D V) (hμ : IsAdmissibleDual D V μ)
    (hν : IsAdmissibleDual D V ν) : IsAdmissibleDual D V (μ + ν) := by
  obtain ⟨hμf, ⟨K, hK, hKD, hKμ⟩, -⟩ := id hμ
  obtain ⟨hνf, ⟨K', hK', hK'D, hKν⟩, -⟩ := id hν
  have := hμf; have := hνf
  refine ⟨inferInstance, ⟨K ∪ K', hK.union hK', union_subset hKD hK'D, ?_⟩, ?_⟩
  · rw [Measure.add_apply, compl_union]
    rw [measure_mono_null inter_subset_left hKμ, measure_mono_null inter_subset_right hKν,
      add_zero]
  · by_cases hpos : ∃ f ∈ V, 0 < dirichletEnergyOn D f
    · rw [dualNormSq_eq_of_pairing hV (add_mem rieszVec_mem rieszVec_mem)
        (pair_add hV hμ hν hpos)]
      exact ENNReal.ofReal_lt_top
    · rw [dualNormSq_eq_zero_of_nopos hpos]; exact ENNReal.zero_lt_top

theorem IsAdmissibleDual.smul (hV : IsDNSpace D V) (hμ : IsAdmissibleDual D V μ) (c : ℝ≥0) :
    IsAdmissibleDual D V (c • μ) := by
  obtain ⟨hμf, ⟨K, hK, hKD, hKμ⟩, hfin⟩ := hμ
  have := hμf
  refine ⟨inferInstance, ⟨K, hK, hKD, by simp [hKμ]⟩, ?_⟩
  by_cases hpos : ∃ f ∈ V, 0 < dirichletEnergyOn D f
  · have hp := pair_rieszVec hV ⟨hμf, ⟨K, hK, hKD, hKμ⟩, hfin⟩ hpos
    have hs : ∀ f ∈ V, ⟪(c : ℝ) • rieszVec D V μ, gradFeat D f⟫ = ∫ x, f x ∂(c • μ) := by
      intro f hf
      rw [real_inner_smul_left, hp f hf, integral_smul_nnreal_measure, NNReal.smul_def,
        smul_eq_mul]
    rw [dualNormSq_eq_of_pairing hV (Submodule.smul_mem _ _ rieszVec_mem) hs]
    exact ENNReal.ofReal_lt_top
  · rw [dualNormSq_eq_zero_of_nopos hpos]; exact ENNReal.zero_lt_top

end GradFeat

end QuantumZipper.K3
