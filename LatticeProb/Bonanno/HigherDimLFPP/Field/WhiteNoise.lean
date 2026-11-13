/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.WhiteNoise at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Kappa
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPKernel
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsBandVersion
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# White noise on `L²(ℝ × ℝ^d)`: existence and the realization layer (packet P-F1, target T5)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1 (white noise `W` with Lebesgue control
measure) and (1.1); planning audit HA2, Details D9 (R1, R2, R5) and §6; ruling H10.

Port of `LQGMetric/Field/WhiteNoise.lean` (planar index space `L²(ℝ × ℂ)`) to the frozen index
space `WN d = L²(ℝ × ℝ^d)` and the frozen predicate `IsWhiteNoise` (the same isonormal
definition).  The generic tools are QuantumZipper's Gaussian series (`GFFExist.gs_*`), the Gram
representation `LQGMetric.Pitt.exists_gram_map_eq`, and `LQGDimension`'s Gram bridge
`gaussianExpectedMax_gram_eq_vecExpectedMax`.

* `exists_isWhiteNoise`: an isonormal process on `WN d` exists on `(ℕ → ℝ, stdP)` (R1).
* `IsWhiteNoise.hasLaw_fintype` (any universe), `cov_eq` (Itô isometry), `integral_eq_zero`,
  `variance_eq`, `isGaussianProcess_comp`, `hasGaussianLaw_fintype` (R2: finite families are
  jointly centered Gaussian with covariance `⟪v i, v j⟫`).
* a.s. linearity: `ae_eq_zero_of_norm_eq_zero`, `add_ae`, `smul_ae`, `sub_ae`, `sum_smul_ae`.
* `IsWhiteNoise.integral_iSup_eq_gaussianExpectedMax`: `E max_{i ∈ F} (W(v i) + b i)` equals
  `LQGDimension.gaussianExpectedMax F (fun i j => ⟪v i, v j⟫) b` (R5).
* `IsWhiteNoise.indepFun_of_inner_eq_zero`: families with orthogonal kernel vectors are
  independent (used for disjoint scale bands, HA2 D2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

/-- `L²(ℝ × ℝ^d)` is separable (Mathlib `Lp.SecondCountableTopology`). -/
instance instSeparableWN (d : ℕ) : TopologicalSpace.SeparableSpace (WN d) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp only [ne_eq, ENNReal.ofNat_ne_top,
    not_false_eq_true]⟩
  have : SecondCountableTopology (WN d) := Lp.SecondCountableTopology
  infer_instance

/-- **Existence of the white noise** (HA2 D9 (R1)): the Gaussian series over a Hilbert basis of
`L²(ℝ × ℝ^d)` (`QuantumZipper.GFFExist.gs_process_hilbert`), on `(ℕ → ℝ, stdP)`. -/
theorem exists_isWhiteNoise (d : ℕ) :
    ∃ W : WN d → (ℕ → ℝ) → ℝ, IsWhiteNoise LQGDimension.ExistAsm.stdP W := by
  obtain ⟨X, hXm, hX⟩ := QuantumZipper.GFFExist.gs_process_hilbert (WN d) (fun f => f)
  exact ⟨X, ⟨hXm, fun f c => hX f c⟩⟩

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

namespace IsWhiteNoise

/-- The defining law for finite families indexed by a type in any universe. -/
theorem hasLaw_fintype (hW : IsWhiteNoise P W) {ι : Type*} [Fintype ι] (f : ι → WN d)
    (c : ι → ℝ) :
    HasLaw (fun ω => ∑ i, c i * W (f i) ω) (gaussianReal 0 (‖∑ i, c i • f i‖ ^ 2).toNNReal) P := by
  classical
  let e := Fintype.equivFin ι
  have h := hW.hasLaw (fun k : Fin (Fintype.card ι) => f (e.symm k)) (fun k => c (e.symm k))
  have h1 : (fun ω => ∑ i, c i * W (f i) ω) =
      fun ω => ∑ k, c (e.symm k) * W (f (e.symm k)) ω := by
    funext ω
    exact (Fintype.sum_equiv e.symm (fun k => c (e.symm k) * W (f (e.symm k)) ω)
      (fun i => c i * W (f i) ω) fun _ => rfl).symm
  have h2 : ∑ i, c i • f i = ∑ k, c (e.symm k) • f (e.symm k) :=
    (Fintype.sum_equiv e.symm (fun k => c (e.symm k) • f (e.symm k)) (fun i => c i • f i)
      fun _ => rfl).symm
  rw [h1, h2]
  exact h

theorem hasLaw_single (hW : IsWhiteNoise P W) (f : WN d) :
    HasLaw (W f) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw (ι := Unit) (fun _ => f) (fun _ => 1)
  simpa only [Finset.univ_unique, PUnit.default_eq_unit, one_mul, Finset.sum_const,
    Finset.card_singleton, one_smul] using h

theorem hasLaw_add (hW : IsWhiteNoise P W) (f g : WN d) :
    HasLaw (fun ω => W f ω + W g ω) (gaussianReal 0 (‖f + g‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw (ι := Fin 2) ![f, g] (fun _ => 1)
  simpa only [one_mul, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_smul] using h

/-- Increments: `W f - W g` is centered Gaussian with variance `‖f - g‖²`. -/
theorem hasLaw_sub (hW : IsWhiteNoise P W) (f g : WN d) :
    HasLaw (fun ω => W f ω - W g ω) (gaussianReal 0 (‖f - g‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw (ι := Fin 2) ![f, g] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, one_smul,
    neg_mul, neg_smul, ← sub_eq_add_neg] at h
  exact h

theorem isProbabilityMeasure (hW : IsWhiteNoise P W) : IsProbabilityMeasure P := by
  refine ⟨?_⟩
  have h := Measure.map_apply (μ := P) (hW.measurable 0) MeasurableSet.univ
  rw [(hW.hasLaw_single 0).map_eq, Set.preimage_univ, measure_univ] at h
  exact h.symm

/-- `W f` is centered. -/
theorem integral_eq_zero (hW : IsWhiteNoise P W) (f : WN d) : ∫ ω, W f ω ∂P = 0 := by
  rw [(hW.hasLaw_single f).integral_eq, integral_id_gaussianReal]

theorem memLp (hW : IsWhiteNoise P W) (f : WN d) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (W f) p P := by
  have hL := (hW.hasLaw_single f)
  have h : MemLp id p (gaussianReal 0 (‖f‖ ^ 2).toNNReal) := by
    lift p to NNReal using hp
    exact memLp_id_gaussianReal p
  rw [← hL.map_eq] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id hL.aemeasurable).1 h

/-- **Itô isometry**: `Cov(W f, W g) = ⟪f, g⟫`. -/
theorem cov_eq (hW : IsWhiteNoise P W) (f g : WN d) : cov[W f, W g; P] = ⟪f, g⟫ := by
  have := hW.isProbabilityMeasure
  exact QuantumZipper.GFFExist.gs_cov_eq (hW.hasLaw_single f) (hW.hasLaw_single g)
    (hW.hasLaw_add f g)

/-- `W` composed with any family of vectors is a Gaussian process. -/
theorem isGaussianProcess_comp (hW : IsWhiteNoise P W) {T : Type*} (F : T → WN d) :
    IsGaussianProcess (fun t => W (F t)) P :=
  QuantumZipper.GFFExist.gs_isGaussianProcess (fun t => (hW.measurable (F t)).aemeasurable)
    fun I c => ⟨_, hW.hasLaw_fintype (fun i : I => F i) c⟩

/-- **Finite families** (HA2 D9 (R2)): `(W(v i))ᵢ` is a Gaussian vector; it is centered
(`integral_eq_zero`) with covariance `⟪v i, v j⟫` (`cov_eq`). -/
theorem hasGaussianLaw_fintype (hW : IsWhiteNoise P W) {ι : Type*} [Fintype ι] (v : ι → WN d) :
    HasGaussianLaw (fun ω i => W (v i) ω) P :=
  LQGDimension.ExistAsm.hasGaussianLaw_pi_of_forall_hasLaw
    (fun i => (hW.measurable (v i)).aemeasurable) fun c => ⟨_, hW.hasLaw_fintype v c⟩

/-- A combination whose vector vanishes vanishes almost surely. -/
theorem ae_eq_zero_of_norm_eq_zero (hW : IsWhiteNoise P W) {ι : Type*} [Fintype ι]
    (f : ι → WN d) (c : ι → ℝ) (h0 : ‖∑ i, c i • f i‖ = 0) :
    (fun ω => ∑ i, c i * W (f i) ω) =ᵐ[P] 0 := by
  have hL := hW.hasLaw_fintype f c
  rw [h0] at hL
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.toNNReal_zero,
    gaussianReal_zero_var] at hL
  have hm : Measurable (fun ω => ∑ i, c i * W (f i) ω) :=
    Finset.measurable_sum _ fun i _ => (hW.measurable (f i)).const_mul _
  have h1 : P ((fun ω => ∑ i, c i * W (f i) ω) ⁻¹' ({0}ᶜ : Set ℝ)) = 0 := by
    rw [← Measure.map_apply hm (measurableSet_singleton 0).compl, hL.map_eq]
    simp only [MeasurableSet.compl_iff, MeasurableSet.singleton, Measure.dirac_apply',
      mem_compl_iff, mem_singleton_iff, not_true_eq_false, not_false_eq_true, indicator_of_notMem]
  rw [EventuallyEq, ae_iff]
  exact h1

/-- a.s. additivity `W (f + g) = W f + W g`. -/
theorem add_ae (hW : IsWhiteNoise P W) (f g : WN d) :
    W (f + g) =ᵐ[P] fun ω => W f ω + W g ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![f + g, f, g] ![1, -1, -1] (by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_three, Fin.isValue,
      Matrix.cons_val_zero, smul_add, one_smul, Matrix.cons_val_one, neg_smul, add_neg_cancel_comm,
      Matrix.cons_val, add_neg_cancel, norm_zero])
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_three, Pi.zero_apply] at hω
  simp only [Fin.isValue, Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd, one_mul,
    Matrix.cons_val_one, neg_mul, Matrix.cons_val] at hω
  linarith

/-- a.s. homogeneity `W (c • f) = c W f`. -/
theorem smul_ae (hW : IsWhiteNoise P W) (c : ℝ) (f : WN d) :
    W (c • f) =ᵐ[P] fun ω => c * W f ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![c • f, f] ![1, -c] (by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, one_smul, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_smul,
      add_neg_cancel, norm_zero])
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_two, Pi.zero_apply] at hω
  simp only [Fin.isValue, Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd, one_mul,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_mul] at hω
  linarith

/-- a.s. `W (f - g) = W f - W g`. -/
theorem sub_ae (hW : IsWhiteNoise P W) (f g : WN d) :
    W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![f - g, f, g] ![1, -1, 1] (by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_three, Fin.isValue,
      Matrix.cons_val_zero, one_smul, Matrix.cons_val_one, neg_smul, Matrix.cons_val, norm_eq_zero]
    abel)
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_three, Pi.zero_apply] at hω
  simp only [Fin.isValue, Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd, one_mul,
    Matrix.cons_val_one, neg_mul, Matrix.cons_val] at hω
  linarith

/-- **Expected maxima** (HA2 D9 (R5)): for a finite family,
`E max_{i ∈ F} (W(v i) + b i) = gaussianExpectedMax F (fun i j => ⟪v i, v j⟫) b`. -/
theorem integral_iSup_eq_gaussianExpectedMax (hW : IsWhiteNoise P W) {ι : Type*}
    (F : Finset ι) (v : ι → WN d) (b : ι → ℝ) :
    ∫ ω, (⨆ i : F, W (v i) ω + b i) ∂P =
      LQGDimension.gaussianExpectedMax F (fun i j => ⟪v i, v j⟫) b := by
  classical
  have := hW.isProbabilityMeasure
  set X : Ω → F → ℝ := fun ω i => W (v i) ω with hX
  have hXG : HasGaussianLaw X P := hW.hasGaussianLaw_fintype (fun i : F => v i)
  obtain ⟨u, hu, hmap⟩ := LQGMetric.Pitt.exists_gram_map_eq hXG
  have hmean : (fun i : F => ∫ ω, X ω i ∂P) = 0 := funext fun i => hW.integral_eq_zero _
  rw [hmean] at hmap
  set u' : ι → EuclideanSpace ℝ F := fun i => if h : i ∈ F then u ⟨i, h⟩ else 0 with hu'def
  have hu' : ∀ i : F, u' i = u i := fun i => by
    simp only [hu'def, i.2, ↓reduceDIte, Subtype.coe_eta]
  have hgram : ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = ⟪u' i, u' j⟫ := by
    intro i hi j hj
    rw [hu' ⟨i, hi⟩, hu' ⟨j, hj⟩, hu, hX, hW.cov_eq]
  rw [LQGDimension.gaussianExpectedMax_congr F b hgram,
    LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  unfold LQGDimension.vecExpectedMax
  have hg : Measurable fun y : F → ℝ => ⨆ i : F, y i + b i :=
    Measurable.iSup fun i => (measurable_pi_apply i).add_const _
  have hcont : Measurable fun x : EuclideanSpace ℝ F =>
      (0 : F → ℝ) + LQGMetric.Pitt.gramCLM u x :=
    (continuous_const.add (LQGMetric.Pitt.gramCLM u).continuous).measurable
  calc ∫ ω, (⨆ i : F, W (v i) ω + b i) ∂P = ∫ ω, (fun y : F → ℝ => ⨆ i : F, y i + b i) (X ω) ∂P :=
        rfl
    _ = ∫ y, (⨆ i : F, y i + b i) ∂(P.map X) :=
        (integral_map hXG.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ x, (⨆ i : F, ((0 : F → ℝ) + LQGMetric.Pitt.gramCLM u x) i + b i)
          ∂(stdGaussian (EuclideanSpace ℝ F)) := by
        rw [hmap, integral_map hcont.aemeasurable hg.aestronglyMeasurable]
    _ = ∫ x, (⨆ i : F, ⟪u' i, x⟫ + b i) ∂(stdGaussian (EuclideanSpace ℝ F)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply, Pi.zero_apply, zero_add, LQGMetric.Pitt.gramCLM_apply, hu']

end IsWhiteNoise

end HigherDimLFPP
