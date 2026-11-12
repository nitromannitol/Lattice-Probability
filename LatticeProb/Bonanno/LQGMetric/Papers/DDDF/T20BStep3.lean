/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BStep3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23CondField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Indep
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldGrad
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiBlock

/-!
# DDDF Theorem 20, Step 3 for `ψ` (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1086–1091 ((5.59) = `eq:SndTerm`):
with `ψ_{0,n} = (ψ_{0,n} − ψ_{0,K}) + ψ_{0,K}` and `ψ̃_{0,K}` an independent copy of `ψ_{0,K}`,
`E((log L^K_n(ψ) − log L_n(ψ))²) ≤ C K`, "using Gaussian concentration as in the proof of
Lemma 23".

Here the resampling is realised on `Ω × Ω` with `P.prod P`: `ψ_{0,K}` is read on the first
coordinate, its copy `ψ̃_{0,K}` on the second, and `ψ_{0,n} − ψ_{0,K} = ψ_{K,n}` (D-DDDF-2 time
split, `psi_add_ae`) on the first. We instantiate `L23.dddf_eq559_generic` (the field form of
(5.59)) with `s = K log 2` (`Var ψ_{0,K}(x) ≤ Var φ_{0,K}(x) = K log 2`, since the truncation
only decreases the kernel).

Results:
* `T20B.variance_psiMN_le`: `Var ψ_{0,K}(x) ≤ K log 2`;
* `T20B.isGaussianProcess_psiMN`, `T20B.integral_psiMN`: `ψ_{0,K}` is a centred Gaussian process;
* `T20B.indepFun_psiMN_scales`: `ψ_{0,K} ⟂ ψ_{K,n}` (white noise on disjoint time sets);
* `T20B.psiMN_add_ae`: a.s. `ψ_{0,n} = ψ_{K,n} + ψ_{0,K}` everywhere (continuous versions);
* `T20B.indepFun_pair_prod`: the product-space independence `(A ∘ fst, B ∘ snd) ⟂ C ∘ fst`;
* `dddf_t20_step3`: (5.59) for `ψ` with `C = 2 ξ² log 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

namespace T20B

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ### Product-space bookkeeping -/

/-- `(A ∘ fst, B ∘ snd) ⟂ C ∘ fst` under `μ ⊗ μ` when `A ⟂ C` under `μ` -/
theorem indepFun_pair_prod {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Ω → α} {B : Ω → β}
    {C : Ω → γ} (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (h : IndepFun A C μ) :
    IndepFun (fun z : Ω × Ω => (A z.1, B z.2)) (fun z => C z.1) (μ.prod μ) := by
  have hAC := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hC.aemeasurable).1 h
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  have h1 : (μ.prod μ).map (fun z : Ω × Ω => ((A z.1, C z.1), B z.2)) =
      ((μ.map A).prod (μ.map C)).prod (μ.map B) := by
    rw [← hAC, Measure.map_prod_map _ _ (hA.prodMk hC) hB]; rfl
  let R : (α × γ) × β → (α × β) × γ := fun w => ((w.1.1, w.2), w.1.2)
  have hR : Measurable R := by fun_prop
  have h2 : (μ.prod μ).map (fun z : Ω × Ω => ((A z.1, B z.2), C z.1)) =
      (((μ.map A).prod (μ.map C)).prod (μ.map B)).map R := by
    rw [← h1, Measure.map_map hR (by fun_prop)]; rfl
  have e1 := measurePreserving_prodAssoc (μ.map A) (μ.map C) (μ.map B)
  have e2 : MeasurePreserving (Prod.map id Prod.swap)
      ((μ.map A).prod ((μ.map C).prod (μ.map B)))
      ((μ.map A).prod ((μ.map B).prod (μ.map C))) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_swap)
  have e3 := (measurePreserving_prodAssoc (μ.map A) (μ.map B) (μ.map C)).symm
  have hcomp := (e3.comp e2).comp e1
  have hRe : R = (MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap) ∘
      MeasurableEquiv.prodAssoc := by
    funext w; rfl
  have hA' : (μ.prod μ).map (fun z : Ω × Ω => (A z.1, B z.2)) = (μ.map A).prod (μ.map B) := by
    rw [Measure.map_prod_map _ _ hA hB]; rfl
  have hC' : (μ.prod μ).map (fun z : Ω × Ω => C z.1) = μ.map C := by
    rw [show (fun z : Ω × Ω => C z.1) = C ∘ Prod.fst from rfl,
      ← Measure.map_map hC measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  rw [h2, hA', hC', hRe, hcomp.map_eq]

theorem map_comp_fst {E : Type*} [MeasurableSpace E] [IsProbabilityMeasure P] {F : Ω → E}
    (hF : Measurable F) : (P.prod P).map (fun z : Ω × Ω => F z.1) = P.map F := by
  rw [show (fun z : Ω × Ω => F z.1) = F ∘ Prod.fst from rfl,
    ← Measure.map_map hF measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

theorem map_comp_snd {E : Type*} [MeasurableSpace E] [IsProbabilityMeasure P] {F : Ω → E}
    (hF : Measurable F) : (P.prod P).map (fun z : Ω × Ω => F z.2) = P.map F := by
  rw [show (fun z : Ω × Ω => F z.2) = F ∘ Prod.snd from rfl,
    ← Measure.map_map hF measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

theorem isGaussianProcess_comp_fst [IsProbabilityMeasure P] {Y : ℂ → Ω → ℝ}
    (hYm : ∀ x, Measurable (Y x)) (hY : IsGaussianProcess Y P) :
    IsGaussianProcess (fun x (z : Ω × Ω) => Y x z.1) (P.prod P) where
  hasGaussianLaw I := by
    have h := hY.hasGaussianLaw I
    have hm : Measurable fun ω => I.restrict (Y · ω) :=
      measurable_pi_iff.2 fun i => hYm i
    refine ⟨(hm.comp measurable_fst).aemeasurable, ?_⟩
    rw [map_comp_fst (F := fun ω => I.restrict (Y · ω)) hm]
    exact h.isGaussian_map

/-! ### `ψ_{0,K}`: centred Gaussian, variance `≤ K log 2` -/

theorem variance_sqrtPi_W (hW : IsWhiteNoise P W) (f : WNSpace) :
    Var[fun ω => Real.sqrt Real.pi * W f ω; P] = Real.pi * ‖f‖ ^ 2 := by
  rw [variance_const_mul, (hW.hasLaw_single f).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity), Real.sq_sqrt Real.pi_pos.le]

theorem variance_psi_le_phi (hW : IsWhiteNoise P W) (Q : PsiParams) {a b : ℝ} (ha : 0 < a)
    (x : ℂ) : Var[psi Q W a b x; P] ≤ Var[phi W a b x; P] := by
  have h1 : Var[psi Q W a b x; P] = Real.pi * ‖Q.psiKernelL2 a b x‖ ^ 2 :=
    variance_sqrtPi_W hW _
  have h2 : Var[phi W a b x; P] = Real.pi * ‖phiKernelL2 a b x‖ ^ 2 :=
    variance_sqrtPi_W hW _
  rw [h1, h2]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) Real.pi_pos.le
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Q.coeFn_psiKernelL2 a b ha x, coeFn_phiKernelL2 a b ha x] with p h1 h2
  rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]
  exact Q.abs_psiKernel_le a b x p

/-- `Var ψ_{0,K}(x) ≤ Var φ_{0,K}(x) = K log 2` -/
theorem variance_psiMN_le (hW : IsWhiteNoise P W) (Q : PsiParams) (K : ℕ) (x : ℂ) :
    Var[psiMN Q W P 0 K x; P] ≤ K * Real.log 2 := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  rw [variance_congr (hψ.ae_eq x)]
  refine (variance_psi_le_phi hW Q (by positivity) x).trans_eq ?_
  rw [variance_phi hW (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (Nat.zero_le K)), pow_zero, one_div, ← inv_pow, inv_inv, Real.log_pow]

theorem isGaussianProcess_psiMN (hW : IsWhiteNoise P W) (Q : PsiParams) {m n : ℕ}
    (hmn : m ≤ n) : IsGaussianProcess (psiMN Q W P m n) P := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW hmn
  refine (hW.isGaussianProcess_comp fun x =>
    Real.sqrt Real.pi • Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) x).congr fun x => ?_
  filter_upwards [hW.smul_ae (Real.sqrt Real.pi)
    (Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) x), hψ.ae_eq x] with ω h1 h2
  rw [h1, h2]; rfl

theorem integral_psiMN (hW : IsWhiteNoise P W) (Q : PsiParams) {m n : ℕ} (hmn : m ≤ n)
    (x : ℂ) : ∫ ω, psiMN Q W P m n x ω ∂P = 0 := by
  rw [integral_congr_ae ((isPsiVersion_psiMN (Q := Q) hW hmn).ae_eq x)]
  simp only [psi]
  rw [integral_const_mul, integral_W hW, mul_zero]

/-! ### Scale split -/

/-- a.s. `ψ_{0,n} = ψ_{K,n} + ψ_{0,K}` at every point (continuous versions) -/
theorem psiMN_add_ae (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n) :
    ∀ᵐ ω ∂P, ∀ x, psiMN Q W P 0 n x ω = psiMN Q W P K n x ω + psiMN Q W P 0 K x ω := by
  have h0n := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hKn' := isPsiVersion_psiMN (Q := Q) hW hKn
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  refine ae_eq_of_continuous_modification h0n.cont (fun ω => (hKn'.cont ω).add (h0K.cont ω))
    fun x => ?_
  filter_upwards [h0n.ae_eq x, hKn'.ae_eq x, h0K.ae_eq x,
    psi_add_ae hW Q (a := (2 : ℝ)⁻¹ ^ n) (b := (2 : ℝ)⁻¹ ^ K) (c := (2 : ℝ)⁻¹ ^ 0)
      (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le K)) x]
    with ω e1 e2 e3 e4
  rw [e1, e2, e3, e4]

/-- `ψ_{0,K} ⟂ ψ_{K,n}` as random continuous fields (white noise on disjoint time sets;
DDDF (2.20)) -/
theorem indepFun_psiMN_scales (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ}
    (hKn : K ≤ n) :
    IndepFun (fun ω x => psiMN Q W P 0 K x ω) (fun ω x => psiMN Q W P K n x ω) P := by
  have := hW.isProbabilityMeasure
  set a : ℝ := (2 : ℝ)⁻¹ ^ n
  set b : ℝ := (2 : ℝ)⁻¹ ^ K
  have ha : 0 < a := by positivity
  have hab : a ≤ b := pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn
  have hI := iIndepFun_psi_psiBlock hW Q ha hab ((2 : ℝ)⁻¹ ^ 0) (ι := Unit)
    (B := fun _ => univ) (fun _ => MeasurableSet.univ)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
  have h2 := hI.indepFun (show (none : Option Unit) ≠ some () from fun h => by cases h)
  have hblk : ∀ x, Q.blockKernelL2 a b univ x = Q.psiKernelL2 a b x := fun x => by
    refine Lp.ext ?_
    filter_upwards [Q.coeFn_blockKernelL2 a b ha MeasurableSet.univ x,
      Q.coeFn_psiKernelL2 a b ha x] with p h1 h2
    rw [h1, h2]
    simp [PsiParams.blockKernel]
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hKn' := isPsiVersion_psiMN (Q := Q) hW hKn
  refine indepFun_modification
    (X := fun x ω => psi Q W b ((2 : ℝ)⁻¹ ^ 0) x ω)
    (Z := fun x ω => psiBlock Q W a b univ x ω)
    (fun x => measurable_psi hW Q _ _ x) (fun x => h0K.meas x)
    (fun x => (hW.measurable _).const_mul _) (fun x => hKn'.meas x)
    (fun x => h0K.ae_eq x) (fun x => ?_) h2
  filter_upwards [hKn'.ae_eq x] with ω h
  rw [h]
  simp only [psi, psiBlock, hblk]
  rfl

end T20B

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

open T20B in
/-- **DDDF (5.59) for `ψ`** (`tightness.tex` l. 1086–1091, Step 3 of Theorem 20): on `Ω × Ω`
with `P ⊗ P`, resampling `ψ_{0,K}` (read on the first coordinate) by its independent copy
`ψ̃_{0,K}` (second coordinate) in `ψ_{0,n} = ψ_{K,n} + ψ_{0,K}` changes `log L^{(n)}_{1,1}` by at most
`E(·)² ≤ 2 ξ² K log 2`. -/
theorem dddf_t20_step3 (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {K n : ℕ}
    (hKn : K ≤ n) :
    Integrable (fun z : Ω × Ω =>
      (L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.2) -
        L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.1)) ^ 2) (P.prod P) ∧
    ∫ z, (L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.2) -
        L23.logLen ξ (fun x => psiMN Q W P K n x z.1 + psiMN Q W P 0 K x z.1)) ^ 2
        ∂(P.prod P) ≤ 2 * (ξ ^ 2 * (K * Real.log 2)) := by
  have := hW.isProbabilityMeasure
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hKn' := isPsiVersion_psiMN (Q := Q) hW hKn
  have hYf : Measurable fun ω x => psiMN Q W P 0 K x ω := measurable_pi_iff.2 h0K.meas
  have hVf : Measurable fun ω x => psiMN Q W P K n x ω := measurable_pi_iff.2 hKn'.meas
  refine L23.dddf_eq559_generic (P := P.prod P)
    (Y := fun x z => psiMN Q W P 0 K x z.1) (Y' := fun x z => psiMN Q W P 0 K x z.2)
    (V := fun x z => psiMN Q W P K n x z.1)
    (fun z => h0K.cont z.1) (fun z => h0K.cont z.2) (fun z => hKn'.cont z.1)
    (fun x => (h0K.meas x).comp measurable_fst) (fun x => (h0K.meas x).comp measurable_snd)
    (fun x => (hKn'.meas x).comp measurable_fst)
    (isGaussianProcess_comp_fst h0K.meas (isGaussianProcess_psiMN hW Q (Nat.zero_le K)))
    (fun x => ?_) (by positivity) (fun x _ => ?_) ?_ ?_ ?_
  · have e := integral_map (μ := P.prod P) measurable_fst.aemeasurable
      (h0K.meas x).aestronglyMeasurable
    rw [Measure.map_fst_prod, measure_univ, one_smul] at e
    rw [← e]
    exact integral_psiMN hW Q (Nat.zero_le K) x
  · have e : Var[fun z : Ω × Ω => psiMN Q W P 0 K x z.1; P.prod P] =
        Var[psiMN Q W P 0 K x; P] := by
      rw [show (fun z : Ω × Ω => psiMN Q W P 0 K x z.1) = psiMN Q W P 0 K x ∘ Prod.fst from rfl,
        ← variance_map (h0K.meas x).aemeasurable measurable_fst.aemeasurable,
        Measure.map_fst_prod, measure_univ, one_smul]
    rw [e]
    exact variance_psiMN_le hW Q K x
  · refine ⟨(hYf.comp measurable_fst).aemeasurable, (hYf.comp measurable_snd).aemeasurable, ?_⟩
    exact (map_comp_fst hYf).trans (map_comp_snd hYf).symm
  · exact indepFun_prod hYf hYf
  · exact indepFun_pair_prod hYf hYf hVf (indepFun_psiMN_scales hW Q hKn)

end DDDF
end LQGMetric
