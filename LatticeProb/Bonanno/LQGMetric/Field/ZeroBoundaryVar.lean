/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ZeroBoundaryVar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Variational formula for the variance; monotonicity in the domain (task P2-ZB, WP-14)

* `ofReal_zeroGFFTestCov_self` : `Var⟨h̊^U, φ⟩ = sup_{f ∈ C_c^∞(U), (f,f)_∇ > 0} (∫ f φ)² / (f,f)_∇`
  — Sheffield's definition of the GFF on `U` (math/0312099 §2: the standard Gaussian of `H₀¹(U)`,
  so `Var (h, φ) = ‖φ‖²_{H⁻¹(U)}`), i.e. the signed-density version of QZ's `dualNormSq`. The proof
  is QZ's `K3.dualNormSq_eq_of_pairing` (QZ/Proofs/GFF/K3/DualNorm.lean) for the functional
  `f ↦ ∫ f φ`, whose representer is `zbRiesz U φ`.
* `zeroGFFTestCov_self_mono` : for `U ⊆ U'`, `Var⟨h̊^U, φ⟩ ≤ Var⟨h̊^{U'}, φ⟩`
  (the sup runs over a larger set with the same energies).
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric

open QuantumZipper QuantumZipper.K3

/-- `sup_{f ∈ C_c^∞(U), (f,f)_∇ > 0} (∫ f φ)² / (f,f)_∇` -/
def zbVarSup (U : Set ℂ) (φ : ℂ → ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ {f ∈ zeroSpace U | 0 < dirichletEnergyOn U f},
    ENNReal.ofReal ((∫ x, f x * φ x) ^ 2 / dirichletEnergyOn U f)

variable {U : Opens ℂ}

/-- **Variational formula** for the variance of `⟨h̊^U, φ⟩`. -/
theorem ofReal_zeroGFFTestCov_self (hadm : ZBAdmissible U) (φ : TestOn U) :
    ENNReal.ofReal (zeroGFFTestCov U φ φ) = zbVarSup U φ := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  rw [zeroGFFTestCov_eq_inner hadm, real_inner_self_eq_norm_sq]
  by_cases hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g
  · set v := zbRiesz U φ
    have hpair : ∀ f ∈ zeroSpace U, ⟪v, gradFeat U f⟫ = ∫ x, f x * φ x :=
      fun f hf => inner_zbRiesz_gradFeat hadm hpos φ hf
    have hE : ∀ f ∈ zeroSpace U, ‖gradFeat U f‖ ^ 2 = dirichletEnergyOn U f :=
      fun f hf => norm_gradFeat_sq (hV.smooth f hf) (hV.energy f hf)
    have hle : ∀ f ∈ zeroSpace U, 0 < dirichletEnergyOn U f →
        ENNReal.ofReal ((∫ x, f x * φ x) ^ 2 / dirichletEnergyOn U f) ≤ zbVarSup U φ :=
      fun f hf hp => le_iSup₂ (f := fun g (_ : g ∈ {g ∈ zeroSpace U | 0 < dirichletEnergyOn U g}) =>
        ENNReal.ofReal ((∫ x, g x * φ x) ^ 2 / dirichletEnergyOn U g)) f ⟨hf, hp⟩
    apply le_antisymm
    · -- `v` is a limit of features `gradFeat f`; Cauchy–Schwarz in the closure
      by_cases htop : zbVarSup U φ = ⊤
      · rw [htop]; exact le_top
      have hN0 : 0 ≤ (zbVarSup U φ).toReal := ENNReal.toReal_nonneg
      have hsub : (Submodule.span ℝ (gradFeat U '' zeroSpace U) : Set (GradSpace U)) ⊆
          {w | ⟪v, w⟫ ≤ √(zbVarSup U φ).toReal * ‖w‖} := by
        intro w hw
        obtain ⟨f, hf, rfl⟩ := mem_image_of_mem_span hV hw
        show ⟪v, gradFeat U f⟫ ≤ √(zbVarSup U φ).toReal * ‖gradFeat U f‖
        rcases (energy_nonneg (U : Set ℂ) f).lt_or_eq with hp | hz
        · have h1 := hle f hf hp
          rw [ENNReal.ofReal_le_iff_le_toReal htop, div_le_iff₀ hp, ← hpair f hf,
            ← hE f hf] at h1
          calc ⟪v, gradFeat U f⟫ ≤ |⟪v, gradFeat U f⟫| := le_abs_self _
            _ = √(⟪v, gradFeat U f⟫ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ √((zbVarSup U φ).toReal * ‖gradFeat U f‖ ^ 2) := Real.sqrt_le_sqrt h1
            _ = √(zbVarSup U φ).toReal * ‖gradFeat U f‖ := by
              rw [Real.sqrt_mul hN0, Real.sqrt_sq (norm_nonneg _)]
        · rw [gradFeat_eq_zero_of_energy hV hf hz.symm]; simp
      have hcl : IsClosed {w : GradSpace U | ⟪v, w⟫ ≤ √(zbVarSup U φ).toReal * ‖w‖} :=
        isClosed_le (continuous_const.inner continuous_id) (continuous_const.mul continuous_norm)
      have hv' : v ∈ closure (Submodule.span ℝ (gradFeat U '' zeroSpace U) :
          Set (GradSpace U)) := by
        rw [← Submodule.topologicalClosure_coe]; exact zbRiesz_mem φ
      have h := closure_minimal hsub hcl hv'
      simp only [Set.mem_ofPred_eq, real_inner_self_eq_norm_sq] at h
      have hv2 : ‖v‖ ≤ √(zbVarSup U φ).toReal := by
        rcases (norm_nonneg v).lt_or_eq with hp | h0
        · nlinarith [Real.sqrt_nonneg (zbVarSup U φ).toReal]
        · rw [← h0]; exact Real.sqrt_nonneg _
      calc ENNReal.ofReal (‖v‖ ^ 2) ≤ ENNReal.ofReal (zbVarSup U φ).toReal := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc ‖v‖ ^ 2 ≤ (√(zbVarSup U φ).toReal) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv2 2
              _ = (zbVarSup U φ).toReal := Real.sq_sqrt hN0
        _ = zbVarSup U φ := ENNReal.ofReal_toReal htop
    · refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hf.2, ← hpair f hf.1, ← hE f hf.1]
      exact inner_sq_le v _
  · rw [zbRiesz_eq_zero_of_nopos hpos]
    have : zbVarSup U φ = 0 :=
      le_antisymm (iSup₂_le fun f hf => (hpos ⟨f, hf.1, hf.2⟩).elim) bot_le
    simp [this]

/-- **Monotonicity in the domain**: `U ⊆ U'` gives `Var⟨h̊^U, φ⟩ ≤ Var⟨h̊^{U'}, φ⟩`. -/
theorem zeroGFFTestCov_self_mono {U' : Opens ℂ} (hUU' : (U : Set ℂ) ⊆ U')
    (hadm : ZBAdmissible U) (hadm' : ZBAdmissible U') (φ : TestOn U) (φ' : TestOn U')
    (hφ : ⇑φ' = ⇑φ) : zeroGFFTestCov U φ φ ≤ zeroGFFTestCov U' φ' φ' := by
  have hmono : zbVarSup U φ ≤ zbVarSup U' φ' := by
    refine iSup₂_le fun f hf => ?_
    have hfU' : f ∈ zeroSpace U' := ⟨hf.1.1, hf.1.2.1, hf.1.2.2.trans hUU'⟩
    have hE : dirichletEnergyOn U f = dirichletEnergyOn U' f := by
      rw [energy_eq_of_tsupport_subset hf.1.2.2,
        energy_eq_of_tsupport_subset (hf.1.2.2.trans hUU')]
    have hp' : 0 < dirichletEnergyOn U' f := hE ▸ hf.2
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun g (_ : g ∈ {g ∈ zeroSpace U' |
      0 < dirichletEnergyOn U' g}) => ENNReal.ofReal ((∫ x, g x * φ' x) ^ 2 /
        dirichletEnergyOn U' g)) f ⟨hfU', hp'⟩)
    rw [hE, hφ]
  rw [← ofReal_zeroGFFTestCov_self hadm, ← ofReal_zeroGFFTestCov_self hadm'] at hmono
  exact (ENNReal.ofReal_le_ofReal_iff (zeroGFFTestCov_self_nonneg hadm' φ')).1 hmono

end LQGMetric
