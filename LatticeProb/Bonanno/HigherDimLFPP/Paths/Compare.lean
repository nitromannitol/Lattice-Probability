/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Paths.Compare at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Paths.DistOn

/-!
# Weight comparison and similarity covariance of internal LFPP distances

Packet P-X1, target T2 (audit HA5, Details D1(c) and D14; DGZ Lemma 2.5, deterministic part).

* **Weight comparison** (`lfppDistOn_le_mul_of_exp_le`, `lfppDistOn_le_exp_mul`,
  `abs_log_lfppDistOn_sub_le`): if `|φ - ψ| ≤ M` on `V`, then
  `|log D_V(x,y)(φ) - log D_V(x,y)(ψ)| ≤ |ζ| M`; the frozen version is
  `abs_log_lfppDistance_sub_le`.  Constant shifts multiply distances by `e^{ζ c}`
  (`lfppDistOn_add_const`); monotonicity in the field for `ζ ≥ 0` (`lfppDistOn_mono_field`).
* **Transport of paths** by a `C¹` bijection with `C¹` inverse that multiplies speeds by `r`
  (`lfppDistOn_comp_of_scales`), and its instances: similarities `T z = x₀ + r • O z`
  (`lfppDistOn_sim`, `lfppDistOn_sim_image`), translations, dilations and linear isometries.
  For `T` a similarity of ratio `r > 0`:
  `D_V(T x, T y)(φ) = r · D_{T⁻¹ V}(x, y)(φ ∘ T)`.

2D sources: `LQGMetric/Papers/DDDF/LenBasic.lean` (`lfppLen_le_of_abs_sub_le`),
`LQGDimension/LFPP/SimilarityCov.lean` (similarities of `ℂ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP

variable {d : ℕ}

/-! ## Weight comparison -/

section Weight

variable {ζ : ℝ} {φ ψ : Rd d → ℝ} {V : Set (Rd d)} {x y : Rd d} {γ : ℝ → Rd d}

/-- If `e^{ζ φ} ≤ C e^{ζ ψ}` along `γ`, then `lfppLength ζ φ γ ≤ C lfppLength ζ ψ γ`. -/
theorem IsPcwC1Path.lfppLength_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ)
    (hγ : IsPcwC1Path γ x y) {C : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, Real.exp (ζ * φ (γ t)) ≤ C * Real.exp (ζ * ψ (γ t))) :
    lfppLength ζ φ γ ≤ C * lfppLength ζ ψ γ := by
  rw [lfppLength_eq_integral, lfppLength_eq_integral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one
    (hγ.intervalIntegrable_lfppIntegrand hφ ζ)
    ((hγ.intervalIntegrable_lfppIntegrand hψ ζ).const_mul C) fun t ht => ?_
  unfold lfppIntegrand
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h t ht) (norm_nonneg _)

/-- If `e^{ζ φ} ≤ C e^{ζ ψ}` on `V` (`C ≥ 0`), then `D_V(x,y)(φ) ≤ C D_V(x,y)(ψ)`. -/
theorem lfppDistOn_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ z ∈ V, Real.exp (ζ * φ z) ≤ C * Real.exp (ζ * ψ z)) :
    lfppDistOn ζ φ V x y ≤ C * lfppDistOn ζ ψ V x y := by
  by_cases hj : PcwJoined V x y
  · conv_rhs => rw [lfppDistOn, Real.mul_iInf_of_nonneg hC]
    have := hj.nonempty
    refine le_ciInf fun γ => (lfppDistOn_le_lfppLength γ.2.1 γ.2.2).trans ?_
    exact γ.2.1.lfppLength_le_mul_of_exp_le hφ hψ fun t ht => h _ (γ.2.2 ht)
  · rw [lfppDistOn_of_not_pcwJoined hj, lfppDistOn_of_not_pcwJoined hj, mul_zero]

theorem exp_mul_le_exp_abs_mul {ζ a b M : ℝ} (h : |a - b| ≤ M) :
    Real.exp (ζ * a) ≤ Real.exp (|ζ| * M) * Real.exp (ζ * b) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : ζ * (a - b) ≤ |ζ| * M :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg ζ))
  linarith [h1]

/-- **Weight comparison for internal distances**: if `|φ - ψ| ≤ M` on `V`, then
`D_V(x,y)(φ) ≤ e^{|ζ| M} D_V(x,y)(ψ)`. -/
theorem lfppDistOn_le_exp_mul (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M) :
    lfppDistOn ζ φ V x y ≤ Real.exp (|ζ| * M) * lfppDistOn ζ ψ V x y :=
  lfppDistOn_le_mul_of_exp_le hφ hψ (Real.exp_pos _).le fun z hz =>
    exp_mul_le_exp_abs_mul (hM z hz)

/-- Two nonnegative reals each at most `e^c` times the other have logarithms within `c`
(with the junk value `log 0 = 0` when both vanish). -/
theorem abs_log_sub_le_of_le_exp_mul {A B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (h₁ : A ≤ Real.exp c * B) (h₂ : B ≤ Real.exp c * A) :
    |Real.log A - Real.log B| ≤ c := by
  rcases hA.lt_or_eq with hA' | hA'
  · rcases hB.lt_or_eq with hB' | hB'
    · rw [abs_sub_le_iff]
      constructor
      · have := Real.log_le_log hA' h₁
        rw [Real.log_mul (Real.exp_pos c).ne' hB'.ne', Real.log_exp] at this
        linarith
      · have := Real.log_le_log hB' h₂
        rw [Real.log_mul (Real.exp_pos c).ne' hA'.ne', Real.log_exp] at this
        linarith
    · rw [← hB', mul_zero] at h₁
      exact absurd hA' (not_lt.2 h₁)
  · rw [← hA', mul_zero] at h₂
    have hB0 : B = 0 := le_antisymm h₂ hB
    rw [← hA', hB0, sub_self, abs_zero]
    exact hc

/-- **Weight comparison, logarithmic form** (HA5 D1(c)): if `|φ - ψ| ≤ M` on `V ∋ x`, then
`|log D_V(x,y)(φ) - log D_V(x,y)(ψ)| ≤ |ζ| M`. -/
theorem abs_log_lfppDistOn_sub_le (hφ : Continuous φ) (hψ : Continuous ψ) (hx : x ∈ V) {M : ℝ}
    (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M) :
    |Real.log (lfppDistOn ζ φ V x y) - Real.log (lfppDistOn ζ ψ V x y)| ≤ |ζ| * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
  refine abs_log_sub_le_of_le_exp_mul (lfppDistOn_nonneg ζ φ V x y)
    (lfppDistOn_nonneg ζ ψ V x y) (mul_nonneg (abs_nonneg ζ) hM0)
    (lfppDistOn_le_exp_mul hφ hψ hM) (lfppDistOn_le_exp_mul hψ hφ fun z hz => ?_)
  rw [abs_sub_comm]; exact hM z hz

/-- **Weight comparison for the frozen LFPP distance**: if `|φ - ψ| ≤ M` on `U`, then
`|log D^ζ(φ) - log D^ζ(ψ)| ≤ |ζ| M`. -/
theorem abs_log_lfppDistance_sub_le (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ z ∈ cube d, |φ z - ψ z| ≤ M) :
    |Real.log (lfppDistance d ζ φ) - Real.log (lfppDistance d ζ ψ)| ≤ |ζ| * M := by
  rw [lfppDistance_eq_lfppDistOn, lfppDistance_eq_lfppDistOn]
  exact abs_log_lfppDistOn_sub_le hφ hψ (zero_mem_cube d) hM

end Weight

/-! ## Transport of paths -/

section Transport

variable {ζ : ℝ} {φ : Rd d → ℝ} {V : Set (Rd d)} {x y : Rd d} {γ : ℝ → Rd d}
/-- Composition with a `C¹` map preserves piecewise `C¹` paths. -/
theorem IsPcwC1Path.comp_contDiff {T : Rd d → Rd d} (hT : ContDiff ℝ 1 T)
    (hγ : IsPcwC1Path γ x y) : IsPcwC1Path (fun t => T (γ t)) (T x) (T y) := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  refine ⟨by simp only [hγ.source], by simp only [hγ.target],
    hT.continuous.comp_continuousOn hγ.continuousOn, k, t, ht, ht0, htk, fun i => ?_⟩
  exact hT.comp_contDiffOn (hC i)

/-- **Length transport.** If `T` multiplies speeds by `r`, then
`lfppLength ζ φ (T ∘ γ) = r · lfppLength ζ (φ ∘ T) γ`. -/
theorem lfppLength_comp_of_scales {T : Rd d → Rd d} {r : ℝ}
    (hderiv : ∀ t, ‖deriv (fun u => T (γ u)) t‖ = r * ‖deriv γ t‖) (ζ : ℝ) (φ : Rd d → ℝ) :
    lfppLength ζ φ (fun u => T (γ u)) = r * lfppLength ζ (fun z => φ (T z)) γ := by
  rw [lfppLength, lfppLength, ← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  rw [hderiv t]
  ring

/-- **Distance transport** by a `C¹` bijection `T` with `C¹` inverse that multiplies speeds by
`r ≥ 0`: `D_V(T x, T y)(φ) = r · D_{T⁻¹ V}(x, y)(φ ∘ T)`. -/
theorem lfppDistOn_comp_of_scales {T Tinv : Rd d → Rd d} (hT : ContDiff ℝ 1 T)
    (hTinv : ContDiff ℝ 1 Tinv) (hTT : ∀ w, T (Tinv w) = w) (hTT' : ∀ z, Tinv (T z) = z)
    {r : ℝ} (hr : 0 ≤ r)
    (hderiv : ∀ (γ : ℝ → Rd d) (t : ℝ), ‖deriv (fun u => T (γ u)) t‖ = r * ‖deriv γ t‖)
    (ζ : ℝ) (φ : Rd d → ℝ) (V : Set (Rd d)) (x y : Rd d) :
    lfppDistOn ζ φ V (T x) (T y) = r * lfppDistOn ζ (fun z => φ (T z)) (T ⁻¹' V) x y := by
  rw [lfppDistOn, lfppDistOn, Real.mul_iInf_of_nonneg hr]
  symm
  refine Function.Surjective.iInf_congr
    (fun γ : {γ : ℝ → Rd d // IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) (T ⁻¹' V)} =>
      (⟨fun u => T (γ.1 u), γ.2.1.comp_contDiff hT, fun u hu => γ.2.2 hu⟩ :
        {γ : ℝ → Rd d // IsPcwC1Path γ (T x) (T y) ∧ MapsTo γ (Icc 0 1) V})) ?_ ?_
  · intro γ'
    have hp : IsPcwC1Path (fun u => Tinv (γ'.1 u)) x y := by
      have := γ'.2.1.comp_contDiff hTinv
      rwa [hTT', hTT'] at this
    refine ⟨⟨fun u => Tinv (γ'.1 u), hp, fun u hu => ?_⟩, ?_⟩
    · show T (Tinv (γ'.1 u)) ∈ V
      rw [hTT]; exact γ'.2.2 hu
    · apply Subtype.ext
      funext u
      exact hTT _
  · intro γ
    exact lfppLength_comp_of_scales (hderiv γ.1) ζ φ

/-- Derivative of a path transported by a similarity `z ↦ x₀ + r • O z`. -/
theorem deriv_sim_comp (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) (γ : ℝ → Rd d) (t : ℝ) :
    deriv (fun u => x₀ + r • O (γ u)) t = r • O (deriv γ t) := by
  rw [deriv_const_add, deriv_fun_const_smul_field]
  congr 1
  rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv]
  have := O.comp_fderiv (f := γ) (x := t)
  rw [show (fun u => O (γ u)) = ⇑O ∘ γ from rfl, this]
  rfl

theorem norm_deriv_sim_comp (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 ≤ r)
    (γ : ℝ → Rd d) (t : ℝ) : ‖deriv (fun u => x₀ + r • O (γ u)) t‖ = r * ‖deriv γ t‖ := by
  rw [deriv_sim_comp, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_nonneg hr]

/-- The similarity `z ↦ x₀ + r • O z`. -/
def simMap (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) (z : Rd d) : Rd d := x₀ + r • O z

/-- Its inverse `w ↦ O⁻¹ (r⁻¹ • (w - x₀))`. -/
def simInv (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) (w : Rd d) : Rd d :=
  O.symm (r⁻¹ • (w - x₀))

theorem simMap_simInv (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : r ≠ 0) (w : Rd d) :
    simMap O x₀ r (simInv O x₀ r w) = w := by
  simp only [simMap, simInv, LinearIsometryEquiv.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ hr, one_smul, add_sub_cancel]

theorem simInv_simMap (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : r ≠ 0) (z : Rd d) :
    simInv O x₀ r (simMap O x₀ r z) = z := by
  simp only [simMap, simInv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul,
    LinearIsometryEquiv.symm_apply_apply]

theorem contDiff_simMap (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) :
    ContDiff ℝ 1 (simMap O x₀ r) :=
  contDiff_const.add ((O.contDiff).const_smul r)

theorem contDiff_simInv (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) :
    ContDiff ℝ 1 (simInv O x₀ r) :=
  O.symm.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

/-- **Similarity covariance** (DGZ Lemma 2.5, deterministic part; HA5 D14): for
`T z = x₀ + r • O z` with `r > 0` and `O` a linear isometry,
`D_V(T x, T y)(φ) = r · D_{T⁻¹ V}(x, y)(φ ∘ T)`. -/
theorem lfppDistOn_sim (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (ζ : ℝ)
    (φ : Rd d → ℝ) (V : Set (Rd d)) (x y : Rd d) :
    lfppDistOn ζ φ V (x₀ + r • O x) (x₀ + r • O y) =
      r * lfppDistOn ζ (fun z => φ (x₀ + r • O z)) ((fun z => x₀ + r • O z) ⁻¹' V) x y :=
  lfppDistOn_comp_of_scales (T := simMap O x₀ r) (Tinv := simInv O x₀ r)
    (contDiff_simMap O x₀ r) (contDiff_simInv O x₀ r) (simMap_simInv O x₀ hr.ne')
    (simInv_simMap O x₀ hr.ne') hr.le (norm_deriv_sim_comp O x₀ hr.le) ζ φ V x y

end Transport

end HigherDimLFPP
