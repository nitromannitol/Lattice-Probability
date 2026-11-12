/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrdCara2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdCara

/-!
# TOPO-ORD, step 2a (cont.): the Carathéodory map of `Ω(K)`

`∂K` with a positive Jordan lift `φ` is a Jordan curve (`w ↦ φ(arg w)` on the circle), so is
`ι(∂K) = ∂Ω(K)`, and `JordanMap.jm_jordan_closedDisc_extension'` (Carathéodory, Pommerenke 1992
Thm 2.6) applies to `Ω(K)` (generic form of GM `jo_disc_map`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF.DD

section Curve

variable {Γ : Set ℂ} {z : ℂ} {φ : ℝ → ℂ} {θ : ℝ → ℝ}

theorem IsPosJordanLift.phi_eq_imp (h : IsPosJordanLift Γ z φ θ) {s t : ℝ} (hst : φ s = φ t) :
    ∃ n : ℤ, s = t + n * (2 * Real.pi) := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  set m := ⌊s / (2 * Real.pi)⌋
  set n := ⌊t / (2 * Real.pi)⌋
  have hred : ∀ x : ℝ, x - ⌊x / (2 * Real.pi)⌋ * (2 * Real.pi) ∈ Ico 0 (2 * Real.pi) := by
    intro x
    have h1 := Int.floor_le (x / (2 * Real.pi))
    have h3 := Int.lt_floor_add_one (x / (2 * Real.pi))
    rw [le_div_iff₀ h2] at h1
    rw [div_lt_iff₀ h2] at h3
    constructor <;> nlinarith
  have hu' := h.phi_add_int (s - m * (2 * Real.pi)) m
  have hv' := h.phi_add_int (t - n * (2 * Real.pi)) n
  simp only [sub_add_cancel] at hu' hv'
  have heq : s - m * (2 * Real.pi) = t - n * (2 * Real.pi) :=
    h.2.2.1 (hred s) (hred t) (by
      show φ (s - m * (2 * Real.pi)) = φ (t - n * (2 * Real.pi))
      rw [← hu', ← hv', hst])
  exact ⟨m - n, by push_cast; linarith⟩

theorem IsPosJordanLift.phi_arg_neg (h : IsPosJordanLift Γ z φ θ) {w : ℂ} (hw : w ≠ 0) :
    φ (Complex.arg w) = φ (Complex.arg (-w) + Real.pi) := by
  have ha : IsAngle w (Complex.arg w) := (Complex.norm_mul_exp_arg_mul_I w).symm
  have hb : IsAngle w (Complex.arg (-w) + Real.pi) := by
    unfold IsAngle
    have := Complex.norm_mul_exp_arg_mul_I (-w)
    rw [norm_neg] at this
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, ← mul_assoc, this,
      show (Real.pi : ℂ) * Complex.I = Real.pi * Complex.I from rfl, Complex.exp_pi_mul_I]
    ring
  obtain ⟨n, hn⟩ := isAngle_sub hw ha hb
  rw [show Complex.arg w = Complex.arg (-w) + Real.pi + n * (2 * Real.pi) by linarith,
    h.phi_add_int]

theorem IsPosJordanLift.continuousAt_phi_arg (h : IsPosJordanLift Γ z φ θ) {w : ℂ}
    (hw : w ≠ 0) : ContinuousAt (fun w => φ (Complex.arg w)) w := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hw with hs | hs
  · exact h.1.continuousAt.comp (Complex.continuousAt_arg hs)
  · have hc : ContinuousAt (fun w : ℂ => φ (Complex.arg (-w) + Real.pi)) w :=
      h.1.continuousAt.comp
        (((Complex.continuousAt_arg hs).comp continuousAt_neg).add continuousAt_const)
    refine hc.congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with v hv
    exact (h.phi_arg_neg hv).symm

theorem IsPosJordanLift.isJordanCurve_inv (h : IsPosJordanLift Γ z φ θ) (hz : z ∉ Γ) :
    JordanMap.IsJordanCurve ((fun x => (x - z)⁻¹) '' Γ) := by
  have hφΓ : ∀ t, φ t ∈ Γ := fun t => h.2.2.2.1 ▸ mem_range_self t
  have hne : ∀ t, φ t - z ≠ 0 := fun t e => hz (sub_eq_zero.1 e ▸ hφΓ t)
  refine ⟨fun w => (φ (Complex.arg w) - z)⁻¹, ?_, ?_, ?_⟩
  · intro w hw
    have hw0 : w ≠ 0 := by
      rintro rfl; simp at hw
    exact ((h.continuousAt_phi_arg hw0).sub continuousAt_const).inv₀ (hne _)
      |>.continuousWithinAt
  · intro w hw w' hw' hww
    have h1 : φ (Complex.arg w) = φ (Complex.arg w') := by
      have := inv_injective hww
      simpa using this
    obtain ⟨n, hn⟩ := h.phi_eq_imp h1
    have hn0 : n = 0 := by
      have hlt : |(n : ℝ) * (2 * Real.pi)| < 1 * (2 * Real.pi) := by
        rw [abs_lt]
        constructor <;> nlinarith [Complex.neg_pi_lt_arg w, Complex.arg_le_pi w,
          Complex.neg_pi_lt_arg w', Complex.arg_le_pi w']
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hlt
      have := lt_of_mul_lt_mul_right hlt (by positivity)
      have : |n| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.1 this
    subst hn0
    simp only [Int.cast_zero, zero_mul, add_zero] at hn
    have e1 := Complex.norm_mul_exp_arg_mul_I w
    have e2 := Complex.norm_mul_exp_arg_mul_I w'
    rw [mem_sphere_zero_iff_norm.1 hw] at e1
    rw [mem_sphere_zero_iff_norm.1 hw'] at e2
    rw [← e1, ← e2, hn]
  · ext y
    constructor
    · rintro ⟨w, -, rfl⟩
      exact ⟨φ (Complex.arg w), hφΓ _, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← h.2.2.2.1] at hx
      obtain ⟨t, rfl⟩ := hx
      set w := Complex.exp ((t : ℂ) * Complex.I)
      have hw : w ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
      have hw0 : w ≠ 0 := Complex.exp_ne_zero _
      have ha : IsAngle w (Complex.arg w) := (Complex.norm_mul_exp_arg_mul_I w).symm
      have ht : IsAngle w t := by
        unfold IsAngle
        rw [mem_sphere_zero_iff_norm.1 hw, Complex.ofReal_one, one_mul]
      obtain ⟨n, hn⟩ := isAngle_sub hw0 ht ha
      refine ⟨w, hw, ?_⟩
      show (φ (Complex.arg w) - z)⁻¹ = (φ t - z)⁻¹
      rw [show t = Complex.arg w + n * (2 * Real.pi) by linarith, h.phi_add_int]

end Curve

/-- **Carathéodory map of `Ω(K)`** (generic `jo_disc_map`) -/
theorem to_disc_map {K : Set ℂ} {z : ℂ} {φ : ℝ → ℂ} {θ : ℝ → ℝ} (hK : IsCompact K)
    (hz : z ∈ interior K) (hKc : IsConnected Kᶜ) (hφ : IsPosJordanLift (frontier K) z φ θ) :
    ∃ f : ℂ → ℂ, ContinuousOn f (closedBall 0 1) ∧ InjOn f (closedBall 0 1) ∧
      DifferentiableOn ℂ f (ball 0 1) ∧ f 0 = 0 ∧ f '' ball 0 1 = toOmega K z ∧
      f '' sphere 0 1 = (fun x => (x - z)⁻¹) '' frontier K := by
  have hzF : z ∉ frontier K := fun h => h.2 hz
  have hfr := to_frontier_omega hK hz
  have hJ : IsPreconnected (frontier K) := hφ.2.2.2.1 ▸ isPreconnected_range hφ.1
  have hJne : (frontier K).Nonempty := hφ.2.2.2.1 ▸ range_nonempty φ
  have hKp := to_isPreconnected_K hK hJ hJne
  have hcomp : ∀ a ∉ toOmega K z, ¬ Bornology.IsBounded (connectedComponentIn (toOmega K z)ᶜ a) := by
    intro a ha hb
    have hzK : z ∉ K \ {z} := fun h => h.2 rfl
    have hpc : IsPreconnected (toOmega K z)ᶜ := by
      rw [to_compl_omega]
      exact (to_isPreconnected_diff hKp hz).image _ (GM.jo_continuousOn_iota _ hzK)
    have hsub := hpc.subset_connectedComponentIn ha subset_rfl
    obtain ⟨r, hr, hΩ⟩ := to_omega_subset hz
    refine GM.jb_not_isBounded_lt_norm (1 / r) (hb.subset (fun w hw => hsub fun hwΩ => ?_))
    have := hΩ hwΩ
    rw [mem_closedBall, dist_zero_right] at this
    exact not_le.2 hw this
  obtain ⟨r, hr, hΩ⟩ := to_omega_subset hz
  rw [← hfr]
  exact JordanMap.jm_jordan_closedDisc_extension' (to_isOpen_omega hK hz)
    (to_isPreconnected_omega hK hz hKc.isPreconnected) (Or.inr rfl)
    ((isBounded_closedBall (x := (0 : ℂ))).subset hΩ) hcomp
    (hfr ▸ hφ.isJordanCurve_inv hzF)

end LQGMetric.CONF.DD
