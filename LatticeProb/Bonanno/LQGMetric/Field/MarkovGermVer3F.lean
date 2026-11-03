/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer3F at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer3E

/-!
# Germ step and leaf (D) for unbounded `V` (task P2-MKD3)

* `mem_range_cmIso_of_orth_unbdd`: the germ step (node (b)) for every open `V` with
  `V ∩ ∂𝔻 = ∅`: `mem_range_cmIso_of_orth_trunc` with the logarithmic cutoffs
  `λₙ = logInf (n+4) (n+4)²` (energy `≤ C²/log((n+4)/2) → 0`), the density
  `ρ = ζ²/∫ζ²` of a bump `ζ` around the unit circle (inside `B_ε(ℂ∖V)` since `∂𝔻 ⊆ ℂ∖V`), and
  the uniform bound `trunc_energy_le`.
* `exists_germ_version_harm`: leaf (D) of the Markov property for every such `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

lemma truncM_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ truncM δ := by
  have hk : 0 < ((1 + δ) ^ 2 - 1) / 2 := by nlinarith
  have := schurL2_nonneg
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold truncM; positivity

/-- the bump around the unit circle -/
lemma exists_ring_bump {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ ζ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
      (∀ x, ζ x ≠ 0 → 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + 2 * δ) ∧
      (∀ x : ℂ, 1 < ‖x‖ → ‖x‖ < 1 + δ → ζ x = 1) ∧ ζ 1 ≠ 0 := by
  have hc : Continuous fun x : ℂ => ‖x‖ := continuous_norm
  obtain ⟨ζ, hs, hr, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (s := {x : ℂ | 1 - δ < ‖x‖} ∩ {x | ‖x‖ < 1 + 2 * δ})
    (t := {x : ℂ | 1 ≤ ‖x‖} ∩ {x | ‖x‖ ≤ 1 + δ})
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))
    ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const))
    (fun x hx => by
      obtain ⟨h1, h2⟩ := hx
      simp only [mem_setOf_eq] at h1 h2
      exact ⟨show 1 - δ < ‖x‖ by linarith, show ‖x‖ < 1 + 2 * δ by linarith⟩)
  refine ⟨ζ, hs, fun x => hr (mem_range_self x), fun x hx => ?_,
    fun x ha hb => (h1 x).1 ⟨ha.le, hb.le⟩, ?_⟩
  · have : x ∈ Function.support ζ := hx
    rw [hsupp] at this; exact this
  · have : (1 : ℂ) ∈ Function.support ζ := by
      rw [hsupp]; simp only [mem_inter_iff, mem_setOf_eq, norm_one]
      constructor <;> linarith
    exact this

/-- **The germ step for unbounded `V`**. -/
theorem mem_range_cmIso_of_orth_unbdd (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {ε : ℝ} (hε : 0 < ε)
    (v : gradClosure ((⊤ : Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : Opens ℂ) : Set ℂ)))
    (hv : ∀ u ∈ germSpan hh.1 (nbhdO ε (V : Set ℂ)ᶜ), ⟪u, cmIso hh.1 ⊤ v⟫ = 0) :
    cmIso hh.1 ⊤ v ∈ Set.range (cmIso hh.1 V) := by
  set δ := min ε 1 / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := by have := min_le_right ε 1; rw [hδdef]; linarith
  have hδε : 2 * δ < ε := by have := min_le_left ε 1; rw [hδdef]; linarith
  obtain ⟨ζ, hζs, hζ01, hζsupp, hζ1, hζne⟩ := exists_ring_bump hδ hδ4
  have hζR : ∀ x, 2 < ‖x‖ → ζ x = 0 := fun x hx => by
    by_contra hne; have := (hζsupp x hne).2; linarith
  have hζc := hasCompactSupport_of_ball2 hζR
  -- `tsupport ζ ⊆ O`
  have hζO : tsupport ζ ⊆ (nbhdO ε (V : Set ℂ)ᶜ : Set ℂ) := by
    have hcl : IsClosed {x : ℂ | 1 - δ ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 2 * δ} :=
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    refine (closure_minimal (fun x hx => ?_) hcl).trans fun x hx => ?_
    · have := hζsupp x hx; exact ⟨this.1.le, this.2.le⟩
    · obtain ⟨h1, h2⟩ := hx
      have hx0 : x ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h1; linarith
      have hn0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
      set y : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) * x
      have hy : ‖y‖ = 1 := by
        simp only [y, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
        field_simp
      have hyV : y ∈ (V : Set ℂ)ᶜ := fun hyV' =>
        Set.disjoint_left.1 hV hyV' (by simpa [mem_sphere_iff_norm] using hy)
      refine Metric.mem_thickening_iff.2 ⟨y, hyV, ?_⟩
      have e : x - y = (((1 - ‖x‖⁻¹) : ℝ) : ℂ) * x := by
        simp only [y]; push_cast; ring
      rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |1 - ‖x‖⁻¹| * ‖x‖ = |‖x‖ - 1| := by
        rw [← abs_norm x, ← abs_mul, abs_norm]; congr 1; field_simp
      rw [this, abs_lt]; constructor <;> linarith
  -- the density `ρ`
  set A := ∫ x, ζ x * ζ x with hA
  have hζ2i : Integrable fun x => ζ x * ζ x :=
    integrable_of_cs (hζs.continuous.mul hζs.continuous) hζc.mul_right
  have hApos : 0 < A := by
    refine (integral_pos_iff_support_of_nonneg (fun x => mul_self_nonneg (ζ x)) hζ2i).2 ?_
    have hopen : IsOpen (Function.support fun x => ζ x * ζ x) :=
      (hζs.continuous.mul hζs.continuous).isOpen_support
    exact hopen.measure_pos _ ⟨1, by simpa using hζne⟩
  set ρ : ℂ → ℝ := fun x => ζ x * ζ x / A with hρ
  have hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := (hζs.mul hζs).div_const A
  have hρc : HasCompactSupport ρ := hcs_of_vanish hζc fun x hx => by simp [ρ, hx]
  have hρO : tsupport ρ ⊆ (nbhdO ε (V : Set ℂ)ᶜ : Set ℂ) :=
    (closure_mono fun x hx => by
      rw [Function.mem_support] at hx ⊢; intro h0; exact hx (by simp [ρ, h0])).trans hζO
  have hρ1 : ∫ x, ρ x = 1 := by
    simp only [ρ]; rw [integral_div]; exact div_self hApos.ne'
  have hcρ : ∀ g : ℂ → ℝ, ∫ y, g y * ρ y = zmean ζ g := fun g => by
    simp only [ρ, zmean]
    rw [← integral_div]; congr 1; funext y; ring
  -- the cutoffs
  set lam : ℕ → ℂ → ℝ := fun n => logInf ((n : ℝ) + 4) (((n : ℝ) + 4) ^ 2) with hlamdef
  have hr4 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 4 := fun n => by positivity
  have h2r : ∀ n : ℕ, 2 * ((n : ℝ) + 4) < ((n : ℝ) + 4) ^ 2 := fun n => by
    have : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
  have hlam : ∀ n, lam n ∈ zeroSpace ((⊤ : Opens ℂ) : Set ℂ) := fun n =>
    logInf_mem_zeroSpace (hr4 n) (h2r n)
  have hlam1 : ∀ (n : ℕ) (x : ℂ), ‖x‖ ≤ (n : ℝ) → lam n x = 1 := fun n x hx =>
    logInf_eq_one (hr4 n) (h2r n) (by linarith)
  have hlamE : Tendsto (fun n => gradEnergy (lam n)) atTop (𝓝 0) := by
    have hup : ∀ n : ℕ, gradEnergy (lam n) ≤
        logCutoffConst ^ 2 * (Real.log (((n : ℝ) + 4) / 2))⁻¹ := fun n => by
      have hb := integral_norm_fderiv_logInf_sq_le (hr4 n) (h2r n)
      have e : ((n : ℝ) + 4) ^ 2 / (2 * ((n : ℝ) + 4)) = ((n : ℝ) + 4) / 2 := by
        have := (hr4 n).ne'; field_simp
      rw [e] at hb
      unfold gradEnergy
      have hpi := Real.pi_pos
      calc (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ (lam n) z‖ ^ 2
          ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * logCutoffConst ^ 2 /
            Real.log (((n : ℝ) + 4) / 2)) := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _ := by field_simp
    have hlog : Tendsto (fun n : ℕ => Real.log (((n : ℝ) + 4) / 2)) atTop atTop :=
      Real.tendsto_log_atTop.comp (Tendsto.atTop_div_const two_pos
        (tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop))
    have h0 : Tendsto (fun n : ℕ => logCutoffConst ^ 2 * (Real.log (((n : ℝ) + 4) / 2))⁻¹)
        atTop (𝓝 0) := by
      simpa using hlog.inv_tendsto_atTop.const_mul (logCutoffConst ^ 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun n => by
        show (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ (lam n) z‖ ^ 2
        exact mul_nonneg (by positivity) (integral_nonneg fun z => sq_nonneg _)) hup
  have hM : ∀ n, ∀ g ∈ zeroSpace ((⊤ : Opens ℂ) : Set ℂ),
      gradEnergy (fun x => lam n x * (g x - ∫ y, g y * ρ y)) ≤ truncM δ * gradEnergy g := by
    intro n g hg
    rw [hcρ g]
    exact trunc_energy_le hh.1 hζs hζ01 hζR hδ (by linarith) hζ1
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) ⟨g, hg⟩
  exact mem_range_cmIso_of_orth_trunc hh hε v hv hρs hρc hρO hρ1 hlam hlam1 hlamE
    (truncM_nonneg hδ) hM

end MarkovGermVer
end LQGMetric
