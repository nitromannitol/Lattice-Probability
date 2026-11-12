/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWExc2Poisson at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: the Poisson integral solves the Dirichlet problem in a disk

For `g` continuous on the circle `|ζ| = ρ`, the Poisson integral
`P[g](w) = ⨍ P(w, ζ) g(ζ)` is the real part of a function analytic in `B(0, ρ)`
(mathlib: `analyticOnNhd_circleAverage_herglotzRieszKernel_smul`), tends to `g(ζ₀)` as `w → ζ₀`
(`lwExc2_poisson_tendsto`), and vanishes on the real diameter when `g` is odd under
conjugation (`lwExc2_poisson_odd`). This is the classical Dirichlet problem for the disk used in
Ahlfors' proof of the reflection principle (L. Ahlfors, *Complex Analysis*, 3rd ed. 1979, Ch. 4
§6.3, Theorem 23 (boundary values of the Poisson integral), p. 168, and §6.5, Theorem 24,
p. 172; `literature/Ahlfors_ComplexAnalysis_1979.pdf`); the boundary limit follows Ahlfors'
approximate-identity argument.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology Real ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The Poisson integral over the circle `|ζ| = ρ`. -/
def lwPoisson (g : ℂ → ℝ) (ρ : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun ζ => poissonKernel 0 w ζ * g ζ) 0 ρ

lemma lwExc2_pk_nonneg {ρ : ℝ} {w ζ : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) (hζ : ζ ∈ sphere (0 : ℂ) ρ) :
    0 ≤ poissonKernel 0 w ζ := by
  rw [poissonKernel_def]
  rw [mem_ball, dist_zero_right] at hw
  rw [mem_sphere, dist_zero_right] at hζ
  simp only [sub_zero]
  refine div_nonneg ?_ (by positivity)
  rw [hζ]; nlinarith [norm_nonneg w]

lemma lwExc2_pk_cont {ρ : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    ContinuousOn (poissonKernel 0 w) (sphere (0 : ℂ) ρ) := by
  have hne : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ - 0 - (w - 0) ≠ 0 := by
    intro ζ hζ h0
    rw [mem_sphere, dist_zero_right] at hζ
    rw [mem_ball, dist_zero_right] at hw
    have : ζ = w := by simpa [sub_eq_zero] using h0
    rw [this] at hζ; linarith
  have : poissonKernel 0 w = fun ζ => (‖ζ - 0‖ ^ 2 - ‖w - 0‖ ^ 2) / ‖(ζ - 0) - (w - 0)‖ ^ 2 := by
    funext ζ; rfl
  rw [this]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ζ hζ => ?_
  exact pow_ne_zero _ (norm_ne_zero_iff.2 (hne ζ hζ))

lemma lwExc2_abs_sphere {ρ : ℝ} (hρ : 0 < ρ) : sphere (0 : ℂ) |ρ| = sphere 0 ρ := by
  rw [abs_of_pos hρ]

lemma lwExc2_pk_avg {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    Real.circleAverage (poissonKernel 0 w) 0 ρ = 1 := by
  have h := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
    (f := fun _ : ℂ => (1 : ℝ)) (c := 0) (R := ρ)
    (fun x _ => InnerProductSpace.harmonicAt_const (1 : ℝ)) hw
  have e : (poissonKernel 0 w • fun _ : ℂ => (1 : ℝ)) = poissonKernel 0 w := by
    funext ζ; simp
  rw [e] at h; exact h

/-- **Boundary values of the Poisson integral** (Ahlfors, Thm 23, p. 168). -/
theorem lwExc2_poisson_tendsto {g : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : ContinuousOn g (sphere (0 : ℂ) ρ)) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere (0 : ℂ) ρ) :
    Tendsto (lwPoisson g ρ) (𝓝[ball (0 : ℂ) ρ] ζ₀) (𝓝 (g ζ₀)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hK : IsCompact (sphere (0 : ℂ) ρ) := isCompact_sphere 0 ρ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM ζ₀ hζ₀)
  -- uniform continuity at `ζ₀`
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 (hg ζ₀ hζ₀) (ε / 2) (half_pos hε)
  set K : ℝ := 2 * M * (8 * ρ / δ ^ 2) with hKdef
  have hKnn : 0 ≤ K := by positivity
  refine ⟨min (δ / 2) (ε / (2 * (K + 1))), lt_min (half_pos hδ) (by positivity),
    fun w hw hdw => ?_⟩
  have hdw1 : dist w ζ₀ < δ / 2 := lt_of_lt_of_le hdw (min_le_left _ _)
  have hdw2 : dist w ζ₀ < ε / (2 * (K + 1)) := lt_of_lt_of_le hdw (min_le_right _ _)
  have hwn : ‖w‖ < ρ := by simpa using hw
  have hζn : ‖ζ₀‖ = ρ := by simpa using hζ₀
  -- pointwise bound
  have hpt : ∀ ζ ∈ sphere (0 : ℂ) ρ,
      |poissonKernel 0 w ζ * g ζ - poissonKernel 0 w ζ * g ζ₀| ≤
        ε / 2 * poissonKernel 0 w ζ + K * dist w ζ₀ := by
    intro ζ hζ
    have hP := lwExc2_pk_nonneg hw hζ
    rw [← mul_sub, abs_mul, abs_of_nonneg hP]
    by_cases hnear : dist ζ ζ₀ < δ
    · have := hδg hζ hnear
      rw [Real.dist_eq] at this
      nlinarith [dist_nonneg (x := w) (y := ζ₀)]
    · push Not at hnear
      have hζn' : ‖ζ‖ = ρ := by simpa using hζ
      -- `|ζ − w| ≥ δ/2`
      have hzw : δ / 2 ≤ ‖ζ - w‖ := by
        have := dist_triangle ζ w ζ₀
        simp only [dist_eq_norm] at this hdw1 hnear
        linarith
      -- `ρ² − |w|² ≤ 2ρ |w − ζ₀|`
      have hnum : ρ ^ 2 - ‖w‖ ^ 2 ≤ 2 * ρ * dist w ζ₀ := by
        have h1 : ρ - ‖w‖ ≤ dist w ζ₀ := by
          have := norm_sub_norm_le ζ₀ w
          rw [hζn] at this; rw [dist_comm, dist_eq_norm]; linarith
        nlinarith [norm_nonneg w]
      have hPle : poissonKernel 0 w ζ ≤ 8 * ρ / δ ^ 2 * dist w ζ₀ := by
        rw [poissonKernel_def]; simp only [sub_zero]
        rw [hζn', div_le_iff₀ (by
          have : 0 < ‖ζ - w‖ := lt_of_lt_of_le (half_pos hδ) hzw
          positivity)]
        have h2 : δ ^ 2 / 4 ≤ ‖ζ - w‖ ^ 2 := by nlinarith
        have h3 : 0 ≤ dist w ζ₀ := dist_nonneg
        calc ρ ^ 2 - ‖w‖ ^ 2 ≤ 2 * ρ * dist w ζ₀ := hnum
          _ = 8 * ρ / δ ^ 2 * dist w ζ₀ * (δ ^ 2 / 4) := by field_simp; ring
          _ ≤ 8 * ρ / δ ^ 2 * dist w ζ₀ * ‖ζ - w‖ ^ 2 := by gcongr
      have hgd : |g ζ - g ζ₀| ≤ 2 * M := by
        have := abs_sub (g ζ) (g ζ₀)
        have h4 := hM ζ hζ; have h5 := hM ζ₀ hζ₀
        rw [Real.norm_eq_abs] at h4 h5
        linarith
      calc poissonKernel 0 w ζ * |g ζ - g ζ₀| ≤ (8 * ρ / δ ^ 2 * dist w ζ₀) * (2 * M) :=
            mul_le_mul hPle hgd (abs_nonneg _) (by positivity)
        _ = K * dist w ζ₀ := by rw [hKdef]; ring
        _ ≤ ε / 2 * poissonKernel 0 w ζ + K * dist w ζ₀ := by
            have := lwExc2_pk_nonneg hw hζ; nlinarith
  -- integrate
  have hs : sphere (0 : ℂ) |ρ| = sphere 0 ρ := lwExc2_abs_sphere hρ
  have hPc := lwExc2_pk_cont hw
  have hi1 : CircleIntegrable (fun ζ => poissonKernel 0 w ζ * g ζ) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rw [hs]; exact hPc.mul hg)
  have hi2 : CircleIntegrable (fun ζ => poissonKernel 0 w ζ * g ζ₀) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rw [hs]; exact hPc.mul continuousOn_const)
  have hi3 : CircleIntegrable (poissonKernel 0 w) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rw [hs]; exact hPc)
  have hconst : Real.circleAverage (fun ζ => poissonKernel 0 w ζ * g ζ₀) 0 ρ = g ζ₀ := by
    have : (fun ζ => poissonKernel 0 w ζ * g ζ₀) = g ζ₀ • poissonKernel 0 w := by
      funext ζ; simp [mul_comm]
    rw [this, Real.circleAverage_smul, lwExc2_pk_avg hρ hw, smul_eq_mul, mul_one]
  have hdiff : lwPoisson g ρ w - g ζ₀ =
      Real.circleAverage (fun ζ => poissonKernel 0 w ζ * g ζ - poissonKernel 0 w ζ * g ζ₀) 0 ρ := by
    rw [lwPoisson, Real.circleAverage_fun_sub hi1 hi2, hconst]
  have hbound : Real.circleAverage
      (fun ζ => |poissonKernel 0 w ζ * g ζ - poissonKernel 0 w ζ * g ζ₀|) 0 ρ ≤
      Real.circleAverage (fun ζ => ε / 2 * poissonKernel 0 w ζ + K * dist w ζ₀) 0 ρ := by
    refine Real.circleAverage_mono ?_ ?_ ?_
    · exact ContinuousOn.circleIntegrable' (by
        rw [hs]; exact ((hPc.mul hg).sub (hPc.mul continuousOn_const)).abs)
    · exact ContinuousOn.circleIntegrable' (by
        rw [hs]; exact (continuousOn_const.mul hPc).add continuousOn_const)
    · intro ζ hζ; rw [hs] at hζ; exact hpt ζ hζ
  have hval : Real.circleAverage (fun ζ => ε / 2 * poissonKernel 0 w ζ + K * dist w ζ₀) 0 ρ =
      ε / 2 + K * dist w ζ₀ := by
    rw [Real.circleAverage_fun_add
      (ContinuousOn.circleIntegrable' (by rw [hs]; exact continuousOn_const.mul hPc)) ?_]
    · rw [Real.circleAverage_const]
      have : (fun ζ => ε / 2 * poissonKernel 0 w ζ) = (ε / 2) • poissonKernel 0 w := by
        funext ζ; simp
      rw [this, Real.circleAverage_smul, lwExc2_pk_avg hρ hw, smul_eq_mul, mul_one]
    · exact ContinuousOn.circleIntegrable' continuousOn_const
  rw [Real.dist_eq, hdiff]
  refine lt_of_le_of_lt (Real.abs_circleAverage_le_circleAverage_abs) ?_
  have habs : (|fun ζ => poissonKernel 0 w ζ * g ζ - poissonKernel 0 w ζ * g ζ₀| : ℂ → ℝ) =
      fun ζ => |poissonKernel 0 w ζ * g ζ - poissonKernel 0 w ζ * g ζ₀| := rfl
  rw [habs]
  refine lt_of_le_of_lt (hbound.trans_eq hval) ?_
  have : K * dist w ζ₀ < ε / 2 := by
    have h1 : K * dist w ζ₀ ≤ (K + 1) * dist w ζ₀ := by nlinarith [dist_nonneg (x := w) (y := ζ₀)]
    have h2 : (K + 1) * dist w ζ₀ < (K + 1) * (ε / (2 * (K + 1))) :=
      mul_lt_mul_of_pos_left hdw2 (by positivity)
    have h3 : (K + 1) * (ε / (2 * (K + 1))) = ε / 2 := by field_simp
    linarith
  linarith

/-- The Poisson integral is harmonic in the disk (real part of the Herglotz–Riesz integral). -/
theorem lwExc2_poisson_harm {g : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : ContinuousOn g (sphere (0 : ℂ) ρ)) (c : ℂ) :
    InnerProductSpace.HarmonicOnNhd (fun z => lwPoisson g ρ (z - c)) (ball c ρ) := by
  have hs : sphere (0 : ℂ) |ρ| = sphere 0 ρ := lwExc2_abs_sphere hρ
  have hgi : CircleIntegrable g 0 ρ := ContinuousOn.circleIntegrable' (by rw [hs]; exact hg)
  have hgiC : CircleIntegrable (fun ζ => (g ζ : ℂ)) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rw [hs]; exact continuous_ofReal.comp_continuousOn hg)
  have hA := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hgiC
  have hrepr : ∀ w ∈ ball (0 : ℂ) ρ, lwPoisson g ρ w =
      (Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 ρ).re := by
    intro w hw
    have hwS : w ∉ sphere (0 : ℂ) |ρ| := by
      rw [hs]; intro h1
      rw [mem_sphere] at h1; rw [mem_ball] at hw; linarith
    rw [re_circleAverage_herglotzRieszKernel_smul hgi hwS, lwPoisson,
      poissonKernel_eq_re_herglotzRieszKernel]
    rfl
  intro w hw
  have hw0 : w - c ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball, dist_zero_right, ← dist_eq_norm]; exact hw
  have hwS : w - c ∈ (sphere (0 : ℂ) |ρ|)ᶜ := by
    rw [hs]; intro h1
    rw [mem_sphere] at h1; rw [mem_ball] at hw0; linarith
  have hAw : AnalyticAt ℂ
      (fun w => Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 ρ) (w - c) :=
    hA _ hwS
  have hAw' : AnalyticAt ℂ (fun z =>
      Real.circleAverage (fun ζ => herglotzRieszKernel 0 (z - c) ζ • (g ζ : ℂ)) 0 ρ) w :=
    AnalyticAt.comp (g := fun w =>
      Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 ρ)
      (f := fun z => z - c) hAw (analyticAt_id.sub analyticAt_const)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hAw'.harmonicAt_re
  filter_upwards [isOpen_ball.mem_nhds hw] with u hu
  have hu0 : u - c ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball, dist_zero_right, ← dist_eq_norm]; exact hu
  exact (hrepr _ hu0).symm

/-- Circle averages about `0` are invariant under conjugation. -/
lemma lwExc2_circleAverage_conj (F : ℂ → ℝ) (ρ : ℝ) :
    Real.circleAverage (fun ζ => F (conj ζ)) 0 ρ = Real.circleAverage F 0 ρ := by
  unfold Real.circleAverage
  congr 1
  calc ∫ θ in 0..2 * π, F (conj (circleMap 0 ρ θ))
      = ∫ θ in 0..2 * π, F (circleMap 0 ρ (-θ)) := by simp [conj_circleMap_zero]
    _ = ∫ θ in 0..2 * π, F (circleMap 0 ρ θ) := by
      rw [intervalIntegral.integral_comp_neg (fun w => F (circleMap 0 ρ w))]
      have t₀ : Function.Periodic (fun w => F (circleMap 0 ρ w)) (2 * π) :=
        fun x => by simp [periodic_circleMap 0 ρ x]
      simpa using (t₀.intervalIntegral_add_eq (-(2 * π)) 0)

/-- The Poisson integral of a conjugation-odd function vanishes on the real diameter. -/
theorem lwExc2_poisson_odd {g : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hodd : ∀ ζ ∈ sphere (0 : ℂ) ρ, g (conj ζ) = - g ζ) {w : ℂ} (hw : w.im = 0) :
    lwPoisson g ρ w = 0 := by
  have hs : sphere (0 : ℂ) |ρ| = sphere 0 ρ := lwExc2_abs_sphere hρ
  have hwc : conj w = w := conj_eq_iff_im.2 hw
  set F : ℂ → ℝ := fun ζ => poissonKernel 0 w ζ * g ζ with hF
  have hPc : ∀ ζ, poissonKernel 0 w (conj ζ) = poissonKernel 0 w ζ := by
    intro ζ
    simp only [poissonKernel_def, sub_zero]
    congr 2
    · rw [Complex.norm_conj]
    · rw [← hwc, ← map_sub, Complex.norm_conj, hwc]
  have h1 := lwExc2_circleAverage_conj F ρ
  have h2 : Real.circleAverage (fun ζ => F (conj ζ)) 0 ρ =
      Real.circleAverage ((-1 : ℝ) • F) 0 ρ := by
    refine Real.circleAverage_congr_sphere fun ζ hζ => ?_
    rw [hs] at hζ
    simp [hF, hPc, hodd ζ hζ]
  rw [h2, Real.circleAverage_smul] at h1
  have : Real.circleAverage F 0 ρ = 0 := by
    simp only [smul_eq_mul] at h1; linarith
  exact this

end LWFar
end Thm18Asm
end QuantumZipper
