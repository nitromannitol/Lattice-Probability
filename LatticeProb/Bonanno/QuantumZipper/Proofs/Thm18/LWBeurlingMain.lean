/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWFarDefs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingODE
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingDeriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingCut
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingExt
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingLogPolar
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-4: the Beurling estimate `BeurlingHarmStmt` (assembly, node B5)

Plan: `handoff/LW-BEURLING.md`. Carleman's method (Garnett–Marshall, *Harmonic Measure*, App. G,
Thm G.1 / Lemma G.2, pp. 480–482) in logarithmic coordinates, applied to `V(ζ) = φ_ε(ĥ(w + e^ζ))`:
B4a–B4c give a `C²`, `2πi`-periodic `V` with `0 ≤ V ≤ 1` and `V_tt + V_θθ ≥ 0` on
`Re ζ < log ρ`; `V = 0` on each circle `|x − w| = e^t`, `d ≤ e^t < ρ` (it meets `K`); B2a/B2b give
Carleman's inequality for `I(t) = ∫ V(t+iθ)² dθ`; B3 gives `I(log d) ≤ 4 (2d/ρ) I(log(ρ/2))` and the
monotonicity of `I`; continuity of `V` at `−∞` gives `2π φ_ε(h w)² ≤ I(log d)`. Hence
`h(w) ≤ 2ε + √(8 d/ρ)`, and `C = 3`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Real Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The core estimate for a fixed cut-off level `ε`, when `d ≤ ρ/2`. -/
lemma lwb_core {D K : Set ℂ} {w : ℂ} {d ρ : ℝ} {h : ℂ → ℝ} (hD : IsOpen D) (hwD : w ∈ D)
    (hd : 0 < d) (hdρ : d ≤ ρ / 2) (hK : IsConnected K) (hKD : Disjoint K D)
    (hKd : (K ∩ closedBall w d).Nonempty) (hKρ : (K \ ball w ρ).Nonempty)
    (hharm : InnerProductSpace.HarmonicOnNhd h (connectedComponentIn (D ∩ ball w ρ) w))
    (hbnd : ∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, 0 ≤ h x ∧ h x ≤ 1)
    (hdecay : ∀ x₀ ∈ frontier D ∩ ball w ρ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, dist x x₀ < δ → h x ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    h w ≤ 2 * ε + Real.sqrt (8 * (d / ρ)) := by
  set Vc := connectedComponentIn (D ∩ ball w ρ) w with hVc
  have hρ : 0 < ρ := by linarith
  have hVco : IsOpen Vc := (hD.inter isOpen_ball).connectedComponentIn
  have hwVc : w ∈ Vc := mem_connectedComponentIn ⟨hwD, mem_ball_self hρ⟩
  have hVcD : Vc ⊆ D := (connectedComponentIn_subset _ _).trans inter_subset_left
  obtain ⟨φ, hφC, hφ0, hφ', hφ'', hφge⟩ := smoothCutStmt_holds ε hε
  -- properties of `φ`
  have hφd : Differentiable ℝ φ := hφC.differentiable (by norm_num)
  have hφmono : Monotone φ := monotone_of_deriv_nonneg hφd fun s => (hφ' s).1
  have hφnn : ∀ s, 0 ≤ φ s := by
    intro s
    rcases le_total s ε with h1 | h1
    · rw [hφ0 s h1]
    · rw [← hφ0 ε le_rfl]; exact hφmono h1
  have hφ1 : φ 1 ≤ 1 := by
    have := image_sub_le_mul_sub_of_deriv_le hφd (fun s => (hφ' s).2) (x := 0) (y := 1) zero_le_one
    rw [hφ0 0 hε.le] at this; linarith
  -- local harmonic conjugates
  have hloc : ∀ x ∈ Vc, ∃ f : ℂ → ℂ, AnalyticAt ℂ f x ∧ h =ᶠ[𝓝 x] fun y => (f y).re := by
    intro x hx
    obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.1 hVco x hx
    obtain ⟨F, hFa, hFeq⟩ := (hharm.mono hrs).exists_analyticOnNhd_ball_re_eq
    refine ⟨F, hFa x (mem_ball_self hr), ?_⟩
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    exact (hFeq hy).symm
  have hform := extLocalFormStmt_holds D w ρ ε h φ hD hε hφC hφ0 hφ'' hloc hdecay
  set v : ℂ → ℝ := fun x => φ (Vc.indicator h x) with hv
  obtain ⟨hVC2, hVsub⟩ := logPolarSubharmStmt_holds v w ρ hρ hform
  set V : ℂ → ℝ := fun ζ => v (w + Complex.exp ζ) with hV
  set T := Real.log ρ with hT
  -- elementary properties of `V`
  have hind : ∀ x, 0 ≤ Vc.indicator h x ∧ Vc.indicator h x ≤ 1 := by
    intro x
    by_cases hx : x ∈ Vc
    · rw [indicator_of_mem hx]; exact hbnd x hx
    · rw [indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hV01 : ∀ ζ, 0 ≤ V ζ ∧ V ζ ≤ 1 := fun ζ =>
    ⟨hφnn _, (hφmono (hind _).2).trans hφ1⟩
  have hper : ∀ ζ : ℂ, V (ζ + 2 * π * Complex.I) = V ζ := by
    intro ζ
    simp only [hV, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hlineV : ∀ t : ℝ, t < T → Continuous fun θ : ℝ => V ((t : ℂ) + (θ : ℂ) * Complex.I) :=
    fun t ht => hVC2.continuousOn.comp_continuous (lwb_line_continuous t)
      fun θ => by simp [ht]
  -- zeros on the circles
  have hzero : ∀ t : ℝ, Real.log d ≤ t → t < T →
      ∃ θ : ℝ, V ((t : ℂ) + (θ : ℂ) * Complex.I) = 0 := by
    intro t hdt htT
    set r := Real.exp t with hr
    have hdr : d ≤ r := by rw [hr, ← Real.exp_log hd]; exact Real.exp_le_exp.2 hdt
    have hrρ : r < ρ := by rw [hr, ← Real.exp_log hρ]; exact Real.exp_lt_exp.2 htT
    obtain ⟨k₁, hk₁K, hk₁⟩ := hKd
    obtain ⟨k₂, hk₂K, hk₂⟩ := hKρ
    have hpc : IsPreconnected ((fun x => ‖x - w‖) '' K) :=
      hK.isPreconnected.image _ (continuous_id.sub continuous_const).norm.continuousOn
    have hmemr : r ∈ (fun x => ‖x - w‖) '' K := by
      refine hpc.Icc_subset ⟨k₁, hk₁K, rfl⟩ ⟨k₂, hk₂K, rfl⟩ ⟨?_, ?_⟩
      · have : ‖k₁ - w‖ ≤ d := by simpa [dist_eq_norm] using hk₁
        linarith
      · have : ρ ≤ ‖k₂ - w‖ := by simpa [dist_eq_norm] using hk₂
        linarith
    obtain ⟨k, hkK, hkr⟩ := hmemr
    refine ⟨Complex.arg (k - w), ?_⟩
    have hexp : Complex.exp ((t : ℂ) + (Complex.arg (k - w) : ℂ) * Complex.I) = k - w := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, ← hr, ← hkr]
      exact Complex.norm_mul_exp_arg_mul_I (k - w)
    have hkVc : k ∉ Vc := fun hk => hKD.ne_of_mem hkK (hVcD hk) rfl
    simp only [hV, hv, hexp, add_sub_cancel, indicator_of_notMem hkVc]
    exact hφ0 0 hε.le
  -- Carleman
  have hderiv := circleEnergyDerivStmt_holds V T hVC2
  have hcarl := carlemanIneqStmt_holds V T hVC2 hper (fun ζ _ => (hV01 ζ).1) hVsub
  have hIbd : ∀ t, t < T → 0 ≤ lpI V t ∧ lpI V t ≤ 2 * π := by
    intro t ht
    have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
    refine ⟨intervalIntegral.integral_nonneg hpi fun θ _ => sq_nonneg _, ?_⟩
    have hc2 : Continuous fun θ : ℝ => V ((t : ℂ) + (θ : ℂ) * Complex.I) ^ 2 :=
      (hlineV t ht).pow 2
    have := intervalIntegral.integral_mono_on (μ := volume) hpi (hc2.intervalIntegrable _ _)
      (intervalIntegrable_const (c := (1 : ℝ))) fun θ _ => by
        have := hV01 ((t : ℂ) + (θ : ℂ) * Complex.I)
        nlinarith
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    unfold lpI; linarith
  have hODE := carlemanODEStmt_holds (lpI V) (lpI1 V) (lpI2 V) T (2 * π) (Real.log d)
    (fun t ht => (hderiv t ht).1) (fun t ht => (hderiv t ht).2) hIbd
    (fun t ht => (hcarl t ht).1) (fun t hdt ht => (hcarl t ht).2 (hzero t hdt ht))
  have hdT : Real.log d < T := by rw [hT]; exact Real.log_lt_log hd (by linarith)
  have hb1 : Real.log d ≤ Real.log (ρ / 2) := Real.log_le_log hd hdρ
  have hb2 : Real.log (ρ / 2) < T := by rw [hT]; exact Real.log_lt_log (by positivity) (by linarith)
  have hmain := hODE.2 (Real.log (ρ / 2)) hb1 hb2
  have hexp : Real.exp (Real.log d - Real.log (ρ / 2)) = 2 * (d / ρ) := by
    rw [Real.exp_sub, Real.exp_log hd, Real.exp_log (by positivity)]; field_simp
  rw [hexp] at hmain
  have hIa : lpI V (Real.log d) ≤ 2 * π * (8 * (d / ρ)) := by
    have := (hIbd _ hb2).2
    have hdρ0 : 0 ≤ d / ρ := by positivity
    nlinarith
  -- the value at the centre
  have hvw : v w = φ (h w) := by simp only [hv, indicator_of_mem hwVc]
  have hvc : ContinuousAt v w := by
    have hhc : ContinuousAt h w := (hharm w hwVc).1.continuousAt
    have : v =ᶠ[𝓝 w] fun x => φ (h x) := by
      filter_upwards [hVco.mem_nhds hwVc] with x hx
      simp only [hv, indicator_of_mem hx]
    exact (continuousAt_congr this).2 (hφd.continuous.continuousAt.comp hhc)
  have hcentre : v w ≤ Real.sqrt (8 * (d / ρ)) := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨r, hr, hrv⟩ := Metric.continuousAt_iff.1 hvc η hη
    set t := min (Real.log d) (Real.log r) - 1 with ht
    have htd : t < Real.log d := by rw [ht]; linarith [min_le_left (Real.log d) (Real.log r)]
    have htr : t < Real.log r := by rw [ht]; linarith [min_le_right (Real.log d) (Real.log r)]
    have htT : t < T := htd.trans hdT
    have hclose : ∀ θ : ℝ, v w - η < V ((t : ℂ) + (θ : ℂ) * Complex.I) := by
      intro θ
      have hdist : dist (w + Complex.exp ((t : ℂ) + (θ : ℂ) * Complex.I)) w < r := by
        rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
        rw [← Real.exp_log hr]; exact Real.exp_lt_exp.2 htr
      have := hrv hdist
      rw [Real.dist_eq] at this
      simp only [hV]
      linarith [abs_lt.1 this]
    by_cases hpos : v w - η ≤ 0
    · linarith [Real.sqrt_nonneg (8 * (d / ρ))]
    push Not at hpos
    have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
    have hlow : 2 * π * (v w - η) ^ 2 ≤ lpI V t := by
      have hc2 : Continuous fun θ : ℝ => V ((t : ℂ) + (θ : ℂ) * Complex.I) ^ 2 :=
        (hlineV t htT).pow 2
      have := intervalIntegral.integral_mono_on (μ := volume) hpi (intervalIntegrable_const
        (c := (v w - η) ^ 2)) (hc2.intervalIntegrable _ _) fun θ _ => by
          have h1 := hclose θ
          nlinarith
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      unfold lpI; linarith
    have hmono : lpI V t ≤ lpI V (Real.log d) :=
      hODE.1 (show t ∈ Iio T from htT) (show Real.log d ∈ Iio T from hdT) htd.le
    have hsq : (v w - η) ^ 2 ≤ 8 * (d / ρ) := by
      have := hlow.trans (hmono.trans hIa)
      nlinarith [Real.pi_pos]
    have := Real.le_sqrt_of_sq_le hsq
    linarith
  have := hφge (h w)
  rw [hvw] at hcentre
  linarith

/-- **LWF-4. The Beurling estimate** (`BeurlingHarmStmt`, with `C = 3`). -/
theorem beurlingHarmStmt_holds : BeurlingHarmStmt := by
  refine ⟨3, by norm_num, ?_⟩
  intro D K w d ρ h hD hwD hd hdρ hK hKD hKd hKρ hharm hbnd hdecay
  have hρ : 0 < ρ := hd.trans_le hdρ
  have hwVc : w ∈ connectedComponentIn (D ∩ ball w ρ) w :=
    mem_connectedComponentIn ⟨hwD, mem_ball_self hρ⟩
  have hhw := hbnd w hwVc
  have hx0 : 0 ≤ d / ρ := by positivity
  have hx1 : d / ρ ≤ 1 := (div_le_one hρ).2 hdρ
  rw [← Real.sqrt_eq_rpow]
  by_cases hsmall : ρ / 2 < d
  · have h1 : d / ρ ≤ Real.sqrt (d / ρ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.self_le_rpow_of_le_one hx0 hx1 (by norm_num)
    have h2 : 1 / 2 < d / ρ := by rw [lt_div_iff₀ hρ]; linarith
    linarith [hhw.2]
  push Not at hsmall
  have hsq8 : Real.sqrt (8 * (d / ρ)) ≤ 3 * Real.sqrt (d / ρ) := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  refine le_of_forall_pos_le_add fun η hη => ?_
  have := lwb_core hD hwD hd hsmall hK hKD hKd hKρ hharm hbnd hdecay (ε := η / 2) (by positivity)
  linarith

end LWFar
end Thm18Asm
end QuantumZipper
