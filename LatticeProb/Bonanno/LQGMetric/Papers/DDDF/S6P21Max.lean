/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P21Max at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMaxExp

/-!
# DDDF (2.11) with integrability (task P2-DDDF6c)

`prop2_expMoment_int`: DDDF Prop. 2, (2.11) (`tightness.tex` l. 306–309; DF Lemma 10.2) as in
`prop2_expMoment` (FieldMaxExp), keeping the integrability of `e^{γ sup |Y|}` that its proof
provides (the proof is that of `prop2_expMoment`, copied; only the conclusion is kept whole).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

theorem prop2_expMoment_int {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : ∃ K : ℝ,
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (n : ℕ) (Y : ℂ → Ω → ℝ),
    (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
    (∀ ω, Continuous fun x => Y x ω) →
    Integrable (fun ω => Real.exp (γ * ⨆ z : ferniqueBox 0 1, |Y z ω|)) P ∧
    ∫ ω, Real.exp (γ * ⨆ z : ferniqueBox 0 1, |Y z ω|) ∂P ≤
      (4 : ℝ) ^ (γ * n + K * Real.sqrt n) := by
  obtain ⟨C, hC, h2⟩ := prop2_tail
  set L := Real.log 4 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set C'' := γ * C / (2 - γ) with hC''
  have hC''0 : 0 ≤ C'' := div_nonneg (by positivity) (by linarith)
  refine ⟨4 * C + 2 * C ^ 2 + Real.log (1 + C'') / L, ?_⟩
  intro Ω _ P W hW n Y hY hYc
  have := hW.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: `φ_{1,1} = 0` a.s.
    subst hn
    simp only [pow_zero, inv_one] at hY
    have hz : ∀ x, (fun ω => Y x ω) =ᵐ[P] fun _ => (0 : ℝ) := by
      intro x
      have hl := hasLaw_phi hW (P := P) 1 1 x
      set v := (Real.pi * ‖phiKernelL2 1 1 x‖ ^ 2).toNNReal
      have hv : (v : ℝ) = 0 := by
        have h1 := hl.variance_eq
        rw [variance_id_gaussianReal, variance_phi_delta hW one_pos le_rfl, inv_one,
          Real.log_one] at h1
        exact h1.symm
      have hv' : v = 0 := by exact_mod_cast hv
      rw [hv', gaussianReal_zero_var] at hl
      have h0 : ∀ᵐ y ∂(P.map (phi W 1 1 x)), y = 0 := by
        rw [hl.map_eq, ae_dirac_eq]; exact eventually_pure.2 rfl
      exact (hY x).trans (ae_of_ae_map hl.aemeasurable h0)
    have hsame := ae_eq_of_continuous_modification (P := P) hYc (fun _ => continuous_const) hz
    have : Nonempty (ferniqueBox (0 : ℂ) 1) := ⟨⟨0, mem_ferniqueBox_self zero_le_one⟩⟩
    have hae : (fun ω => Real.exp (γ * ⨆ z : ferniqueBox 0 1, |Y z ω|)) =ᵐ[P]
        fun _ => (1 : ℝ) := by
      filter_upwards [hsame] with ω hω
      simp [hω]
    refine ⟨(integrable_const (1 : ℝ)).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae]
    simp
  set N : ℝ := (n : ℝ) with hN_def
  have hN1 : 1 ≤ N := by rw [hN_def]; exact_mod_cast hn
  have hsN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
  have hsN2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  set M : Ω → ℝ := fun ω => ⨆ z : ferniqueBox 0 1, |Y z ω| with hM
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => Real.iSup_nonneg fun _ => abs_nonneg _
  have ha : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have ha1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hMm : AEMeasurable M P := aemeasurable_sup_abs hW ha ha1 hY hYc
  set s := N + C * Real.sqrt N with hs
  have hs0 : 0 < s := by positivity
  set x₀ := s ^ 2 * L / N with hx₀
  have hx₀0 : 0 ≤ x₀ := by positivity
  set β := N / (s ^ 2 * L) with hβ
  have hβx : β * x₀ = 1 := by rw [hβ, hx₀]; field_simp
  set κ := 2 - γ with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set B := γ * C * Real.exp (N * L + x₀) with hB
  have h4 : (4 : ℝ) ^ n = Real.exp (N * L) := by
    rw [hN_def, hL_def, ← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have htail : ∀ t, x₀ < t → γ * Real.exp (γ * t) * P.real {ω | t ≤ M ω} ≤
      B * Real.exp (-κ * t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hx₀0 ht
    have hP := h2 hW n Y hY hYc (t / s) (by positivity)
    have e1 : t / s * (↑n + C * Real.sqrt ↑n) = t := by
      rw [← hN_def, ← hs]; field_simp
    rw [e1] at hP
    have e2 : -(t / s) ^ 2 * ↑n / Real.log 4 = -β * t ^ 2 := by
      rw [← hN_def, ← hL_def, hβ]; field_simp
    rw [e2] at hP
    have key : γ * t + N * L + -β * t ^ 2 ≤ N * L + x₀ + -κ * t := by
      have iden : (N * L + x₀ + -κ * t) - (γ * t + N * L + -β * t ^ 2) = β * (t - x₀) ^ 2 := by
        rw [hκ]; exact tangent_iden β x₀ t γ (N * L) hβx
      have : 0 ≤ β * (t - x₀) ^ 2 := by rw [hβ]; positivity
      linarith
    calc γ * Real.exp (γ * t) * P.real {ω | t ≤ M ω}
        ≤ γ * Real.exp (γ * t) * (C * 4 ^ n * Real.exp (-β * t ^ 2)) := by gcongr
      _ = γ * C * Real.exp (γ * t + N * L + -β * t ^ 2) := by
          rw [h4, Real.exp_add, Real.exp_add]; ring
      _ ≤ γ * C * Real.exp (N * L + x₀ + -κ * t) := by gcongr
      _ = B * Real.exp (-κ * t) := by rw [hB, Real.exp_add (N * L + x₀)]; ring
  obtain ⟨hI, hE⟩ := integral_exp_le_of_tail hM0 hMm hγ0 hx₀0 hκ0 (by positivity) htail
  refine ⟨hI, hE.trans ?_⟩
  have hBe : B * Real.exp (-κ * x₀) / κ = C'' * Real.exp (N * L + (γ - 1) * x₀) := by
    rw [hB, hC'', mul_assoc (γ * C), ← Real.exp_add, hκ]
    rw [show N * L + x₀ + -(2 - γ) * x₀ = N * L + (γ - 1) * x₀ by ring]
    ring
  rw [hBe]
  have hx₀e : x₀ = L * (N + 2 * C * Real.sqrt N + C ^ 2) := by
    rw [hx₀, hs, div_eq_iff (by positivity : N ≠ 0)]
    linear_combination L * C ^ 2 * hsN2
  set Q := L * (γ * N + 4 * C * Real.sqrt N + 2 * C ^ 2) with hQ
  have hpos : 0 ≤ 2 * C * Real.sqrt N + C ^ 2 := by positivity
  have hfirst : Real.exp (γ * x₀) ≤ Real.exp Q := by
    rw [Real.exp_le_exp, hx₀e, hQ]
    have : γ * (2 * C * Real.sqrt N + C ^ 2) ≤ 2 * (2 * C * Real.sqrt N + C ^ 2) :=
      mul_le_mul_of_nonneg_right hγ2.le hpos
    nlinarith
  have hsecond : Real.exp (N * L + (γ - 1) * x₀) ≤ Real.exp Q := by
    rw [Real.exp_le_exp, hx₀e, hQ]
    have : (γ - 1) * (2 * C * Real.sqrt N + C ^ 2) ≤ 2 * (2 * C * Real.sqrt N + C ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos
    nlinarith
  have hlog : 0 ≤ Real.log (1 + C'') := Real.log_nonneg (by linarith)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), ← hL_def]
  calc Real.exp (γ * x₀) + C'' * Real.exp (N * L + (γ - 1) * x₀)
      ≤ (1 + C'') * Real.exp Q := by nlinarith
    _ = Real.exp (Real.log (1 + C'') + Q) := by
        rw [Real.exp_add (Real.log (1 + C'')) Q, Real.exp_log (by linarith)]
    _ ≤ Real.exp (L * (γ * N + (4 * C + 2 * C ^ 2 + Real.log (1 + C'') / L) * Real.sqrt N)) := by
        rw [Real.exp_le_exp, hQ]
        have h1 : Real.log (1 + C'') ≤ Real.log (1 + C'') * Real.sqrt N :=
          le_mul_of_one_le_right hlog hsN
        have h2' : 2 * C ^ 2 ≤ 2 * C ^ 2 * Real.sqrt N :=
          le_mul_of_one_le_right (by positivity) hsN
        have e3 : L * (Real.log (1 + C'') / L * Real.sqrt N) =
            Real.log (1 + C'') * Real.sqrt N := by field_simp
        have key : L * (γ * N + (4 * C + 2 * C ^ 2 + Real.log (1 + C'') / L) * Real.sqrt N) =
            L * (γ * N + 4 * C * Real.sqrt N) + L * (2 * C ^ 2 * Real.sqrt N) +
              Real.log (1 + C'') * Real.sqrt N := by
          linear_combination e3
        rw [key]
        nlinarith [mul_le_mul_of_nonneg_left h2' hL.le]


end DDDF
end LQGMetric
