/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.Version at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandVec
import LatticeProb.Bonanno.HigherDimLFPP.Field.WhiteNoise
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1Proc

/-!
# Continuous versions of the band fields (packet P-F1; HA2 Details D9 (R3))

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1)–(1.2) (the path integrals of (1.2) use a
continuous version of `H_{ε,1}`); ruling H10; HA2 (F4) and D9 (R3).

For a white noise `W`, an admissible kernel `κ` and `0 < a` (any `b`), the process
`z ↦ W(k_{a,b,z})` has Gaussian increments with variance `‖k_z - k_w‖² ≤ L ‖z - w‖² / a²`
(`norm_bandVec_sub_sq_le`), hence `E|Z_q - Z_{q'}|^{2(d+1)} ≤ K ‖q - q'‖^{2(d+1)}` in the
coordinates `q ∈ Fin d → ℝ` (`‖toLp q‖² ≤ d ‖q‖²_∞`), and the Kolmogorov–Čentsov theorem
(`LQGMetric.WhiteNoise.exists_meas_continuous_modification_N`, built on QuantumZipper's
`KolmN.exists_continuous_modification_N`; exponent `2(d+1) > d`) gives a modification that is
continuous for every `ω` and measurable at every point:

* `exists_isBandVersion`: `∃ H, IsBandVersion P W κ a b H` (the frozen `IsBandVersion`).

Template: `LQGMetric/Field/WhiteNoiseCont.lean` (`exists_continuous_modification_phi`, planar heat
kernel field, coordinates `Fin 2 → ℝ`), with `ℂ ≅ Fin 2 → ℝ` replaced by
`ℝ^d = WithLp 2 (Fin d → ℝ)` and fourth moments by moments of order `2(d+1)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

variable {d : ℕ}

/-- The Euclidean norm is at most `√d` times the sup norm: `‖toLp q‖² ≤ d ‖q‖²`. -/
theorem norm_toLp_sq_le_dim_mul (q : Fin d → ℝ) : ‖(WithLp.toLp 2 q : Rd d)‖ ^ 2 ≤ d * ‖q‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc ∑ i, ‖(WithLp.toLp 2 q : Rd d).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, ‖q‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [PiLp.toLp_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm q i) 2
    _ = d * ‖q‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}

/-- **Continuous versions** (HA2 D9 (R3)): for `0 < a` (and every `b`) the band field
`z ↦ H_{a,b}(z) = W(k_{a,b,z})` has a version that is continuous for every `ω` and measurable at
every point. -/
theorem exists_isBandVersion (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a : ℝ} (ha : 0 < a)
    (b : ℝ) : ∃ H : Rd d → Ω → ℝ, IsBandVersion P W κ a b H := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  set Z : (Fin d → ℝ) → Ω → ℝ := fun q => W (bandVec κ a b (WithLp.toLp 2 q)) with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q => hW.measurable _
  set c : ℝ := L * d / a ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set M : ℝ := QuantumZipper.gaussianAbsMoment (2 * (d + 1)) with hM
  have hM0 : 0 ≤ M := QuantumZipper.gaussianAbsMoment_nonneg _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * (d + 1)) ((2 * (d + 1) : ℕ) : ℝ) K R := by
    intro R
    refine ⟨c ^ (d + 1) * M, by positivity, fun q _ q' _ => ?_⟩
    have hlaw := hW.hasLaw_sub (bandVec κ a b (WithLp.toLp 2 q))
      (bandVec κ a b (WithLp.toLp 2 q'))
    have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hW.measurable _).sub (hW.measurable _)) (d + 1) hlaw.map_eq
    simp only [Pi.sub_apply] at hE
    simp only [hZ]
    rw [hE]
    refine ENNReal.ofReal_le_ofReal ?_
    set v : ℝ := ‖bandVec κ a b (WithLp.toLp 2 q) - bandVec κ a b (WithLp.toLp 2 q')‖ ^ 2
      with hv
    have hv0 : 0 ≤ v := sq_nonneg _
    have hvc : v ≤ c * ‖q - q'‖ ^ 2 := by
      have h1 := hL a ha b (WithLp.toLp 2 q) (WithLp.toLp 2 q')
      rw [← WithLp.toLp_sub] at h1
      have h2 := norm_toLp_sq_le_dim_mul (q - q')
      calc v ≤ L * ‖(WithLp.toLp 2 (q - q') : Rd d)‖ ^ 2 / a ^ 2 := h1
        _ ≤ L * (d * ‖q - q'‖ ^ 2) / a ^ 2 := by gcongr
        _ = c * ‖q - q'‖ ^ 2 := by rw [hc]; ring
    have hcoe : ((v.toNNReal : NNReal) : ℝ) = v := Real.coe_toNNReal _ hv0
    rw [hcoe, Real.rpow_natCast]
    calc v ^ (d + 1) * M ≤ (c * ‖q - q'‖ ^ 2) ^ (d + 1) * M := by gcongr
      _ = c ^ (d + 1) * M * ‖q - q'‖ ^ (2 * (d + 1)) := by ring
  have hpos : (d : ℝ) < ((2 * (d + 1) : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Y, hYc, hYm, hYZ⟩ := LQGMetric.WhiteNoise.exists_meas_continuous_modification_N
    (P := P) (Z := Z) hZm (p := 2 * (d + 1)) (by omega) hpos hmom
  refine ⟨fun z ω => Y (WithLp.ofLp z) ω, ⟨fun ω => ?_, fun z => hYm _, fun z => ?_⟩⟩
  · exact (hYc ω).comp (PiLp.continuous_ofLp 2 _)
  · have h := hYZ (WithLp.ofLp z)
    simp only [hZ, WithLp.toLp_ofLp] at h
    exact h

end HigherDimLFPP
