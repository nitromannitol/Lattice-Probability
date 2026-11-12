/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L37Q1 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aemeasurable). -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBCirc2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37P1

/-!
# DGo's white-noise zero-boundary GFF on `𝕊(1)` as a random distribution (task P2-DGZB)

**`dgZBRealization : DG.L37P.DGZBRealization`**, hence (with `dgLem3_7_of_realization`, P2-HEAT3)
**`dgLem3_7 : Blueprint.DGLem3_7`**.

* the random distribution: `ZB.exists_zbDist` (`⟨hz, φ⟩ = √π W(zbKer(φ 1_D))` a.s., vanishing off
  `cl D` for every `ω`) and `ZB.isZBGFFExtDist_of_zb`;
* the circle averages (DGo (3.1), Lemma 3.1, DGo:491–515; DG:1104): `circleAvg (hz ω) δ x` is the
  limit of `⟨hz, f_n⟩`, `f_n = σ_{x,δ} * ψ_n` (`CircleAvg.circleAverage_pairing`), and
  `⟨hz, f_n⟩ = √π W(zbKer f_n)` a.s.; by `ZB.norm_zbKerL2_circBump_sub_le` and DGo (3.9)
  (`dgo_incr_bound_compact`), `E|√π W(zbKer f_n) − √π W(K_{δ,x})|² = O(2^{-n})`, so the
  convergence is a.s. (Borel–Cantelli, `ae_tendsto_zero_of_sq_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real Topology
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DG
namespace L37Q

open WhiteNoise HeatSq DDDF.P29WN GFFExist DGo.HeatDir DGo.ZB CircleAvg SupTail

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Borel–Cantelli in `L²`**: geometric second moments give a.s. convergence to `0`. -/
lemma ae_tendsto_zero_of_sq_le {Z : ℕ → Ω → ℝ} (hZ : ∀ n, MemLp (Z n) 2 P) {C q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hb : ∀ n, ∫ ω, Z n ω ^ 2 ∂P ≤ C * q ^ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 0) := by
  have hm : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (Z n ω ^ 2)) P := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((hZ n).aemeasurable.pow_const 2)
  have hle : ∀ n, ∫⁻ ω, ENNReal.ofReal (Z n ω ^ 2) ∂P ≤ ENNReal.ofReal (C * q ^ n) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hZ n).integrable_sq
      (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hC : 0 ≤ C := by
    have h0 := (integral_nonneg (fun ω => sq_nonneg (Z 0 ω))).trans (hb 0)
    simpa using h0
  have hsum : ∫⁻ ω, ∑' n, ENNReal.ofReal (Z n ω ^ 2) ∂P ≠ ∞ := by
    rw [lintegral_tsum hm]
    refine ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal (C * q ^ n)) ?_
      (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left C)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hm) hsum] with ω hω
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun n => Z n ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simp only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_zero] at this
    exact this
  have h3 : Tendsto (fun n => |Z n ω|) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    exact this
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h3


variable {W : WNSpace → Ω → ℝ} {a L δ : ℝ}

/-- a.s. additivity (copy of `DDDF.S6DG.wn_sub_ae`) -/
lemma wn_sub_ae' (hW : IsWhiteNoise P W) (f g : WNSpace) :
    W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![f - g, f, g] ![1, -1, 1] (by
    simp [Fin.sum_univ_three]; abel)
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at hω
  linarith

/-- **Circle averages of the zero-boundary random distribution** (DGo (3.1)): for `hz` with
`⟨hz, φ⟩ = h^D(φ 1_D)` a.s. and circles `∂B(x + z, δ)`, `|z| < η`, inside a compact convex
`K ⊆ D`: `h_δ(x) = √π W(K_{δ,x})` a.s. -/
theorem ae_circleAvg_eq_of_zb (hL : 0 < L) (hW : IsWhiteNoise P W) {hz : Ω → DistC}
    (hv : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] DGo.HeatDir.zbXSq a L hL W
      (extZeroTest (sqOpens a L) φ))
    (hδ : 0 < δ) {x : ℂ} {K : Set ℂ} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKU : K ⊆ sqOpen a L) {η : ℝ} (hη : 0 < η)
    (hxK : ∀ z : ℂ, ‖z‖ < η → closedBall (x + z) δ ⊆ K) :
    (fun ω => circleAvg (hz ω) δ x) =ᵐ[P] fun ω => Real.sqrt π * W (dirCircKernel a L δ x) ω := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := dgo_incr_bound_compact hL hK hKc hKU
  set A := (2 / δ + 2 * C / L) / π with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hr : ∀ n, (2 : ℝ)⁻¹ ^ (n + n0) ≤ (2 : ℝ)⁻¹ ^ n0 * (2 : ℝ)⁻¹ ^ n := fun n => by
    rw [pow_add, mul_comm]
  have hrη : ∀ n, (2 : ℝ)⁻¹ ^ (n + n0) < η := fun n =>
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left n0 n)).trans_lt hn0
  have hx0 : closedBall x δ ⊆ K := by simpa using hxK 0 (by simpa using hη)
  set Kx := dirCircKernel a L δ x
  set k : ℕ → WNSpace := fun m => zbKerL2 a L hL (circBd a L m x δ)
  have hk : ∀ n, ‖k (n + n0) - Kx‖ ^ 2 ≤ A * (2 : ℝ)⁻¹ ^ (n + n0) := by
    intro n
    have hB : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ (n + n0) → closedBall (x + z) δ ⊆ sqOpen a L :=
      fun z hz => (hxK z (hz.trans (hrη n))).trans hKU
    have hM : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ (n + n0) →
        ‖dirCircKernel a L δ (x + z) - dirCircKernel a L δ x‖ ≤
          Real.sqrt (A * (2 : ℝ)⁻¹ ^ (n + n0)) := by
      intro z hz
      refine Real.le_sqrt_of_sq_le ?_
      have h := hC δ hδ (x + z) x (hxK z (hz.trans (hrη n))) hx0
      rw [add_sub_cancel_left] at h
      rw [hA, div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos, mul_comm]
      exact h.trans (mul_le_mul_of_nonneg_left hz.le (by positivity))
    have := norm_zbKerL2_circBump_sub_le hL hδ hB hM
    calc ‖k (n + n0) - Kx‖ ^ 2 ≤ (Real.sqrt (A * (2 : ℝ)⁻¹ ^ (n + n0))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (by positivity)
  set Z : ℕ → Ω → ℝ := fun n ω =>
    W (Real.sqrt π • k (n + n0)) ω - W (Real.sqrt π • Kx) ω with hZ
  have hZm : ∀ n, MemLp (Z n) 2 P := fun n => (wn_memLp hW _).sub (wn_memLp hW _)
  have hZb : ∀ n, ∫ ω, Z n ω ^ 2 ∂P ≤ (π * A * (2 : ℝ)⁻¹ ^ n0) * (2 : ℝ)⁻¹ ^ n := by
    intro n
    have e : ∫ ω, Z n ω ^ 2 ∂P =
        ‖Real.sqrt π • k (n + n0) - Real.sqrt π • Kx‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
      refine integral_congr_ae ?_
      filter_upwards [wn_sub_ae' hW (Real.sqrt π • k (n + n0)) (Real.sqrt π • Kx)]
        with ω h
      rw [h, sq]
    rw [e, ← smul_sub, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt Real.pi_pos.le]
    calc π * ‖k (n + n0) - Kx‖ ^ 2 ≤ π * (A * (2 : ℝ)⁻¹ ^ (n + n0)) :=
          mul_le_mul_of_nonneg_left (hk n) Real.pi_pos.le
      _ = _ := by rw [pow_add]; ring
  have hBC := ae_tendsto_zero_of_sq_le hZm (by norm_num) (by norm_num) hZb
  have hpair : ∀ᵐ ω ∂P, ∀ m : ℕ, hz ω (circBump m x δ) = W (Real.sqrt π • k m) ω := by
    rw [ae_all_iff]; intro m; exact hv (circBump m x δ)
  filter_upwards [hBC, hpair, hW.smul_ae (Real.sqrt π) Kx] with ω h1 h2 h3
  rw [← h3]
  have ht : Tendsto (fun m => hz ω (circBump m x δ)) atTop (𝓝 (W (Real.sqrt π • Kx) ω)) := by
    refine (tendsto_add_atTop_iff_nat n0).1 ?_
    have := h1.add_const (W (Real.sqrt π • Kx) ω)
    rw [zero_add] at this
    refine this.congr fun n => ?_
    simp only [hZ, h2, sub_add_cancel]
  unfold circleAvg
  simp_rw [circleAverage_pairing]
  exact ht.limUnder_eq


/-- **DGo's white-noise zero-boundary GFF on `𝕊(1)` as a random distribution with circle
averages `√π W(K_{δ,x})`** (DGo (3.1), Lemma 3.1; DG:1104). -/
theorem dgZBRealization : L37P.DGZBRealization := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have hL : (0 : ℝ) < 3 := by norm_num
  obtain ⟨hz, hm, hv, h0⟩ := exists_zbDist (a := -1) (L := 3) hL hW
  refine ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, W, hz, hW, ?_, ?_⟩
  · have hU : Blueprint.sqOne = sqOpens (-1) 3 := TopologicalSpace.Opens.ext L37P.sqOne_eq
    rw [hU]
    exact isZBGFFExtDist_of_zb hL hW hm hv h0
  · intro δ hδ x hx
    obtain ⟨hδ0, hδ1⟩ := hδ
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    set η := (1 / 2 - δ) / 2 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    set K := ferniqueBox ⟨-1 + η, -1 + η⟩ (3 - 2 * η)
    have hKU : K ⊆ sqOpen (-1) 3 := by
      intro w hw
      rw [mem_ferniqueBox_iff] at hw
      obtain ⟨h1, h2, h3, h4⟩ := hw
      simp only at h1 h2 h3 h4
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    have hxK : ∀ z : ℂ, ‖z‖ < η → closedBall (x + z) δ ⊆ K := by
      intro z hz w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      have e1 := Complex.abs_re_le_norm (w - (x + z))
      have e2 := Complex.abs_im_le_norm (w - (x + z))
      have e3 := Complex.abs_re_le_norm z
      have e4 := Complex.abs_im_le_norm z
      simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im] at e1 e2
      rw [abs_le] at e1 e2 e3 e4
      rw [mem_ferniqueBox_iff]
      simp only
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    exact ae_circleAvg_eq_of_zb hL hW hv hδ0 (isCompact_ferniqueBox _ _)
      (L37P.convex_ferniqueBox' _ _) hKU hη0 hxK

/-- **DG Lemma 3.7** (`lem-circle-avg-approx`, DG:1096–1102), unconditionally. -/
theorem dgLem3_7 : Blueprint.DGLem3_7 := L37P.dgLem3_7_of_realization dgZBRealization

end L37Q
end DG
end LQGMetric
