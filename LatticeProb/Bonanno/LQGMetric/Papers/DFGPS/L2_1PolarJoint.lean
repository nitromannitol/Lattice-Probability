/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1PolarJoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarJointBC
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Joint existence and continuity of `g*_ε(z)` in `(ε, z)`; DFGPS Lemma 2.1 modulo the radial
pairing formula

* `lem2_1HeatJoint : Lem2_1HeatJoint`: for a whole-plane GFF, a.s. the truncated pairings
  `⟨g, p_{e^u}(z,·)χ_n⟩` converge locally uniformly in `(u, z) ∈ ℝ × ℂ` (Weierstrass M-test with the
  bounds of `ae_eventually_gaussDiff3_le`), hence `g*_ε(z)` exists for all `(ε, z)` and is
  continuous on `(0, ∞) × ℂ`. Same route as `Field/HeatMollifyUnif` (fixed `ε`).
* `lem2_1_of_radialPairing'`: DFGPS Lemma 2.1 modulo `Lem2_1RadialPairing` only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

open LFPP

/-- the compact parameter box `|u| ≤ R`, `‖z‖ ≤ R` -/
def parBox (R : ℕ) : Set (ℝ × ℂ) := {p | |p.1| ≤ R ∧ ‖p.2‖ ≤ R}

lemma exists_mem_boxD3 {R : ℕ} {p : ℝ × ℂ} (hp : p ∈ parBox R) :
    ∃ q ∈ QuantumZipper.KolmD.boxD (d := 3) R, sz3 q = p := by
  refine ⟨![p.1, p.2.re, p.2.im], fun i => ?_, ?_⟩
  · fin_cases i
    · exact hp.1
    · exact (Complex.abs_re_le_norm _).trans hp.2
    · exact (Complex.abs_im_le_norm _).trans hp.2
  · simp [sz3]

lemma parBox_mem_nhds (p : ℝ × ℂ) : ∃ R : ℕ, parBox R ∈ 𝓝 p := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max |p.1| ‖p.2‖)
  refine ⟨R, ?_⟩
  have ho : IsOpen {x : ℝ × ℂ | |x.1| < R ∧ ‖x.2‖ < R} :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  refine Filter.mem_of_superset (ho.mem_nhds ⟨(le_max_left _ _).trans_lt hR,
    (le_max_right _ _).trans_lt hR⟩) fun x hx => ⟨hx.1.le, hx.2.le⟩

/-- `|∫ D_n(e^u, z)| ≤ K_R e^{−n} π (n+3)²` on the box -/
lemma abs_integral_heatDiffE_le (R : ℕ) {p : ℝ × ℂ} (hp : p ∈ parBox R) (n : ℕ) :
    |∫ w, heatDiff (Real.exp p.1) p.2 n w| ≤
      (2 * Real.pi * Real.exp (-(R : ℝ)))⁻¹ * Real.exp (Real.exp R / 2 + R) *
        Real.exp (-(n : ℝ)) * (Real.pi * ((n : ℝ) + 3) ^ 2) := by
  have hs0 : 0 < Real.exp p.1 := Real.exp_pos _
  have hs := abs_le.1 hp.1
  have := abs_integral_heatDiff_le (Real.exp p.1) hs0 R p.2 hp.2 n (fun _ => 1) 1 (by simp)
  simp only [mul_one] at this
  refine this.trans ?_
  have h1 : (2 * Real.pi * Real.exp p.1)⁻¹ ≤ (2 * Real.pi * Real.exp (-(R : ℝ)))⁻¹ :=
    inv_anti₀ (by positivity) (by
      have := Real.exp_le_exp.2 hs.1; nlinarith [Real.pi_pos])
  have h2 : Real.exp (Real.exp p.1 / 2 + R) ≤ Real.exp (Real.exp R / 2 + R) :=
    Real.exp_le_exp.2 (by linarith [Real.exp_le_exp.2 hs.2])
  gcongr

/-- **Joint existence and continuity of `g*_ε(z)`** for the whole-plane GFF. -/
theorem lem2_1HeatJoint.{u} : Lem2_1HeatJoint.{u} := by
  intro Ω _ P g hg
  filter_upwards [ae_eventually_gaussDiff3_le hg] with ω hω
  set F : ℕ → ℝ × ℂ → ℝ := fun N p => g ω (heatTrunc (Real.exp p.1) p.2 N)
  set d : ℕ → ℝ × ℂ → ℝ := fun n p => g ω (heatDiff (Real.exp p.1) p.2 n)
  set G : ℝ × ℂ → ℝ := fun p => F 0 p + ∑' n, d n p
  have hF : ∀ N p, F N p = F 0 p + ∑ n ∈ Finset.range N, d n p := by
    intro N p
    have : ∀ n, d n p = F (n + 1) p - F n p := fun n => by
      simp only [d, F, heatDiff, map_sub]
    simp_rw [this, Finset.sum_range_sub (fun n => F n p)]
    ring
  have hU : ∀ R : ℕ, TendstoUniformlyOn F G atTop (parBox R) := by
    intro R
    set K1 : ℝ := (2 * Real.pi * Real.exp (-(R : ℝ)))⁻¹ * Real.exp (Real.exp R / 2 + R)
    set u : ℕ → ℝ := fun n => 25 * Real.exp (-(n : ℝ) / 2) +
      K1 * Real.exp (-(n : ℝ)) * (Real.pi * ((n : ℝ) + 3) ^ 2) * |g ω refTest|
    have hu : Summable u := by
      refine (summable_exp_neg_half.mul_left 25).add ?_
      exact (((summable_shift_pow_mul_exp 2).mul_left (K1 * Real.pi)).mul_right
        |g ω refTest|).congr fun n => by ring
    have hev : ∀ᶠ n in atTop, ∀ p ∈ parBox R, ‖d n p‖ ≤ u n := by
      filter_upwards [hω R] with n hn p hp
      obtain ⟨q, hq, rfl⟩ := exists_mem_boxD3 hp
      rw [Real.norm_eq_abs]
      simp only [d]
      rw [pair_eq_meanZeroPart (g ω)]
      refine (abs_add_le _ _).trans (add_le_add (hn q hq) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_integral_heatDiffE_le R hp n) (abs_nonneg _)
    have hT := tendstoUniformlyOn_tsum_nat_eventually hu (f := d) (s := parBox R) hev
    rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
    intro δ hδ
    filter_upwards [hT δ hδ] with N hN p hp
    simp only [G, hF N p, dist_add_left]
    exact hN p hp
  have hLU : TendstoLocallyUniformly F G atTop := by
    intro v hv x
    obtain ⟨R, hR⟩ := parBox_mem_nhds x
    exact ⟨parBox R, hR, hU R v hv⟩
  have hGc : Continuous G := hLU.continuous (Frequently.of_forall fun N =>
    (g ω).continuous.comp (continuous_heatTruncE N))
  have hlim : ∀ p : ℝ × ℂ, Tendsto (fun N => F N p) atTop (𝓝 (G p)) := fun p => by
    obtain ⟨R, hR⟩ := parBox_mem_nhds p
    exact (hU R).tendsto_at (mem_of_mem_nhds hR)
  have hεF : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, Tendsto (fun n : ℕ => g ω (heatTrunc (ε ^ 2 / 2) z n))
      atTop (𝓝 (G (Real.log (ε ^ 2 / 2), z))) := by
    intro ε hε z
    have := hlim (Real.log (ε ^ 2 / 2), z)
    simp only [F] at this
    rwa [Real.exp_log (by positivity)] at this
  refine ⟨fun ε hε z => ⟨_, hεF ε hε z⟩, ?_⟩
  have heq : EqOn (fun p : ℝ × ℂ => heatMollify p.1 (g ω) p.2)
      (fun p => G (Real.log (p.1 ^ 2 / 2), p.2)) (Ioi 0 ×ˢ univ) := by
    intro p hp
    exact (hεF p.1 (mem_prod.1 hp).1 p.2).limUnder_eq
  refine ContinuousOn.congr ?_ heq
  refine hGc.comp_continuousOn (ContinuousOn.prodMk ?_ continuous_snd.continuousOn)
  refine Real.continuousOn_log.comp ((continuous_fst.pow 2).div_const 2).continuousOn ?_
  intro p hp
  have : 0 < p.1 := (mem_prod.1 hp).1
  exact (by positivity : (0 : ℝ) < p.1 ^ 2 / 2).ne'

end LQGMetric.DFGPS
