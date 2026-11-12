/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Fin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Aux
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Wire

/-!
# DDDF Prop 28 Part 1 Step 1 for the family `δ ∈ (0,1)` (task P2-DDDF28U)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1414–1436 (+ l. 1648): for `0 < β < ξ(Q−2)`,
`P(∃ x, x' : |x − x'| > δ, d_δ(x, x') > C |x − x'|^β) ≤ ε` uniformly in `δ ∈ (0,1)`
(`upper_step1 : S6P28.S6UpperStep1 (xiGamma γ) W P β`).

Proof, following DDDF: for a pair at distance `t ∈ (2^{-n-1}, 2^{-n}]` the chaining at scale
`K = n − 1` (`ae_chain`) gives `d(x, x') ≤ 2E + R_K`; Markov's inequality with
`E R_K ≤ A λ_δ 2^{-θK}` (`mean_RK`, `β < θ < ξ(Q−2)`) at the threshold `A' λ_δ 2^{-βK}` and the
union bound over `K` give the DDDF series `Σ_K 2^{-K(θ−β)}` (l. 1430–1436). The finest link `E`
and the pairs with `t ≤ 64 δ` are bounded by the maximum of the field (`link_small`, as in
Step 2); pairs with `t > 1/4` are cut into four pieces (scale `K = 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28U

open WhiteNoise Blueprint SupTail S6P28 LFPP S6D

set_option maxHeartbeats 1000000 in
/-- **DDDF Prop 28 Part 1 Step 1 for the family** (l. 1414–1436, 1648). -/
theorem upper_step1 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < xiGamma γ * (LQGMetric.Q γ - 2)) : S6UpperStep1 (xiGamma γ) W P β := by
  intro ε hε
  have hP := hW.isProbabilityMeasure
  have hξ : 0 < xiGamma γ := xiGamma_pos' hγ
  have h698 := s6_eq6_98_of_554 hγ hγ2 hW h554
  set ξ := xiGamma γ with hξdef
  set θ := (β + ξ * (LQGMetric.Q γ - 2)) / 2 with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hθ : θ < ξ * (LQGMetric.Q γ - 2) := by rw [hθdef]; linarith
  have hβθ : β < θ := by rw [hθdef]; linarith
  obtain ⟨q, hq2, A, hA0, hmean⟩ := mean_RK hγ hγ2 hW h554 hθ0 hθ
  obtain ⟨CL, hCL0, hlink⟩ := link_small hW hξ h554 h698 hβ0 hβ (ε / 2) (by positivity)
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  set u := Real.exp (-(L * (θ - β))) with hu
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  set G := 1 / (1 - u) with hG
  have hG0 : 0 < G := by rw [hG]; have : 0 < 1 - u := by linarith
                         positivity
  set A' := 2 * (A + 1) * G / ε with hA'
  have hA'0 : 0 < A' := by positivity
  set C := CL * (64 : ℝ) ^ |1 - β| + 64 * CL + 4 * A' * (4 : ℝ) ^ β + 1 with hC
  refine ⟨C, fun δ hδ => ?_⟩
  obtain ⟨N, r, hr0, hr1, hδr⟩ := exists_split' hδ.1 hδ.2
  obtain ⟨M, hMP, hMb⟩ := hlink N r hr0.le hr1 (hδr ▸ hδ.2)
  rw [← hδr] at hMP hMb
  have hδ0 := hδ.1
  obtain ⟨hδa, hδb⟩ := split_bounds N hr0.le hr1
  rw [← hδr] at hδa hδb
  have hδN : δ ≤ (2 : ℝ)⁻¹ ^ N := by rw [inv_pow]; exact hδb
  set lδ := lambdaDelta ξ W P δ with hlδ_def
  have hlδ : 0 < lδ := S6Thm.lambdaDelta_pos_of_698 hW h698 hδ
  have hq0 : q ≠ 0 := by omega
  have hφ := isPhiVersion_phiVer hW hδ0 hδ.2.le
  -- the bad events
  set B1 := {ω | M < ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|}
  set B2 : ℕ → Set Ω := fun K =>
    {ω | ENNReal.ofReal (A' * lδ * Real.exp (-(L * β) * K)) ≤ RK ξ W P δ q K (N - 1) ω}
  have hch := ae_chain (ξ := ξ) hW hξ.le hδ0 hδN hq0
  rw [ae_iff] at hch
  set B0 := {ω | ¬ (∀ K : ℕ, 1 ≤ K → K + 1 ≤ N → ∀ E : ℝ≥0∞,
      (∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare, ‖w - z‖ ≤ 2 * (2 : ℝ)⁻¹ ^ (N - 1) →
        lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare z w ≤ E) →
      ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare,
        |x.re - y.re| < (2 : ℝ)⁻¹ ^ K → |x.im - y.im| < (2 : ℝ)⁻¹ ^ K →
        lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare x y ≤
          2 * E + RK ξ W P δ q K (N - 1) ω)}
  -- Markov for each scale
  have hB2 : ∀ K ∈ Finset.Icc 1 (N - 1), P (B2 K) ≤ ENNReal.ofReal (A / A' * u ^ K) := by
    intro K hK
    obtain ⟨hK1, hK2⟩ := Finset.mem_Icc.1 hK
    have hpos : 0 < A' * lδ * Real.exp (-(L * β) * K) := by positivity
    refine (meas_ge_le_lintegral_div
      (measurable_RK hW hδ0 hδN q (by omega)).aemeasurable
      (by simpa using hpos) ENNReal.ofReal_ne_top).trans ?_
    have hm := hmean N r hr0 hr1 K hK1 (by omega)
    rw [← hδr] at hm
    refine (ENNReal.div_le_div_right hm _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hpos]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have e : Real.exp (-(L * θ) * K) = Real.exp (-(L * β) * K) * u ^ K := by
      rw [hu, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    rw [e]; field_simp
    exact (by ring : A * lδ * u ^ K = A * u ^ K * lδ)
  have hsumB2 : ∑ K ∈ Finset.Icc 1 (N - 1), ENNReal.ofReal (A / A' * u ^ K) ≤
      ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun K _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hgeo : ∑ K ∈ Finset.Icc 1 (N - 1), u ^ K ≤ G := by
      calc ∑ K ∈ Finset.Icc 1 (N - 1), u ^ K ≤ ∑ K ∈ Finset.range N, u ^ K := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun K hK => ?_) fun _ _ _ => by
              positivity
            simp only [Finset.mem_Icc] at hK; simp only [Finset.mem_range]; omega
        _ = ∑ K ∈ Finset.Ico 0 N, u ^ K := by rw [Finset.range_eq_Ico]
        _ ≤ u ^ 0 / (1 - u) := geom_sum_Ico_le_of_lt_one hu0 hu1
        _ = G := by rw [pow_zero, hG]
    rw [← Finset.mul_sum]
    calc A / A' * ∑ K ∈ Finset.Icc 1 (N - 1), u ^ K ≤ A / A' * G := by gcongr
      _ = ε / 2 * (A / (A + 1)) := by rw [hA']; field_simp
      _ ≤ ε / 2 * 1 := by
          gcongr; rw [div_le_one (by linarith)]; linarith
      _ = ε / 2 := mul_one _
  -- the inclusion
  have hincl : {ω | ∃ x y : closedUnitSquare, δ < ‖(x : ℂ) - y‖ ∧ C * ‖(x : ℂ) - y‖ ^ β <
      lδ⁻¹ * lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y} ⊆
      B1 ∪ (⋃ K ∈ Finset.Icc 1 (N - 1), B2 K) ∪ B0 := by
    rintro ω ⟨x, y, hxy, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨hn1, hn2⟩, hn0⟩ := hcon
    have hprop : ∀ K : ℕ, 1 ≤ K → K + 1 ≤ N → ∀ E : ℝ≥0∞,
        (∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare, ‖w - z‖ ≤ 2 * (2 : ℝ)⁻¹ ^ (N - 1) →
          lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare z w ≤ E) →
        ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare,
          |x.re - y.re| < (2 : ℝ)⁻¹ ^ K → |x.im - y.im| < (2 : ℝ)⁻¹ ^ K →
          lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare x y ≤
            2 * E + RK ξ W P δ q K (N - 1) ω := by
      by_contra h; exact hn0 h
    have hRK : ∀ K : ℕ, 1 ≤ K → K + 1 ≤ N →
        RK ξ W P δ q K (N - 1) ω ≤ ENNReal.ofReal (A' * lδ * Real.exp (-(L * β) * K)) := by
      intro K hK1 hK2
      have := hn2 K (Finset.mem_Icc.2 ⟨hK1, by omega⟩)
      simp only [B2, mem_ofPred_eq, not_le] at this
      exact this.le
    -- the field is bounded by `M`
    have hsup : ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω| ≤ M := by
      simpa [B1] using hn1
    have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |phiVer W P δ 1 v ω|) := by
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hφ.cont ω)).continuousOn
      rwa [Set.image_eq_range] at this
    have hM : ∀ z ∈ closedUnitSquare, |phiVer W P δ 1 z ω| ≤ M := fun z hz =>
      (le_ciSup hbdd ⟨z, closedUnitSquare_sub_box hz⟩).trans hsup
    have hseg : ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare z w ≤
          ENNReal.ofReal (Real.exp (ξ * M) * ‖w - z‖) := fun z hz w hw =>
      lfppDOn_le_of_bound_on DFGPS.convex_closedUnitSquare hz hw fun v hv =>
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM v hv)) hξ.le)
    set t := ‖(x : ℂ) - y‖ with ht_def
    have ht0 : 0 < t := hδ0.trans hxy
    have hre : |(x : ℂ).re - (y : ℂ).re| ≤ t := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have him : |(x : ℂ).im - (y : ℂ).im| ≤ t := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have ht2 : t ≤ 2 := by
      obtain ⟨a1, a2, a3, a4⟩ := x.2
      obtain ⟨b1, b2, b3, b4⟩ := y.2
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.sub_re, Complex.sub_im]
      have : |(x : ℂ).re - (y : ℂ).re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have : |(x : ℂ).im - (y : ℂ).im| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have hlen0 : 0 ≤ lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y :=
      ENNReal.toReal_nonneg
    have htβ : δ ^ β ≤ t ^ β := Real.rpow_le_rpow hδ0.le hxy.le hβ0.le
    have hCt : 0 ≤ t ^ β := Real.rpow_nonneg ht0.le _
    have h4β : (1 : ℝ) ≤ (4 : ℝ) ^ β := Real.one_le_rpow (by norm_num) hβ0.le
    have hδβ : δ ^ (β - 1) * δ = δ ^ β := by
      rw [← Real.rpow_add_one hδ0.ne']; ring_nf
    have hC1 : CL * (64 : ℝ) ^ |1 - β| ≤ C := by
      have : 0 ≤ 64 * CL + 4 * A' * (4 : ℝ) ^ β := by positivity
      rw [hC]; linarith
    -- the key bound `λ^{-1} d ≤ C t^β`
    have key : lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y ≤
        lδ * (C * t ^ β) := by
      rcases le_or_gt t (64 * δ) with hA | hA
      · -- small pairs: the maximum of the field
        have h1 := lenMetricOn_le_exp hξ.le hM x.2 y.2
        rw [norm_sub_rev] at h1
        calc _ ≤ Real.exp (ξ * M) * t := h1
          _ ≤ CL * lδ * δ ^ (β - 1) * t := by gcongr
          _ = lδ * (CL * (δ ^ (β - 1) * t)) := by ring
          _ ≤ lδ * (CL * ((64 : ℝ) ^ |1 - β| * t ^ β)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (rpow_ratio hδ0 hxy.le hA) hCL0) hlδ.le
          _ ≤ lδ * (C * t ^ β) := mul_le_mul_of_nonneg_left (by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hC1 hCt) hlδ.le
      · -- far pairs: the chaining at scale `K`
        have hN5 : 5 ≤ N := by
          by_contra hN
          push Not at hN
          have h1 : (2 : ℝ)⁻¹ ^ 4 ≤ (2 : ℝ)⁻¹ ^ N := inv_two_pow_anti (by omega)
          have h2 : ((2 : ℝ) ^ N)⁻¹ ≤ 2 * δ := hδa
          rw [← inv_pow] at h2
          norm_num at h1
          linarith
        have hNN : 2 * (2 : ℝ)⁻¹ ^ (N - 1) ≤ 8 * δ := by
          have e : (2 : ℝ)⁻¹ ^ (N - 1) = 2 * (2 : ℝ)⁻¹ ^ N := by
            rw [show N = N - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel]; ring
          have h2 : ((2 : ℝ) ^ N)⁻¹ ≤ 2 * δ := hδa
          rw [← inv_pow] at h2
          rw [e]; linarith
        set E := ENNReal.ofReal (Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1))) with hEdef
        have hE : ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
            ‖w - z‖ ≤ 2 * (2 : ℝ)⁻¹ ^ (N - 1) →
            lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare z w ≤ E :=
          fun z hz w hw hzw => (hseg z hz w hw).trans
            (ENNReal.ofReal_le_ofReal (by gcongr))
        have hEb : Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1)) ≤ 8 * CL * lδ * δ ^ β := by
          calc Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1))
              ≤ CL * lδ * δ ^ (β - 1) * (8 * δ) := by gcongr
            _ = 8 * CL * lδ * (δ ^ (β - 1) * δ) := by ring
            _ = 8 * CL * lδ * δ ^ β := by rw [hδβ]
        have hE0 : 0 ≤ Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1)) := by positivity
        rcases le_or_gt t (1 / 4) with hB | hB
        · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ 1 / t by
            rw [le_div_iff₀ ht0]; linarith) (show (1 : ℝ) < 2 by norm_num)
          have htn : t ≤ (2 : ℝ)⁻¹ ^ n := by
            rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]
            rw [le_div_iff₀ ht0] at hn1; linarith
          have htn1 : (2 : ℝ)⁻¹ ^ (n + 1) < t := by
            rw [inv_pow, ← one_div, div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ ht0] at hn2; linarith
          have hn2' : 2 ≤ n := by
            by_contra h
            push Not at h
            have : (2 : ℝ) ^ (n + 1) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
            have h4 : (4 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
            norm_num at this; linarith
          have hnN : n + 1 ≤ N := by
            by_contra h
            push Not at h
            have h1' : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ N := inv_two_pow_anti (by omega)
            have h2 : ((2 : ℝ) ^ N)⁻¹ ≤ 2 * δ := hδa
            rw [← inv_pow] at h2
            have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ N := by positivity
            linarith
          set K := n - 1 with hKdef
          have hK2 : (2 : ℝ)⁻¹ ^ K = 2 * (2 : ℝ)⁻¹ ^ n := by
            rw [show n = K + 1 by omega, pow_succ]; ring
          have hcoord : ∀ a b : ℝ, |a - b| ≤ t → |a - b| < (2 : ℝ)⁻¹ ^ K := fun a b h => by
            have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
            rw [hK2]; linarith
          have hc := hprop K (by omega) (by omega) E hE x x.2 y y.2 (hcoord _ _ hre)
            (hcoord _ _ him)
          have hR := hRK K (by omega) (by omega)
          have hlfpp : lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare x y ≤
              ENNReal.ofReal (2 * (Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1))) +
                A' * lδ * Real.exp (-(L * β) * K)) := by
            refine hc.trans ?_
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul
              (by norm_num), ENNReal.ofReal_ofNat]
            gcongr
          have hexpK : Real.exp (-(L * β) * K) ≤ (4 : ℝ) ^ β * t ^ β := by
            have e : Real.exp (-(L * β) * K) = ((2 : ℝ)⁻¹ ^ K) ^ β := by
              rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_inv]
              congr 1; rw [hL]; ring
            rw [e, ← Real.mul_rpow (by norm_num) ht0.le]
            refine Real.rpow_le_rpow (by positivity) ?_ hβ0.le
            have : (2 : ℝ)⁻¹ ^ (n + 1) = (2 : ℝ)⁻¹ ^ n * 2⁻¹ := pow_succ _ _
            rw [hK2]; linarith
          refine (lenMetricOn_le_of (by positivity) hlfpp).trans ?_
          calc 2 * (Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1))) +
                A' * lδ * Real.exp (-(L * β) * K)
              ≤ 2 * (8 * CL * lδ * δ ^ β) + A' * lδ * ((4 : ℝ) ^ β * t ^ β) := by gcongr
            _ ≤ 2 * (8 * CL * lδ * t ^ β) + A' * lδ * ((4 : ℝ) ^ β * t ^ β) := by gcongr
            _ = lδ * ((16 * CL + A' * (4 : ℝ) ^ β) * t ^ β) := by ring
            _ ≤ lδ * (C * t ^ β) := by
                gcongr
                have : 0 ≤ CL * (64 : ℝ) ^ |1 - β| := by positivity
                have : A' * (4 : ℝ) ^ β ≤ 4 * A' * (4 : ℝ) ^ β := by
                  have : 0 ≤ A' * (4 : ℝ) ^ β := by positivity
                  linarith
                rw [hC]; linarith
        · -- `t > 1/4`: four pieces at scale `1`
          have hR := hRK 1 le_rfl (by omega)
          have h4 := four_pieces (d := lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare)
            (fun a b c => lfppDOn_triangle a b c) x.2 y.2
            (B := 2 * E + RK ξ W P δ q 1 (N - 1) ω) fun z hz w hw h1 h2 =>
              hprop 1 le_rfl (by omega) E hE z hz w hw (by simpa using h1) (by simpa using h2)
          have hlfpp : lfppDOn ξ (fun x => phiVer W P δ 1 x ω) closedUnitSquare x y ≤
              ENNReal.ofReal (4 * (2 * (Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1))) +
                A' * lδ * Real.exp (-(L * β) * (1 : ℕ)))) := by
            refine h4.trans ?_
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity)
              (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
              ENNReal.ofReal_ofNat]
            gcongr
          have hexp1 : Real.exp (-(L * β) * (1 : ℕ)) ≤ (4 : ℝ) ^ β * t ^ β := by
            have h1 : Real.exp (-(L * β) * (1 : ℕ)) ≤ 1 :=
              Real.exp_le_one_iff.2 (by push_cast; nlinarith)
            have h2 : (1 : ℝ) ≤ (4 * t) ^ β := Real.one_le_rpow (by linarith) hβ0.le
            rw [Real.mul_rpow (by norm_num) ht0.le] at h2
            linarith
          refine (lenMetricOn_le_of (by positivity) hlfpp).trans ?_
          calc 4 * (2 * (Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ (N - 1))) +
                A' * lδ * Real.exp (-(L * β) * (1 : ℕ)))
              ≤ 4 * (2 * (8 * CL * lδ * δ ^ β) + A' * lδ * ((4 : ℝ) ^ β * t ^ β)) := by
                gcongr
            _ ≤ 4 * (2 * (8 * CL * lδ * t ^ β) + A' * lδ * ((4 : ℝ) ^ β * t ^ β)) := by gcongr
            _ = lδ * ((64 * CL + 4 * A' * (4 : ℝ) ^ β) * t ^ β) := by ring
            _ ≤ lδ * (C * t ^ β) := by
                gcongr
                have : 0 ≤ CL * (64 : ℝ) ^ |1 - β| := by positivity
                rw [hC]; linarith
    exact absurd hlt (not_lt.2 ((inv_mul_le_iff₀ hlδ).2 key))
  -- the measure
  calc P {ω | ∃ x y : closedUnitSquare, δ < ‖(x : ℂ) - y‖ ∧ C * ‖(x : ℂ) - y‖ ^ β <
        lδ⁻¹ * lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y}
      ≤ P (B1 ∪ (⋃ K ∈ Finset.Icc 1 (N - 1), B2 K) ∪ B0) := measure_mono hincl
    _ ≤ P B1 + P (⋃ K ∈ Finset.Icc 1 (N - 1), B2 K) + P B0 :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ENNReal.ofReal (ε / 2) + ∑ K ∈ Finset.Icc 1 (N - 1), P (B2 K) + 0 := by
        gcongr
        · exact measure_biUnion_finset_le _ _
        · exact hch.le
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) + 0 := by
        gcongr
        exact (Finset.sum_le_sum hB2).trans hsumB2
    _ = ENNReal.ofReal ε := by rw [add_zero]; exact half_add_half ε hε

end S6P28U
end DDDF
end LQGMetric
