/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_12Loc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLim
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.DFLem71

/-!
# DFGPS Lemma 2.12, localization (T:1039–1046)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1039–1043: "By taking a limit as
`ε → 0` in the estimate of Lemma 2.10, then sending `p → 1`, we find that a.s. for each `r > 0` and
each `C > 1`, there exists `r' = r'(r, C) > 0` (random) such that
`sup_{u,v ∈ S_r(0)} D_h(u,v) ≤ (2C)⁻¹ D_h(S_r(0), ∂S_{r'}(0))`."

We do this for a subsequential limit law `μ` of `𝔞_ε⁻¹ D_h^ε` (portmanteau on the closed set
`agreeSetK`, as in `lem2_5_lim`), with the distance to `∂S_{r'}(0)` replaced by the distance to the
complement of the open square (equivalent for LFPP by the first-hit cut `lfppC_cut`; this form is
closed and needs no path argument for the limit). Then (`loc_of_agree`, deterministic) we derive the
localization hypothesis of `Blueprint.DFLem7_1` with Euclidean balls and spheres (T:1044–1048).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- `k d(x,y) ≤ d(u,w)` for `x, y, u ∈ S_r(0)` and `w ∉ int S_s(0)` (closed in `d`) -/
def agreeSetK (k r s : ℝ) : Set C(ℂ × ℂ, ℝ) :=
  {d | ∀ x ∈ sqC r 0, ∀ y ∈ sqC r 0, ∀ u ∈ sqC r 0, ∀ w, w ∉ interior (sqC s 0) →
    k * d (x, y) ≤ d (u, w)}

theorem isClosed_agreeSetK (k r s : ℝ) : IsClosed (agreeSetK k r s) := by
  have e : agreeSetK k r s = ⋂ x ∈ sqC r 0, ⋂ y ∈ sqC r 0, ⋂ u ∈ sqC r 0,
      ⋂ w ∈ (interior (sqC s 0))ᶜ, {d : C(ℂ × ℂ, ℝ) | k * d (x, y) ≤ d (u, w)} := by
    ext d; simp [agreeSetK]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_biInter fun u _ =>
    isClosed_biInter fun w _ =>
      isClosed_le (continuous_const.mul (continuous_eval_const _)) (continuous_eval_const _)

theorem agreeSetK_mono_s {k r s s' : ℝ} (hss : s ≤ s') : agreeSetK k r s ⊆ agreeSetK k r s' :=
  fun _ hd x hx y hy u hu w hw => hd x hx y hy u hu w fun h =>
    hw (interior_mono (sqC_mono hss) h)

/-- the event of Lemma 2.10 (constant `k`) puts `𝔞_ε⁻¹ D_h^ε` in `agreeSetK k r (R r)` -/
theorem lfppC_mem_agreeSetK {ξ ε k r R : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (hk : 0 < k) (hr : 0 < r) (hR : 1 < R) (hE : sqBdyEvent ξ ε k r R g) :
    lfppC ξ ε g ∈ agreeSetK k r (R * r) := by
  intro x hx y hy u hu w hw
  have hfr : ∀ w' ∈ frontier (sqC (R * r) 0), k * lfppC ξ ε g (x, y) ≤ lfppC ξ ε g (u, w') := by
    intro w' hw'
    simp only [lfppC_apply_of_continuous hc]
    set c := (aEpsDF ξ ε)⁻¹
    have hc0 : 0 ≤ c := inv_nonneg.2 (aEpsDF_nonneg_sq _ _)
    unfold sqBdyEvent at hE
    have h1 : lfppDistE ξ ε g x y ≤ ⨆ u ∈ sqC r 0, ⨆ v ∈ sqC r 0, lfppDistE ξ ε g u v :=
      le_iSup₂_of_le (f := fun u _ => ⨆ v ∈ sqC r 0, lfppDistE ξ ε g u v) x hx
        (le_iSup₂_of_le (f := fun v _ => lfppDistE ξ ε g x v) y hy le_rfl)
    have h2 : (⨅ u ∈ sqC r 0, ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε g u v) ≤
        lfppDistE ξ ε g u w' :=
      iInf₂_le_of_le (f := fun u _ => ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε g u v) u hu
        (iInf₂_le_of_le (f := fun v _ => lfppDistE ξ ε g u v) w' hw' le_rfl)
    have h3 : lfppDistE ξ ε g x y ≤ ENNReal.ofReal k⁻¹ * lfppDistE ξ ε g u w' :=
      (h1.trans hE.le).trans (by gcongr)
    have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lfppDistE_ne_top' hc u w')) h3
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h4
    have h5 : k * (lfppDistE ξ ε g x y).toReal ≤ (lfppDistE ξ ε g u w').toReal := by
      have := mul_le_mul_of_nonneg_left h4 hk.le
      rwa [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul] at this
    nlinarith
  have hrR : r < R * r := by nlinarith
  exact lfppC_cut hc (isCompact_sqC (by positivity)).isClosed (sqC_subset_interior hrR hu) hw hfr

/-- **DFGPS T:1039–1043** for a subsequential limit law `μ`: `μ`-a.s., for all `k, r ∈ ℕ` there is
`s ∈ ℕ` with `d ∈ agreeSetK (k+1) (r+1) s`. -/
theorem ae_agreeSetK (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P) (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(ℂ × ℂ, ℝ))
    (μ : ProbabilityMeasure C(ℂ × ℂ, ℝ))
    (hν : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppC (xiGamma γ) (εn n) (h ω))
    (hε0 : Tendsto εn atTop (𝓝 0)) (hlim : Tendsto ν atTop (𝓝 μ)) :
    ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), ∀ k r : ℕ, ∃ s : ℕ,
      d ∈ agreeSetK ((k : ℝ) + 1) ((r : ℝ) + 1) s := by
  set ξ := xiGamma γ
  have hcS : ∀ n, ∀ᵐ ω ∂P, Continuous (heatMollify (εn n) (h ω)) := fun n =>
    (hh.ae_tendstoLocallyUniformly_heatMollify (εn n) (hν n).1.1.ne').mono fun ω hω => hω.2
  have hFC : ∀ n, AEMeasurable (fun ω => lfppC ξ (εn n) (h ω)) P := fun n =>
    aemeasurable_lfppC hh (hν n).1.1.ne'
  have hεn' : Tendsto εn atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall fun n => (hν n).1.1⟩
  rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro r₀
  set k' : ℝ := (k : ℝ) + 1
  have hk' : 0 < k' := by positivity
  set r : ℝ := (r₀ : ℝ) + 1
  have hr : 0 < r := by positivity
  refine ae_iff.2 (le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_) zero_le)
  set ζ : ℝ := min ((ε' : ℝ) / 2) (1 / 2) with hζdef
  have hζ0 : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨R, hR1, hRp⟩ := lem2_10 h28 γ hγ hγ2 P h hh (1 - ζ / 2)
    ⟨by linarith, by linarith⟩ k' hk'
  set s : ℕ := ⌈R * r⌉₊
  have hs1 : R * r ≤ s := Nat.le_ceil _
  have hF := isClosed_agreeSetK k' r (R * r)
  have hμF : ENNReal.ofReal (1 - ζ) ≤ (μ : Measure C(ℂ × ℂ, ℝ)) (agreeSetK k' r (R * r)) := by
    refine le_measure_of_isClosed hlim hF ?_
    have hq : ENNReal.ofReal (1 - ζ) <
        liminf (fun ε => P {ω | sqBdyEvent ξ ε k' r R (h ω)}) (𝓝[>] 0) :=
      lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
        (hRp r hr)
    filter_upwards [hεn'.eventually (eventually_lt_of_lt_liminf hq)] with n hn
    refine hn.le.trans ?_
    rw [(hν n).2, Measure.map_apply_of_aemeasurable (hFC n) hF.measurableSet]
    refine measure_mono_ae ?_
    filter_upwards [hcS n] with ω hω hE
    exact lfppC_mem_agreeSetK hω hk' hr hR1 hE
  have hsub : {d : C(ℂ × ℂ, ℝ) | ¬ ∃ s : ℕ, d ∈ agreeSetK k' r s} ⊆
      (agreeSetK k' r (R * r))ᶜ := by
    intro d hd hdF
    exact hd ⟨s, agreeSetK_mono_s hs1 hdF⟩
  calc (μ : Measure C(ℂ × ℂ, ℝ)) {d | ¬ ∃ s : ℕ, d ∈ agreeSetK k' r s}
      ≤ (μ : Measure C(ℂ × ℂ, ℝ)) (agreeSetK k' r (R * r))ᶜ := measure_mono hsub
    _ ≤ ENNReal.ofReal ζ := by
        rw [prob_compl_eq_one_sub hF.measurableSet]
        refine tsub_le_iff_right.2 ?_
        calc (1 : ℝ≥0∞) = ENNReal.ofReal ζ + ENNReal.ofReal (1 - ζ) := by
              rw [← ENNReal.ofReal_add hζ0.le (by linarith)]; simp
          _ ≤ ENNReal.ofReal ζ + (μ : Measure C(ℂ × ℂ, ℝ)) (agreeSetK k' r (R * r)) := by
              gcongr
    _ ≤ 0 + (ε' : ℝ≥0∞) := by
        rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (by
          have := ε'.coe_nonneg; linarith))

/-- **DFGPS T:1044–1048, deterministic part**: the agreement condition for all `k, r` gives the
localization hypothesis of `Blueprint.DFLem7_1` (for any constant `c` in place of `e^{2|ξ|M}`). -/
theorem loc_of_agree {D : ContMetric}
    (hA : ∀ k r : ℕ, ∃ s : ℕ, D.1 ∈ agreeSetK ((k : ℝ) + 1) ((r : ℝ) + 1) s) (c : ℝ) :
    ∀ ρ : ℝ, 0 < ρ → ∃ ρ' : ℝ, ρ < ρ' ∧
      ENNReal.ofReal c * supDist D (closedBall 0 ρ) < setDist D (closedBall 0 ρ) (sphere 0 ρ') := by
  intro ρ hρ
  obtain ⟨k, hk⟩ := exists_nat_gt c
  set r : ℕ := ⌈2 * ρ⌉₊
  have hr : 2 * ρ ≤ r := Nat.le_ceil _
  obtain ⟨s, hs⟩ := hA k r
  have hB : ∀ x ∈ closedBall (0 : ℂ) ρ, x ∈ sqC ((r : ℝ) + 1) 0 := fun x hx => by
    rw [mem_closedBall, dist_zero_right] at hx
    exact mem_sqC_of_norm_le (by linarith)
  set ρ' : ℝ := s + ρ + 1
  have hS : ∀ v ∈ sphere (0 : ℂ) ρ', v ∉ interior (sqC s 0) := fun v hv hvi => by
    have h1 := norm_le_of_mem_sqC (interior_subset hvi)
    rw [mem_sphere, dist_zero_right] at hv
    linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnn : ∀ x y : ℂ, 0 ≤ D.1 (x, y) := fun x y => dist_nonneg (x := D.pt x) (y := D.pt y)
  -- the supremum is bounded by `D(u,v)/(k+1)`
  have hsup : ∀ u ∈ closedBall (0 : ℂ) ρ, ∀ v ∈ sphere (0 : ℂ) ρ',
      supDist D (closedBall 0 ρ) ≤ ENNReal.ofReal (D.1 (u, v) / ((k : ℝ) + 1)) := by
    intro u hu v hv
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hk1, mul_comm]
    exact hs x (hB x hx) y (hB y hy) u (hB u hu) v (hS v hv)
  have h0B : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := mem_closedBall_self hρ.le
  have hρ'S : ((ρ' : ℝ) : ℂ) ∈ sphere (0 : ℂ) ρ' := by
    rw [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hρB : ((ρ : ℝ) : ℂ) ∈ closedBall (0 : ℂ) ρ := by
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hStop : supDist D (closedBall 0 ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsup 0 h0B _ hρ'S)
  have hpos : 0 < D.1 (0, (ρ : ℂ)) := by
    refine lt_of_le_of_ne (hnn _ _) fun h0 => ?_
    have := D.2.eq_of_eq_zero 0 (ρ : ℂ) h0.symm
    have h' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    exact h' this.symm
  have hS0 : supDist D (closedBall 0 ρ) ≠ 0 := by
    refine (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos) ?_).ne'
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ closedBall (0 : ℂ) ρ) =>
      ⨆ v ∈ closedBall (0 : ℂ) ρ, ENNReal.ofReal (D.1 (u, v))) 0 h0B
      (le_iSup₂_of_le (f := fun v (_ : v ∈ closedBall (0 : ℂ) ρ) =>
        ENNReal.ofReal (D.1 (0, v))) _ hρB le_rfl)
  refine ⟨ρ', by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)], ?_⟩
  calc ENNReal.ofReal c * supDist D (closedBall 0 ρ)
      < ENNReal.ofReal ((k : ℝ) + 1) * supDist D (closedBall 0 ρ) := by
        rw [mul_comm _ (supDist D _), mul_comm _ (supDist D _)]
        exact ENNReal.mul_lt_mul_right hS0 hStop
          ((ENNReal.ofReal_lt_ofReal_iff hk1).2 (by linarith))
    _ ≤ setDist D (closedBall 0 ρ) (sphere 0 ρ') := by
        unfold setDist
        rw [le_setEDist]
        rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
        rw [edist_dist]
        calc ENNReal.ofReal ((k : ℝ) + 1) * supDist D (closedBall 0 ρ)
            ≤ ENNReal.ofReal ((k : ℝ) + 1) * ENNReal.ofReal (D.1 (u, v) / ((k : ℝ) + 1)) := by
              gcongr; exact hsup u hu v hv
          _ = ENNReal.ofReal (D.1 (u, v)) := by
              rw [← ENNReal.ofReal_mul hk1.le, mul_div_cancel₀ _ hk1.ne']
          _ = ENNReal.ofReal (dist (D.pt u) (D.pt v)) := rfl

end LQGMetric.DFGPS
