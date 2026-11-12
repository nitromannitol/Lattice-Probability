/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117G3 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_one_eq_lintegral_enorm takes the measurability argument. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G1

/-!
# D117 packet P-SIM: (eq-def-M-eta) along the scales `c 2^{-n}` (P2-DZZSIM2)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-M-eta), l. 1209–1213) define
`M_γ^{h̃}(A) = lim_{δ → 0} ∫_A e^{γ h̃_δ(z) − γ²/2 E h̃_δ(z)²} dz`, a limit of martingales
(l. 680–682, "c.f. [RV14]"). The library proves the limit along `δ = 2^{-n}`
(`ae_isChaosLimit_wickQArea`). Along `c 2^{-n}`, `c ∈ (0, 1]`, we use the martingale argument
suggested in handoff/P2-DZZSIM.md: with `2^{-k-1} < c ≤ 2^{-k}` the merged scales
`s_{2n} = 2^{-(n+k)}`, `s_{2n+1} = c 2^{-n}` decrease, the approximations along `s` form a
nonnegative martingale (`setLIntegral_tMass_eq`, S5D117G2) with mean `Leb(E)`, hence converge
a.s. (Doob, `Submartingale.ae_tendsto_limitProcess`); the even subsequence has the limit `M^W(B)`,
so the odd one too.

* `ae_tendsto_tMass`: a.s. convergence along any decreasing positive scale sequence;
* **`dzzWickChaosAlong_of`**: `DZZWickChaosAlong c` for `0 < c ≤ 1`;
* **`dzzSimCoupleU_of_norm_le`**: `DZZSimCoupleU γ ξ K a` for all `0 < ‖a‖ ≤ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent GMCIdent4 GMCIdent5

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma lintegral_tDens (hW : IsWhiteNoise P W) (γ : ℝ) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ∫⁻ ω, tDens W γ t z ω ∂P = 1 := by
  set κ := wndKernelL2 openSquare (Ioi (t ^ 2)) z
  have he : (fun ω => tDens W γ t z ω) =ᵐ[P] fun ω =>
      ENNReal.ofReal (Real.exp (-(γ ^ 2 / 2 * (Real.pi * ‖κ‖ ^ 2))) *
        Real.exp ((γ * Real.sqrt Real.pi) * W κ ω)) := by
    filter_upwards [tVer_ae_eq hW ht z] with ω h
    simp only [tDens, h, tildeHInf, wnField, tildeVar]
    rw [← Real.exp_add]; congr 2; ring
  have hint := (integrable_exp_wn hW (γ * Real.sqrt Real.pi) κ).const_mul
    (Real.exp (-(γ ^ 2 / 2 * (Real.pi * ‖κ‖ ^ 2))))
  rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun ω => by positivity), integral_const_mul, integral_exp_wn hW,
    ← Real.exp_add]
  have : -(γ ^ 2 / 2 * (Real.pi * ‖κ‖ ^ 2)) + (γ * Real.sqrt Real.pi) ^ 2 / 2 * ‖κ‖ ^ 2 = 0 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring
  rw [this, Real.exp_zero, ENNReal.ofReal_one]

lemma lintegral_tMass (hW : IsWhiteNoise P W) (γ : ℝ) {t : ℝ} (ht : 0 < t) (E : Set ℂ) :
    ∫⁻ ω, tMass W γ t E ω ∂P = volume E := by
  have := hW.isProbabilityMeasure
  simp only [tMass]
  rw [lintegral_lintegral_swap (μ := P) (ν := volume.restrict E)
    (f := fun ω z => tDens W γ t z ω) (measurable_tDens hW γ ht).aemeasurable]
  simp only [lintegral_tDens hW γ ht, lintegral_const, one_mul, Measure.restrict_apply_univ]

/-- The filtration `𝓖_{s_m}` along a decreasing positive scale sequence. -/
def scaleFil (hW : IsWhiteNoise P W) {s : ℕ → ℝ} (hs0 : ∀ m, 0 < s m) (hanti : Antitone s) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq m := wnSigma W (scaleSet (s m))
  mono' _ _ hij := wnSigma_mono (scaleSet_anti (hs0 _).le (hanti hij))
  le' _ := wnSigma_le hW _

/-- The approximations along a decreasing positive scale sequence converge a.s. -/
theorem ae_tendsto_tMass (hW : IsWhiteNoise P W) (γ : ℝ) {s : ℕ → ℝ} (hs0 : ∀ m, 0 < s m)
    (hanti : Antitone s) {E : Set ℂ} (hEf : volume E ≠ ⊤) :
    ∃ L : Ω → ℝ, ∀ᵐ ω ∂P,
      Tendsto (fun m => tMass W γ (s m) E ω) atTop (𝓝 (ENNReal.ofReal (L ω))) := by
  have hP := hW.isProbabilityMeasure
  set X : ℕ → Ω → ℝ := fun m ω => (tMass W γ (s m) E ω).toReal with hX
  have hfin : ∀ m, ∀ᵐ ω ∂P, tMass W γ (s m) E ω < ⊤ := fun m =>
    ae_lt_top (measurable_tMass hW γ (hs0 m) E) (by rw [lintegral_tMass hW γ (hs0 m) E]; exact hEf)
  have hsub : Submartingale X (scaleFil hW hs0 hanti) P := by
    refine submartingale_of_setIntegral_le
      (fun m => (measurable_tMass_scale hW γ (hs0 m) E).ennreal_toReal.stronglyMeasurable)
      (fun m => integrable_toReal_of_lintegral_ne_top
        (measurable_tMass hW γ (hs0 m) E).aemeasurable
        (by rw [lintegral_tMass hW γ (hs0 m) E]; exact hEf)) (fun i j hij A hA => ?_)
    simp only [X]
    rw [integral_toReal (measurable_tMass hW γ (hs0 i) E).aemeasurable
        (ae_restrict_of_ae (hfin i)),
      integral_toReal (measurable_tMass hW γ (hs0 j) E).aemeasurable
        (ae_restrict_of_ae (hfin j)), setLIntegral_tMass_eq hW γ (hs0 j) (hanti hij) hA E]
  have hbdd : ∀ m, eLpNorm (X m) 1 P ≤ ((volume E).toNNReal : ℝ≥0∞) := fun m => by
    rw [ENNReal.coe_toNNReal hEf, eLpNorm_one_eq_lintegral_enorm (hsub.integrable m).aestronglyMeasurable,
      ← lintegral_tMass hW γ (hs0 m) E]
    refine lintegral_mono fun ω => ?_
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  refine ⟨(scaleFil hW hs0 hanti).limitProcess X P, ?_⟩
  filter_upwards [hsub.ae_tendsto_limitProcess hbdd, ae_all_iff.2 hfin] with ω h1 h2
  have e : (fun m => tMass W γ (s m) E ω) = fun m => ENNReal.ofReal (X m ω) :=
    funext fun m => (ENNReal.ofReal_toReal (h2 m).ne).symm
  rw [e]; exact ENNReal.tendsto_ofReal h1

/-- Two jointly measurable versions of a field agree for a.e. `z`, almost surely. -/
lemma ae_ae_eq_of_version (hW : IsWhiteNoise P W) {Y Y' : ℂ → Ω → ℝ}
    (hY : Measurable fun p : ℂ × Ω => Y p.1 p.2) (hY' : Measurable fun p : ℂ × Ω => Y' p.1 p.2)
    (h : ∀ z, Y z =ᵐ[P] Y' z) : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), Y z ω = Y' z ω := by
  have := hW.isProbabilityMeasure
  have hm : MeasurableSet {p : ℂ × Ω | Y p.1 p.2 = Y' p.1 p.2} := measurableSet_eq_fun hY hY'
  exact (Measure.ae_ae_comm (μ := (volume : Measure ℂ)) (ν := P) hm).1 (ae_of_all _ h)

/-- **(eq-def-M-eta) along `c 2^{-n}`** for `0 < c ≤ 1`. -/
theorem dzzWickChaosAlong_of {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : DZZWickChaosAlong c := by
  intro Ω' _ P' W hW γ hγ hγ2
  have hP := hW.isProbabilityMeasure
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hc hc1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  set Z : ℝ → ℂ → Ω' → ℝ := fun s => if hs : 0 < s then
    (exists_continuous_tildeHInf hW hs).choose else fun _ _ => 0 with hZ
  have hZs : ∀ s (hs : 0 < s), (∀ ω, Continuous fun x => Z s x ω) ∧
      (∀ x, Measurable (Z s x)) ∧ ∀ x, Z s x =ᵐ[P'] tildeHInf W s x := fun s hs => by
    simp only [Z, hs, ↓reduceDIte]; exact (exists_continuous_tildeHInf hW hs).choose_spec
  have hcn : ∀ n : ℕ, 0 < c * (1 / 2 : ℝ) ^ n := fun n => by positivity
  refine ⟨Z, fun n ω => (hZs _ (hcn n)).1 ω, fun n x => (hZs _ (hcn n)).2.2 x, ?_⟩
  -- the merged scales
  set s : ℕ → ℝ := fun m => if m % 2 = 0 then (1 / 2 : ℝ) ^ (m / 2 + k)
    else c * (1 / 2 : ℝ) ^ (m / 2) with hs
  have hse : ∀ n, s (2 * n) = (1 / 2 : ℝ) ^ (n + k) := fun n => by
    have h1 : 2 * n % 2 = 0 := by omega
    have h2 : 2 * n / 2 = n := by omega
    simp only [s, h1, h2, ↓reduceIte]
  have hso : ∀ n, s (2 * n + 1) = c * (1 / 2 : ℝ) ^ n := fun n => by
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp only [s, h1, h2, one_ne_zero, ↓reduceIte]
  have hs0 : ∀ m, 0 < s m := fun m => by simp only [s]; split_ifs <;> positivity
  have hanti : Antitone s := by
    refine antitone_nat_of_succ_le fun m => ?_
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [hso, hse, pow_add, mul_comm]
      exact mul_le_mul_of_nonneg_left hk2 (by positivity)
    · rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, hse, hso,
        show n + 1 + k = n + (k + 1) by ring, pow_add, mul_comm c]
      exact mul_le_mul_of_nonneg_left hk1.le (by positivity)
  have hwz : ∀ j : ℕ, Measurable fun p : ℂ × Ω' => wickZeta hW ((1 / 2 : ℝ) ^ j) p.1 p.2 :=
    fun j => by
      have e : (fun p : ℂ × Ω' => wickZeta hW ((1 / 2 : ℝ) ^ j) p.1 p.2) =
          fun p => coarseVer hW j p.1 p.2 := funext fun p => wickZeta_pow hW j p.1 p.2
      rw [e]; exact measurable_coarseVer_uncurry hW j
  have key : ∀ (q : ℚ × ℚ) (r : ℚ), ∀ᵐ ω ∂P', 0 < r →
      Tendsto (fun n : ℕ => ∫⁻ z in Metric.ball (ratPt q) r ∩ dzzV,
        ENNReal.ofReal (Real.exp (γ * Z (c * (1 / 2 : ℝ) ^ n) z ω -
          γ ^ 2 / 2 * tildeVar (c * (1 / 2 : ℝ) ^ n) z)))
        atTop (𝓝 (wickQArea γ W ω (Metric.ball (ratPt q) r))) := by
    intro q r
    set E := Metric.ball (ratPt q) (r : ℝ) ∩ dzzV
    have hEf : volume E ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
    obtain ⟨L, hL⟩ := ae_tendsto_tMass hW γ hs0 hanti hEf
    have hv1 : ∀ n : ℕ, ∀ᵐ ω ∂P', ∀ᵐ z ∂(volume : Measure ℂ),
        tVer W ((1 / 2 : ℝ) ^ (n + k)) z ω = wickZeta hW ((1 / 2 : ℝ) ^ (n + k)) z ω :=
      fun n => ae_ae_eq_of_version hW (measurable_tVer' hW _) (hwz (n + k)) fun z =>
        (tVer_ae_eq hW (by positivity) z).trans ((wickZeta_spec hW).2 (n + k) z).symm
    have hv2 : ∀ n : ℕ, ∀ᵐ ω ∂P', ∀ᵐ z ∂(volume : Measure ℂ),
        tVer W (c * (1 / 2 : ℝ) ^ n) z ω = Z (c * (1 / 2 : ℝ) ^ n) z ω :=
      fun n => ae_ae_eq_of_version hW (measurable_tVer' hW _)
        (measurable_uncurry_of_continuous_of_measurable (hZs _ (hcn n)).1 (hZs _ (hcn n)).2.1)
        fun z => (tVer_ae_eq hW (hcn n) z).trans ((hZs _ (hcn n)).2.2 z).symm
    filter_upwards [hL, ae_all_iff.2 hv1, ae_all_iff.2 hv2,
      ae_isChaosLimit_wickQArea hW hγ hγ2] with ω hLω h1 h2 h3 hr
    have hev : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => show n ≤ 2 * n by omega) tendsto_id
    have hod : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => show n ≤ 2 * n + 1 by omega)
        tendsto_id
    have hd : ∀ n, tMass W γ (s (2 * n)) E ω = ∫⁻ z in E,
        ENNReal.ofReal (Real.exp (γ * wickZeta hW ((1 / 2 : ℝ) ^ (n + k)) z ω -
          γ ^ 2 / 2 * tildeVar ((1 / 2 : ℝ) ^ (n + k)) z)) := fun n => by
      rw [hse, tMass]
      exact lintegral_congr_ae (ae_restrict_of_ae ((h1 n).mono fun z hz => by simp only [tDens, hz]))
    have ho : ∀ n, tMass W γ (s (2 * n + 1)) E ω = ∫⁻ z in E,
        ENNReal.ofReal (Real.exp (γ * Z (c * (1 / 2 : ℝ) ^ n) z ω -
          γ ^ 2 / 2 * tildeVar (c * (1 / 2 : ℝ) ^ n) z)) := fun n => by
      rw [hso, tMass]
      exact lintegral_congr_ae (ae_restrict_of_ae ((h2 n).mono fun z hz => by simp only [tDens, hz]))
    have hA := hLω.comp hev
    have hB := hLω.comp hod
    have hC := (h3 q r hr).comp (tendsto_add_atTop_nat k)
    simp only [Function.comp_def] at hA hB hC
    simp only [hd] at hA
    simp only [ho] at hB
    have hμ : wickQArea γ W ω (Metric.ball (ratPt q) r) = ENNReal.ofReal (L ω) :=
      tendsto_nhds_unique hC hA
    rw [hμ]
    exact hB
  filter_upwards [ae_all_iff.2 fun q => ae_all_iff.2 (key q)] with ω h q r hr
  exact h q r hr

/-- **`DZZSimCoupleU` for all similarities with `0 < ‖a‖ ≤ 1`** (DZZ lem-scaling-coupling,
l. 611–624, composed with L3.8-walled). -/
theorem dzzSimCoupleU_of_norm_le {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    (hξ2 : ξ < 1 / 2) {K : Set ℂ} (hK : IsClosed K) (hKξ : K ⊆ dzzVXi ξ) {a : ℂ} (ha0 : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) : DZZSimCoupleU γ ξ K a :=
  dzzSimCoupleU_of_along hγ hγ2 hξ hξ2 hK hKξ ha0 ha1
    (dzzWickChaosAlong_of (norm_pos_iff.2 ha0) ha1)
    (dzzLemma27Along_of (norm_pos_iff.2 ha0) ha1)

end DZZ
end LQGMetric
