/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityProb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Regularity
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Metric.SetDist

/-!
# GM Lemma 4.11: conditions 1 and 6 of `ℰ_𝕣`

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, proof of Lemma 4.11 (`lem-reg-event-prob`),
l. 1983 (condition 1, "By Axiom V … we can find a bounded open set `V ⊃ U`, depending only on
`U`") and l. 1989 (condition 6, "By Lemma 2.13 and a union bound over values of
`ε ∈ (0,a] ∩ {2^{-n}}`").

* `gm_regC1_prob`: condition 1 (comparison of domains). GM cite "Axiom V (tightness across
  scales)"; the needed statement — the `D_h`-diameter of a ball is smaller than its distance to a
  much larger concentric circle — is `Blueprint.GMS2_4e` (GM U:1434, U:3605). We take
  `V := B_{Rρ}(0)` with `U ⊂ B_ρ(0)`, and `R` from GMS2_4e.
* `gm_regC6_prob`: condition 6, by CONF Lemma 3.5 (= GM Lemma 2.13, `CONFLem3_5At`) with
  `K := cl B_{ρ+4ℓ}(0) ⊃ B_{4ℓ}(V)` and a union bound over dyadic `ε = 2^{-n} ≤ a`; the bound
  `C₀ε² ≤ C₀ a 2^{-n}` gives failure probability `≤ 2C₀a → 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

theorem gm_setDist_anti (D : ContMetric) {A A' B B' : Set ℂ} (hA : A ⊆ A') (hB : B ⊆ B') :
    setDist D A' B' ≤ setDist D A B :=
  MetricGeometry.setEDist_anti (image_mono hA) (image_mono hB)

theorem gm_rScale_subset_ball {𝕣 ρ : ℝ} (h𝕣 : 0 < 𝕣) {A : Set ℂ} (hA : A ⊆ Metric.ball 0 ρ) :
    rScale 𝕣 A ⊆ Metric.ball 0 (𝕣 * ρ) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hA hx
  rw [mem_ball_zero_iff] at hx' ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
  exact mul_lt_mul_of_pos_left hx' h𝕣

theorem gm_rScale_sphere {𝕣 s : ℝ} (h𝕣 : 0 < 𝕣) :
    rScale 𝕣 (Metric.sphere 0 s) ⊆ Metric.sphere 0 (𝕣 * s) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_sphere_zero_iff_norm] at hx ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣, hx]

/-- **GM Lemma 4.11, condition 1** (l. 1983): for bounded `U` and `β ∈ (0,1)` there is a bounded
connected open `V ⊃ U` (a ball) such that condition 1 of `ℰ_𝕣` fails with probability `≤ β` for
every `𝕣 > 0`. -/
theorem gm_regC1_prob (h24e : GMS2_4e) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {U : Set ℂ} (hU : Bornology.IsBounded U) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ V : Set ℂ, IsOpen V ∧ Bornology.IsBounded V ∧ IsConnected V ∧ U ⊆ V ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ R : RegPar, R.U = U → R.V = V → ∀ 𝕣 : ℝ, 0 < 𝕣 →
        P (regC1 D h R 𝕣)ᶜ ≤ ENNReal.ofReal β := by
  obtain ⟨Rr, hRr1, hRr⟩ := h24e γ hγ hγ2 D c hD β hβ0 hβ1
  obtain ⟨ρ₀, hρ₀⟩ := hU.subset_ball (0 : ℂ)
  set ρ := max ρ₀ 1 with hρ
  have hρpos : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hUρ : U ⊆ Metric.ball 0 ρ := hρ₀.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hRρ : 0 < Rr * ρ := mul_pos (by linarith) hρpos
  refine ⟨Metric.ball 0 (Rr * ρ), Metric.isOpen_ball, Metric.isBounded_ball,
    (convex_ball _ _).isConnected (Metric.nonempty_ball.2 hRρ),
    hUρ.trans (Metric.ball_subset_ball (le_mul_of_one_le_left hρpos.le hRr1.le)), ?_⟩
  intro Ω _ P _ h hh R hRU hRV 𝕣 h𝕣
  refine le_trans (measure_mono ?_) (hRr P h hh 0 (𝕣 * ρ) (mul_pos h𝕣 hρpos))
  intro ω hω
  simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
  intro hgood
  apply hω
  simp only [regC1, mem_ofPred_eq, hRU, hRV]
  have hsub : rScale 𝕣 U ⊆ Metric.ball 0 (𝕣 * ρ) := gm_rScale_subset_ball h𝕣 hUρ
  have hfr : rScale 𝕣 (frontier (Metric.ball (0 : ℂ) (Rr * ρ))) ⊆
      Metric.sphere 0 (Rr * (𝕣 * ρ)) := by
    rw [frontier_ball _ hRρ.ne']
    refine (gm_rScale_sphere h𝕣).trans (le_of_eq ?_)
    congr 1; ring
  refine le_trans ?_ (le_trans hgood.le (gm_setDist_anti _ hsub hfr))
  exact iSup₂_le fun z hz => iSup₂_le fun w hw =>
    le_iSup₂_of_le (f := fun z (_ : z ∈ Metric.ball (0 : ℂ) (𝕣 * ρ)) =>
      ⨆ v ∈ Metric.ball (0 : ℂ) (𝕣 * ρ), ENNReal.ofReal ((D (h ω)).1 (z, v))) z (hsub hz)
      (le_iSup₂_of_le (f := fun v (_ : v ∈ Metric.ball (0 : ℂ) (𝕣 * ρ)) =>
        ENNReal.ofReal ((D (h ω)).1 (z, v))) w (hsub hw) le_rfl)

/-- points of `B_{4ℓ𝕣}(𝕣V)` lie in `𝕣 cl B_{ρ+4ℓ}(0)` when `V ⊂ B_ρ(0)` -/
theorem gm_regRegion_subset {R : RegPar} {𝕣 ρ : ℝ} (h𝕣 : 0 < 𝕣) (hV : R.V ⊆ Metric.ball 0 ρ) :
    regRegion R 𝕣 ⊆ (fun x : ℂ => (𝕣 : ℂ) * x + 0) '' Metric.closedBall 0 (ρ + 4 * R.ℓ) := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.1 hz
  have hy' := gm_rScale_subset_ball h𝕣 hV hy
  rw [mem_ball_zero_iff] at hy'
  have h𝕣c : (𝕣 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h𝕣.ne'
  refine ⟨z / 𝕣, ?_, by field_simp; ring⟩
  rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣,
    div_le_iff₀ h𝕣]
  have : ‖z‖ ≤ ‖y‖ + dist z y := by
    rw [dist_eq_norm]; linarith [norm_sub_norm_le z y, norm_nonneg (z - y)]
  nlinarith

/-- **GM Lemma 4.11, condition 6** (l. 1989): by CONF Lemma 3.5 (GM Lemma 2.13) and a union bound
over dyadic `ε ∈ (0,a]`, condition 6 of `ℰ_𝕣` holds with probability `→ 1` as `a → 0`, uniformly
in `𝕣`. -/
theorem gm_regC6_prob {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (h35 : CONFLem3_5At γ D c p) {V : Set ℂ} {ℓ : ℝ} (hV : Bornology.IsBounded V) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ R : RegPar,
      R.ξ = xiGamma γ → R.c = c → R.p = p → R.V = V → R.ℓ = ℓ →
      RegCondAt P (regC6 D P h R) q a₀ := by
  obtain ⟨ρ₀, hρ₀⟩ := hV.subset_ball (0 : ℂ)
  obtain ⟨C₀, ε₀, hC₀, hε₀, H⟩ := h35 (Metric.closedBall 0 (ρ₀ + 4 * ℓ))
    (isCompact_closedBall _ _)
  intro q hq
  have hq' : 0 < 1 - q := by linarith
  refine ⟨min (ε₀ / 2) ((1 - q) / (2 * C₀)), lt_min (by linarith) (by positivity), ?_⟩
  intro Ω _ P _ h hh R hξ hc hp hRV hRℓ
  subst hRV hRℓ
  rintro a ⟨ha0, ha⟩ 𝕣 h𝕣
  have haε : a < ε₀ := lt_of_le_of_lt (ha.trans (min_le_left _ _)) (by linarith)
  have haq : 2 * C₀ * a ≤ 1 - q := by
    have := ha.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set B : ℕ → Set Ω := fun n => {ω | ∃ z ∈ gridPts ((2 : ℝ)⁻¹ ^ n * 𝕣 / 4) ∩
      Metric.thickening ((2 : ℝ)⁻¹ ^ n * 𝕣)
        ((fun x : ℂ => (𝕣 : ℂ) * x + 0) '' Metric.closedBall 0 (ρ₀ + 4 * R.ℓ)),
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ (1 / 2 : ℝ) * 𝕣) <
        confRho (xiGamma γ) c D P h p ((2 : ℝ)⁻¹ ^ n * 𝕣) z (confN p ((2 : ℝ)⁻¹ ^ n)) ω}
    with hB
  have hsub : (regC6 D P h R 𝕣 a)ᶜ ⊆ ⋃ n, ⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n := by
    intro ω hω
    simp only [regC6, hξ, hc, hp, mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨n, hn, z, hz, hlt⟩ := hω
    refine mem_iUnion₂.2 ⟨n, hn, z, ⟨hz.1, ?_⟩, hlt⟩
    exact Metric.self_subset_thickening (by positivity) _ (gm_regRegion_subset h𝕣 hρ₀ hz.2)
  have hterm : ∀ n, P (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) ≤
      ENNReal.ofReal (C₀ * a * (2 : ℝ)⁻¹ ^ n) := by
    intro n
    by_cases hn : (2 : ℝ)⁻¹ ^ n ≤ a
    · refine (measure_mono (iUnion_subset fun _ => subset_rfl)).trans ?_
      have hpos : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
      refine (H P h hh 0 𝕣 h𝕣 _ ⟨hpos, lt_of_le_of_lt hn haε⟩).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have : ((2 : ℝ)⁻¹ ^ n) ^ 2 ≤ a * (2 : ℝ)⁻¹ ^ n := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hn hpos.le
      nlinarith
    · have : (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) = ∅ :=
        eq_empty_of_subset_empty (iUnion_subset fun h' => (hn h').elim)
      rw [this, measure_empty]; exact bot_le
  have hsum : HasSum (fun n : ℕ => C₀ * a * (2 : ℝ)⁻¹ ^ n) (C₀ * a * 2) := by
    have := (hasSum_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
      (C₀ * a)
    have e : (1 - (2 : ℝ)⁻¹)⁻¹ = 2 := by norm_num
    rwa [e] at this
  calc P (regC6 D P h R 𝕣 a)ᶜ ≤ P (⋃ n, ⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) := measure_mono hsub
    _ ≤ ∑' n, P (⋃ (_ : (2 : ℝ)⁻¹ ^ n ≤ a), B n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (C₀ * a * (2 : ℝ)⁻¹ ^ n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C₀ * a * 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq]
    _ ≤ ENNReal.ofReal (1 - q) := ENNReal.ofReal_le_ofReal (by linarith)

end LQGMetric.GM
