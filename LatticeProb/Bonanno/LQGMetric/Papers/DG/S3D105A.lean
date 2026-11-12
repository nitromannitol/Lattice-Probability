/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12NegMain
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12Chain
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuL8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Lemma 3.8, lower half, for the LQG measure of the zero-boundary GFF on `𝕍` (D105)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.8 (`lem-max-ball-radius`,
DG:1112–1123): "for each `β̲ ∈ (0, 2/(2+γ)²)` … with polynomially high probability as `ε → 0`,
`inf_{z∈𝕊} μ_h(B_{ε^β̲}(z)) ≥ ε`"; DG cite GMS (arXiv:1807.07511) Lemma 2.5 for it.

Here it is derived from the project's sharp negative moments instead (decision D105): DZZ
(arXiv:1807.00422, (eq-LQG-negative-moment), l. 684–688) give, for `p < 0` and a ball
`B(w,s) ⊆ 𝕍`, `E μ_h(B(w,s))^p ≤ C s^{−A}` with **`A = p(p−1)γ²/2 − 2p = −f(p)`**, `f` DG's
moment exponent `f(p) = (2 + γ²/2)p − γ²p²/2` (DG:1127). The project's
`DZZ.negU_ball_neg_moment` hides `A` behind an existential; `negU_ball_neg_moment_exp` is the
same proof with the exponent explicit. Then (DG's own scheme for the upper half, DG:1131–1137,
applied to the lower tail):

* Markov: `P[μ(B(w,s)) ≤ t] ≤ C t^q s^{−A}` for `q = −p > 0` (`negU_ball_lower_tail_exp`);
* union bound over the grid `(ε^β/4) ℤ²` (`DZZ.prob_grid_light_le`), and every ball `B(z, ε^β)`
  with `z` in the target set contains a grid ball (`DZZ.large_ball_heavy_of_grid`):
  `dgL38Lower_of_tail`;
* the exponent `q − β(A + 2)` is maximized at `q = 2/γ`, where it equals
  `(2/γ)(1 − β(2+γ)²/2) > 0` exactly when `β < 2/(2+γ)²` (`dgL38_exponent`): DG's threshold.

Main result: `dgL38Lower_qArea`: `DGL38Lower P (μ_h) (closedBall u R) β` for
`closedBall u (2R) ⊆ 𝕍` and `0 < β < 2/(2+γ)²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace DG

open DZZ DGMC DGMC.Neg3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- `DZZ.negU_ball_neg_moment` with the exponent `A = p(p−1)γ²/2 − 2p` explicit (same proof). -/
theorem negU_ball_neg_moment_exp (hX : IsZeroBoundaryGFFOn openSquare X P) {γ p : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p < 0) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ openSquare) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ w ∈ K, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      closedBall w s ⊆ openSquare ∧
      ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (ball w s) ^ p ∂P ≤
        ENNReal.ofReal (C * s ^ (-(p * (p - 1) * γ ^ 2 / 2 - 2 * p))) := by
  classical
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  set A := p * (p - 1) * γ ^ 2 / 2 - 2 * p with hA
  rcases K.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · exact ⟨0, 1, one_pos, fun w hw => absurd hw (notMem_empty w)⟩
  obtain ⟨δ, hδ, hKδ⟩ := exists_sqIn_of_isCompact hK hKU
  set K' := sqIn (δ / 2)
  have hK'U : K' ⊆ openSquare := sqIn_subset_openSquare (by positivity)
  have hK'c : Convex ℝ K' := convex_sqIn _
  have hK'k : IsCompact K' := isCompact_sqIn (by positivity)
  have hball : ∀ w ∈ K, closedBall w (δ / 2) ⊆ K' := fun w hw =>
    negU_closedBall_subset_sqIn_half (hKδ hw)
  obtain ⟨cK, hcK⟩ := circleCov_two_sided hK'U hK'c hK'k
  set cK' := max cK 0
  have hK' : ∀ {z w : ℂ} {r : ℝ}, 0 < r → closedBall z r ⊆ K' → closedBall w r ⊆ K' →
      |cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w r); P] +
        Real.log (max r ‖z - w‖)| ≤ cK' := fun hr h1 h2 =>
    (hcK hX hr h1 h2).trans (le_max_left _ _)
  obtain ⟨m₁, hm₁⟩ := exists_radius_le (show 0 < δ / 2 / 2 by positivity)
  have hQ₁ := negU_hQ_center w₀ (hm₁ m₁ le_rfl)
  have hQ₁' : ∀ w ∈ unitSq, closedBall ((w₀ - radius m₁ • (⟨1 / 2, 1 / 2⟩ : ℂ)) +
      radius m₁ • w) (2 * radius m₁) ⊆ K' := fun w hw =>
    (hQ₁ w hw).trans ((closedBall_subset_closedBall (by linarith)).trans (hball w₀ hw₀))
  obtain ⟨c₁, hc₁⟩ := logCorr_bZ hX γ hK'U hK'c hK'k hQ₁'
  have hβ4 : γ ^ 2 < 4 := by nlinarith
  obtain ⟨C₁, hC₁⟩ := hc₁.exists_uniform_neg_moment (by positivity) hβ4 hp
  have hC₁0 : 0 ≤ C₁ := (integral_nonneg fun ω =>
    Real.rpow_nonneg (gM_pos _ _ (grid_nonempty' 0) ω).le _).trans (hC₁ 0 0 le_rfl)
  refine ⟨Real.exp (-(γ ^ 2 * cK' / 2)) ^ p * Real.exp (p * (p - 1) * (2 * γ ^ 2 * cK') / 2) *
      Real.exp (p * (p - 1) * (γ ^ 2 * cK' + c₁) / 2) * C₁ * 16 ^ A, min (δ / 2) 1,
      lt_min (by positivity) one_pos, fun w hw s hs hsr => ?_⟩
  have hs1 : s ≤ 1 := hsr.trans (min_le_right _ _)
  have hsδ : s ≤ δ / 2 := hsr.trans (min_le_left _ _)
  have hcl : closedBall w s ⊆ K' := (closedBall_subset_closedBall hsδ).trans (hball w hw)
  refine ⟨hcl.trans hK'U, ?_⟩
  have hex : ∃ m : ℕ, 4 * radius m ≤ s / 2 := by
    obtain ⟨k₀, hk₀⟩ := exists_radius_le (show 0 < s / 2 by positivity)
    exact ⟨k₀, hk₀ k₀ le_rfl⟩
  set m := Nat.find hex
  have hma : 4 * radius m ≤ s / 2 := Nat.find_spec hex
  have hlow : s / 16 ≤ radius m := by
    rcases Nat.eq_zero_or_eq_succ_pred m with h0 | h1
    · have e : radius m = 1 := by simp [radius, h0]
      rw [e] at hma; linarith
    · have hlt : ¬ 4 * radius (m - 1) ≤ s / 2 := Nat.find_min hex (by omega)
      push Not at hlt
      have e : radius m = radius (m - 1) * (2 : ℝ)⁻¹ := by
        rw [h1]; simp [radius, pow_succ]
      rw [e]; linarith
  have ha1 : radius m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine (negU_lintegral_ball_rpow_le hX hγ hγ2 hs (ball_subset_closedBall.trans
    (hcl.trans hK'U)) hp hma (fun z₀ hQ k j v hkj hv =>
      negU_integral_nM_rpow_le hX hp.le hK'U (le_max_right _ _) hK' hc₁ hC₁
        (fun w' hw' => (hQ w' hw').trans ((closedBall_subset_closedBall (by linarith)).trans hcl))
        k j hkj hv)).trans (ENNReal.ofReal_le_ofReal ?_)
  exact negU_real_bound (radius_pos m) ha1 hs hlow hp hA hC₁0

/-- **Sharp small-ball lower tail** (Markov on `negU_ball_neg_moment_exp` with `p = −q`):
`P[μ_h(B(w,s)) ≤ t] ≤ C s^{−(q(q+1)γ²/2 + 2q)} t^q`. -/
theorem negU_ball_lower_tail_exp (hX : IsZeroBoundaryGFFOn openSquare X P) {γ q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hq : 0 < q) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ openSquare) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ w ∈ K, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      closedBall w s ⊆ openSquare ∧ ∀ t : ℝ, 0 < t →
      P {ω | qAreaMeasureOn γ (X ω) openSquare (ball w s) ≤ ENNReal.ofReal t} ≤
        ENNReal.ofReal (C * t ^ q * s ^ (-(q * (q + 1) * γ ^ 2 / 2 + 2 * q))) := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  obtain ⟨C, r₀, hr₀, hb⟩ :=
    negU_ball_neg_moment_exp (P := P) hX hγ hγ2 (p := -q) (by linarith) hK hKU
  refine ⟨C, r₀, hr₀, fun w hw s hs hsr => ?_⟩
  obtain ⟨hcl, hmom⟩ := hb w hw s hs hsr
  refine ⟨hcl, fun t ht => ?_⟩
  have e : -(-q * (-q - 1) * γ ^ 2 / 2 - 2 * -q) = -(q * (q + 1) * γ ^ 2 / 2 + 2 * q) := by ring
  rw [e] at hmom
  set ε : ℝ≥0∞ := ENNReal.ofReal t ^ (-q)
  have hε : ε = (ENNReal.ofReal t ^ q)⁻¹ := ENNReal.rpow_neg _ _
  have hε0 : ε ≠ 0 := by
    rw [hε]; exact ENNReal.inv_ne_zero.2 (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
  have hεt : ε ≠ ⊤ := by
    rw [hε]
    exact ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 ht) ENNReal.ofReal_ne_top).ne'
  have hsub : {ω | qAreaMeasureOn γ (X ω) openSquare (ball w s) ≤ ENNReal.ofReal t} ⊆
      {ω | ε ≤ qAreaMeasureOn γ (X ω) openSquare (ball w s) ^ (-q)} := fun ω h =>
    ennrpow_anti (by linarith) h
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
    ((DG.aemeasurable_qAreaMeasureOn_ball hX hγ hγ2 hcl).pow_const _) hε0 hεt).trans ?_)
  rw [hε, ENNReal.div_eq_inv_mul, inv_inv, mul_comm]
  refine (mul_le_mul_left hmom _).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_pos ht, ← ENNReal.ofReal_mul' (Real.rpow_nonneg ht.le _)]
  congr 1; ring

/-- the exponent of DG Lemma 3.8 (lower half) at `q = 2/γ`:
`q − β (q(q+1)γ²/2 + 2q + 2) = (2/γ)(1 − β(2+γ)²/2) > 0` iff `β < 2/(2+γ)²`. -/
lemma dgL38_exponent {γ β : ℝ} (hγ : 0 < γ) (hβ : β < 2 / (2 + γ) ^ 2) :
    0 < 2 / γ - β * ((2 / γ) * (2 / γ + 1) * γ ^ 2 / 2 + 2 * (2 / γ) + 2) := by
  have e : (2 / γ) * (2 / γ + 1) * γ ^ 2 / 2 + 2 * (2 / γ) + 2 = (2 + γ) ^ 2 / γ := by
    field_simp; ring
  rw [e]
  have h2 : β * (2 + γ) ^ 2 < 2 := by
    rwa [lt_div_iff₀ (by positivity)] at hβ
  have : 2 / γ - β * ((2 + γ) ^ 2 / γ) = (2 - β * (2 + γ) ^ 2) / γ := by ring
  rw [this]
  exact div_pos (by linarith) hγ

/-- rpow bookkeeping for the union bound: with `s = ε^β/4`,
`c₀²/s² · (C ε^q s^{−A}) = c₀² C 4^{A+2} ε^{q − β(A+2)}`. -/
lemma dgL38_rpow_alg {ε β A q c₀ C : ℝ} (hε : 0 < ε) :
    c₀ ^ 2 / (ε ^ β / 4) ^ 2 * (C * ε ^ q * (ε ^ β / 4) ^ (-A)) =
      c₀ ^ 2 * C * (4 : ℝ) ^ (A + 2) * ε ^ (q - β * (A + 2)) := by
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have h4 : (0 : ℝ) < 4 := by norm_num
  rw [Real.div_rpow hεβ.le h4.le, Real.rpow_neg hεβ.le, Real.rpow_neg h4.le,
    show q - β * (A + 2) = q + β * (-A) + β * (-2) by ring, Real.rpow_add hε, Real.rpow_add hε,
    Real.rpow_mul hε.le, Real.rpow_mul hε.le, Real.rpow_neg hεβ.le, Real.rpow_neg hεβ.le,
    Real.rpow_add h4, Real.rpow_two, Real.rpow_two]
  field_simp

/-- **DG Lemma 3.8, lower half, from a sharp small-ball lower tail** (grid union bound,
DG:1137 scheme): if `P[μ(B(w,s)) ≤ t] ≤ C t^q s^{−A}` for `w ∈ B̄(u, 2R)`, `s ≤ r₀`, and
`q − β(A+2) > 0`, then with polynomially high probability every `B(z, ε^β)`, `z ∈ B̄(u,R)`, has
`μ`-mass `≥ ε`. -/
theorem dgL38Lower_of_tail {μ : Ω → Measure ℂ} {u : ℂ} {R r₀ C q A β : ℝ} (hR : 0 < R)
    (hr₀ : 0 < r₀) (hβ : 0 < β) (hexp : 0 < q - β * (A + 2))
    (htail : ∀ w ∈ closedBall u (2 * R), ∀ s : ℝ, 0 < s → s ≤ r₀ → ∀ t : ℝ, 0 < t →
      P {ω | μ ω (ball w s) ≤ ENNReal.ofReal t} ≤ ENNReal.ofReal (C * t ^ q * s ^ (-A))) :
    DGL38Lower P μ (closedBall u R) β := by
  set m : ℝ := min 4 (min (4 * r₀) (4 * R / 3)) with hm
  have hm0 : 0 < m := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  set c₀ : ℝ := 2 * (‖u‖ + R) + 9
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨q - β * (A + 2), c₀ ^ 2 * max C 0 * (4 : ℝ) ^ (A + 2), m ^ β⁻¹, hexp,
    Real.rpow_pos_of_pos hm0 _, fun ε hε hεm => ?_⟩
  -- the scale `s = ε^β/4`
  have hεβm : ε ^ β < m := by
    have := Real.rpow_lt_rpow hε.le hεm hβ
    rwa [Real.rpow_inv_rpow hm0.le hβ.ne'] at this
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  set s : ℝ := ε ^ β / 4 with hs_def
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    have : ε ^ β < 4 := hεβm.trans_le (min_le_left _ _)
    rw [hs_def]; linarith
  have hsr : s ≤ r₀ := by
    have : ε ^ β < 4 * r₀ := hεβm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rw [hs_def]; linarith
  have hsR : R + 3 * s ≤ 2 * R := by
    have : ε ^ β < 4 * R / 3 := hεβm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [hs_def]; linarith
  -- the bad event is contained in the grid event
  have hsub : {ω | ¬ ∀ z ∈ closedBall u R, ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ β))} ⊆
      {ω | ∃ i j : ℤ, ‖(⟨i * s, j * s⟩ : ℂ) - u‖ ≤ R + 3 * s ∧
        μ ω (ball ⟨i * s, j * s⟩ s) ≤ ENNReal.ofReal ε} := by
    intro ω hω
    by_contra hcon
    apply hω
    intro z hz
    have key := large_ball_heavy_of_grid (μ := μ ω) (δ := Real.sqrt ε) hs
      (fun i j hij => by
        rw [Real.sq_sqrt hε.le]
        exact lt_of_not_ge fun hle => hcon ⟨i, j, hij, hle⟩)
      z (ε ^ β) (by rw [hs_def]; linarith) ⟨z, mem_ball_self hεβ, hz⟩
    rw [Real.sq_sqrt hε.le] at key
    exact key.le
  refine (measure_mono hsub).trans ?_
  have hgrid := prob_grid_light_le (P := P) (μ := μ) (u := u) (R := R) (s := s) (t := ε)
    (p := q) (A := A) (C := C) (r₀ := r₀) hR.le hs hsr hε
    (fun w hw s' hs' hs'r t ht =>
      htail w (closedBall_subset_closedBall hsR hw) s' hs' hs'r t ht)
  refine hgrid.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the count
  set x : ℝ := (‖u‖ + (R + 3 * s)) / s with hx
  have hx0 : 0 < x := by positivity
  have hceil : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hceil0 : (0 : ℝ) ≤ 2 * (⌈x⌉ : ℝ) + 1 := by
    have : (0 : ℝ) < (⌈x⌉ : ℝ) := by exact_mod_cast (Int.ceil_pos.2 hx0)
    linarith
  have hN : 2 * (⌈x⌉ : ℝ) + 1 ≤ c₀ / s := by
    have e : c₀ / s = 2 * x + 3 + (2 * (‖u‖ + R) + 9 - (2 * (‖u‖ + R) + 9 * s)) / s := by
      rw [hx]; field_simp; ring
    have hnn : 0 ≤ (2 * (‖u‖ + R) + 9 - (2 * (‖u‖ + R) + 9 * s)) / s :=
      div_nonneg (by linarith) hs.le
    rw [e]; linarith
  have hN2 : (2 * (⌈x⌉ : ℝ) + 1) ^ 2 ≤ c₀ ^ 2 / s ^ 2 := by
    rw [← div_pow]; exact pow_le_pow_left₀ hceil0 hN 2
  have hT : C * ε ^ q * s ^ (-A) ≤ max C 0 * ε ^ q * s ^ (-A) := by
    gcongr; exact le_max_left _ _
  have hT0 : 0 ≤ max C 0 * ε ^ q * s ^ (-A) := by positivity
  calc (2 * (⌈x⌉ : ℝ) + 1) ^ 2 * (C * ε ^ q * s ^ (-A))
      ≤ c₀ ^ 2 / s ^ 2 * (max C 0 * ε ^ q * s ^ (-A)) := by
        rcases le_or_gt 0 (C * ε ^ q * s ^ (-A)) with h0 | h0
        · exact mul_le_mul hN2 hT h0 (by positivity)
        · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le).trans (by positivity)
    _ = c₀ ^ 2 * max C 0 * (4 : ℝ) ^ (A + 2) * ε ^ (q - β * (A + 2)) := dgL38_rpow_alg hε

end DG
end LQGMetric
