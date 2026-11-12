/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53K2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53K1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117B
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3EtaB1

/-!
# The proxy mass map in the similarity comparison (P2-DZZ53K, packet P-131C, interface)

The proxy `ν_B` of S5L53K1 is a mass map on rational balls (DZZ's `M̃_{γ,s',η}` is defined set
by set), not a measure. The scaling coupling of DZZ (eq-scaling-invariance-approximate), l. 2474,
with the mass comparison l. 2501–2503, is in the library for measures (`chaos_sim_ball_le`,
S5D117B; `lgd_sim_upper`, S5D125C). This file adapts the upper half to a mass map on the small
side `θK`, the side whose LGD is bounded:

* `exists_rat_radii_lt`: `exists_rat_radii` (LGDMeas) with strict `q_i < ρ_i` (same proof);
* **`lgdRat_le_lgdDZZ_of_lt`**: if `m(x, q) ≤ μ(B(x, r))` whenever `q < r`, then
  `lgdRat m δ {u} {v} ≤ lgdDZZ μ δ u v`;
* **`lgdRat_sim_upper`**: the mass-map form of `lgd_sim_upper` (proof copied and modified): if
  `M₂` is the limit of `∫_{B} e^{F₂ n}` on the rational balls `B ⊆ θK` and
  `F₂ n ∘ θ ≤ c + (γζ₁ − γ²/2 V₁)(s₁ n)` on `K`, `μ₁` the chaos limit along `s₁`, then
  `D^{θK}_{‖a‖δe^{c/2}}[M₂](θx, θy) ≤ D^K_δ[μ₁](x, y)` (walls `wallMass`, `dzzWall`);
* **`ae_dzzMuIn_ball_le_proxyMass`**: the limit step of R2 (DZZ (eq-M-A-upper-bound-bis), l. 2455,
  "similar to (eq-PCAF-approx)"): a.s., for every rational ball `B ⊆ (0,1)² ∩ S` and `c`, if
  eventually `e^{γh̃_{2^{-n}} − γ²/2 Var} ≤ c e^{γη^{s'}_{2^{-n}} − γ²/2 Var}` a.e. on `B`, then
  `μIn(B) ≤ ν_B(B)` with `ν_B = proxyMass W γ m c S` (from `wickQArea_le_of_open`, S3EtaB1). This
  replaces the exact identity `dzzMuIn_eq_withDensity_fineChaos` of DEC-131 §3;
* `ae_tendsto_fineMass_exp`: `fineMass` satisfies the hypothesis on `M₂` with
  `F₂ n z = γ η^{s'}_{2^{-n}}(z) − γ²/2 Var η^{s'}_{2^{-n}}(z)` (versions `etaVer`), a.s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- `exists_rat_radii` (LGDMeas) with strict inequalities `q_i < ρ_i` (same proof). -/
lemma exists_rat_radii_lt {x y : ℂ} (P : Path x y) {N : ℕ} (c : Fin N → ℂ) (ρ : Fin N → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hcov : ∀ t, ∃ i, P t ∈ Metric.ball (c i) (ρ i)) :
    ∃ q : Fin N → ℚ, (∀ i, 0 < q i ∧ (q i : ℝ) < ρ i) ∧
      ∀ t, ∃ i, P t ∈ Metric.ball (c i) (q i) := by
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; have := n.cast_nonneg (α := ℝ); linarith
    simp only [hr]; linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hr]; linarith
  set U : ℕ → Set ℂ := fun n => ⋃ i, Metric.ball (c i) (ρ i * r n) with hU
  obtain ⟨n, hn⟩ := (isCompact_range P.continuous).elim_directed_cover U
    (fun n => isOpen_iUnion fun i => Metric.isOpen_ball) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨i, hi⟩ := hcov t
      rw [Metric.mem_ball] at hi
      have hpos : 0 < 1 - dist (P t) (c i) / ρ i := by
        rw [sub_pos, div_lt_one (hρ i)]; exact hi
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨i, Metric.mem_ball.2 ?_⟩⟩
      have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h3 : dist (P t) (c i) / ρ i < r n := by simp only [hr]; linarith
      rwa [div_lt_iff₀ (hρ i), mul_comm] at h3)
    (by
      intro a b
      refine ⟨max a b, ?_, ?_⟩ <;>
      · refine iUnion_mono fun i => Metric.ball_subset_ball ?_
        exact mul_le_mul_of_nonneg_left (shrinkFac_mono (by omega)) (hρ i).le)
  have hq : ∀ i, ∃ q : ℚ, ρ i * r n < q ∧ (q : ℝ) < ρ i := fun i =>
    exists_rat_btwn (by nlinarith [hρ i, hr1 n])
  choose q hq1 hq2 using hq
  refine ⟨q, fun i => ⟨?_, hq2 i⟩, fun t => ?_⟩
  · have : (0 : ℝ) < q i := lt_trans (mul_pos (hρ i) (hr0 n)) (hq1 i)
    exact_mod_cast this
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hn ⟨t, rfl⟩)
    exact ⟨i, Metric.ball_subset_ball (hq1 i).le hi⟩

/-- **a mass map below the masses of slightly larger balls has smaller LGD** -/
theorem lgdRat_le_lgdDZZ_of_lt {m : ℚ × ℚ → ℚ → ℝ≥0∞} {μ : Measure ℂ}
    (h : ∀ (x : ℚ × ℚ) (q : ℚ) (r : ℝ), 0 < q → (q : ℝ) < r → m x q ≤ μ (ball (ratPt x) r))
    (δ : ℝ) (u v : ℂ) : lgdRat m δ {u} {v} ≤ lgdDZZ μ δ u v := by
  unfold lgdRat lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  obtain ⟨q, hq, hcov⟩ := exists_rat_radii_lt P (fun i => ratPt (c i)) ρ (fun i => (h1 i).1) h2
  refine iInf₂_le N ⟨c, q, ⟨u, mem_singleton u, v, mem_singleton v, P, hcov⟩,
    fun i => ⟨(hq i).1, ?_⟩⟩
  exact (h (c i) (q i) (ρ i) (hq i).1 (hq i).2).trans (h1 i).2

variable {γ c : ℝ} {ζ₁ V₁ : ℝ → ℂ → ℝ} {s₁ : ℕ → ℝ} {μ₁ : Measure ℂ}

/-- **The upper half of the similarity comparison with a mass map on the small side** (DZZ
(eq-scaling-invariance-approximate) l. 2474 and the mass comparison l. 2501–2503; `lgd_sim_upper`,
S5D125C, with `μ₂` replaced by the mass map `M₂`, proof copied and modified). -/
theorem lgdRat_sim_upper (h₁ : IsChaosLimit γ ζ₁ V₁ s₁ μ₁) {F₂ : ℕ → ℂ → ℝ}
    {M₂ : ℚ × ℚ → ℚ → ℝ≥0∞} {a : ℂ} (ha : a ≠ 0) (b : ℂ) {K : Set ℂ} (hK : IsClosed K)
    (hKV : K ⊆ dzzV)
    (h₂ : ∀ (x : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt x) q ⊆ simMap a b '' K →
      Tendsto (fun n => ∫⁻ z in ball (ratPt x) q, ENNReal.ofReal (Real.exp (F₂ n z))) atTop
        (𝓝 (M₂ x q)))
    (hpt : ∀ n : ℕ, ∀ z ∈ K,
      F₂ n (simMap a b z) ≤ c + (γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z))
    (δ : ℝ) (x y : ℂ) :
    lgdRat (wallMass (simMap a b '' K) M₂) (‖a‖ * δ * Real.exp (c / 2))
        {simMap a b x} {simMap a b y} ≤ lgdDZZ (dzzWall K (dzzWall dzzV μ₁)) δ x y := by
  set θ := simMap a b with hθ
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  set μA := dzzWall K (dzzWall dzzV μ₁) with hμA
  set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (‖a‖ ^ 2) with hC
  have hJ0 : ENNReal.ofReal (‖a‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have he0 : ENNReal.ofReal (Real.exp c) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos c
  have hC0 : C ≠ 0 := mul_ne_zero he0 hJ0
  have hCt : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  set ν₂ : Measure ℂ := (C • μA).map θ with hν₂
  have hθm : Measurable θ := (continuous_simMap a b).measurable
  have hpre : ∀ p : ℂ, ∃ p₀ : ℂ, ∀ r : ℝ, θ ⁻¹' ball p r = ball p₀ (r / ‖a‖) := by
    intro p
    obtain ⟨p₀, rfl⟩ := simMap_surjective ha b p
    refine ⟨p₀, fun r => ?_⟩
    have := simMap_preimage_ball ha b p₀ (r / ‖a‖)
    rwa [mul_div_cancel₀ _ hna.ne'] at this
  have hθK : IsClosed (θ '' K) := isClosed_simMap_image ha b hK
  have hμ₁A : μ₁ ≤ μA := (le_dzzWall dzzV μ₁).trans (le_dzzWall K _)
  -- the mass comparison
  have hmass : ∀ (x' : ℚ × ℚ) (q' : ℚ) (r' : ℝ), 0 < q' → (q' : ℝ) < r' →
      wallMass (θ '' K) M₂ x' q' ≤ ν₂ (ball (ratPt x') r') := by
    intro x' q' r' hq' hqr
    have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
    rw [hν₂, Measure.map_apply hθm measurableSet_ball, Measure.smul_apply, smul_eq_mul]
    obtain ⟨p₀, hp₀⟩ := hpre (ratPt x')
    have himg : θ '' (θ ⁻¹' ball (ratPt x') q') = ball (ratPt x') q' :=
      image_preimage_eq _ (simMap_surjective ha b)
    by_cases hsub : ball (ratPt x') q' ⊆ θ '' K
    · have hSK : θ ⁻¹' ball (ratPt x') q' ⊆ K := by
        intro z hz
        obtain ⟨w, hw, hwz⟩ := hsub hz
        rwa [← simMap_injective ha b hwz]
      have hw0 : wallMass (θ '' K) M₂ x' q' = M₂ x' q' := by
        unfold wallMass
        rw [show ball (ratPt x') q' ∩ (θ '' K)ᶜ = ∅ from
          eq_empty_of_forall_notMem fun z hz => hz.2 (hsub hz.1), measure_empty, mul_zero,
          add_zero]
      rw [hw0]
      obtain ⟨x'', q'', hq''0, hsub1, hsub2⟩ := exists_ratBall_between (w := p₀)
        (show (0 : ℝ) ≤ q' / ‖a‖ by positivity) (div_lt_div_of_pos_right hqr hna)
      rw [hp₀] at hSK
      have hSm : MeasurableSet (θ ⁻¹' ball (ratPt x') q') :=
        measurableSet_ball.preimage hθm
      refine (le_of_tendsto_of_tendsto' (h₂ x' q' hq' hsub)
        (ENNReal.Tendsto.const_mul (h₁ x'' q'' (by exact_mod_cast hq''0)) (Or.inr hCt))
        fun n => ?_).trans (mul_le_mul_of_nonneg_left ((hμ₁A _).trans (measure_mono ?_)) zero_le)
      · set G₁ : ℂ → ℝ≥0∞ := fun z =>
          ENNReal.ofReal (Real.exp (γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z))
        set G₂ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (F₂ n z))
        calc ∫⁻ z in ball (ratPt x') q', G₂ z
            = ∫⁻ z in θ '' (θ ⁻¹' ball (ratPt x') q'), G₂ z := by rw [himg]
          _ = ENNReal.ofReal (‖a‖ ^ 2) * ∫⁻ z in θ ⁻¹' ball (ratPt x') q', G₂ (θ z) :=
              lintegral_simMap_image ha b hSm _
          _ ≤ ENNReal.ofReal (‖a‖ ^ 2) *
                ∫⁻ z in θ ⁻¹' ball (ratPt x') q', ENNReal.ofReal (Real.exp c) * G₁ z := by
              refine mul_le_mul_of_nonneg_left (setLIntegral_mono' hSm fun z hz => ?_) zero_le
              simp only [G₁, G₂]
              rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, ← Real.exp_add]
              exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
                (hpt n z (hSK (by rw [← hp₀]; exact hz))))
          _ = C * ∫⁻ z in θ ⁻¹' ball (ratPt x') q', G₁ z := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hC]; ring
          _ ≤ C * ∫⁻ z in ball (ratPt x'') q'' ∩ dzzV, G₁ z := by
              refine mul_le_mul_of_nonneg_left (lintegral_mono_set fun z hz => ⟨?_, ?_⟩) zero_le
              · rw [hp₀] at hz; exact hsub1 hz
              · exact hKV (hSK (by rw [← hp₀]; exact hz))
      · rw [hp₀]; exact hsub2
    · have hw0 : wallMass (θ '' K) M₂ x' q' = ⊤ := by
        unfold wallMass
        obtain ⟨z, hz, hzK⟩ := not_subset.1 hsub
        have hpos : 0 < volume (ball (ratPt x') q' ∩ (θ '' K)ᶜ) :=
          (isOpen_ball.inter hθK.isOpen_compl).measure_pos volume ⟨z, hz, hzK⟩
        rw [ENNReal.top_mul hpos.ne', add_top]
      rw [hw0]
      have hnK : ¬ θ ⁻¹' ball (ratPt x') r' ⊆ K := by
        intro h
        apply hsub
        rw [← himg]
        exact image_mono ((preimage_mono (ball_subset_ball hqr.le)).trans h)
      have hopen : IsOpen (θ ⁻¹' ball (ratPt x') r') := isOpen_ball.preimage (continuous_simMap a b)
      rw [hμA, dzzWall_eq_top_of_not_subset hK _ hopen hnK, ENNReal.mul_top hC0]
  -- the LGD comparisons
  have h1 := lgdRat_le_lgdDZZ_of_lt hmass (‖a‖ * δ * Real.exp (c / 2)) (θ x) (θ y)
  have h2 : lgdDZZ ν₂ (‖a‖ * δ * Real.exp (c / 2)) (θ x) (θ y) =
      lgdDZZ (C • μA) (‖a‖ * δ * Real.exp (c / 2)) x y :=
    lgdDZZ_map_similarity ha b _ _ x y
  set L := Real.log ‖a‖
  have hL : Real.exp L = ‖a‖ := Real.exp_log hna
  have e4 : ENNReal.ofReal (Real.exp (c + 2 * L)) = C := by
    rw [hC, show c + 2 * L = c + L + L by ring, Real.exp_add, Real.exp_add, hL, mul_assoc, ← sq,
      ENNReal.ofReal_mul (Real.exp_pos c).le]
  have h3 := lgdDZZ_le_of_ball_le (μ := C • μA) (ν := μA) (c := c + 2 * L)
    (fun x r => by rw [e4, Measure.smul_apply, smul_eq_mul]) (‖a‖ * δ * Real.exp (c / 2)) x y
  have f2 : ‖a‖ * δ * Real.exp (c / 2) * Real.exp (-(c + 2 * L) / 2) = δ := by
    rw [show -(c + 2 * L) / 2 = -L + -(c / 2) by ring, Real.exp_add, Real.exp_neg, Real.exp_neg,
      hL, show ‖a‖ * δ * Real.exp (c / 2) * (‖a‖⁻¹ * (Real.exp (c / 2))⁻¹) =
        (‖a‖ * ‖a‖⁻¹) * δ * (Real.exp (c / 2) * (Real.exp (c / 2))⁻¹) by ring,
      mul_inv_cancel₀ hna.ne', mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul, mul_one]
  rw [f2] at h3
  exact h1.trans (h2.le.trans h3)

/-- **`fineMass` is the limit of its approximations** in the form used by `lgdRat_sim_upper`:
a.s., for all rational balls, `∫_B e^{γ η^{s'}_{2^{-n}} − γ²/2 Var} → M̃_{γ,s',η}(B)`. -/
theorem ae_tendsto_fineMass_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (γ : ℝ) (m : ℕ) :
    ∀ᵐ ω ∂P, ∀ (x : ℚ × ℚ) (q : ℚ), Tendsto (fun n => ∫⁻ z in ball (ratPt x) q,
      ENNReal.ofReal (Real.exp (γ * etaVer W ((2 : ℝ)⁻¹ ^ m) n z ω -
        γ ^ 2 / 2 * etaBVar ((2 : ℝ)⁻¹ ^ m) n z))) atTop (𝓝 (fineMass W γ m ω x q)) :=
  ae_tendsto_fineMass hW γ m

/-- **R2, the limit step** (DZZ (eq-M-A-upper-bound-bis), l. 2455): a.s., for every rational ball
`B ⊆ (0,1)² ∩ S` and every `c`, the eventual a.e. density comparison on `B` gives
`μIn(B) ≤ c · M̃_{γ,s',η}(B) = ν_B(B)` (`wickQArea_le_of_open`, S3EtaB1). -/
theorem ae_dzzMuIn_ball_le_proxyMass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (m : ℕ)
    (S : Set ℂ) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (x : ℚ × ℚ) (q : ℚ), ball (ratPt x) q ⊆ openSquare →
      ball (ratPt x) q ⊆ S →
      (∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict (ball (ratPt x) q)),
        wickDensC hW γ n z ω ≤ ENNReal.ofReal c * etaDens W γ ((2 : ℝ)⁻¹ ^ m) n z ω) →
      dzzMuIn γ W ω (ball (ratPt x) q) ≤ proxyMass W γ m (ENNReal.ofReal c) S ω x q := by
  filter_upwards [ae_isVagueLimitOn_wickMeasC hW hγ hγ2, ae_tendsto_fineMass hW γ m]
    with ω hv ht c x q hBV hBS hd
  rw [proxyMass_of_subset γ m _ ω hBS, dzzMuIn,
    dzzWall_eq_of_subset _ (hBV.trans openSquare_subset_dzzV) measurableSet_ball]
  exact wickQArea_le_of_open hW hv isOpen_ball hBV hd (ht x q)

end DZZ
end LQGMetric
