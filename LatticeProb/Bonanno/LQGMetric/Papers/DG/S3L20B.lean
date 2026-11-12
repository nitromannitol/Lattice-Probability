/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L20B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L20
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105B
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105U1

/-!
# DG Lemma 3.20 (`lem-annulus-lower`) from DZZ Proposition 3.17 + Lemma 6.1 (P2-DG105h, D105 P9)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.20 (DG:1625–1636): "For
each `ζ ∈ (0,1)`, it holds with probability tending to 1 as `ε → 0` that
`D^ε_{ĥ^tr}(𝕊, ∂𝕊(1/2)) ≥ ε^{−1/(d_γ+ζ)}`." Proof (DG:1633–1635): DZZ Proposition 3.17 and
Lemma 6.1 "give the analogous statement for Liouville graph distances with respect to a
zero-boundary GFF on a square of appropriate side length", combined with DG Lemma 3.2.

Formalization (D105 §1 items 1, 7; §4 P9):
* `𝕊 = 𝕍̄_{u,α}` (`l312Box u (α/20)`) and `𝕊(1/2) = 𝕍̄_u` (`l312Box u (1/20)`), DZZ's boxes of
  Lemma 6.1 (DG: `α = 1/2`); the box `ferniqueBox y b` of `μ_{ĥ^tr}` contains `B̄(u, 1/10)`.
* the DZZ input `DZZL61Whp P ν α χ u` is verbatim the conclusion of `DZZ.dzz_lem61_lower_whp`
  (Papers/DZZ/S5Defs) at `μ = ν` (`l312Box = DZZ.sqBox` by definition); `hν` compares DZZ's
  measure with `μ_{h^𝕍}` on balls inside `B̄(u,1/10)` (for `ν = dzzMuIn γ W` or `wickQArea γ W`:
  `DZZ.dzzWall_ball_of_subset` and `DZZ.wickArea_le_of_compact`).
* DG's distance is unrestricted; the balls of small `μ_{ĥ^tr}`-mass meeting `𝕊(1/2)` stay in
  `B̄(u, 1/10)` with probability `→ 1` (grid lower tail `muHU_ball_lower_tail`, union bound
  `prob_grid_event_le`, DG:1131–1137 scheme, and `l320_heavy`) — own glue, needed because DG's
  `D^ε` allows arbitrary balls.
* DG Lemma 3.2's comparison is used in its pathwise form `μ_{h^𝕍}(B) ≤ e^{γA} μ_{ĥ^tr}(B)` on
  `{max |h^𝕍 − ĥ^tr| ≤ A}` (DG Lemma 3.1 tail `trMod_spec`); `A` is fixed with
  `P[max > A] ≤ η/3` before `ε → 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail

/-- **The DZZ input of DG Lemma 3.20** (DG:1627; D105 N9): for `ι > 0`,
`P[min_{x ∈ ∂𝕍̄_{u,α}, y ∈ ∂𝕍̄_u} D_δ(ν)(x,y) < δ^{−χ+ι}] → 0`. Verbatim the conclusion of
`DZZ.dzz_lem61_lower_whp` (DZZ Proposition 3.17 + Lemma 6.1) at `μ = ν`. -/
def DZZL61Whp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ν : Ω → Measure ℂ)
    (α χ : ℝ) (u : ℂ) : Prop :=
  ∀ ι : ℝ, 0 < ι → Tendsto (fun δ => P {ω | ¬ ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
    ((DZZ.lgdMinSet (ν ω) δ (frontier (l312Box u (α / 20))) (frontier (l312Box u (1 / 20))) :
      ℕ∞) : ℝ≥0∞)}) (𝓝[>] 0) (𝓝 0)

lemma l320_exp_ev {K θ κ : ℝ} (hK : 0 < K) (hθ : θ < κ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (-θ) ≤ Real.sqrt (K * ε) ^ (-(2 * κ)) := by
  have ht := tendsto_rpow_neg_nhdsGT_zero (y := -(κ - θ)) (by linarith)
  filter_upwards [ht.eventually_ge_atTop (K ^ κ), self_mem_nhdsWithin] with ε h1 hε
  have hε0 : 0 < ε := hε
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.mul_rpow hK.le hε0.le]
  have e1 : (1 / 2 : ℝ) * -(2 * κ) = -κ := by ring
  have e : ε ^ (-κ) = ε ^ (-θ) * ε ^ (-(κ - θ)) := by
    rw [← Real.rpow_add hε0]; ring_nf
  rw [e1, e, Real.rpow_neg hK.le]
  have hKκ : 0 < K ^ κ := Real.rpow_pos_of_pos hK κ
  have h2 : 1 ≤ (K ^ κ)⁻¹ * ε ^ (-(κ - θ)) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hKκ, one_mul]; exact h1
  calc ε ^ (-θ) = ε ^ (-θ) * 1 := (mul_one _).symm
    _ ≤ ε ^ (-θ) * ((K ^ κ)⁻¹ * ε ^ (-(κ - θ))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- pathwise DG Lemma 3.2 step: on `{max_K |h^𝕍 − ĥ^tr| ≤ A}`, `μ_{h^𝕍}(B) ≤ e^{γA} μ_{ĥ^tr}(B)`
for `B ⊆ K` -/
lemma muHU_le_muTr (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 ≤ γ) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) {A : ℝ} {ω : Ω}
    (hA : ∀ z ∈ ferniqueBox y b, |trMod hW hb hK z ω| ≤ A) {B : Set ℂ} (hB : MeasurableSet B)
    (hBK : B ⊆ ferniqueBox y b) :
    muHU W γ ω B ≤ ENNReal.ofReal (Real.exp (γ * A)) * muTr hW γ hb hK ω B := by
  have h1 : ENNReal.ofReal (Real.exp (-(γ * A))) * muHU W γ ω B ≤ muTr hW γ hb hK ω B := by
    unfold muTr muOfMod
    rw [withDensity_apply _ hB]
    calc ENNReal.ofReal (Real.exp (-(γ * A))) * muHU W γ ω B
        = ∫⁻ _z in B, ENNReal.ofReal (Real.exp (-(γ * A))) ∂(muHU W γ ω).restrict
            (ferniqueBox y b) := by
          rw [setLIntegral_const, Measure.restrict_apply hB, inter_eq_left.2 hBK]
      _ ≤ _ := by
          refine setLIntegral_mono' hB fun z hz => ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.2 ?_)
          have := abs_le.1 (hA z (hBK hz))
          nlinarith
  calc muHU W γ ω B = ENNReal.ofReal (Real.exp (γ * A)) *
        (ENNReal.ofReal (Real.exp (-(γ * A))) * muHU W γ ω B) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

/-- **DG Lemma 3.20** (`lem-annulus-lower`, DG:1625–1636) at `𝕊 = 𝕍̄_{u,α}`, `𝕊(1/2) = 𝕍̄_u`
(DG: `α = 1/2`): for `ζ > 0`, with probability tending to `1` as `ε → 0`,
`D^ε_{ĥ^tr}(z, w) ≥ ε^{−1/(d_γ+ζ)}` for all `z ∈ 𝕊`, `w ∈ ∂𝕊(1/2)` (unrestricted distance,
`d_γ = 2/χ`). Inputs: DZZ P3.17 + L6.1 (`hDZZ`, DZZ's measure `ν ≤ e^{b'} μ_{h^𝕍}` on balls in
`B̄(u, 1/10)`), DG Lemma 3.1's tail for `h^𝕍 − ĥ^tr`, and the lower tail of `μ_{h^𝕍}(B(w,g))`. -/
theorem dg_lemma320 (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ} {b : ℝ}
    (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) {u : ℂ}
    (hR : closedBall u (1 / 10) ⊆ ferniqueBox y b) {ν : Ω → Measure ℂ} {b' : ℝ}
    (hν : ∀ ω x r, ball x r ⊆ closedBall u (1 / 10) →
      ν ω (ball x r) ≤ ENNReal.ofReal (Real.exp b') * muHU W γ ω (ball x r))
    {α χ : ℝ} (hα : α < 1) (hχ : 0 < χ) (hDZZ : DZZL61Whp P ν α χ u) {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun ε => P {ω | ¬ ∀ z ∈ l312Box u (α / 20), ∀ w ∈ frontier (l312Box u (1 / 20)),
      ENNReal.ofReal (ε ^ (-(1 / (2 / χ + ζ)))) ≤
        ((dgLGD (muTr hW γ hb hK ω) ε univ z w : ℕ∞) : ℝ≥0∞)}) (𝓝[>] 0) (𝓝 0) := by
  have hP := hW.isProbabilityMeasure
  set θ := 1 / (2 / χ + ζ) with hθ
  have hθχ : θ < χ / 2 := by
    have h1 : 0 < 2 / χ := by positivity
    have := one_div_lt_one_div_of_lt h1 (by linarith : 2 / χ < 2 / χ + ζ)
    rw [one_div_div] at this
    rw [hθ]; exact this
  set ι := χ / 2 - θ with hι
  have hι0 : 0 < ι := by linarith
  have hθκ : θ < (χ - ι) / 2 := by rw [hι]; linarith [(by positivity : 0 < θ)]
  -- DG Lemma 3.1's tail, the lower tail of `μ_{h^𝕍}` on small balls
  obtain ⟨-, -, ⟨b₀, b₁, hb₁, htail⟩, -⟩ := trMod_spec hW hb hK
  have hRV : closedBall u (1 / 10) ⊆ openSquare := hR.trans (ferniqueBox_subset hK)
  obtain ⟨Ct, r₀, hr₀, hlt⟩ := muHU_ball_lower_tail hW (q := 1) hγ hγ2 one_pos
    (isCompact_closedBall u (1 / 10)) hRV
  set g := min (1 / 400 : ℝ) r₀ with hgdef
  have hg0 : 0 < g := lt_min (by norm_num) hr₀
  have hg' : g ≤ 1 / 400 := min_le_left _ _
  have hgr : g ≤ r₀ := min_le_right _ _
  set Rg : ℝ := 1 / 16 - 2 * g with hRg
  have hRg0 : 0 ≤ Rg := by rw [hRg]; linarith
  set Eg : ℝ → ℂ → Set Ω := fun t w => {ω | muHU W γ ω (ball w g) ≤ ENNReal.ofReal t}
  set Gr : ℝ → Set Ω := fun t => {ω | ∃ i j : ℤ, ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ Rg + 3 * g ∧
    ω ∈ Eg t ⟨i * g, j * g⟩}
  obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, ∀ t a : ℝ, (∀ w ∈ closedBall u (Rg + 3 * g),
      P (Eg t w) ≤ ENNReal.ofReal a) → P (Gr t) ≤ ENNReal.ofReal (M0 * a) :=
    ⟨_, fun t a ha => prob_grid_event_le (E := Eg t) hRg0 hg0 ha⟩
  have hball_sub : ∀ w : ℂ, ‖w - u‖ ≤ Rg + 3 * g → closedBall w g ⊆ closedBall u (1 / 10) := by
    intro w hw x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have := norm_sub_le_norm_sub_add_norm_sub x w u
    linarith
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηt
  · exact Eventually.of_forall fun _ => le_top
  set r := η.toReal / 3 with hr
  have hr0 : 0 < r := by have := ENNReal.toReal_pos hη.ne' hηt; positivity
  have hrr : ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r = η := by
    rw [← ENNReal.ofReal_add hr0.le hr0.le, ← ENNReal.ofReal_add (by positivity) hr0.le, hr]
    rw [show η.toReal / 3 + η.toReal / 3 + η.toReal / 3 = η.toReal by ring,
      ENNReal.ofReal_toReal hηt]
  -- the threshold `A` of DG Lemma 3.1 with `b₀ e^{−b₁A²} < r`
  have hT : Tendsto (fun T : ℝ => b₀ * Real.exp (-b₁ * T ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => -b₁ * T ^ 2) atTop atBot := by
      have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).const_mul_atTop hb₁
      exact (tendsto_neg_atTop_atBot.comp this).congr fun T => by simp
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul b₀
  obtain ⟨A, hA1, hA0⟩ := ((hT.eventually (gt_mem_nhds hr0)).and (eventually_gt_atTop 0)).exists
  set K := Real.exp b' * Real.exp (γ * A) with hKdef
  have hK0 : 0 < K := by positivity
  have hδt : Tendsto (fun ε => Real.sqrt (K * ε)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (Real.continuous_sqrt.comp ((continuous_const : Continuous fun _ : ℝ => K).mul
        continuous_id)).tendsto 0
      simpa [Function.comp_def] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact Real.sqrt_pos.2 (mul_pos hK0 hε)
  have hlin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M0 * (Ct * (Real.exp (γ * A) * ε) ^ (1 : ℝ) *
      g ^ (-((1 : ℝ) * (1 + 1) * γ ^ 2 / 2 + 2 * 1))) < r := by
    have hc : Continuous fun ε : ℝ => M0 * (Ct * (Real.exp (γ * A) * ε) *
        g ^ (-((1 : ℝ) * (1 + 1) * γ ^ 2 / 2 + 2 * 1))) := by fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simp only [mul_zero, zero_mul] at h0
    simpa only [Real.rpow_one] using h0.eventually (gt_mem_nhds hr0)
  filter_upwards [hlin, ((hDZZ ι hι0).comp hδt).eventually
      (Iic_mem_nhds (ENNReal.ofReal_pos.2 hr0)), l320_exp_ev hK0 hθκ, self_mem_nhdsWithin]
    with ε hε1 hε2 hε3 hε
  have hε0 : 0 < ε := hε
  have h2κ : 2 * ((χ - ι) / 2) = χ - ι := by ring
  rw [h2κ] at hε3
  have htε : 0 < Real.exp (γ * A) * ε := by positivity
  -- the three bad events
  have hPG : P (Gr (Real.exp (γ * A) * ε)) ≤ ENNReal.ofReal r := by
    refine (hM0 _ _ fun w hw => ?_).trans (ENNReal.ofReal_le_ofReal hε1.le)
    have hwK : w ∈ closedBall u (1 / 10) := by
      rw [mem_closedBall, dist_eq_norm] at hw ⊢; rw [hRg] at hw; linarith
    exact (hlt w hwK g hg0 hgr).2 _ htε
  set Tl := {ω | ¬ ∀ z ∈ ferniqueBox y b, |trMod hW hb hK z ω| ≤ A} with hTl
  have hPT : P Tl ≤ ENNReal.ofReal r :=
    (htail A hA0.le).trans (ENNReal.ofReal_le_ofReal hA1.le)
  set Dz := {ω | ¬ ENNReal.ofReal (Real.sqrt (K * ε) ^ (-(χ - ι))) ≤
    ((DZZ.lgdMinSet (ν ω) (Real.sqrt (K * ε)) (frontier (l312Box u (α / 20)))
      (frontier (l312Box u (1 / 20))) : ℕ∞) : ℝ≥0∞)} with hDz
  have hincl : {ω | ¬ ∀ z ∈ l312Box u (α / 20), ∀ w ∈ frontier (l312Box u (1 / 20)),
      ENNReal.ofReal (ε ^ (-θ)) ≤ ((dgLGD (muTr hW γ hb hK ω) ε univ z w : ℕ∞) : ℝ≥0∞)} ⊆
      Tl ∪ Gr (Real.exp (γ * A) * ε) ∪ Dz := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨hT', hG'⟩, hD'⟩ := hcon
    have hA' := not_not.1 hT'
    have hD'' := not_not.1 hD'
    apply hω
    intro z hz w hw
    -- every grid ball is `μ_{ĥ^tr}`-heavy
    have hgrid : ∀ i j : ℤ, ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ (1 / 16 - 2 * g) + 3 * g →
        ENNReal.ofReal ε < muTr hW γ hb hK ω (ball ⟨i * g, j * g⟩ g) := by
      intro i j hij
      have h1 : ENNReal.ofReal (Real.exp (γ * A) * ε) < muHU W γ ω (ball ⟨i * g, j * g⟩ g) := by
        by_contra hle
        exact hG' ⟨i, j, hij, not_lt.1 hle⟩
      have h2 := muHU_le_muTr hW hγ.le hb hK hA' measurableSet_ball
        ((ball_subset_closedBall.trans (hball_sub _ hij)).trans hR)
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at h1
      by_contra hle
      have h3 : ENNReal.ofReal (Real.exp (γ * A)) * muTr hW γ hb hK ω (ball ⟨i * g, j * g⟩ g) ≤
          ENNReal.ofReal (Real.exp (γ * A)) * ENNReal.ofReal ε := by gcongr; exact not_lt.1 hle
      exact absurd ((h1.trans_le h2).trans_le h3) (lt_irrefl _)
    have hcore := l320_core (μT := muTr hW γ hb hK ω) (ν := ν ω) (ε := ε)
      (δ := Real.sqrt (K * ε)) hα hz hw (fun x ρ ⟨p, hp, hpO⟩ hm => by
        by_cases hsub : ball x ρ ⊆ closedBall u (1 / 10)
        · calc ν ω (ball x ρ) ≤ ENNReal.ofReal (Real.exp b') * muHU W γ ω (ball x ρ) :=
                hν ω x ρ hsub
            _ ≤ ENNReal.ofReal (Real.exp b') * (ENNReal.ofReal (Real.exp (γ * A)) *
                muTr hW γ hb hK ω (ball x ρ)) := by
                gcongr; exact muHU_le_muTr hW hγ.le hb hK hA' measurableSet_ball (hsub.trans hR)
            _ ≤ ENNReal.ofReal (Real.exp b') * (ENNReal.ofReal (Real.exp (γ * A)) *
                ENNReal.ofReal ε) := by gcongr
            _ = ENNReal.ofReal (Real.sqrt (K * ε) ^ 2) := by
                rw [Real.sq_sqrt (by positivity), hKdef, ENNReal.ofReal_mul (by positivity),
                  ENNReal.ofReal_mul (by positivity), mul_assoc]
        · exfalso
          have hpu : ‖p - u‖ ≤ 1 / 20 := by
            refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
            have h1 := hpO.1
            have h2 := hpO.2
            simp only [Complex.sub_re, Complex.sub_im] at h1 h2 ⊢
            linarith
          exact absurd hm (not_le.2 (l320_heavy hg0 hg' hgrid hp hpu hsub)))
    calc ENNReal.ofReal (ε ^ (-θ)) ≤ ENNReal.ofReal (Real.sqrt (K * ε) ^ (-(χ - ι))) :=
          ENNReal.ofReal_le_ofReal hε3
      _ ≤ _ := hD''
      _ ≤ _ := ENat.toENNReal_le.2 hcore
  calc _ ≤ _ := measure_mono hincl
    _ ≤ P Tl + P (Gr (Real.exp (γ * A) * ε)) + P Dz :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r := by
        gcongr
        exact hε2
    _ = η := hrr

end DG
end LQGMetric
