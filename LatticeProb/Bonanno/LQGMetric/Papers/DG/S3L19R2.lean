/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19R2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19R1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L12W
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3TrInv4

/-!
# DG Lemma 3.19 at `μ = μ_ĥ`: the unit-frame event `E_𝕊` and (eqn-perc-prob') (P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.19
(DG:1641–1648). In the unit frame (centre `u = 1/2 + i/2`, the grid square of side `1/32` is
`𝕊 = l312Box u (1/32) = 𝕍̄_{u,5/8}` and DG's crossing box is `𝕍̄_u = l312Box u (1/20)`), the
event `l319Ev μ t M` has DG's two conditions (DG:1642–1643):

1. `l319Heavy`: every grid ball `B(w, 1/400)`, `w ∈ (1/400)ℤ²`, `|w − u| ≤ 1/28 + 3/560 + 1/400`, has
   mass `> t`. By `l319_heavy` (S3L19R1) this gives DG's condition 2 (balls of mass `≤ t`
   meeting `𝕍̄_u` stay in `B̄(u, 13/280)`, our `S(3/4)`).
2. `D^t(𝕊, ∂𝕍̄_u; B̄(u,13/280)) ≥ M` (DG's condition 1, with the balls in `B̄(u,13/280)`, which on
   condition 2 is the unrestricted distance; this form is local).

* `l319_heavy_tendsto`: `P[¬ l319Heavy (μ_{ĥ^tr}) t] → 0` as `t → 0` ("`μ_{ĥ^tr}` assigns
  positive mass to every open set", DG:1645), by DG Lemma 3.1's tail and the lower tail of
  `μ_{h^𝕍}` on small balls, as in `dg_lemma320` (S3L20B).
* `prob_l319Ev_muTr_eq`: the law of the event does not depend on the white noise (DG:1644).
* **`l319_unit_unif`** (DG (eqn-perc-prob')): one `ε_*` for all white noises, from DG Lemma 3.20
  (`dg_lemma320_muIn` at `α = 5/8`, input `DZZL61Whp`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail DZZ

/-- the unit-frame centre `u = 1/2 + i/2` -/
abbrev l319U : ℂ := ⟨1 / 2, 1 / 2⟩

/-- the grid spacing and radius of the heavy-ball condition -/
abbrev l319g : ℝ := 1 / 400

/-- the radius of the region `B̄(u, l319r)` (DG's `S(3/4)`) of the unit-frame event -/
abbrev l319r : ℝ := 13 / 280

/-- **DG's condition 2 of `E_S` (DG:1643), grid form**: the grid balls near `u` are heavy -/
def l319Heavy (μ : Measure ℂ) (t : ℝ) : Prop :=
  ∀ i j : ℤ, ‖(⟨i * l319g, j * l319g⟩ : ℂ) - l319U‖ ≤ 1 / 28 + 3 / 560 + l319g →
    ENNReal.ofReal t < μ (ball ⟨i * l319g, j * l319g⟩ l319g)

/-- **the unit-frame event `E_𝕊^t` of DG Lemma 3.19** (DG:1642–1643) -/
def l319Ev (μ : Measure ℂ) (t M : ℝ) : Prop :=
  l319Heavy μ t ∧ ENNReal.ofReal M ≤ (dgLGDSet μ t (closedBall l319U l319r)
    (l312Box l319U (1 / 32)) (frontier (l312Box l319U (1 / 20))) : ℝ≥0∞)

/-- the heavy-ball condition in rational ball masses -/
def l319HeavyRat (t : ℝ) : Set (ℚ × ℚ → ℚ → ℝ≥0∞) :=
  {m | ∀ i j : ℤ, ‖(⟨i * l319g, j * l319g⟩ : ℂ) - l319U‖ ≤ 1 / 28 + 3 / 560 + l319g →
    ENNReal.ofReal t < m ((i : ℚ) / 400, (j : ℚ) / 400) (1 / 400)}

lemma measurableSet_l319HeavyRat (t : ℝ) : MeasurableSet (l319HeavyRat t) := by
  have e : l319HeavyRat t = ⋂ i : ℤ, ⋂ j : ℤ,
      {m : ℚ × ℚ → ℚ → ℝ≥0∞ | ‖(⟨i * l319g, j * l319g⟩ : ℂ) - l319U‖ ≤ 1 / 28 + 3 / 560 + l319g →
        ENNReal.ofReal t < m ((i : ℚ) / 400, (j : ℚ) / 400) (1 / 400)} := by
    ext m; simp [l319HeavyRat]
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases h : ‖(⟨i * l319g, j * l319g⟩ : ℂ) - l319U‖ ≤ 1 / 28 + 3 / 560 + l319g
  · simp only [h, true_implies]
    exact measurableSet_lt measurable_const
      ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [h, false_implies, setOf_true, MeasurableSet.univ]

lemma ratPt_l319 (i j : ℤ) :
    ratPt ((i : ℚ) / 400, (j : ℚ) / 400) = (⟨i * l319g, j * l319g⟩ : ℂ) := by
  apply Complex.ext <;> simp [ratPt, l319g] <;> ring

lemma l319Heavy_iff (μ : Measure ℂ) (t : ℝ) : l319Heavy μ t ↔ ballMassQ μ ∈ l319HeavyRat t := by
  simp only [l319Heavy, l319HeavyRat, mem_setOf_eq, ballMassQ, ratPt_l319]
  norm_num

/-- the event `E_𝕊^t` in rational ball masses -/
def l319EvRat (t M : ℝ) : Set (ℚ × ℚ → ℚ → ℝ≥0∞) :=
  l319HeavyRat t ∩ (fun m => dgLGDSetRat m t (closedBall l319U l319r)
    (l312Box l319U (1 / 32)) (frontier (l312Box l319U (1 / 20)))) ⁻¹'
      {k : ℕ∞ | ENNReal.ofReal M ≤ (k : ℝ≥0∞)}

lemma l319Ev_iff (μ : Measure ℂ) (t M : ℝ) : l319Ev μ t M ↔ ballMassQ μ ∈ l319EvRat t M := by
  simp only [l319Ev, l319EvRat, mem_inter_iff, mem_preimage, mem_setOf_eq, l319Heavy_iff,
    dgLGDSet_eq_dgLGDSetRat]

lemma measurableSet_l319EvRat (t M : ℝ) : MeasurableSet (l319EvRat t M) :=
  (measurableSet_l319HeavyRat t).inter
    (measurable_dgLGDSetRat t _ _ _ (MeasurableSet.of_discrete))

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}

/-- **the law of `E_𝕊^t` for `μ_{ĥ^tr}` does not depend on the white noise** (DG:1644) -/
theorem prob_l319Ev_muTr_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) (t M : ℝ) :
    P {ω | ¬ l319Ev (muTr hW γ hb hK ω) t M} = P' {ω | ¬ l319Ev (muTr hW' γ hb hK ω) t M} := by
  simp_rw [l319Ev_iff]
  exact prob_muTr_eq hW hW' hγ hγ2 hb hK (measurableSet_l319EvRat t M).compl

/-- **the grid balls are `μ_{ĥ^tr}`-heavy with probability `→ 1`** (DG:1645) -/
theorem l319_heavy_tendsto (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    (hR : closedBall l319U (1 / 10) ⊆ ferniqueBox y b) :
    Tendsto (fun t => P {ω | ¬ l319Heavy (muTr hW γ hb hK ω) t}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨-, -, ⟨b₀, b₁, hb₁, htail⟩, -⟩ := trMod_spec hW hb hK
  have hRV : closedBall l319U (1 / 10) ⊆ openSquare := hR.trans (ferniqueBox_subset hK)
  obtain ⟨Ct, r₀, hr₀, hlt⟩ := muHU_ball_lower_tail hW (q := 1) hγ hγ2 one_pos
    (isCompact_closedBall l319U (1 / 10)) hRV
  set g' := min l319g r₀ with hg'def
  have hg'0 : 0 < g' := lt_min (by norm_num) hr₀
  set Eg : ℝ → ℂ → Set Ω := fun t w => {ω | muHU W γ ω (ball w g') ≤ ENNReal.ofReal t}
  set Gr : ℝ → Set Ω := fun t => {ω | ∃ i j : ℤ,
    ‖(⟨i * l319g, j * l319g⟩ : ℂ) - l319U‖ ≤ 1 / 28 + 3 / 560 - 2 * l319g + 3 * l319g ∧
      ω ∈ Eg t ⟨i * l319g, j * l319g⟩}
  obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, ∀ t a : ℝ, (∀ w ∈ closedBall l319U (1 / 28 + 3 / 560 - 2 * l319g + 3 * l319g),
      P (Eg t w) ≤ ENNReal.ofReal a) → P (Gr t) ≤ ENNReal.ofReal (M0 * a) :=
    ⟨_, fun t a ha => prob_grid_event_le (E := Eg t) (by norm_num) (by norm_num) ha⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηt
  · exact Eventually.of_forall fun _ => le_top
  set r := η.toReal / 2 with hr
  have hr0 : 0 < r := by have := ENNReal.toReal_pos hη.ne' hηt; positivity
  have hrr : ENNReal.ofReal r + ENNReal.ofReal r = η := by
    rw [← ENNReal.ofReal_add hr0.le hr0.le, hr,
      show η.toReal / 2 + η.toReal / 2 = η.toReal by ring, ENNReal.ofReal_toReal hηt]
  have hT : Tendsto (fun T : ℝ => b₀ * Real.exp (-b₁ * T ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => -b₁ * T ^ 2) atTop atBot := by
      have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).const_mul_atTop hb₁
      exact (tendsto_neg_atTop_atBot.comp this).congr fun T => by simp
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul b₀
  obtain ⟨A, hA1, hA0⟩ := ((hT.eventually (gt_mem_nhds hr0)).and (eventually_gt_atTop 0)).exists
  have hlin : ∀ᶠ t in 𝓝[>] (0 : ℝ), M0 * (Ct * (Real.exp (γ * A) * t) ^ (1 : ℝ) *
      g' ^ (-((1 : ℝ) * (1 + 1) * γ ^ 2 / 2 + 2 * 1))) < r := by
    have hc : Continuous fun t : ℝ => M0 * (Ct * (Real.exp (γ * A) * t) *
        g' ^ (-((1 : ℝ) * (1 + 1) * γ ^ 2 / 2 + 2 * 1))) := by fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simp only [mul_zero, zero_mul] at h0
    simpa only [Real.rpow_one] using h0.eventually (gt_mem_nhds hr0)
  filter_upwards [hlin, self_mem_nhdsWithin] with t ht1 ht
  have ht0 : 0 < t := ht
  have htε : 0 < Real.exp (γ * A) * t := by positivity
  have hPG : P (Gr (Real.exp (γ * A) * t)) ≤ ENNReal.ofReal r := by
    refine (hM0 _ _ fun w hw => ?_).trans (ENNReal.ofReal_le_ofReal ht1.le)
    have hwK : w ∈ closedBall l319U (1 / 10) := by
      rw [mem_closedBall, dist_eq_norm] at hw ⊢; norm_num at hw ⊢; linarith
    exact (hlt w hwK g' hg'0 (min_le_right _ _)).2 _ htε
  set Tl := {ω | ¬ ∀ z ∈ ferniqueBox y b, |trMod hW hb hK z ω| ≤ A} with hTl
  have hPT : P Tl ≤ ENNReal.ofReal r :=
    (htail A hA0.le).trans (ENNReal.ofReal_le_ofReal hA1.le)
  have hincl : {ω | ¬ l319Heavy (muTr hW γ hb hK ω) t} ⊆ Tl ∪ Gr (Real.exp (γ * A) * t) := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨hT', hG'⟩ := hcon
    have hA' := not_not.1 hT'
    apply hω
    intro i j hij
    have h1 : ENNReal.ofReal (Real.exp (γ * A) * t) <
        muHU W γ ω (ball ⟨i * l319g, j * l319g⟩ l319g) := by
      refine lt_of_lt_of_le ?_ (measure_mono (ball_subset_ball (min_le_left l319g r₀)))
      by_contra hle
      exact hG' ⟨i, j, by norm_num at hij ⊢; linarith, not_lt.1 hle⟩
    have hsub : ball (⟨i * l319g, j * l319g⟩ : ℂ) l319g ⊆ ferniqueBox y b := by
      refine (ball_subset_closedBall.trans ?_).trans hR
      intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      have := norm_sub_le_norm_sub_add_norm_sub x (⟨i * l319g, j * l319g⟩ : ℂ) l319U
      norm_num at hij hx ⊢; linarith
    have h2 := muHU_le_muTr hW hγ.le hb hK hA' measurableSet_ball hsub
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at h1
    by_contra hle
    have h3 : ENNReal.ofReal (Real.exp (γ * A)) *
        muTr hW γ hb hK ω (ball ⟨i * l319g, j * l319g⟩ l319g) ≤
        ENNReal.ofReal (Real.exp (γ * A)) * ENNReal.ofReal t := by gcongr; exact not_lt.1 hle
    exact absurd ((h1.trans_le h2).trans_le h3) (lt_irrefl _)
  calc _ ≤ _ := measure_mono hincl
    _ ≤ P Tl + P (Gr (Real.exp (γ * A) * t)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add hPT hPG
    _ = η := hrr

/-- the restricted distance dominates the unrestricted one -/
lemma dgLGD_univ_le (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) :
    dgLGD μ ε univ z w ≤ dgLGD μ ε U z w :=
  le_iInf₂ fun N hN => iInf₂_le N (LGDWit.mono (by simp) hN)

/-- **DG (eqn-perc-prob') with a uniform `ε_*`** (DG:1644–1648): from DG Lemma 3.20 at
`𝕊 = 𝕍̄_{u,5/8}` (`dg_lemma320_muIn`, input DZZ P3.17 + L6.1 `hDZZ` for `W`), one threshold
`ε_*` gives `P[¬ E_𝕊^t] ≤ p` for `μ_{ĥ^tr}` of every white noise on `(Ω, P)` and `t < ε_*`,
at `M = t^{−1/(d_γ+ζ)}`, `d_γ = 2/χ`. -/
theorem l319_unit_unif (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    (hR : closedBall l319U (1 / 10) ⊆ ferniqueBox y b) {χ : ℝ} (hχ : 0 < χ)
    (hDZZ : DZZL61Whp P (DZZ.dzzMuIn γ W) (5 / 8) χ l319U) {ζ : ℝ} (hζ : 0 < ζ)
    {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ εs : ℝ, 0 < εs ∧ ∀ t : ℝ, 0 < t → t < εs → ∀ (W₁ : WNSpace → Ω → ℝ)
      (hW₁ : IsWhiteNoise P W₁),
      P {ω | ¬ l319Ev (muTr hW₁ γ hb hK ω) t (t ^ (-(1 / (2 / χ + ζ))))} ≤ p := by
  have h1 := dg_lemma320_muIn hW hγ hγ2 hb hK hR (by norm_num : (5 / 8 : ℝ) < 1) hχ hDZZ hζ
  have h2 := l319_heavy_tendsto hW hγ hγ2 hb hK hR
  have h3 := h1.add h2
  rw [add_zero] at h3
  have hev := h3.eventually (Iic_mem_nhds hp)
  obtain ⟨εs, hεs, hεs'⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨εs, hεs, fun t ht htl W₁ hW₁ => ?_⟩
  rw [prob_l319Ev_muTr_eq hW₁ hW hγ hγ2 hb hK]
  refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans (hεs' ⟨?_, ht⟩))
  · intro ω hω
    by_contra hcon
    simp only [mem_union, mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hD, hH⟩ := hcon
    refine hω ⟨hH, ?_⟩
    unfold dgLGDSet
    simp only [ENat.toENNReal_iInf]
    refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
    have hz' : z ∈ l312Box l319U (5 / 8 / 20) := by norm_num; exact hz
    exact (hD z hz' w hw).trans (ENat.toENNReal_le.2 (dgLGD_univ_le _ _ _ z w))
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]; exact htl

end DG
end LQGMetric
