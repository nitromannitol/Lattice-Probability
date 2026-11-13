/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Lemma47 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Bookkeeping

/-!
# [18] Lemma 4.7: the outer localized degree

Source: [18] Lemma 4.7 : "There exists `α = α(γ) > 0` such that for
each `ζ ∈ (0, 1)`, `P[sup_{z ∈ B_ρ(0)} deg^ε_out(z) > ε^{−ζ}] = O_ε(ε^α)`."

Proof (as in the source, with the corrected lower bound in (4.18)):
* (4.18), upper: [18] Lemma 2.7 for all segments (`GMSLemma27.lemma27_segments`) gives
  `diam η([τ_z − ε, τ_z + ε]) ≤ 2ε^q` (`diam_locWindow_le_two_mul`);
* (4.18), lower: the upper mass bound `UpperMassBound`  gives `diam ≥ ε^{2/ξ}`
  (`pow_le_diam_locWindow`);
* GHM15 Prop 3.4 + Rem 3.9 (`GMSLemma27.SegmentsContainBalls`, bundle S8(a)) at scale `2ε^q` gives the balls, and the
  packing bound (`locDegOut_le_of_balls`, `packing_ratio_le`) gives `deg^ε_out ≤ 16 ε^{−ζ/2} ≤ ε^{−ζ}`.

`locDegOut_le_of_good` is the deterministic implication; `lemma47_holds` the probability estimate on L27's cell model.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

/-- **Deterministic core of Lemma 4.7.** Let `c` be continuous with null overlaps, `t₀` a root time with
`c(t₀) ∈ B_ρ(0)`, and `ε^p ≤ diam c([t₀ − ε, t₀ + ε]) ≤ 2ε^q` with `8ε^q < 1 − ρ`. If every segment `c([a, b])`
inside `𝔻` with `diam ≥ δ^{1−r}` (`r = ζ/(4p + ζ)`, `δ ∈ (0, 2ε^q]`) contains a ball of radius `≥ δ` (GHM15's event),
then `deg^ε_out ≤ 16 ε^{−ζ/2}`. -/
theorem locDegOut_le_of_good {c : ℝ → ℂ} (hc : Continuous c) (hnull : NullOverlaps c)
    {ε q ρ p ζ : ℝ} (hε : 0 < ε) (hp : 0 < p) (hζ : 0 < ζ)
    {t₀ : ℝ} (ht₀ : c t₀ ∈ ball (0 : ℂ) ρ)
    (hup : diam (locWindow ε c t₀) ≤ 2 * ε ^ q) (hsmall : 8 * ε ^ q < 1 - ρ)
    (hlow : ε ^ p ≤ diam (locWindow ε c t₀))
    (hGHM : ∀ δ ∈ Ioc (0 : ℝ) (2 * ε ^ q), ∀ a b : ℝ, a < b → c '' Icc a b ⊆ ball (0 : ℂ) 1 →
      δ ^ (1 - ζ / (4 * p + ζ)) ≤ diam (c '' Icc a b) →
        ∃ w : ℂ, ∃ t : ℝ, δ ≤ t ∧ ball w t ⊆ c '' Icc a b) :
    ((locDegOut ε c t₀ : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (16 * ε ^ (-(ζ / 2))) := by
  set D := diam (locWindow ε c t₀) with hD
  have hDpos : 0 < D := (Real.rpow_pos_of_pos hε p).trans_le hlow
  have h4 : 0 < 4 * p + ζ := by positivity
  set r : ℝ := ζ / (4 * p + ζ) with hr
  have hr1 : r < 1 := by rw [hr, div_lt_one h4]; linarith
  have h1r : 0 < 1 - r := by linarith
  set e : ℝ := 1 / (1 - r) with he
  have he1 : 1 ≤ e := by
    rw [he, le_div_iff₀ h1r, one_mul]
    have : 0 ≤ r := div_nonneg hζ.le h4.le
    linarith
  set r₀ : ℝ := D ^ e with hr₀
  have hr₀pos : 0 < r₀ := Real.rpow_pos_of_pos hDpos e
  have hq0 : 0 < ε ^ q := Real.rpow_pos_of_pos hε q
  have hD1 : D ≤ 1 := by
    have : 2 * ε ^ q ≤ 1 := by nlinarith [ht₀, mem_ball_zero_iff.mp ht₀, norm_nonneg (c t₀)]
    linarith
  have hr₀D : r₀ ≤ D := by
    calc r₀ = D ^ e := rfl
      _ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hDpos hD1 he1
      _ = D := Real.rpow_one D
  have hball : ∀ a b : ℝ, a < b → c '' Icc a b ⊆ locBall ε c t₀ →
      D ≤ diam (c '' Icc a b) → ∃ w : ℂ, ball w r₀ ⊆ c '' Icc a b := by
    intro a b hab hsub hdiam
    have hsub1 : c '' Icc a b ⊆ ball (0 : ℂ) 1 := by
      refine hsub.trans fun w hw => ?_
      rw [locBall, mem_closedBall] at hw
      rw [mem_ball_zero_iff]
      have h0 := mem_ball_zero_iff.mp ht₀
      calc ‖w‖ ≤ ‖w - c t₀‖ + ‖c t₀‖ := by
            calc ‖w‖ = ‖(w - c t₀) + c t₀‖ := by rw [sub_add_cancel]
              _ ≤ _ := norm_add_le _ _
        _ < 1 := by rw [← dist_eq_norm]; linarith
    have hpow : r₀ ^ (1 - r) = D := by
      rw [hr₀, ← Real.rpow_mul hDpos.le, he, one_div, inv_mul_cancel₀ h1r.ne', Real.rpow_one]
    obtain ⟨w, t, ht, hwt⟩ := hGHM r₀ ⟨hr₀pos, hr₀D.trans hup⟩ a b hab hsub1 (by rw [hpow]; exact hdiam)
    exact ⟨w, (ball_subset_ball ht).trans hwt⟩
  have hpack := locDegOut_le_of_balls hc hε.le hnull hr₀pos hball
  refine hpack.trans (ENNReal.ofReal_le_ofReal ?_)
  exact packing_ratio_le hε hp hζ hlow

/-- `(2ε^q)^s = 2^s ε^{qs}`. -/
private theorem two_mul_rpow_rpow {ε q s : ℝ} (hε : 0 < ε) :
    (2 * ε ^ q) ^ s = 2 ^ s * ε ^ (q * s) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_pos_of_pos hε q).le, ← Real.rpow_mul hε.le]

/-- **[18] Lemma 4.7**, on L27's cell model. There is `α > 0` (depending only on the exponents of
The inputs, i.e. on `γ`) such that for every `ρ, ζ ∈ (0, 1)`, `P[sup_{z ∈ B_ρ(0)} deg^ε_out(z) > ε^{−ζ}] ≤ C ε^α` for
all `ε ∈ (0, 1)` (outer measure). Inputs: L27's (Lemma 2.7) `SegmentsContainBalls` (bundle S8(a)), `GMCLowerTail` and
`AreaDominatesWholePlaneGFF` (SLE-free); `UpperMassBound` (SLE-free, the upper mass estimate); `SpaceFillingGeometry` (bundle). -/
theorem lemma47_holds {γ : ℝ} (M : CellModel γ) (hγ : 0 < γ) (hSLE : SegmentsContainBalls M)
    (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M) (hmass : UpperMassBound M)
    (hgeom : SpaceFillingGeometry M) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (ε ^ (-ζ)) < ((degreeOut ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * ε ^ α) := by
  -- exponents
  set q : ℝ := 1 / (2 + γ) ^ 2 with hq
  have hq0 : 0 < q := by positivity
  have hq' : q < 2 / (2 + γ) ^ 2 := by
    rw [hq]; exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  have hexp := lemma27Exponent_pos hγ hq0 hq'
  set α₁ : ℝ := lemma27Exponent q γ / 2 with hα₁
  have hα₁0 : 0 < α₁ := by positivity
  obtain ⟨ξ₀, β, hξ₀, hβ, hmassρ⟩ := hmass
  set ξ : ℝ := min ξ₀ 1 with hξ
  have hξ0 : 0 < ξ := lt_min hξ₀ one_pos
  have hξ1 : ξ ≤ 1 := min_le_right _ _
  set p : ℝ := 2 / ξ with hp
  have hp0 : 0 < p := by positivity
  set α : ℝ := min α₁ (p * β) with hα
  have hα0 : 0 < α := lt_min hα₁0 (by positivity)
  refine ⟨α, hα0, fun ρ hρ ζ hζ => ?_⟩
  obtain ⟨C₁, hC₁⟩ := lemma27_segments M hSLE hGMC hdom hγ hq0 hq' hρ.1 hρ.2
    (show α₁ < lemma27Exponent q γ by rw [hα₁]; linarith)
  obtain ⟨C₂, hC₂⟩ := hmassρ ρ hρ
  have h4 : 0 < 4 * p + ζ := by linarith [hζ.1]
  set r : ℝ := ζ / (4 * p + ζ) with hr
  have hr0 : 0 < r := div_pos hζ.1 h4
  have hr1 : r < 1 := by rw [hr, div_lt_one h4]; linarith
  -- GHM15 at scale `2ε^q`
  have hGHMo := hSLE r ⟨hr0, hr1⟩ 1 one_pos (α / q)
  have hGHMev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (M.P (segmentBallEvent M 1 r (2 * ε ^ q))ᶜ).toReal ≤ (2 * ε ^ q) ^ (α / q) := by
    have htend : Tendsto (fun ε : ℝ => 2 * ε ^ q) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h := ((tendsto_rpow_nhdsGT_zero hq0).mono_right nhdsWithin_le_nhds).const_mul (2 : ℝ)
        simpa using h
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_pos two_pos (Real.rpow_pos_of_pos hε q)
    exact htend.eventually (eventually_le_rpow_of_isLittleO hGHMo)
  -- the a.s. regularity set
  set N : Set M.Ω := {ω | Continuous (M.curve ω) ∧
    (∀ a b : ℝ, a ≤ b → M.area ω (M.curve ω '' Icc a b) = ENNReal.ofReal (b - a)) ∧
    Function.Surjective (M.curve ω) ∧ Tendsto (M.curve ω) (cocompact ℝ) (cocompact ℂ) ∧
    NullOverlaps (M.curve ω)} with hN
  have hNc : M.P Nᶜ = 0 := by
    have hae : ∀ᵐ ω ∂M.P, ω ∈ N := by
      filter_upwards [M.ae_continuous_curve, M.ae_area_curve, hgeom] with ω h1 h2 h3
      exact ⟨h1, h2, h3⟩
    exact ae_iff.mp hae
  set C₀ : ℝ := max C₁ 0 + max C₂ 0 * 2 ^ β + 2 ^ (α / q) with hC₀
  -- the bound for small `ε`
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (ε ^ (-ζ)) < ((degreeOut ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)} ≤
        ENNReal.ofReal (C₀ * ε ^ α) := by
    filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsGT_zero one_pos,
      eventually_rpow_lt hq0 (show (0 : ℝ) < (1 - ρ) / 8 by linarith [hρ.2]),
      eventually_rpow_lt hp0 (show (0 : ℝ) < 1 / 2 by norm_num),
      eventually_rpow_lt (show (0 : ℝ) < ζ / 2 by linarith [hζ.1]) (show (0 : ℝ) < 1 / 16 by norm_num),
      hGHMev] with ε hε0 hε1 hεq hεp hεζ hGHMε
    have hε0' : (0 : ℝ) < ε := hε0
    set δε : ℝ := 2 * ε ^ p with hδε
    have hδε0 : 0 < δε := mul_pos two_pos (Real.rpow_pos_of_pos hε0' p)
    have hδε1 : δε < 1 := by rw [hδε]; linarith
    set E1 : Set M.Ω := segmentDiamGood M ε q ρ
    set E2 : Set M.Ω := {ω | ∀ z ∈ ball (0 : ℂ) ρ, M.area ω (ball z δε) ≤ ENNReal.ofReal (δε ^ ξ₀)}
    set E3 : Set M.Ω := segmentBallEvent M 1 r (2 * ε ^ q)
    have hsub : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (ε ^ (-ζ)) < ((degreeOut ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)} ⊆
        E1ᶜ ∪ E2ᶜ ∪ E3ᶜ ∪ Nᶜ := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, hNω⟩ := hcon
      obtain ⟨hcont, harea, hsurj, htrans, hnull⟩ := hNω
      obtain ⟨z, hz, hlt⟩ := hω
      set c := M.curve ω
      set τ := hitTime c z
      have hτ : c τ = z := hitTime_spec hcont htrans (hsurj z)
      have hτρ : c τ ∈ ball (0 : ℂ) ρ := hτ ▸ hz
      have hup : diam (locWindow ε c τ) ≤ 2 * ε ^ q :=
        diam_locWindow_le_two_mul hε0'.le (fun a b hab hmeet => h1 a b hab hmeet) hτρ
      have hlow : ε ^ p ≤ diam (locWindow ε c τ) := by
        refine pow_le_diam_locWindow hcont harea hε0' hε1 hξ0 hξ1 ?_
        have hm := h2 z hz
        rw [← hτ] at hm
        refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow_of_exponent_ge hδε0 hδε1.le (min_le_left _ _)
      have hbound := locDegOut_le_of_good hcont hnull hε0' hp0 hζ.1 hτρ hup
        (by linarith) hlow (fun δ hδ a b hab hsub1 hdiam => h3 δ hδ a b hab hsub1 hdiam)
      have h16 : 16 * ε ^ (-(ζ / 2)) ≤ ε ^ (-ζ) := by
        have hpos : 0 < ε ^ (ζ / 2) := Real.rpow_pos_of_pos hε0' _
        have hsplit : ε ^ (-ζ) = ε ^ (-(ζ / 2)) * ε ^ (-(ζ / 2)) := by
          rw [← Real.rpow_add hε0']; ring_nf
        have hinv : ε ^ (-(ζ / 2)) = (ε ^ (ζ / 2))⁻¹ := Real.rpow_neg hε0'.le _
        have h16' : 16 ≤ ε ^ (-(ζ / 2)) := by
          rw [hinv, le_inv_comm₀ (by norm_num) hpos]; linarith
        rw [hsplit]
        nlinarith [Real.rpow_pos_of_pos hε0' (-(ζ / 2))]
      exact absurd (hbound.trans (ENNReal.ofReal_le_ofReal h16)) (not_le.mpr hlt)
    -- the measure bound
    have hP1 : M.P E1ᶜ ≤ ENNReal.ofReal (max C₁ 0 * ε ^ α) := by
      refine (hC₁ ε ⟨hε0', hε1⟩).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : ε ^ α₁ ≤ ε ^ α := Real.rpow_le_rpow_of_exponent_ge hε0' hε1.le (min_le_left _ _)
      calc C₁ * ε ^ α₁ ≤ max C₁ 0 * ε ^ α₁ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε0'.le _)
        _ ≤ max C₁ 0 * ε ^ α := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    have hP2 : M.P E2ᶜ ≤ ENNReal.ofReal (max C₂ 0 * 2 ^ β * ε ^ α) := by
      have hset : E2ᶜ = {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (δε ^ ξ₀) < M.area ω (ball z δε)} := by
        ext ω; simp [E2, not_le]
      rw [hset]
      refine (hC₂ δε ⟨hδε0, hδε1⟩).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : δε ^ β = 2 ^ β * ε ^ (p * β) := two_mul_rpow_rpow hε0'
      have h2 : ε ^ (p * β) ≤ ε ^ α := Real.rpow_le_rpow_of_exponent_ge hε0' hε1.le (min_le_right _ _)
      rw [h1]
      calc C₂ * (2 ^ β * ε ^ (p * β)) ≤ max C₂ 0 * (2 ^ β * ε ^ (p * β)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C₂ 0 * (2 ^ β * ε ^ α) := by gcongr
        _ = max C₂ 0 * 2 ^ β * ε ^ α := by ring
    have hP3 : M.P E3ᶜ ≤ ENNReal.ofReal (2 ^ (α / q) * ε ^ α) := by
      refine measure_le_ofReal_of_toReal_le (hGHMε.trans (le_of_eq ?_))
      rw [two_mul_rpow_rpow hε0', mul_div_cancel₀ _ hq0.ne']
    calc _ ≤ M.P (E1ᶜ ∪ E2ᶜ ∪ E3ᶜ ∪ Nᶜ) := measure_mono hsub
      _ ≤ M.P E1ᶜ + M.P E2ᶜ + M.P E3ᶜ + M.P Nᶜ := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (max C₁ 0 * ε ^ α) + ENNReal.ofReal (max C₂ 0 * 2 ^ β * ε ^ α) +
            ENNReal.ofReal (2 ^ (α / q) * ε ^ α) + 0 := by
          rw [hNc]; gcongr
      _ = ENNReal.ofReal (C₀ * ε ^ α) := by
          have hεα : 0 ≤ ε ^ α := Real.rpow_nonneg hε0'.le _
          rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity), hC₀]
          congr 1; ring
  exact exists_bound_of_eventually (fun _ => prob_le_one) hev

end MatedCRTHarmonic.GMS4b
