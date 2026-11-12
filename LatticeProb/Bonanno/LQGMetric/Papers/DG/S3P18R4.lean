/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18R4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18R3

/-!
# DG:1774–1777: P3.22 in `𝕊(1)` coordinates for a whole-plane GFF, assembly (task P2-DG105q)

* `r18P322_of` — `R18P322` from the reference coupling of `dgLem37V_exists_box` with the side
  facts on `p18Half` (handoff/P2-DG105m.md §6) and the L3.11 / L3.19 inputs of
  `dg_prop322_sqOne_muHat`;
* **`r18_unit`** — DG:1776 "the same is true with a whole-plane GFF": for a normalized whole-plane
  GFF `h` with continuous circle averages `H`,
  `P{¬ ∀ z, w ∈ 𝕊, D_{H_δ}(z, w; 𝕊(1/2)) ≤ δ^{λ−ζ}} ≤ Cδ^p`. L2.2 (`L22T.dg_lemma22_tr`) and the
  law transfer `r18_transfer`; the harmonic part is bounded by `A = (ζ/2ξ) log δ⁻¹` on `𝕊(1/2)`
  off an event of probability `≤ a₀ e^{−a₁A²} ≤ a₀ δ`, and `D_{H_δ} ≤ e^{ξA} D_{H_δ − 𝔥}`
  (`p18_lfpp_compare`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise SupTail

/-- `e^{−a₁(κL)²} ≤ e^{−L}` for `L ≥ 1/(a₁κ²)` -/
lemma r18_tail_le {a₁ κ L : ℝ} (ha₁ : 0 < a₁) (hκ : 0 < κ) (hL : 1 / (a₁ * κ ^ 2) ≤ L) :
    Real.exp (-a₁ * (κ * L) ^ 2) ≤ Real.exp (-L) := by
  have h0 : 0 < a₁ * κ ^ 2 := by positivity
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have h1 : 1 ≤ a₁ * κ ^ 2 * L := by
    rw [div_le_iff₀ h0] at hL; linarith
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_le_mul_of_nonneg_left h1 hL0]

/-- **DG:1776, P3.22 in `𝕊(1)` coordinates for a whole-plane GFF** -/
theorem r18_unit (hR : R18P322) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    {H : ℝ → ℂ → Ω → ℝ} (hHc : ∀ r, 0 < r → ∀ ω, Continuous fun z => H r z ω)
    (hH : ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP (xiGamma γ) (fun x => H δ x ω) p18Half z w ≤ δ ^ (dgLambda γ - ζ)} ≤
        ENNReal.ofReal (C * δ ^ p) := by
  have := hh.1.gaussian.isProbabilityMeasure
  obtain ⟨Ω₁, _, P₁, hz₁, hc₁, hZ₁, hcont₁, hver₁, h322⟩ := hR
  obtain ⟨p, C, δ₁, hp, hδ₁, hb⟩ := h322 γ hγ hγ2 (ζ / 2) (by positivity)
  obtain ⟨hh', hz, hsum, hharm, hZ, a₀, a₁, ha₁, htail⟩ :=
    L22T.dg_lemma22_tr hh r18_sqOne_bdd r18_p18Half_compact
      (fun x hx => r18_ball_sqOne hx (by norm_num : (0 : ℝ) < 1 / 2) (mem_closedBall_self le_rfl))
  set ξ := xiGamma γ with hξ
  have hξ0 : 0 < ξ := xiGamma_pos hγ
  set κ := ζ / (2 * ξ) with hκ
  have hκ0 : 0 < κ := by positivity
  set δ₂ := Real.exp (-(1 / (a₁ * κ ^ 2))) with hδ₂
  refine ⟨min p 1, |C| + |a₀|, min δ₁ (min (1 / 9) δ₂), lt_min hp one_pos,
    lt_min hδ₁ (lt_min (by norm_num) (Real.exp_pos _)), fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδ1 : δ < δ₁ := hδlt.trans_le (min_le_left _ _)
  have hδ9 : δ < 1 / 9 := hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδδ₂ : δ < δ₂ := hδlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδI : δ ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hδ0, by linarith⟩
  set L := Real.log δ⁻¹ with hL
  have hLge : 1 / (a₁ * κ ^ 2) ≤ L := by
    rw [hL, Real.log_inv, le_neg]
    have := Real.log_lt_log hδ0 hδδ₂
    rw [hδ₂, Real.log_exp] at this
    linarith
  set A := κ * L with hA
  have hA0 : 0 ≤ A := mul_nonneg hκ0.le (le_trans (by positivity) hLge)
  -- the field `H_δ − 𝔥`
  set hcz : ℂ → Ω → ℝ := fun x ω => H δ x ω - r18G Blueprint.sqOne hh' ω x with hhcz
  have hczc : ∀ ω, ContinuousOn (fun x => hcz x ω) (r18X (-1 / 2) (3 / 2)) := fun ω => by
    refine (hHc δ hδ0 ω).continuousOn.sub ((r18G_continuousOn _ hh' ω).mono fun x hx => ?_)
    rw [← r18_p18Half_eq] at hx
    exact r18_ball_sqOne hx (by norm_num : (0 : ℝ) < 1 / 2) (mem_closedBall_self le_rfl)
  have hczv : ∀ x ∈ r18X (-1 / 2) (3 / 2),
      hcz x =ᵐ[P] fun ω => circleAvg (hz ω) δ x := fun x hx => by
    rw [← r18_p18Half_eq] at hx
    exact r18_ae_version hh hH hsum hharm hδ0 (by linarith : δ < 1 / 9)
      (r18_ball_sqOne hx (by norm_num))
  have hc₁c : ∀ ω, ContinuousOn (fun x => hc₁ δ x ω) (r18X (-1 / 2) (3 / 2)) := fun ω => by
    rw [← r18_p18Half_eq]; exact hcont₁ δ hδI ω
  have hc₁v : ∀ x ∈ r18X (-1 / 2) (3 / 2),
      (fun ω => hc₁ δ x ω) =ᵐ[P₁] fun ω => circleAvg (hz₁ ω) δ x := fun x hx => by
    rw [← r18_p18Half_eq] at hx; exact hver₁ δ hδI x hx
  set t := δ ^ (dgLambda γ - ζ / 2) with ht
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hδ0 _).le
  -- the transferred event
  have hE₁ : P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
      dgLFPP ξ (fun x => hcz x ω) p18Half z w ≤ t} ≤ ENNReal.ofReal (C * δ ^ p) := by
    have e : ∀ {Ω₀ : Type} (k : ℂ → Ω₀ → ℝ),
        {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
          dgLFPP ξ (fun x => k x ω) p18Half z w ≤ t} =
        {ω | r18F ξ closedUnitSquare (r18X (-1 / 2) (3 / 2)) (fun x => k x ω) ∈
          {s | ¬ s ≤ ENNReal.ofReal t}} := fun k => by
      ext ω
      simp only [mem_ofPred_eq, ← r18_p18Half_eq]
      rw [r18_diam_iff ht0]
    rw [e hcz, r18_transfer (by norm_num) (r18_cmp_diam hξ0.le _ _) (r18_loc_diam ξ _ _)
      Blueprint.sqOne hδ0 (fun x hx => by
        rw [← r18_p18Half_eq] at hx
        exact sphere_subset_closedBall.trans (r18_ball_sqOne hx (by linarith)))
      hZ hZ₁ hczc hc₁c hczv hc₁v {s | ¬ s ≤ ENNReal.ofReal t} (by exact measurableSet_Iic.compl),
      ← e (fun x ω => hc₁ δ x ω)]
    exact hb δ ⟨hδ0, hδ1⟩
  -- the harmonic event
  set E₂ := {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g (Blueprint.sqOne : Set ℂ) ∧
      (∀ φ : TestOn Blueprint.sqOne, restrictTo Blueprint.sqOne (hh' ω) φ = ∫ x, g x * φ x) ∧
      ∃ z ∈ p18Half, A < |g z|}
  have hE₂ : P E₂ ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ * A ^ 2)) := htail A hA0
  set N := {ω | ¬ ∃ g : ℂ → ℝ, HarmonicOnNhd g (Blueprint.sqOne : Set ℂ) ∧
      ∀ φ : TestOn Blueprint.sqOne, restrictTo Blueprint.sqOne (hh' ω) φ = ∫ x, g x * φ x}
  have hN : P N = 0 := by
    have := hharm
    rw [ae_iff] at this
    exact this
  -- inclusion
  have hexp : Real.exp (ξ * A) * t = δ ^ (dgLambda γ - ζ) := by
    have e1 : ξ * A = ζ / 2 * L := by
      rw [hA, hκ]; field_simp
    rw [e1, ht, hL, Real.log_inv, Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hδ0,
      ← Real.exp_add]
    congr 1; ring
  have hsub : {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
      dgLFPP ξ (fun x => H δ x ω) p18Half z w ≤ δ ^ (dgLambda γ - ζ)} ⊆
      {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP ξ (fun x => hcz x ω) p18Half z w ≤ t} ∪ E₂ ∪ N := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h1' : ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP ξ (fun x => hcz x ω) p18Half z w ≤ t := by
      by_contra hn; exact h1 hn
    have hg : ∃ g : ℂ → ℝ, HarmonicOnNhd g (Blueprint.sqOne : Set ℂ) ∧
        ∀ φ : TestOn Blueprint.sqOne, restrictTo Blueprint.sqOne (hh' ω) φ = ∫ x, g x * φ x := by
      by_contra hn; exact h3 hn
    have hs := r18G_spec hg
    have hGA : ∀ x ∈ p18Half, |r18G Blueprint.sqOne hh' ω x| ≤ A := fun x hx => by
      by_contra hn
      exact h2 ⟨_, hs.1, hs.2, x, hx, not_le.1 hn⟩
    apply hω
    intro z hz w hw
    have hcmp := p18_lfpp_compare hξ0.le (φ := fun x => H δ x ω) (ψ := fun x => hcz x ω)
      (S := p18Half) (a := A) (by rw [r18_p18Half_eq]; exact hczc ω)
      (fun x hx => by
        have := (abs_le.1 (hGA x hx)).2
        simp only [hhcz]; linarith) z w
    calc dgLFPP ξ (fun x => H δ x ω) p18Half z w
        ≤ Real.exp (ξ * A) * dgLFPP ξ (fun x => hcz x ω) p18Half z w := hcmp
      _ ≤ Real.exp (ξ * A) * t :=
          mul_le_mul_of_nonneg_left (h1' z hz w hw) (Real.exp_pos _).le
      _ = δ ^ (dgLambda γ - ζ) := hexp
  -- the bound
  have htailδ : a₀ * Real.exp (-a₁ * A ^ 2) ≤ |a₀| * δ := by
    have h1 : Real.exp (-a₁ * A ^ 2) ≤ δ := by
      have h2 : Real.exp (-L) = δ := by rw [hL, Real.log_inv, neg_neg, Real.exp_log hδ0]
      exact (r18_tail_le ha₁ hκ0 hLge).trans h2.le
    calc a₀ * Real.exp (-a₁ * A ^ 2) ≤ |a₀| * Real.exp (-a₁ * A ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |a₀| * δ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hpow1 : δ ^ p ≤ δ ^ min p 1 :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith) (min_le_left _ _)
  have hpow2 : δ ≤ δ ^ min p 1 := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith : δ ≤ 1) (min_le_right p 1)
    rwa [Real.rpow_one] at this
  calc P _ ≤ P ({ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP ξ (fun x => hcz x ω) p18Half z w ≤ t} ∪ E₂ ∪ N) := measure_mono hsub
    _ ≤ P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP ξ (fun x => hcz x ω) p18Half z w ≤ t} + P E₂ + P N :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ENNReal.ofReal (C * δ ^ p) + ENNReal.ofReal (|a₀| * δ) + 0 := by
        rw [hN]
        gcongr
        exact hE₂.trans (ENNReal.ofReal_le_ofReal htailδ)
    _ ≤ ENNReal.ofReal ((|C| + |a₀|) * δ ^ min p 1) := by
        rw [add_zero]
        have hdp : 0 ≤ δ ^ p := (Real.rpow_pos_of_pos hδ0 _).le
        refine (add_le_add (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_abs_self C) hdp)) le_rfl).trans ?_
        rw [← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hdp)
          (mul_nonneg (abs_nonneg _) hδ0.le)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left hpow1 (abs_nonneg C)
        have := mul_le_mul_of_nonneg_left hpow2 (abs_nonneg a₀)
        nlinarith

/-- the output of `r18_unit`: P3.22 in `𝕊(1)` coordinates for every normalized whole-plane GFF
with a continuous version of its circle averages (input of the scaling step DG:1775) -/
def R18Unit : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC},
    IsNormalizedWPGFF h P → ∀ {H : ℝ → ℂ → Ω → ℝ}, (∀ r, 0 < r → ∀ ω, Continuous fun z => H r z ω) →
    (∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z) →
    ∀ ζ : ℝ, 0 < ζ → ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP (xiGamma γ) (fun x => H δ x ω) p18Half z w ≤ δ ^ (dgLambda γ - ζ)} ≤
        ENNReal.ofReal (C * δ ^ p)

theorem r18Unit_of (hR : R18P322) : R18Unit :=
  fun _ hγ hγ2 _ _ _ _ hh _ hHc hH _ hζ => r18_unit hR hγ hγ2 hh hHc hH hζ

end LQGMetric.DG
