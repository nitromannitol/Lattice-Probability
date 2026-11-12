/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18S3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18S2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17

/-!
# DG:1593–1595: P3.17 in `𝕊(1)` coordinates for a whole-plane GFF (task P2-DG105s, P-118d)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, DG:1593–1595 (P3.17 is
transferred to the whole-plane GFF "as in" DG:1774–1777) and DG Lemma 2.2. Same route as
`r18_unit` (S3P18R4), for the lower event `{δ^{λ+ζ} ≤ D^δ(K, ∂U)}`:

* the reference coupling is that of `dgProp3_17_of` (`IsDGCoupling`, D118 version clause on
  `𝕊(1/2) ⊇ 𝕊`); the event is a function of the field on `Ū ⊆ 𝕊 = r18X 0 1` with the comparison
  property (`t18_cmp_p17`), so `r18_transfer` moves it to the zero-boundary part `hz` of the L2.2
  split `h = 𝔥 + hz` of a normalized whole-plane GFF;
* off `{max_{𝕊(1/2)} |𝔥| > A}`, `A = (ζ/2ξ) log δ⁻¹`, `D_{H_δ − 𝔥} ≤ e^{ξA} D_{H_δ}`
  (`s17_cmp`, the comparison with the roles exchanged), so `D_{H_δ} ≥ δ^{ζ/2} δ^{λ+ζ/2}`.

* **`r17_unit`**: `R17Unit` from the coupling of `dgProp3_17_of`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise SupTail

/-- the output of the lower analogue of `r18_unit`: P3.17 in `𝕊(1)` coordinates for every
normalized whole-plane GFF with a continuous version of its circle averages -/
def R17Unit : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC},
    IsNormalizedWPGFF h P → ∀ {H : ℝ → ℂ → Ω → ℝ},
    (∀ r, 0 < r → ∀ ω, Continuous fun z => H r z ω) →
    (∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z) →
    ∀ K U : Set ℂ, IsCompact K → IsOpen U → K ⊆ U → U ⊆ closedUnitSquare →
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
        p17SetDist (xiGamma γ) (fun x => H δ x ω) K U} ≤ ENNReal.ofReal (C * δ ^ p)

lemma s17_X01_eq : r18X 0 1 = closedUnitSquare := by
  ext x; simp [r18X, closedUnitSquare, and_assoc]

lemma s17_X01_half : r18X 0 1 ⊆ sqHalf := by
  rw [s17_X01_eq, ← p18Half_eq_sqHalf]; exact closedUnitSquare_sub_p18Half

/-- the comparison of `t18_cmp_p17` without measurability of the smaller field -/
lemma s17_cmp {ξ : ℝ} (hξ : 0 ≤ ξ) (K U : Set ℂ) {φ ψ : ℂ → ℝ} (hψ : Measurable ψ) {B : ℝ}
    (hB : ∀ x ∈ closure U, |ψ x| ≤ B) {η : ℝ} (hφψ : ∀ x ∈ closure U, φ x ≤ ψ x + η) :
    p17SetDist ξ φ K U ≤ ENNReal.ofReal (Real.exp (ξ * η)) * p17SetDist ξ ψ K U := by
  have h0 : ENNReal.ofReal (Real.exp (ξ * η)) ≠ 0 := by simp [Real.exp_pos]
  simp only [p17SetDist]
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun z => iInf_mono fun _ => iInf_mono fun w => iInf_mono fun _ =>
    iInf_mono fun q => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (t18_lfppLength_le_meas hξ hψ hB hφψ q.2)

/-- `p17SetDist` only depends on the field on `X ⊇ Ū` -/
lemma s17_loc (ξ : ℝ) (K U X : Set ℂ) (hUX : closure U ⊆ X) (φ ψ : ℂ → ℝ) (h : EqOn φ ψ X) :
    p17SetDist ξ φ K U = p17SetDist ξ ψ K U := by
  simp only [p17SetDist]
  refine iInf_congr fun z => iInf_congr fun _ => iInf_congr fun w => iInf_congr fun _ =>
    iInf_congr fun q => ?_
  congr 1
  unfold LQGDimension.lfppLength
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [h (hUX (q.2.mapsTo ht))]

/-- **DG:1593–1595, P3.17 in `𝕊(1)` coordinates for a whole-plane GFF** -/
theorem r17_unit (hR : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hz : Ω → DistC) (hc : ℝ → ℂ → Ω → ℝ), IsDGCoupling P W hz hc ∧
      ∀ γ : ℝ, 0 < γ → γ < 2 → DGP317For P hc γ) : R17Unit := by
  intro γ hγ hγ2 Ω _ P h hh H hHc hH K U hK hU hKU hUS ζ hζ
  have := hh.1.gaussian.isProbabilityMeasure
  obtain ⟨Ω₁, _, P₁, W₁, hz₁, hc₁, hcpl, h317⟩ := hR
  obtain ⟨hζ0, hζ1⟩ := hζ
  obtain ⟨p, C, δ₁, hp, hδ₁, hb⟩ :=
    h317 γ hγ hγ2 K U hK hU hKU hUS (ζ / 2) ⟨by positivity, by linarith⟩
  obtain ⟨hh', hz, hsum, hharm, hZ, a₀, a₁, ha₁, htail⟩ :=
    L22T.dg_lemma22_tr hh r18_sqOne_bdd r18_p18Half_compact
      (fun x hx => r18_ball_sqOne hx (by norm_num : (0 : ℝ) < 1 / 2) (mem_closedBall_self le_rfl))
  set ξ := xiGamma γ with hξ
  have hξ0 : 0 < ξ := xiGamma_pos hγ
  set κ := ζ / (2 * ξ) with hκ
  have hκ0 : 0 < κ := by positivity
  set δ₂ := Real.exp (-(1 / (a₁ * κ ^ 2))) with hδ₂
  have hUX : U ⊆ r18X 0 1 := s17_X01_eq ▸ hUS
  have hcl : closure U ⊆ r18X 0 1 := by
    refine closure_minimal hUX ?_
    rw [s17_X01_eq]; exact p17_isClosed_sq
  have hXsq : ∀ x ∈ r18X 0 1, x ∈ p18Half := fun x hx =>
    closedUnitSquare_sub_p18Half (s17_X01_eq ▸ hx)
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
  have hczc : ∀ ω, ContinuousOn (fun x => hcz x ω) (r18X 0 1) := fun ω => by
    refine (hHc δ hδ0 ω).continuousOn.sub ((r18G_continuousOn _ hh' ω).mono fun x hx => ?_)
    exact r18_ball_sqOne (hXsq x hx) (by norm_num : (0 : ℝ) < 1 / 2) (mem_closedBall_self le_rfl)
  have hczv : ∀ x ∈ r18X 0 1, hcz x =ᵐ[P] fun ω => circleAvg (hz ω) δ x := fun x hx =>
    r18_ae_version hh hH hsum hharm hδ0 (by linarith : δ < 1 / 9)
      (r18_ball_sqOne (hXsq x hx) (by norm_num))
  have hc₁c : ∀ ω, ContinuousOn (fun x => hc₁ δ x ω) (r18X 0 1) := fun ω =>
    (hcpl.2.2.2.1 δ hδI ω).mono s17_X01_half
  have hc₁v : ∀ x ∈ r18X 0 1,
      (fun ω => hc₁ δ x ω) =ᵐ[P₁] fun ω => circleAvg (hz₁ ω) δ x := fun x hx =>
    hcpl.2.2.2.2 δ hδI x (s17_X01_half hx)
  set t := δ ^ (dgLambda γ + ζ / 2) with ht
  -- the transferred event
  have hF : T18Cmp ξ (r18X 0 1) (fun φ => p17SetDist ξ φ K U) :=
    fun φ ψ hφ hψ ⟨B, hB⟩ η hη hle => t18_cmp_p17 hξ0.le K U φ ψ hφ hψ
      ⟨B, fun x hx => hB x (hcl hx)⟩ η hη fun x hx => hle x (hcl hx)
  have hE₁ : P {ω | ¬ ENNReal.ofReal t ≤ p17SetDist ξ (fun x => hcz x ω) K U} ≤
      ENNReal.ofReal (C * δ ^ p) := by
    have e := r18_transfer (by norm_num) hF (s17_loc ξ K U _ hcl) Blueprint.sqOne hδ0
      (fun x hx => sphere_subset_closedBall.trans (r18_ball_sqOne (hXsq x hx) (by linarith)))
      hZ hcpl.2.2.1.1 hczc hc₁c hczv hc₁v {s | ¬ ENNReal.ofReal t ≤ s}
      (by exact measurableSet_Ici.compl)
    exact (le_of_eq e).trans (hb δ ⟨hδ0, hδ1⟩)
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
  have hexp : Real.exp (ξ * A) * δ ^ (dgLambda γ + ζ) = t := by
    have e1 : ξ * A = ζ / 2 * L := by
      rw [hA, hκ]; field_simp
    rw [e1, ht, hL, Real.log_inv, Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hδ0,
      ← Real.exp_add]
    congr 1; ring
  have hsub : {ω | ¬ ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
      p17SetDist ξ (fun x => H δ x ω) K U} ⊆
      {ω | ¬ ENNReal.ofReal t ≤ p17SetDist ξ (fun x => hcz x ω) K U} ∪ E₂ ∪ N := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h1' : ENNReal.ofReal t ≤ p17SetDist ξ (fun x => hcz x ω) K U := by
      by_contra hn; exact h1 hn
    have hg : ∃ g : ℂ → ℝ, HarmonicOnNhd g (Blueprint.sqOne : Set ℂ) ∧
        ∀ φ : TestOn Blueprint.sqOne, restrictTo Blueprint.sqOne (hh' ω) φ = ∫ x, g x * φ x := by
      by_contra hn; exact h3 hn
    have hs := r18G_spec hg
    have hGA : ∀ x ∈ p18Half, |r18G Blueprint.sqOne hh' ω x| ≤ A := fun x hx => by
      by_contra hn
      exact h2 ⟨_, hs.1, hs.2, x, hx, not_le.1 hn⟩
    obtain ⟨B, hB⟩ := r18_p18Half_compact.exists_bound_of_continuousOn
      (hHc δ hδ0 ω).continuousOn
    have hcmp := s17_cmp hξ0.le K U (φ := fun x => hcz x ω) (ψ := fun x => H δ x ω)
      (hHc δ hδ0 ω).measurable (B := B)
      (fun x hx => by rw [← Real.norm_eq_abs]; exact hB x (hXsq x (hcl hx))) (η := A)
      (fun x hx => by
        have := (abs_le.1 (hGA x (hXsq x (hcl hx)))).1
        simp only [hhcz]; linarith)
    apply hω
    have hE : ENNReal.ofReal (Real.exp (ξ * A)) ≠ 0 := by simp [Real.exp_pos]
    rw [← ENNReal.mul_le_mul_iff_right hE ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul
      (Real.exp_pos _).le, hexp]
    exact h1'.trans hcmp
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
  calc P _ ≤ P ({ω | ¬ ENNReal.ofReal t ≤ p17SetDist ξ (fun x => hcz x ω) K U} ∪ E₂ ∪ N) :=
        measure_mono hsub
    _ ≤ P {ω | ¬ ENNReal.ofReal t ≤ p17SetDist ξ (fun x => hcz x ω) K U} + P E₂ + P N :=
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

end LQGMetric.DG
