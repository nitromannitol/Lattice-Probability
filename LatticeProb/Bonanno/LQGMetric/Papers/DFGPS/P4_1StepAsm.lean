/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1StepAsm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepAnn
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1Cov
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1Xi
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# DFGPS Proposition 4.1: Step 3, the assembly for a set satisfying the tube condition

DFGPS (Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
percolation*, arXiv:1905.00380), Proposition 4.1 (`prop-line-path`, T:2444–2451), proof Step 3
(T:2494–2511): on the event that all the annulus bounds of Step 1 hold (`ann_bound_general`, with
`A = ε^{-η/2}`, union bound over the `O(ε⁻¹)` centres) and that the circle-average sums of
Step 4 (`circSum_lower`, with `p − 2η` in place of `p`) are large for each of the finitely many
blocks, Step 2 (`tube_sum_le`) and Theorem 1.5 (`hscal`, `𝔠_{δ𝕣} ≥ δ^{ξQ+η/2} 𝔠_𝕣`) give
`D_h(u,v; B_{ε𝕣}(𝕣L)) ≥ ε^{p + ξQ − 1 − ξ²/2} 𝔠_𝕣 e^{ξ h_𝕣(0)}`; the exponent loss `η` is
chosen so that `(p−2η)²/(2ξ²) − ζ/4 ≥ p²/(2ξ²) − ζ/2` ("sending `ζ → 0`", T:2510).

The geometric input is `TubeBlocks L b` (Steps 2–3, T:2486–2490, T:2502).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS.P41

open Blueprint

lemma eventually_rpow_lt {a K : ℝ} (ha : 0 < a) (hK : 0 < K) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ a < K := by
  have h : Tendsto (fun x : ℝ => x ^ a) (𝓝 0) (𝓝 0) := by
    have := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
    rw [ContinuousAt, Real.zero_rpow ha.ne'] at this
    exact this
  exact (h.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hK)

/-- the exponent bookkeeping of Step 3 (T:2507–2509) -/
lemma expo_bound {ε η e a b' : ℝ} (hε : 0 < ε) (hη : ε ^ η ≤ (8 / 3 : ℝ) ^ (a + b'))
    (hab : a + b' = e - 3 * η / 2) :
    ε ^ e ≤ ε ^ (η / 2) * ((8 / 3 * ε) ^ a * (8 / 3 * ε) ^ b') := by
  have h83 : (0 : ℝ) < 8 / 3 := by norm_num
  rw [← Real.rpow_add (by positivity), Real.mul_rpow h83.le hε.le, hab]
  have h1 : ε ^ e = ε ^ η * ε ^ (e - η) := by rw [← Real.rpow_add hε]; ring_nf
  have h2 : ε ^ (η / 2) * ε ^ (e - 3 * η / 2) = ε ^ (e - η) := by
    rw [← Real.rpow_add hε]; ring_nf
  rw [h1, ← hab]
  calc ε ^ η * ε ^ (e - η) ≤ (8 / 3 : ℝ) ^ (a + b') * ε ^ (e - η) :=
        mul_le_mul_of_nonneg_right hη (by positivity)
    _ = ε ^ (η / 2) * ((8 / 3 : ℝ) ^ (a + b') * ε ^ (a + b')) := by
        rw [hab, ← h2]; ring

/-- **Step 3 on the good event** (T:2494–2509): if all annulus bounds hold at the centres of every
block and every block's circle-average sum is `≥ E`, then every pair `u, v` in the tube at
distance `≥ b𝕣` has internal distance `≥ X` whenever `X ≤ A⁻¹ 𝔠_s e^{ξ h_𝕣(0)} E`. -/
lemma good_event_bound {ξ : ℝ} {D : ContMetric} {c : ℝ → ℝ} (g : DistC) {L : Set ℂ}
    {b ε 𝕣 A E X : ℝ} {M : ℕ} (n : Fin M → ℕ) (w : (m : Fin M) → Fin (n m) → ℂ)
    (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hA : 0 < A) (hcs : 0 ≤ c (8 / 3 * ε * 𝕣))
    (hsep : ∀ m j k, j ≠ k → 9 * ε ≤ ‖w m j - w m k‖)
    (hgeo : ∀ u ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L),
        ∀ v ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L), b * 𝕣 ≤ ‖u - v‖ →
        ∀ γ : ℝ → ℂ, Continuous γ → γ 0 = u → γ 1 = v →
          γ '' Icc 0 1 ⊆ thickening (ε * 𝕣) (scaleSet 𝕣 0 L) →
          ∃ m : Fin M, (∀ k, 4 * (ε * 𝕣) < ‖u - 𝕣 * w m k‖) ∧
            ∀ k, ∃ t ∈ Icc (0 : ℝ) 1, ‖γ t - 𝕣 * w m k‖ ≤ 2 * (ε * 𝕣))
    (hann : ∀ m k, ENNReal.ofReal (A⁻¹ * scaleFac ξ c g (8 / 3 * ε * 𝕣) (𝕣 * w m k)) ≤
      setDistIn D (closedBall (𝕣 * w m k) (2 * (ε * 𝕣))) (sphere (𝕣 * w m k) (4 * (ε * 𝕣)))
        (ball (𝕣 * w m k) (16 / 3 * (ε * 𝕣))))
    (hsum : ∀ m, E ≤ ∑ k, Real.exp (ξ * (circleAvg g (8 / 3 * ε * 𝕣) (𝕣 * w m k) -
      circleAvg g 𝕣 0)))
    (hX : X ≤ A⁻¹ * c (8 / 3 * ε * 𝕣) * Real.exp (ξ * circleAvg g 𝕣 0) * E) :
    ∀ u ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L),
      ∀ v ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L), b * 𝕣 ≤ ‖u - v‖ →
        ENNReal.ofReal X ≤ D.internal (thickening (ε * 𝕣) (scaleSet 𝕣 0 L)) u v := by
  intro u hu v hv huv
  unfold ContMetric.internal MetricGeometry.internalEDist
  refine le_iInf fun γ' => ?_
  obtain ⟨γ', hγV⟩ := γ'
  obtain ⟨hs1, hs2, hs3, hs4⟩ := path_shadow D γ' hγV
  obtain ⟨m, hum, hmeet⟩ := hgeo u hu v hv huv _ hs1 hs2 hs3 hs4
  have hnorm : ∀ x y : ℂ, ‖(𝕣 : ℂ) * x - 𝕣 * y‖ = 𝕣 * ‖x - y‖ := by
    intro x y
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h𝕣.le]
  have hsep' : ∀ j k, j ≠ k → 9 * (ε * 𝕣) ≤ ‖(𝕣 : ℂ) * w m j - 𝕣 * w m k‖ := by
    intro j k hjk
    rw [hnorm]
    nlinarith [hsep m j k hjk]
  have ha0 : ∀ k, 0 ≤ A⁻¹ * scaleFac ξ c g (8 / 3 * ε * 𝕣) (𝕣 * w m k) := by
    intro k; unfold scaleFac; have := Real.exp_pos (ξ * circleAvg g (8 / 3 * ε * 𝕣) (𝕣 * w m k))
    positivity
  have key := tube_sum_le_path D (fun k => (𝕣 : ℂ) * w m k) (mul_pos hε h𝕣) hsep' hum γ'
    hmeet _ ha0 (hann m)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) key
  refine hX.trans ?_
  have hsplit : ∀ k, A⁻¹ * scaleFac ξ c g (8 / 3 * ε * 𝕣) (𝕣 * w m k) =
      A⁻¹ * c (8 / 3 * ε * 𝕣) * Real.exp (ξ * circleAvg g 𝕣 0) *
        Real.exp (ξ * (circleAvg g (8 / 3 * ε * 𝕣) (𝕣 * w m k) - circleAvg g 𝕣 0)) := by
    intro k
    unfold scaleFac
    rw [mul_assoc (A⁻¹ * c _), ← Real.exp_add]
    ring_nf
  simp only [hsplit, ← Finset.mul_sum]
  have : 0 ≤ A⁻¹ * c (8 / 3 * ε * 𝕣) * Real.exp (ξ * circleAvg g 𝕣 0) := by positivity
  exact mul_le_mul_of_nonneg_left (hsum m) this

lemma sum_fin_ofReal_const (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ _k : Fin n, ENNReal.ofReal x = ENNReal.ofReal (n * x) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- **DFGPS Proposition 4.1** (T:2444–2451) for a set `L` satisfying the tube condition
`TubeBlocks L b` (Steps 2–3), from DFGPS Prop 3.1 (Step 1), Theorem 1.5 (`hscal`) and
`ξ < 1` (`hXQ`, T:2531). -/
theorem prop4_1_of_tube (h31 : Prop3_1) (hscal : DFGPSScaling) (hXQ : GMXiQBound)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {L : Set ℂ} {b : ℝ} (hT : TubeBlocks L b) {p : ℝ} (hp : 0 < p)
    {ζ : ℝ} (hζ : 0 < ζ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
          P (h ⁻¹' {g : DistC | ∀ u ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L),
              ∀ v ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L), b * 𝕣 ≤ ‖u - v‖ →
              ENNReal.ofReal (ε ^ (p + xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2) *
                  scaleFac (xiGamma γ) c g 𝕣 0) ≤
                (D g).internal (thickening (ε * 𝕣) (scaleSet 𝕣 0 L)) u v})ᶜ ≤
            ENNReal.ofReal (ε ^ (p ^ 2 / (2 * xiGamma γ ^ 2) - ζ)) := by
  have hξ0 : 0 < xiGamma γ := DG.xiGamma_pos hγ0
  have hξ1 : xiGamma γ < 1 := xiGamma_lt_one hXQ hγ0 hγ2
  set ξ := xiGamma γ with hξdef
  obtain ⟨κ, K, c₀, R, ε₁, M, hκ, hc₀, hR, hε₁, hTε⟩ := hT
  set η := min (p / 4) (ζ * ξ ^ 2 / (8 * p)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηp : η ≤ p / 4 := min_le_left _ _
  have hηζ : η ≤ ζ * ξ ^ 2 / (8 * p) := min_le_right _ _
  set p' := p - 2 * η with hp'
  have hp'0 : 0 < p' := by linarith
  set T := p ^ 2 / (2 * ξ ^ 2) - ζ with hTdef
  set T' := p' ^ 2 / (2 * ξ ^ 2) - ζ / 4 with hT'def
  have hTT : T + ζ / 2 ≤ T' := by
    have h1 : p ^ 2 - p' ^ 2 ≤ ζ * ξ ^ 2 / 2 := by
      have : p ^ 2 - p' ^ 2 ≤ 4 * p * η := by rw [hp']; nlinarith
      have h2 : 4 * p * η ≤ 4 * p * (ζ * ξ ^ 2 / (8 * p)) :=
        mul_le_mul_of_nonneg_left hηζ (by positivity)
      have h3 : 4 * p * (ζ * ξ ^ 2 / (8 * p)) = ζ * ξ ^ 2 / 2 := by field_simp; ring
      linarith
    have hξ2 : 0 < 2 * ξ ^ 2 := by positivity
    rw [hTdef, hT'def]
    have : p ^ 2 / (2 * ξ ^ 2) - p' ^ 2 / (2 * ξ ^ 2) ≤ ζ / 4 := by
      rw [← sub_div, div_le_iff₀ hξ2]; nlinarith
    linarith
  set p₁ := (|T| + 2) / (η / 2) with hp₁def
  have hp₁ : 0 < p₁ := by positivity
  obtain ⟨Ca, A₀, hAnn⟩ := ann_bound_general h31 hγ0 hγ2 hD p₁ hp₁
  obtain ⟨δ₀, hδ₀, hsc⟩ := hscal γ hγ0 hγ2 D c hD (η / 2) (by positivity)
  obtain ⟨εc, hεc, hcs⟩ := circSum_lower (κ := 8 / 3 * κ) (R := R) (c := 3 / 8 * c₀) (p := p')
    (ζ := ζ / 4) hξ0 hξ1 (by positivity) hR (by positivity) hp'0 (by positivity)
  set E := ξ * Q γ + η / 2 + (p' - 1 - ξ ^ 2 / 2) with hEdef
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A₀ < ε ^ (-(η / 2)) ∧ ε ^ η < (8 / 3 : ℝ) ^ E ∧
      ε ^ (ζ / 2) < 1 / (2 * (M * (8 / 3 : ℝ) ^ T' + 1)) :=
    ((tendsto_rpow_neg_nhdsGT_zero (by linarith : -(η / 2) < 0)).eventually_gt_atTop A₀).and
      ((eventually_rpow_lt hη (by positivity)).and (eventually_rpow_lt (by positivity)
        (by positivity)))
  obtain ⟨ε₂, hε₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hε₂0 : 0 < ε₂ := hε₂
  set B := 1 / (2 * (M * |K| * |Ca| + 1)) with hBdef
  have hB : 0 < B := by positivity
  refine ⟨min (min ε₂ ε₁) (min 1 (min (3 / 8 * εc) (min (3 / 8 * δ₀) B))), by positivity, ?_⟩
  intro Ω _ P _ h hh ε hε 𝕣 h𝕣
  obtain ⟨hε0, hεlt⟩ := hε
  simp only [lt_min_iff] at hεlt
  obtain ⟨⟨hεε₂, hεε₁⟩, hε1, hεc', hεδ', hεB⟩ := hεlt
  obtain ⟨hAA₀, hεη, hεζ⟩ := hsub ⟨hε0, hεε₂⟩
  obtain ⟨n, w, hn, hwR, hwsep, hgeo⟩ := hTε ε ⟨hε0, hεε₁⟩
  set A := ε ^ (-(η / 2)) with hAdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos hε0 _
  have hAinv : A⁻¹ = ε ^ (η / 2) := by rw [hAdef, Real.rpow_neg hε0.le, inv_inv]
  set s := 8 / 3 * ε * 𝕣 with hsdef
  have hs : 0 < s := by positivity
  have hc𝕣 : 0 < c 𝕣 := hD.tightness.1 𝕣 h𝕣
  have hcs0 : 0 < c s := hD.tightness.1 s hs
  set Ann : (m : Fin M) → Fin (n m) → Set Ω := fun m k =>
    {ω | ENNReal.ofReal (A⁻¹ * scaleFac ξ c (h ω) s (𝕣 * w m k)) ≤
      setDistIn (D (h ω)) (closedBall (𝕣 * w m k) (3 / 4 * s)) (sphere (𝕣 * w m k) (3 / 2 * s))
        (ball (𝕣 * w m k) (2 * s))}ᶜ with hAnndef
  set Sm : Fin M → Set Ω := fun m =>
    {ω | ∑ k, Real.exp (ξ * (circleAvg (h ω) (8 / 3 * ε * 𝕣) (𝕣 * w m k) -
      circleAvg (h ω) 𝕣 0)) < (8 / 3 * ε) ^ (p' - 1 - ξ ^ 2 / 2)} with hSmdef
  have hincl : (h ⁻¹' {g : DistC | ∀ u ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L),
      ∀ v ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 L), b * 𝕣 ≤ ‖u - v‖ →
      ENNReal.ofReal (ε ^ (p + ξ * Q γ - 1 - ξ ^ 2 / 2) * scaleFac ξ c g 𝕣 0) ≤
        (D g).internal (thickening (ε * 𝕣) (scaleSet 𝕣 0 L)) u v})ᶜ ⊆
      (⋃ m, ⋃ k, Ann m k) ∪ ⋃ m, Sm m := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hc
    apply hω
    have e1 : 3 / 4 * s = 2 * (ε * 𝕣) := by rw [hsdef]; ring
    have e2 : 3 / 2 * s = 4 * (ε * 𝕣) := by rw [hsdef]; ring
    have e3 : 2 * s = 16 / 3 * (ε * 𝕣) := by rw [hsdef]; ring
    refine good_event_bound (ξ := ξ) (E := (8 / 3 * ε) ^ (p' - 1 - ξ ^ 2 / 2)) (h ω) n w hε0 h𝕣 hA0 hcs0.le (fun m j k hjk => (hwsep m j k hjk).1)
      (hgeo 𝕣 h𝕣) (fun m k => ?_) (fun m => ?_) ?_
    · have := hc.1 m k
      simp only [hAnndef, mem_compl_iff, not_not, mem_setOf_eq] at this
      rw [e1, e2, e3] at this
      exact this
    · have := hc.2 m
      simp only [hSmdef, mem_setOf_eq, not_lt] at this
      exact this
    · -- the exponent bookkeeping
      have hscl := (hsc (8 / 3 * ε) ⟨by positivity, by linarith only [hεδ']⟩ 𝕣 h𝕣).1
      rw [le_div_iff₀ hc𝕣] at hscl
      have hexp := expo_bound (e := p + ξ * Q γ - 1 - ξ ^ 2 / 2) (a := ξ * Q γ + η / 2)
        (b' := p' - 1 - ξ ^ 2 / 2) hε0 hεη.le (by rw [hp']; ring)
      have hX0 : 0 < Real.exp (ξ * circleAvg (h ω) 𝕣 0) := Real.exp_pos _
      unfold scaleFac
      rw [hAinv]
      have hb0 : 0 ≤ (8 / 3 * ε) ^ (p' - 1 - ξ ^ 2 / 2) := by positivity
      calc ε ^ (p + ξ * Q γ - 1 - ξ ^ 2 / 2) * (c 𝕣 * Real.exp (ξ * circleAvg (h ω) 𝕣 0))
          ≤ ε ^ (η / 2) * ((8 / 3 * ε) ^ (ξ * Q γ + η / 2) *
              (8 / 3 * ε) ^ (p' - 1 - ξ ^ 2 / 2)) *
              (c 𝕣 * Real.exp (ξ * circleAvg (h ω) 𝕣 0)) :=
            mul_le_mul_of_nonneg_right hexp (by positivity)
        _ = ε ^ (η / 2) * ((8 / 3 * ε) ^ (ξ * Q γ + η / 2) * c 𝕣) *
              Real.exp (ξ * circleAvg (h ω) 𝕣 0) * (8 / 3 * ε) ^ (p' - 1 - ξ ^ 2 / 2) := by ring
        _ ≤ ε ^ (η / 2) * c s * Real.exp (ξ * circleAvg (h ω) 𝕣 0) *
              (8 / 3 * ε) ^ (p' - 1 - ξ ^ 2 / 2) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ?_ (by positivity)) hX0.le) hb0
            rw [hsdef]; exact hscl
  -- probability bounds
  have hAnnP : ∀ m k, P (Ann m k) ≤ ENNReal.ofReal (|Ca| * ε ^ (|T| + 2)) := by
    intro m k
    refine (hAnn A hAA₀ P h hh s hs (𝕣 * w m k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : A ^ (-p₁) = ε ^ (|T| + 2) := by
      rw [hAdef, ← Real.rpow_mul hε0.le, hp₁def]
      congr 1
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hSmP : ∀ m, P (Sm m) ≤ ENNReal.ofReal ((8 / 3 * ε) ^ T') := by
    intro m
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    refine hcs (8 / 3 * ε) ⟨by positivity, by linarith only [hεc']⟩ P h hh.1 𝕣 h𝕣 (n m)
      (fun k => (𝕣 : ℂ) * w m k) ?_ ?_ ?_
    · have := (hn m).1
      calc 8 / 3 * κ / (8 / 3 * ε) = κ / ε := by field_simp
        _ ≤ n m := this
    · intro k
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h𝕣.le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hwR m k) h𝕣.le
    · intro j k hjk
      have hnorm : ‖(𝕣 : ℂ) * w m j - 𝕣 * w m k‖ = 𝕣 * ‖w m j - w m k‖ := by
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h𝕣.le]
      rw [hnorm]
      obtain ⟨h9, hcn⟩ := hwsep m j k hjk
      constructor
      · have h1 := mul_le_mul_of_nonneg_left h9 h𝕣.le
        have h2 := mul_pos hε0 h𝕣
        linarith only [h1, h2]
      · have : 3 / 8 * c₀ * (8 / 3 * ε * 𝕣) * ((dN j k : ℝ) + 1) =
            𝕣 * (c₀ * ε * ((dN j k : ℝ) + 1)) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hcn h𝕣.le
  -- the two union bounds
  have hεT : 0 < ε ^ T := Real.rpow_pos_of_pos hε0 _
  have hpart1 : P (⋃ m, ⋃ k, Ann m k) ≤ ENNReal.ofReal (ε ^ T / 2) := by
    refine (measure_iUnion_fintype_le P _).trans ?_
    refine (Finset.sum_le_sum fun m _ => (measure_iUnion_fintype_le P _).trans
      (Finset.sum_le_sum fun k _ => hAnnP m k)).trans ?_
    simp only [sum_fin_ofReal_const _ (by positivity : 0 ≤ |Ca| * ε ^ (|T| + 2))]
    rw [← ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity]
    refine ENNReal.ofReal_le_ofReal ?_
    have hnK : ∀ m, (n m : ℝ) ≤ |K| / ε := fun m =>
      (hn m).2.trans (div_le_div_of_nonneg_right (le_abs_self K) hε0.le)
    have hx0 : 0 ≤ |Ca| * ε ^ (|T| + 2) := by positivity
    calc ∑ m, (n m : ℝ) * (|Ca| * ε ^ (|T| + 2))
        ≤ ∑ _m : Fin M, |K| / ε * (|Ca| * ε ^ (|T| + 2)) :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right (hnK m) hx0
      _ = M * |K| * |Ca| * ε ^ (|T| + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            show |T| + 2 = (|T| + 1) + 1 by ring, Real.rpow_add_one hε0.ne']
          field_simp
      _ ≤ M * |K| * |Ca| * (ε ^ T * ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Real.rpow_add_one hε0.ne']
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith only [le_abs_self T])
      _ ≤ ε ^ T / 2 := by
          have h1 : M * |K| * |Ca| * ε ≤ 1 / 2 := by
            have hden : 0 < 2 * (M * |K| * |Ca| + 1) := by positivity
            have := hεB
            rw [hBdef, lt_div_iff₀ hden] at this
            linarith only [this, hε0]
          have h2 := mul_le_mul_of_nonneg_left h1 hεT.le
          linarith only [h2]
  have hpart2 : P (⋃ m, Sm m) ≤ ENNReal.ofReal (ε ^ T / 2) := by
    refine (measure_iUnion_fintype_le P _).trans ?_
    refine (Finset.sum_le_sum fun m _ => hSmP m).trans ?_
    rw [sum_fin_ofReal_const _ (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.mul_rpow (by norm_num) hε0.le]
    have h1 : ε ^ T' ≤ ε ^ T * ε ^ (ζ / 2) := by
      rw [← Real.rpow_add hε0]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hTT
    have h2 : (M : ℝ) * (8 / 3 : ℝ) ^ T' * ε ^ (ζ / 2) ≤ 1 / 2 := by
      have hden : 0 < 2 * (M * (8 / 3 : ℝ) ^ T' + 1) := by positivity
      have := hεζ
      rw [lt_div_iff₀ hden] at this
      have h0 : 0 ≤ ε ^ (ζ / 2) := by positivity
      linarith only [this, h0]
    have h3 : 0 ≤ (M : ℝ) * (8 / 3 : ℝ) ^ T' := by positivity
    calc (M : ℝ) * ((8 / 3 : ℝ) ^ T' * ε ^ T') ≤ M * (8 / 3 : ℝ) ^ T' * (ε ^ T * ε ^ (ζ / 2)) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h1 h3
      _ = ε ^ T * (M * (8 / 3 : ℝ) ^ T' * ε ^ (ζ / 2)) := by ring
      _ ≤ ε ^ T * (1 / 2) := mul_le_mul_of_nonneg_left h2 hεT.le
      _ = ε ^ T / 2 := by ring
  calc _ ≤ P ((⋃ m, ⋃ k, Ann m k) ∪ ⋃ m, Sm m) := measure_mono hincl
    _ ≤ P (⋃ m, ⋃ k, Ann m k) + P (⋃ m, Sm m) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε ^ T / 2) + ENNReal.ofReal (ε ^ T / 2) := add_le_add hpart1 hpart2
    _ = ENNReal.ofReal (ε ^ T) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end LQGMetric.DFGPS.P41
