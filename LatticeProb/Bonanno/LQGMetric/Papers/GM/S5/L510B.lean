/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510A

/-!
# GM Lemma 5.10: choice of the parameters and the union bound (task P2-M2M5, D83 packet P6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.10 (`lem-geo-event-prob`, l. 3307–3335). GM choose, in this order and each with failure
probability `≤ q := (1 − 𝕡)/9` (GM: `(1 − 𝕡)/100` per condition), uniformly in `r`:
`Δ` and then `δ` (condition (4), l. 3308, here `gm_L510_setDist`, `gm_L510_near`); `b, ρ, ε₀, U`
from Lemma 5.8 with `p = 1 − q` (l. 3309–3311, conditions (1)–(3)); `A` (condition (5),
l. 3313–3320); `ζ` (condition (6), l. 3322); `a` (condition (7), l. 3324, `gm_L510_across`);
`θ` (condition (8), l. 3326, `gm_L510_near`); `M` (condition (9), l. 3329); the bumps and `Λ₀`
(condition (10), l. 3331–3333). `gm_L5_10_of_parts` is this argument; the union bound is the
subadditivity `P[linkEvent] ≤ P[E_r] + Σ P[condition i fails]` (no measurability needed).

Open inputs (hypotheses of `gm_L5_10_of_parts`):
* `L5_8`: GM Lemma 5.8 (l. 3045: "there exists a **deterministic** connected open set
  `U_r^{x,y}`", decision D92, with the attachment clause (T5) of D83 (c));
* `L510Diam` (condition (5): GM (5.33) from Lemma 2.9 = DFGPS Lemma 3.20, and the chaining over
  the squares of a connected square tube, l. 3313–3320);
* `L510Bdy` (condition (6): GM Lemma 2.10 = DFGPS Prop 4.1 and a union bound over the sides of the
  squares of `𝓢_{ε₀r}(B_{2r}(0))`, l. 3322);
* `L510Line` (condition (9): Axiom V and Lemma 2.9 for the squares of `W_r^x`, l. 3329);
* `L510Dir` (condition (10): bumps chosen from finitely many rescaled templates, scale
  invariance of the Dirichlet energy, Gaussian tails of `(h, φ)_∇`, l. 3189–3192, 3331–3333).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **Condition (5) of `E_r`** (GM l. 3313–3320): simultaneously for all connected square tubes of
side `ε₀r` in `cl 𝔸_{r/2,2r}(0)`, the `D_h`-internal diameter is `≤ A 𝔠_r e^{ξh_r(0)}`. -/
def L510Diam : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c →
  ∀ {ε₀ q : ℝ}, 0 < ε₀ → 0 < q → ∃ A : ℝ, 1 < A ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
    P {ω | ¬ ∀ V : Set ℂ, IsOpen V → IsConnected V →
      IsSquareTube V (ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} →
      internalDiam (D (h ω)) V V ≤ ENNReal.ofReal (A * scaleFac (xiGamma γ) c (h ω) r 0)} ≤
      ENNReal.ofReal q

/-- **Condition (6) of `E_r`** (GM l. 3322, Lemma 2.10 and a union bound over square sides) -/
def L510Bdy : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c →
  ∀ {ε₀ A q : ℝ}, 0 < ε₀ → 0 < A → 0 < q → ∃ ζ : ℝ, 0 < ζ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
    P {ω | ¬ ∀ V : Set ℂ, IsOpen V → IsConnected V →
      IsSquareTube V (ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} →
      ∀ (Q : ℝ → ℂ) (s t : ℝ), s ≤ t → ContinuousOn Q (Icc s t) →
        Q '' Icc s t ⊆ Metric.thickening (2 * ζ * r) (frontier V) →
        ε₀ * r / 100 ≤ Metric.diam (Q '' Icc s t) →
        ENNReal.ofReal (100 * A * scaleFac (xiGamma γ) c (h ω) r 0) ≤ (D (h ω)).len Q s t} ≤
      ENNReal.ofReal q

/-- **Condition (9) of `E_r`** (GM l. 3329, Axiom V and Lemma 2.9) -/
def L510Line : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c →
  ∀ {θ q : ℝ}, 0 < θ → 0 < q → ∃ M : ℝ, 1 < M ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
    P {ω | ¬ ∀ x ∈ Metric.sphere (0 : ℂ) (2 * r),
      internalDiam (D (h ω)) (lineTube θ r x) (lineTube θ r x) ≤
        ENNReal.ofReal (M * scaleFac (xiGamma γ) c (h ω) r 0)} ≤ ENNReal.ofReal q

/-- **Condition (10) of `E_r`** (GM l. 3189–3192, 3331–3333): bumps chosen deterministically for
each `r`, `Λ₀` uniform in `r` (the family `𝓖_r` does not involve `Λ₀`) -/
def L510Dir : Prop := ∀ (S : EData), S.Ranges → ∀ {q : ℝ}, 0 < q → ∃ Λ₀ : ℝ, 1 < Λ₀ ∧
  ∀ r : ℝ, 0 < r → ∀ U : ℂ → ℂ → Set ℂ, IsTubeFam S U r →
  ∃ fb gb : Set ℂ → TestC, IsBumpChoice S U fb gb r ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    P {ω | ¬ ∀ φ ∈ bumpFam S U fb gb r, |dirInner (h ω) φ| + gradEnergy φ / 2 ≤ Λ₀} ≤
      ENNReal.ofReal q

lemma l510_norm_smul_real (t : ℝ) (ht : 0 ≤ t) (x : ℂ) : ‖(t : ℂ) * x‖ = t * ‖x‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]

set_option maxHeartbeats 1000000 in
/-- **GM Lemma 5.10** from Lemma 5.8 (deterministic tubes) and the conditions (5), (6), (9), (10);
conditions (4), (7), (8) are proved in `L510A.lean`. GM l. 3307–3335. -/
theorem gm_L5_10_of_parts (h58 : L5_8) (hDiam : L510Diam) (hBdy : L510Bdy) (hLine : L510Line)
    (hDir : L510Dir) : L5_10 := by
  intro γ D D' c cs Cs hPS hRat hcs hcsC α p₀ hα3 hα1 hp0 hp1 hEnd c₁ c₂ η hc1 hc12 hc2 hη 𝕡 h𝕡
  obtain ⟨hγ0, hγ2, hD, -⟩ := id hPS
  have hξ : 0 < xiGamma γ := xiGamma_pos hγ0
  set q : ℝ := (1 - 𝕡) / 9 with hqdef
  have hq : 0 < q := by have := h𝕡.2; rw [hqdef]; linarith
  -- (4): `Δ`, then `δ`
  obtain ⟨Δ, hΔ, H4b⟩ := gm_L510_setDist hD hq
  obtain ⟨β₁, hβ₁, H4a⟩ := gm_L510_near hD hΔ.1 hq
  set δ : ℝ := min (β₁ / 2) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδβ : 3 / 2 * δ ≤ β₁ := by
    have := min_le_left (β₁ / 2) (1 / 2); rw [← hδdef] at this; linarith
  -- (1)–(3): Lemma 5.8 with `p = 1 − q`
  obtain ⟨b, ρ, ε₀, hb, hρ, hε₀, H58⟩ := h58 hPS hRat hcs hcsC hα3 hα1 hp0 hp1 hEnd hc1 hc12 hc2
    hη (p := 1 - q) (δ := δ) ⟨by linarith [h𝕡.1], by linarith⟩ ⟨hδ0, hδ1⟩
  -- (5)
  obtain ⟨A, hA, H5⟩ := hDiam hγ0 hγ2 hD hε₀.1 hq
  -- (6)
  obtain ⟨ζ₁, hζ₁, H6⟩ := hBdy hγ0 hγ2 hD hε₀.1 (by linarith : (0 : ℝ) < A) hq
  set ζ : ℝ := min ζ₁ (min (ε₀ / 200) (δ / 200)) with hζdef
  have hζ0 : 0 < ζ := lt_min hζ₁ (lt_min (by linarith [hε₀.1]) (by linarith))
  have hζζ₁ : ζ ≤ ζ₁ := min_le_left _ _
  have hζε : ζ ≤ ε₀ / 200 := (min_le_right _ _).trans (min_le_left _ _)
  have hζδ : ζ ≤ δ / 200 := (min_le_right _ _).trans (min_le_right _ _)
  -- (7)
  obtain ⟨a, ha, H7⟩ := gm_L510_across hD hζ0 hq
  -- (8)
  set t₈ : ℝ := Real.exp (-xiGamma γ * ((xiGamma γ)⁻¹ * Real.log (100 * A / (a * Δ))))
    with ht₈
  obtain ⟨β₂, hβ₂, H8⟩ := gm_L510_near hD (Real.exp_pos _ : 0 < t₈) hq
  set θ : ℝ := min (β₂ / 2) (ζ / 200) with hθdef
  have hθ0 : 0 < θ := lt_min (by linarith) (by linarith)
  have hθβ : 2 * θ ≤ β₂ := by
    have := min_le_left (β₂ / 2) (ζ / 200); rw [← hθdef] at this; linarith
  have hθζ : θ ≤ ζ / 200 := min_le_right _ _
  have hζ1 : ζ < 1 := by linarith [hε₀.2, hb.2]
  -- (9)
  obtain ⟨M, hM, H9⟩ := hLine hγ0 hγ2 hD hθ0 hq
  -- the data
  let SL : ℝ → EData := fun L => EData.mk (xiGamma γ) c cs Cs c₁ η δ ρ b ε₀ Δ A ζ a θ M L
  let S₀ : EData := SL 2
  have hRg : ∀ L : ℝ, 1 < L → (SL L).Ranges := fun L hL =>
    ⟨hξ, ⟨hδ0, hδ1⟩, hb, hρ, hε₀, hΔ, ⟨hζ0, by linarith⟩, ha, ⟨hθ0, by linarith⟩, hA, hM, hL,
      by show ζ < δ / 100; linarith⟩
  -- (10)
  obtain ⟨Λ₀, hΛ₀, H10⟩ := hDir S₀ (hRg 2 (by norm_num)) hq
  refine ⟨SL Λ₀, rfl, rfl, rfl, rfl, rfl, rfl, hRg Λ₀ hΛ₀, ?_⟩
  intro r hρr
  have hr : 0 < r := pos_of_mul_pos_right hρr.1 hρ.1.le
  obtain ⟨U, hU, HU⟩ := H58 r hρr
  obtain ⟨fb, gb, hB, HB⟩ := H10 r hr U hU
  refine ⟨U, fb, gb, hU, hB, ?_⟩
  intro Ω _ P _ h hh
  set B1 := {ω | ¬ ∀ u v : ℂ, 5 / 2 * r ≤ ‖u‖ → ‖u‖ ≤ 3 * r → 5 / 2 * r ≤ ‖v‖ → ‖v‖ ≤ 3 * r →
        ‖u - v‖ ≤ β₁ * r → (D (h ω)).internal (annulus 0 r (4 * r)) u v ≤
          ENNReal.ofReal (Δ * scaleFac (xiGamma γ) c (h ω) r 0)} with hB1
  set B2 := {ω | ¬ ENNReal.ofReal (Δ * scaleFac (xiGamma γ) c (h ω) r 0) ≤
        setDist (D (h ω)) (sphere 0 (2 * r)) (sphere 0 (3 * r))} with hB2
  set B3 := {ω | ¬ ∀ V : Set ℂ, IsOpen V → IsConnected V →
      IsSquareTube V (ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} →
      internalDiam (D (h ω)) V V ≤ ENNReal.ofReal (A * scaleFac (xiGamma γ) c (h ω) r 0)}
    with hB3
  set B4 := {ω | ¬ ∀ V : Set ℂ, IsOpen V → IsConnected V →
      IsSquareTube V (ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} →
      ∀ (Q : ℝ → ℂ) (s t : ℝ), s ≤ t → ContinuousOn Q (Icc s t) →
        Q '' Icc s t ⊆ Metric.thickening (2 * ζ₁ * r) (frontier V) →
        ε₀ * r / 100 ≤ Metric.diam (Q '' Icc s t) →
        ENNReal.ofReal (100 * A * scaleFac (xiGamma γ) c (h ω) r 0) ≤ (D (h ω)).len Q s t}
    with hB4
  set B5 := {ω | ¬ ∀ z₁ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ),
        ∀ z₂ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ), ζ * r ≤ ‖z₁ - z₂‖ →
          ENNReal.ofReal (a * scaleFac (xiGamma γ) c (h ω) r 0) ≤
            (D (h ω)).internal (annulus 0 (r / 4) (4 * r)) z₁ z₂} with hB5
  set B6 := {ω | ¬ ∀ u v : ℂ, 5 / 2 * r ≤ ‖u‖ → ‖u‖ ≤ 3 * r → 5 / 2 * r ≤ ‖v‖ → ‖v‖ ≤ 3 * r →
        ‖u - v‖ ≤ β₂ * r → (D (h ω)).internal (annulus 0 r (4 * r)) u v ≤
          ENNReal.ofReal (t₈ * scaleFac (xiGamma γ) c (h ω) r 0)} with hB6
  set B7 := {ω | ¬ ∀ x ∈ Metric.sphere (0 : ℂ) (2 * r),
      internalDiam (D (h ω)) (lineTube θ r x) (lineTube θ r x) ≤
        ENNReal.ofReal (M * scaleFac (xiGamma γ) c (h ω) r 0)} with hB7
  set B8 := {ω | ¬ ∀ φ ∈ bumpFam S₀ U fb gb r, |dirInner (h ω) φ| + gradEnergy φ / 2 ≤ Λ₀}
    with hB8
  have hsub : h ⁻¹' linkEvent D D' cs Cs c₁ η δ ρ b ε₀ r U ⊆
      h ⁻¹' eventE D D' (SL Λ₀) U fb gb r ∪
        (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ B8) := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or, hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, mem_ofPred_eq,
      not_not] at hc
    obtain ⟨hE, ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩⟩ := hc
    apply hE
    refine ⟨hω, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [mem_sphere_zero_iff_norm] at hx hy
      refine ⟨h1 _ _ ?_ ?_ ?_ ?_ ?_, h2⟩
      · rw [norm_mul, hx]; norm_num; linarith
      · rw [norm_mul, hx]; norm_num; linarith
      · rw [norm_mul, hy]; norm_num; linarith
      · rw [norm_mul, hy]; norm_num; linarith
      · rw [← mul_sub, norm_mul]; norm_num; nlinarith
    · intro x hx y hy hxy
      obtain ⟨o, cn, -, sq, -⟩ := hU x hx y hy hxy
      exact h3 _ o cn sq
    · intro x hx y hy hxy Q s t hst hQ hQV hdiam
      obtain ⟨o, cn, -, sq, -⟩ := hU x hx y hy hxy
      refine h4 _ o cn sq Q s t hst hQ (hQV.trans (Metric.thickening_mono ?_ _)) hdiam
      show 2 * ζ * r ≤ 2 * ζ₁ * r
      nlinarith
    · exact h5
    · intro x hx
      rw [mem_sphere_zero_iff_norm] at hx
      have hθ4 : θ ≤ 1 / 4 := by linarith
      have e1 : ‖((3 / 2 - θ : ℝ) : ℂ) * x‖ = (3 / 2 - θ) * (2 * r) := by
        rw [l510_norm_smul_real _ (by linarith), hx]
      refine h6 _ _ ?_ ?_ ?_ ?_ ?_
      · rw [norm_mul, hx]; norm_num; linarith
      · rw [norm_mul, hx]; norm_num; linarith
      · rw [e1]; nlinarith
      · rw [e1]; nlinarith
      · have : (3 / 2 : ℂ) * x - ((3 / 2 - θ : ℝ) : ℂ) * x = (θ : ℂ) * x := by push_cast; ring
        rw [this, l510_norm_smul_real _ hθ0.le, hx]; nlinarith
    · exact h7
    · exact h8
  have hlink := HU P h hh
  have hsum : P (h ⁻¹' linkEvent D D' cs Cs c₁ η δ ρ b ε₀ r U) ≤
      P (h ⁻¹' eventE D D' (SL Λ₀) U fb gb r) + 8 * ENNReal.ofReal q := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl ?_))
    have e8 : (8 : ℝ≥0∞) * ENNReal.ofReal q = ENNReal.ofReal q + ENNReal.ofReal q +
        ENNReal.ofReal q + ENNReal.ofReal q + ENNReal.ofReal q + ENNReal.ofReal q +
        ENNReal.ofReal q + ENNReal.ofReal q := by ring
    rw [e8]
    have hU8 : P (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ B8) ≤
        P B1 + P B2 + P B3 + P B4 + P B5 + P B6 + P B7 + P B8 := by
      iterate 6 refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measure_union_le _ _
    refine hU8.trans ?_
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · exact H4a P h hh r hr
    · exact H4b P h hh r hr
    · exact H5 P h hh r hr
    · exact H6 P h hh r hr
    · exact H7 P h hh r hr
    · exact H8 P h hh r hr
    · exact H9 P h hh r hr
    · exact HB P h hh
  have e : ENNReal.ofReal (1 - q) = ENNReal.ofReal 𝕡 + 8 * ENNReal.ofReal q := by
    rw [show (1 - q) = 𝕡 + 8 * q by rw [hqdef]; ring, ENNReal.ofReal_add h𝕡.1.le (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hfin := hlink.trans hsum
  rw [e] at hfin
  exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp : (8 : ℝ≥0∞) ≠ ∞) ENNReal.ofReal_ne_top) hfin

end LQGMetric.GM
