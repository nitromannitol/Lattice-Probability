/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L4_4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 4.4 (`lem-geo-bdy-annuli`) (task P2-DFA10)

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
`C`-good balls (T:2620–2624, (4.3)): `B_r(z)` is `C`-good if
`sup_{u,v∈∂B_r(z)} D_h(u,v; 𝔸_{r/2,2r}(z)) ≤ C D_h(∂B_r(z), ∂B_{2r}(z))`.

Lemma 4.4 (T:2626–2631): for `ζ ∈ (0,1)`, `M > 0` there is `C = C(ζ, M) > 1` such that for each
`𝕣 > 0`, with probability `1 − O_ε(ε^M)` uniformly in `𝕣`, `B_{ε^{-M}𝕣}(0)` is covered by `C`-good
balls with radii in `[2ε𝕣, ε^{1−ζ}𝕣]`.

Proof (T:2632–2634): "an immediate consequence of Lemma 3.2 applied with `ε^{1−ζ}` in place of
`ε` and any `ν ∈ (0, 1/(1−ζ) − 1)`". We take `ν = ζ/(2(1−ζ))` and `M' = M/(1−ζ)` in Lemma 3.2
(`lem3_2`); an `E_r(w; C₀)` annulus is `C₀²`-good (the two bounds of (3.4) divide out the scale
`𝔠_r e^{ξh_r(w)}`), and `ε^{(1−ζ)(1+ν)} = ε^{1−ζ/2} ≥ 2ε` for small `ε`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-- `B_r(z)` is `C`-good for the metric `Dg` (DFGPS (4.3), T:2622) -/
def CGood (Dg : ContMetric) (C r : ℝ) (z : ℂ) : Prop :=
  internalDiam Dg (Metric.sphere z r) (annulus z (r / 2) (2 * r)) ≤
    ENNReal.ofReal C * setDist Dg (Metric.sphere z r) (Metric.sphere z (2 * r))

/-- the sharpened covering event (`lem4_4_half`): radii in `[4ε𝕣, ε^{1−ζ}𝕣]`, and every point
of `B_{ε^{-M}𝕣}(0)` in the concentric ball of half the radius -/
def CGoodCoverH (Dg : ContMetric) (C ζ M ε 𝕣 : ℝ) : Prop :=
  ∀ z ∈ ball (0 : ℂ) (ε ^ (-M) * 𝕣), ∃ w : ℂ, ∃ ρ : ℝ, 4 * ε * 𝕣 ≤ ρ ∧ ρ ≤ ε ^ (1 - ζ) * 𝕣 ∧
    CGood Dg C ρ w ∧ z ∈ ball w (ρ / 2)

lemma cGood_of_annEvent {ξ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {C r : ℝ} {w : ℂ}
    {g : DistC} (hC : 0 < C) (hg : g ∈ annEvent ξ D c C r w) : CGood (D g) (C ^ 2) r w := by
  obtain ⟨h1, h2⟩ := hg
  refine h1.trans ?_
  set S := scaleFac ξ c g r w
  have e : ENNReal.ofReal (C * S) = ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (C⁻¹ * S) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [e]
  gcongr

/-- **Lemma 4.4, sharpened form** (same proof, T:2632–2634): the covering balls have radii in
`[4ε𝕣, ε^{1−ζ}𝕣]` and each covered point lies in the concentric ball of half the radius (Lemma
3.2 gives `z ∈ B_{ε'^{1+ν}𝕣/2}(w)` with `r ≥ ε'^{1+ν}𝕣`). This is the form needed in the proof of
Prop 4.3 so that `P(τ_k)` and a nearby point of `∂𝓑_s` lie in the same `C`-good ball. -/
theorem lem4_4_half (h31a : LMLem3_1a) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {ζ M : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hM : 0 < M) :
    ∃ C : ℝ, 1 < C ∧ ∃ K ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
          P {ω | ¬ CGoodCoverH (D (h ω)) C ζ M ε 𝕣} ≤ ENNReal.ofReal (K * ε ^ M) := by
  have h1ζ : 0 < 1 - ζ := by linarith
  set ν := ζ / (2 * (1 - ζ)) with hν
  have hν0 : 0 < ν := by positivity
  set M' := M / (1 - ζ) with hM'
  have hM'0 : 0 < M' := by positivity
  obtain ⟨C₀, hC₀, K, ε₁, hε₁, H⟩ := lem3_2 h31a γ hγ hγ2 D c hD ν M' hν0 hM'0
  have hexp : (1 - ζ) * (1 + ν) = 1 - ζ / 2 := by rw [hν]; field_simp; ring
  -- `ε₀`: `ε^{1−ζ} < ε₁` and `ε^{ζ/2} ≤ 1/2`
  set ε₀ := min (ε₁ ^ (1 / (1 - ζ))) ((1 / 4 : ℝ) ^ (2 / ζ)) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (Real.rpow_pos_of_pos hε₁ _) (by positivity)
  refine ⟨C₀ ^ 2, by nlinarith, K, ε₀, hε₀0, fun P _ h hh 𝕣 h𝕣 ε hε => ?_⟩
  obtain ⟨hε0, hεε₀⟩ := hε
  set ε' := ε ^ (1 - ζ) with hε'
  have hε'0 : 0 < ε' := Real.rpow_pos_of_pos hε0 _
  have hε'1 : ε' < ε₁ := by
    have h1 : ε < ε₁ ^ (1 / (1 - ζ)) := hεε₀.trans_le (min_le_left _ _)
    have := Real.rpow_lt_rpow hε0.le h1 h1ζ
    rwa [← Real.rpow_mul hε₁.le, one_div, inv_mul_cancel₀ h1ζ.ne', Real.rpow_one] at this
  have hRad : ε' ^ (-M') = ε ^ (-M) := by
    rw [hε', ← Real.rpow_mul hε0.le, hM']; congr 1; field_simp
  have hPow : ε' ^ M' = ε ^ M := by
    rw [hε', ← Real.rpow_mul hε0.le, hM']; congr 1; field_simp
  have hLow : ε' ^ (1 + ν) = ε ^ (1 - ζ / 2) := by
    rw [hε', ← Real.rpow_mul hε0.le, hexp]
  have h2ε : 4 * ε ≤ ε ^ (1 - ζ / 2) := by
    have h1 : ε ≤ (1 / 4 : ℝ) ^ (2 / ζ) := hεε₀.le.trans (min_le_right _ _)
    have h2 : ε ^ (ζ / 2) ≤ 1 / 4 := by
      have := Real.rpow_le_rpow hε0.le h1 (by positivity : (0 : ℝ) ≤ ζ / 2)
      rwa [← Real.rpow_mul (by norm_num), div_mul_div_comm, mul_comm 2 ζ,
        div_self (by positivity), Real.rpow_one] at this
    have e : ε = ε ^ (ζ / 2) * ε ^ (1 - ζ / 2) := by
      rw [← Real.rpow_add hε0]; simp
    have hpos : 0 < ε ^ (1 - ζ / 2) := Real.rpow_pos_of_pos hε0 _
    nlinarith
  refine le_trans (measure_mono ?_) ((H P h hh 𝕣 h𝕣 ε' ⟨hε'0, hε'1⟩).trans_eq (by rw [hPow]))
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  intro hG
  apply hω
  intro z hz
  have hz' : z ∈ ball (0 : ℂ) (𝕣 * ε' ^ (-M')) := by
    rw [hRad, mul_comm]; exact hz
  obtain ⟨w, -, r, -, hr1, hr2, hgood, hzw⟩ := hG z hz'
  refine ⟨w, r, ?_, ?_, cGood_of_annEvent (by linarith) hgood, ?_⟩
  · rw [hLow] at hr1; nlinarith
  · exact hr2
  · refine ball_subset_ball ?_ hzw
    rw [mul_comm]; linarith

end LQGMetric.DFGPS
