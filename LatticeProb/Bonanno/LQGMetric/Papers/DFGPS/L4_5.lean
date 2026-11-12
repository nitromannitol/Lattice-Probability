/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L4_5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L4_5Det
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10TailMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 4.5 (`lem-geo-bdy-ratio`) (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 4.5 (T:2638–2644): for
each `M > 0` there is `A = A(M) > 0` such that, with probability `1 − O_ε(ε^M)` uniformly in `𝕣`,
`D_h(z, w) ≥ ε^A sup_{u,v ∈ B_{ε^{-M}𝕣}(0)} D_h(u, v)` for all `z, w ∈ B_{ε^{-M}𝕣}(0)` with
`|z − w| ≥ ε𝕣`.

Proof (T:2645–2681), followed step by step, with both sides normalized by
`𝔠_{𝕣'} e^{ξ h_{𝕣'}(0)}`, `𝕣' = ε^{-M}𝕣`, instead of `𝔠_𝕣 e^{ξh_𝕣(0)}` (the comparison
`h_{𝕣'}(0)` vs `h_𝕣(0)` and `𝔠_{𝕣'}` vs `𝔠_𝕣` of T:2671–2672 then cancels; DEV-DF-A10-1):
* (`eqn-geo-bdy-across`) Prop 3.1 at all grid points `x` with `A = ε⁻¹` and a union bound;
* (`eqn-geo-bdy-circle-avg`) the circle averages `h_{ε𝕣}(x) − h_{𝕣'}(0)` are `≤ 8 log ε'^{-1}`,
  `ε' = ε^{1+M}` (Lemma 3.4, which is the Gaussian tail + union bound of T:2652–2655);
* (`eqn-geo-bdy-const`) Theorem 1.5: `𝔠_{ε𝕣} = 𝔠_{ε'𝕣'} ≥ ε'^{ξQ+1} 𝔠_{𝕣'}`;
* (`eqn-geo-bdy-moment`, `eqn-geo-bdy-upper`) the upper tail of
  `𝔠_{𝕣'}^{-1}e^{-ξh_{𝕣'}(0)} sup_{u,v∈B_{𝕣'}(0)} D_h(u,v)`: we use the polynomial tail
  `diam_K_upper_tail` from which Prop 3.9's moment bound is derived (T:1767–1775), in place of
  "Prop 3.9 + Markov" (the Markov step needs measurability of the internal diameter; the tail
  is the same estimate; DEV-DF-A10-2).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L45

open Blueprint LQGDimension.LFPPRecords L320

/-- the event of Lemma 4.5 -/
def ev45 (D : DistC → ContMetric) (M A ε 𝕣 : ℝ) : Set DistC :=
  {g | ∀ z ∈ ball (0 : ℂ) (ε ^ (-M) * 𝕣), ∀ w ∈ ball (0 : ℂ) (ε ^ (-M) * 𝕣), ε * 𝕣 ≤ ‖z - w‖ →
    ENNReal.ofReal (ε ^ A) * supDist (D g) (ball 0 (ε ^ (-M) * 𝕣)) ≤
      ENNReal.ofReal ((D g).1 (z, w))}

/-- the exponent `A` of Lemma 4.5 -/
def expA45 (γ M : ℝ) : ℝ :=
  1 + (1 + M) * (xiGamma γ * Q γ + 1 + xiGamma γ * 8) + M / (2 * dGamma γ / γ ^ 2)

lemma expA45_pos {γ M : ℝ} (hγ : 0 < γ) (hM : 0 < M) : 0 < expA45 γ M := by
  have hξ := DG.xiGamma_pos hγ
  have hQ := Q_pos hγ
  have hd := DG.dGamma_pos γ
  unfold expA45
  positivity

set_option maxHeartbeats 1000000 in
/-- **Lemma 4.5 on the canonical space** -/
theorem lem4_5_canon (h31a : LMLem3_1a) (hS : DFGPSScaling) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) {M : ℝ}
    (hM : 0 < M) :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
      μ (ev45 D M (expA45 γ M) ε 𝕣)ᶜ ≤ ENNReal.ofReal (K * ε ^ M) := by
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := DG.xiGamma_pos hγ0
  have hQ : 0 < Q γ := Q_pos hγ0
  have hd := DG.dGamma_pos γ
  set a := 2 * dGamma γ / γ ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have ha4 : a < 4 * dGamma γ / γ ^ 2 := by
    rw [ha]; apply div_lt_div_of_pos_right _ (by positivity); linarith
  set B := 1 + (1 + M) * (ξ * Q γ + 1 + ξ * 8) with hB
  have hAB : expA45 γ M = B + M / a := rfl
  -- inputs
  have h31 := prop3_1 h31a
  obtain ⟨C₁, A₀, hP1⟩ := prop3_1_centre_plane h31 hγ0 hγ2 hD hμ (7 + 6 * M) (by positivity)
  obtain ⟨C₂, hC₂⟩ := lem3_4 hμ.1 (ν := 1) (q := 8) (R := 2) zero_le_one (by norm_num)
    (by norm_num)
  obtain ⟨C₃, t₀, ht₀, hC₃0, hC₃⟩ := diam_K_upper_tail (diamTailRS_of h31 hS) hγ0 hγ2 hD hμ
    isOpen_ball (isCompact_closedBall (0 : ℂ) 1) (isConnected_closedBall zero_le_one)
    (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)) ha0 ha4
  obtain ⟨δ₀, hδ₀, hδ⟩ := hS γ hγ0 hγ2 D c hD 1 one_pos
  have hlen0 : μ {g | ¬ (D g).IsLength} = 0 :=
    ae_iff.1 (hD.length μ id (GM.Tight.isGFFPlusCont_of_wp hμ.1))
  set ε₀ := min (min (1 / 2) δ₀) (min (1 / (|A₀| + 1)) (min (1 / (|C₁| + 1)) (t₀ ^ (-(a / M)))))
    with hε₀
  have hε₀0 : 0 < ε₀ := by
    have : 0 < t₀ ^ (-(a / M)) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have he4 : (8 : ℝ) ^ 2 / (2 * (1 + Real.sqrt 1) ^ 2) - 2 - 2 * 1 = 4 := by
    rw [Real.sqrt_one]; norm_num
  refine ⟨578 + |C₂| + C₃, ε₀, hε₀0, fun ε hε 𝕣 h𝕣 => ?_⟩
  obtain ⟨hε0, hεε₀⟩ := hε
  have hε12 : ε < 1 / 2 := hεε₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : ε < δ₀ := hεε₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεA : ε < 1 / (|A₀| + 1) :=
    hεε₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε < 1 / (|C₁| + 1) :=
    hεε₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεt : ε < t₀ ^ (-(a / M)) :=
    hεε₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hε1 : ε < 1 := by linarith
  -- scales
  set ε' := ε ^ (1 + M) with hε'
  have hε'0 : 0 < ε' := Real.rpow_pos_of_pos hε0 _
  have hε'ε : ε' ≤ ε := by
    calc ε' ≤ ε ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
      _ = ε := Real.rpow_one ε
  set 𝕣' := ε ^ (-M) * 𝕣 with h𝕣'
  have h𝕣'0 : 0 < 𝕣' := by positivity
  set ρ := ε * 𝕣 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hε'𝕣' : ε' * 𝕣' = ρ := by
    rw [hε', h𝕣', hρ, ← mul_assoc, ← Real.rpow_add hε0]; congr 1; ring_nf; exact Real.rpow_one ε
  set m := ε' ^ (1 + 1 : ℝ) * 𝕣' / 4 with hm
  have hε'2 : ε' ^ (1 + 1 : ℝ) = ε' * ε' := by
    rw [show (1 + 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hm0 : 0 < m := by rw [hm, hε'2]; positivity
  have hmρ : 8 * m ≤ ρ := by
    rw [hm, hε'2, ← hε'𝕣']; nlinarith [mul_pos hε'0 h𝕣'0]
  have hm𝕣' : 2 * m ≤ 𝕣' := by
    have h1 : ε' * ε' ≤ 1 := by nlinarith
    rw [hm, hε'2]; nlinarith [mul_le_mul_of_nonneg_right h1 h𝕣'0.le]
  set t := ε ^ (-(M / a)) with ht
  have htt₀ : t₀ ≤ t := by
    have := Real.rpow_le_rpow_of_nonpos hε0 hεt.le (by
      have : 0 ≤ M / a := by positivity
      linarith : -(M / a) ≤ 0)
    rwa [← Real.rpow_mul (by linarith), show -(a / M) * -(M / a) = 1 by field_simp,
      Real.rpow_one] at this
  have hε'1 : ε' ≤ 1 := by linarith
  have h0 : ε' ≤ ε ^ M := by
    rw [hε']; exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  have h1 : ε' * ε' ≤ ε ^ M := (mul_le_of_le_one_left hε'0.le hε'1).trans h0
  have h4 : ε' ^ (4 : ℝ) ≤ ε ^ M := by
    rw [hε', ← Real.rpow_mul hε0.le]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  -- the bad events
  obtain ⟨Bk, hBk⟩ : ∃ Bk : ℕ → ℤ × ℤ → Set DistC, Bk = fun k a => {g | k = 0 ∧ g ∈
    {g | ENNReal.ofReal ((ε⁻¹)⁻¹ * scaleFac ξ c g ρ (gridPt (1 / 4 * (ε' ^ (1 + 1 : ℝ) *
        (1 / 2 : ℝ) ^ k) * 𝕣') a)) ≤
      setDistIn (D g) (closedBall (gridPt (1 / 4 * (ε' ^ (1 + 1 : ℝ) * (1 / 2 : ℝ) ^ k) * 𝕣') a)
          (1 / 4 * ρ))
        (sphere (gridPt (1 / 4 * (ε' ^ (1 + 1 : ℝ) * (1 / 2 : ℝ) ^ k) * 𝕣') a) (1 / 2 * ρ))
        univ}ᶜ} := ⟨_, rfl⟩
  obtain ⟨G1, eG1⟩ : ∃ G1 : Set DistC, G1 = ⋃ k, ⋃ a ∈ gridSel (1 / 4 * (ε' ^ (1 + 1 : ℝ) * (1 / 2 : ℝ) ^ k) * 𝕣') (2 * 𝕣'),
    Bk k a := ⟨_, rfl⟩
  obtain ⟨G2, eG2⟩ : ∃ G2 : Set DistC, G2 = {g : DistC | ∃ w ∈ ball (0 : ℂ) (2 * 𝕣') ∩ gridPts (ε' ^ (1 + 1 : ℝ) * 𝕣' / 4),
    ∃ r ∈ ({ρ} : Set ℝ), 8 * Real.log ε'⁻¹ <
      |circleAvg (id g) r w - circleAvg (id g) 𝕣' 0|} := ⟨_, rfl⟩
  obtain ⟨G3, eG3⟩ : ∃ G3 : Set DistC, G3 = {g : DistC | ENNReal.ofReal t < ENNReal.ofReal (scaleFac ξ c g 𝕣' 0)⁻¹ *
    internalDiam (D g) (scaleSet 𝕣' 0 (closedBall 0 1)) (scaleSet 𝕣' 0 (ball 0 2))} := ⟨_, rfl⟩
  obtain ⟨G4, eG4⟩ : ∃ G4 : Set DistC, G4 = {g : DistC | ¬ (D g).IsLength} := ⟨_, rfl⟩
  -- probability bounds
  have hε''0 : 0 < ε' ^ (1 + 1 : ℝ) := by rw [hε'2]; exact mul_pos hε'0 hε'0
  have hε''1 : ε' ^ (1 + 1 : ℝ) ≤ 1 := by rw [hε'2]; exact mul_le_of_le_one_left hε'0.le hε'1 |>.trans hε'1
  have hA : A₀ < ε⁻¹ := by
    have h1 : |A₀| + 1 < ε⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hε0]; simpa [one_div] using hεA
    linarith [le_abs_self A₀]
  have hC : C₁ * ε ≤ 1 := by
    have h1 : ε * (|C₁| + 1) < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hεC; linarith
    have h2 : C₁ * ε ≤ |C₁| * ε := mul_le_mul_of_nonneg_right (le_abs_self C₁) hε0.le
    linarith
  have hpt : C₁ * (ε⁻¹) ^ (-(7 + 6 * M)) ≤ (ε' ^ (1 + 1 : ℝ) * (1 / 2 : ℝ) ^ (0 : ℕ)) ^
      ((1 : ℝ) + 2) := by
    rw [Real.inv_rpow hε0.le, Real.rpow_neg hε0.le, inv_inv, pow_zero,
      mul_one, hε', ← Real.rpow_mul hε0.le, ← Real.rpow_mul hε0.le]
    have e1 : ε ^ (7 + 6 * M) = ε * ε ^ ((1 + M) * (1 + 1) * (1 + 2)) := by
      rw [← Real.rpow_one_add' hε0.le (y := (1 + M) * (1 + 1) * (1 + 2)) (by positivity)]
      congr 1; ring
    rw [e1, ← mul_assoc]
    have : 0 ≤ ε ^ ((1 + M) * (1 + 1) * (1 + 2)) := by positivity
    calc C₁ * ε * ε ^ ((1 + M) * (1 + 1) * (1 + 2))
        ≤ 1 * ε ^ ((1 + M) * (1 + 1) * (1 + 2)) := mul_le_mul_of_nonneg_right hC this
      _ = _ := one_mul _
  have hBb : ∀ k a', a' ∈ gridSel (1 / 4 * (ε' ^ (1 + 1 : ℝ) * (1 / 2 : ℝ) ^ k) * 𝕣') (2 * 𝕣') →
      μ (Bk k a') ≤ ENNReal.ofReal ((ε' ^ (1 + 1 : ℝ) * (1 / 2 : ℝ) ^ k) ^ ((1 : ℝ) + 2)) := by
    intro k a' _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hBk]
      exact (measure_mono fun g hg => hg.2).trans
        ((hP1 ε⁻¹ hA ρ hρ0 _).trans (ENNReal.ofReal_le_ofReal hpt))
    · have : Bk k a' = ∅ := by
        ext g; simp only [hBk, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro h0; omega
      rw [this, measure_empty]; exact bot_le
  have hGU := grid_union_bound μ (ρ := 1 / 2) (κ := 1 / 4) (R := 2) (β := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) one_pos hε''0 hε''1 h𝕣'0 Bk hBb
  have hG1 : μ G1 ≤ ENNReal.ofReal (578 * ε ^ M) := by
    rw [eG1]
    refine hGU.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_one, Real.rpow_one, hε'2]
    have e : (2 * 2 / (1 / 4) + 1 : ℝ) ^ 2 / (1 - 1 / 2) = 578 := by norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hG2 : μ G2 ≤ ENNReal.ofReal (|C₂| * ε ^ M) := by
    have hS' : ({ρ} : Set ℝ) ⊆ Icc (ε' ^ (1 + 1 : ℝ) * 𝕣') (ε' * 𝕣') := by
      rw [singleton_subset_iff, hε'2, hε'𝕣']
      refine ⟨?_, le_rfl⟩
      rw [← hε'𝕣']
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hε'0.le hε'1) h𝕣'0.le
    rw [eG2]
    refine (hC₂ 𝕣' h𝕣'0 ε' ⟨hε'0, hε'ε.trans_lt hε1⟩ {ρ} (countable_singleton ρ) hS').trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [he4]
    have : 0 ≤ ε' ^ (4 : ℝ) := by positivity
    calc C₂ * ε' ^ (4 : ℝ) ≤ |C₂| * ε' ^ (4 : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self C₂) this
      _ ≤ |C₂| * ε ^ M := mul_le_mul_of_nonneg_left h4 (abs_nonneg C₂)
  have hG3 : μ G3 ≤ ENNReal.ofReal (C₃ * ε ^ M) := by
    rw [eG3]
    refine (hC₃ 𝕣' h𝕣'0 t htt₀).trans_eq ?_
    rw [ht, ← Real.rpow_mul hε0.le, show -(M / a) * -a = M by field_simp]
  -- the inclusion
  have hsub : (ev45 D M (expA45 γ M) ε 𝕣)ᶜ ⊆ G1 ∪ G2 ∪ G3 ∪ G4 := by
    intro g hg
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hn
    apply hg
    have hlen : (D g).IsLength := by simpa [eG4] using n4
    set S' := scaleFac ξ c g 𝕣' 0 with hS'
    have hc𝕣' : 0 < c 𝕣' := hD.tightness.1 𝕣' h𝕣'0
    have hS'0 : 0 < S' := by rw [hS', scaleFac]; positivity
    -- upper bound
    have hup : supDist (D g) (ball 0 (ε ^ (-M) * 𝕣)) ≤ ENNReal.ofReal (t * S') := by
      have h3 : ENNReal.ofReal S'⁻¹ * internalDiam (D g) (scaleSet 𝕣' 0 (closedBall 0 1))
          (scaleSet 𝕣' 0 (ball 0 2)) ≤ ENNReal.ofReal t := by
        simpa [eG3] using n3
      refine (supDist_le_internalDiam (D g) (V := scaleSet 𝕣' 0 (ball 0 2))
        (A' := scaleSet 𝕣' 0 (closedBall 0 1)) ?_).trans ?_
      · rw [scaleSet_closedBall h𝕣'0, one_mul]; exact ball_subset_closedBall
      · have e : internalDiam (D g) (scaleSet 𝕣' 0 (closedBall 0 1)) (scaleSet 𝕣' 0 (ball 0 2)) =
            ENNReal.ofReal S' * (ENNReal.ofReal S'⁻¹ * internalDiam (D g)
              (scaleSet 𝕣' 0 (closedBall 0 1)) (scaleSet 𝕣' 0 (ball 0 2))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hS'0.le, mul_inv_cancel₀ hS'0.ne',
            ENNReal.ofReal_one, one_mul]
        rw [e, mul_comm t, ENNReal.ofReal_mul hS'0.le]
        gcongr
    -- lower bound
    have hlow : ∀ z ∈ ball (0 : ℂ) (ε ^ (-M) * 𝕣), ∀ w ∈ ball (0 : ℂ) (ε ^ (-M) * 𝕣),
        ε * 𝕣 ≤ ‖z - w‖ → ε ^ B * S' ≤ (D g).1 (z, w) := by
      intro z hz w _ hzw
      refine det_lower (D g) hlen hm0 hmρ hm𝕣' ?_ (by simpa using hz) hzw
      intro a' ha' u hu v hv
      have hmesh : 1 / 4 * (ε' ^ (1 + 1 : ℝ) * (1 / 2 : ℝ) ^ (0 : ℕ)) * 𝕣' = m := by
        rw [hm]; ring
      set x := gridPt m a' with hx
      -- Prop 3.1 at `x`
      have h1 : ENNReal.ofReal ((ε⁻¹)⁻¹ * scaleFac ξ c g ρ x) ≤
          setDistIn (D g) (closedBall x (1 / 4 * ρ)) (sphere x (1 / 2 * ρ)) univ := by
        by_contra hc
        apply n1
        rw [eG1]
        refine mem_iUnion.2 ⟨0, mem_iUnion₂.2 ⟨a', ?_, ?_⟩⟩
        · show ‖gridPt _ a'‖ ≤ 2 * 𝕣'
          rw [hmesh]; exact ha'.le
        · rw [hBk]
          refine ⟨rfl, ?_⟩
          simp only [hmesh]
          exact hc
      have hcr := le_of_setDistIn_univ (D g) hlen h1
        (sphere_subset_closedBall (by rw [show 1 / 4 * ρ = ρ / 4 by ring]; exact hu))
        (by rw [show 1 / 2 * ρ = ρ / 2 by ring]; exact hv)
      rw [inv_inv] at hcr
      -- circle averages at `x`
      have h2 : circleAvg g 𝕣' 0 - 8 * Real.log ε'⁻¹ ≤ circleAvg g ρ x := by
        by_contra hc
        push Not at hc
        apply n2
        rw [eG2]
        refine ⟨x, ⟨by simpa using ha', a'.1, a'.2, ?_⟩, ρ, rfl, ?_⟩
        · rw [hx, hm]; rfl
        · show 8 * Real.log ε'⁻¹ < |circleAvg g ρ x - circleAvg g 𝕣' 0|
          rw [abs_sub_comm]
          exact lt_of_lt_of_le (by linarith) (le_abs_self _)
      -- scaling of `𝔠`
      have h3 : ε' ^ (ξ * Q γ + 1) * c 𝕣' ≤ c ρ := by
        have := (hδ ε' ⟨hε'0, hε'ε.trans_lt hεδ⟩ 𝕣' h𝕣'0).1
        rw [le_div_iff₀ hc𝕣', hε'𝕣'] at this
        exact this
      -- combine
      have hexp : Real.exp (ξ * circleAvg g 𝕣' 0) * ε' ^ (ξ * 8) ≤
          Real.exp (ξ * circleAvg g ρ x) := by
        have e : ε' ^ (ξ * 8) = Real.exp (-(ξ * (8 * Real.log ε'⁻¹))) := by
          rw [Real.rpow_def_of_pos hε'0, Real.log_inv]; ring_nf
        rw [e, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      have hB' : ε ^ B = ε * ε' ^ (ξ * Q γ + 1) * ε' ^ (ξ * 8) := by
        rw [hε', ← Real.rpow_mul hε0.le, ← Real.rpow_mul hε0.le, mul_assoc, ← Real.rpow_add hε0,
          ← Real.rpow_one_add' hε0.le (y := (1 + M) * (ξ * Q γ + 1) + (1 + M) * (ξ * 8))
            (by positivity), hB]
        congr 1; ring
      have hcρ : 0 ≤ c ρ := (hD.tightness.1 ρ hρ0).le
      calc ε ^ B * S' = ε * ((ε' ^ (ξ * Q γ + 1) * c 𝕣') *
            (Real.exp (ξ * circleAvg g 𝕣' 0) * ε' ^ (ξ * 8))) := by
            rw [hB', hS', scaleFac]; ring
        _ ≤ ε * (c ρ * Real.exp (ξ * circleAvg g ρ x)) := by
            gcongr
        _ = ε * scaleFac ξ c g ρ x := rfl
        _ ≤ (D g).1 (u, v) := hcr
    intro z hz w hw hzw
    calc ENNReal.ofReal (ε ^ expA45 γ M) * supDist (D g) (ball 0 (ε ^ (-M) * 𝕣))
        ≤ ENNReal.ofReal (ε ^ expA45 γ M) * ENNReal.ofReal (t * S') := by gcongr
      _ = ENNReal.ofReal (ε ^ B * S') := by
          rw [← ENNReal.ofReal_mul (by positivity), hAB, ht, ← mul_assoc,
            ← Real.rpow_add hε0]
          congr 2; ring
      _ ≤ ENNReal.ofReal ((D g).1 (z, w)) := ENNReal.ofReal_le_ofReal (hlow z hz w hw hzw)
  calc μ (ev45 D M (expA45 γ M) ε 𝕣)ᶜ ≤ μ (G1 ∪ G2 ∪ G3 ∪ G4) := measure_mono hsub
    _ ≤ μ G1 + μ G2 + μ G3 + μ G4 := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (578 * ε ^ M) + ENNReal.ofReal (|C₂| * ε ^ M) +
          ENNReal.ofReal (C₃ * ε ^ M) + 0 := by
        rw [eG4, hlen0]; gcongr
    _ = ENNReal.ofReal ((578 + |C₂| + C₃) * ε ^ M) := by
        have hεM : 0 ≤ ε ^ M := by positivity
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **DFGPS Lemma 4.5** (T:2638–2644), constants uniform in `𝕣` and in the field (D57 form) -/
theorem lem4_5 (h31a : LMLem3_1a) (hS : DFGPSScaling) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {M : ℝ} (hM : 0 < M) :
    ∃ A : ℝ, 0 < A ∧ ∃ K ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWPGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
          P (h ⁻¹' ev45 D M A ε 𝕣)ᶜ ≤ ENNReal.ofReal (K * ε ^ M) := by
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  obtain ⟨K, ε₀, hε₀, H⟩ := lem4_5_canon h31a hS hγ0 hγ2 hD hμ hM
  exact ⟨expA45 γ M, expA45_pos hγ0 hM, K, ε₀, hε₀, fun P _ h hh ε hε 𝕣 h𝕣 =>
    (prob_le_canonical hμ P h hh _).trans (H ε hε 𝕣 h𝕣)⟩

end L45

end LQGMetric.DFGPS
