/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V17 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V5

/-!
# LM Theorem 1.7: the mesh-uniform bound (domination for `ε → 0`)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Step 2 of the proof of Theorem 1.7 (l. 1038–1055) with only the
near-geodesic `P₂` of `F = d(z,w;B_{n+1})` (D107 §3(ii)): `A(S) ≤ b₂(S)` and, by LM Lemma 5.1 /
(5.11), `A(S) ≤ (C² − 1) F`, so `∑_S A(S)² ≤ (C² − 1) F ∑_S b₂(S) ≤ (C² − 1) F (C²(F + ε³) + ε³ #𝒮)`
for every mesh `ε > 0` (no `ε₀`): the dominating bound for the limit `ε → 0` (D107 §3(v)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.LM

open MetricGeometry

/-- **the mesh-uniform per-metric bound** -/
theorem t17v_perD₂ {d : ContMetric} (hd : d.IsLength) {C : ℝ} (hC : 1 ≤ C) {n : ℕ} {z w : ℂ}
    (hz : ‖z‖ < n) (hw : ‖w‖ < n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), θ.1 ∈ Icc (0 : ℝ) 1 → θ.2 ∈ Icc (0 : ℝ) 1 →
      ∃ b : t17Box ε ((n : ℝ) + 1) → ℝ, (∀ k, 0 ≤ b k) ∧
        (∀ (k : t17Box ε ((n : ℝ) + 1)) (d'' : ContMetric),
          T17Compat C ε θ (t17Box ε ((n : ℝ) + 1)) d d'' k →
          max ((t17F (n + 1) z w d'').toReal - (t17F (n + 1) z w d).toReal) 0 ^ 2 ≤ b k) ∧
        ∑ k, b k ≤ (C ^ 2 - 1) * (t17F (n + 1) z w d).toReal *
          (C ^ 2 * ((t17F (n + 1) z w d).toReal + ε ^ 3) +
            ε ^ 3 * (t17Box ε ((n : ℝ) + 1)).card) := by
  have hn1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  set c := C ^ 2 with hcdef
  have hc1 : 1 ≤ c := by nlinarith
  have hzn : z ∈ Metric.ball (0 : ℂ) ((n + 1 : ℕ) : ℝ) :=
    Metric.ball_subset_ball hn1.le (mem_ball_zero_iff.2 hz)
  have hwn : w ∈ Metric.ball (0 : ℂ) ((n + 1 : ℕ) : ℝ) :=
    Metric.ball_subset_ball hn1.le (mem_ball_zero_iff.2 hw)
  have hI1 : d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w ≠ ⊤ :=
    DFGPS.T12.internal_ne_top d hd Metric.isOpen_ball (convex_ball _ _).isPreconnected hzn hwn
  have e1 : t17F (n + 1) z w d = d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w :=
    (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm
  have hε3 : (0 : ℝ) < ε ^ 3 := by positivity
  obtain ⟨P₂, hP₂c, hP₂0, hP₂1, hP₂m, hP₂l⟩ := t17v_near_path d hI1 hε3
  have g2 := @t17_grid_null ε hε P₂ hP₂c.measurable (t17LenMeas (d.pt ∘ P₂) 0 1)
    (t17v_sfinite d P₂ 0 1)
  filter_upwards [g2] with θ hθb hθ1 hθ2
  set s := t17Box ε ((n : ℝ) + 1) with hs
  set F₁ := (t17F (n + 1) z w d).toReal
  have hfin₂ : d.len P₂ 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
  have hcb : Metric.ball (0 : ℂ) ((n + 1 : ℕ) : ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by push_cast; rfl))
  have hPR₂ : MapsTo P₂ (Icc 0 1) (Metric.closedBall 0 ((n : ℝ) + 1)) :=
    fun t ht => hcb (hP₂m ht)
  have hnull₂ : t17LenMeas (d.pt ∘ P₂) 0 1 (Icc 0 1 ∩ P₂ ⁻¹' t17Grid ε θ) = 0 :=
    measure_mono_null inter_subset_right hθb
  have hlen₂ : (d.len P₂ 0 1).toReal ≤ F₁ + ε ^ 3 := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
    rwa [ENNReal.toReal_add hI1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε3.le, ← e1] at this
  have hF₁len₂ : F₁ ≤ (d.len P₂ 0 1).toReal := by
    refine ENNReal.toReal_mono hfin₂ ?_
    rw [e1, ← hP₂0, ← hP₂1]
    exact internalEDist_le_curveLength (X := d.Space) zero_le_one
      (d.continuous_pt.comp_continuousOn hP₂c.continuousOn) (fun t ht => ⟨P₂ t, hP₂m ht, rfl⟩)
  have hF₁0 : 0 ≤ F₁ := ENNReal.toReal_nonneg
  have hsum₂ : (d.len P₂ 0 1).toReal = ∑ k ∈ s, t17Piece d P₂ 0 1 ε θ k :=
    (t17v_resample (d'' := d) zero_le_one (fun x y => by rw [one_mul]) hε hθ1 hθ2 hP₂c
      zero_le_one hfin₂ hPR₂ hnull₂ (k₀ := (0, 0)) (fun _ _ _ _ _ _ _ => rfl)).2.2.2.1
  have hpn : ∀ k, 0 ≤ t17Piece d P₂ 0 1 ε θ k := fun _ => ENNReal.toReal_nonneg
  set b₂ : s → ℝ := fun k => (d.len P₂ 0 1).toReal - F₁ + (c - 1) * t17Piece d P₂ 0 1 ε θ k
  have hb₂ : ∀ k, 0 ≤ b₂ k := by
    intro k
    have h2 := hpn k
    simp only [b₂]
    nlinarith
  have hF0 : t17F (n + 1) z w d ≠ ⊤ := e1 ▸ hI1
  have hA : ∀ (k : s) (d'' : ContMetric), T17Compat C ε θ s d d'' k →
      max ((t17F (n + 1) z w d'').toReal - F₁) 0 ≤ b₂ k ∧
        max ((t17F (n + 1) z w d'').toReal - F₁) 0 ≤ (c - 1) * F₁ := by
    intro k d'' hcomp
    refine ⟨t17v_A_bound hc1 hcomp.2.1 hε hθ1 hθ2 hP₂c zero_le_one hfin₂ hPR₂ hP₂m hP₂0 hP₂1
      hnull₂ k.2 hcomp.2.2.2, max_le ?_ (by nlinarith)⟩
    have h1 := t17_chainInf_le hd (by positivity : (0 : ℝ) < c) hcomp.2.1
      (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ((n + 1 : ℕ) : ℝ))) z w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF0) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    have : (t17F (n + 1) z w d'').toReal ≤ c * F₁ := h2
    linarith
  refine ⟨fun k => (c - 1) * F₁ * b₂ k, fun k => mul_nonneg (mul_nonneg (by linarith) hF₁0)
    (hb₂ k), fun k d'' hcomp => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hA k d'' hcomp
    have h0 : 0 ≤ max ((t17F (n + 1) z w d'').toReal - F₁) 0 := le_max_right _ _
    rw [sq]
    exact mul_le_mul h2 h1 h0 (h0.trans h2)
  · rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) hF₁0)
    have hsplit : ∑ k, b₂ k = s.card * ((d.len P₂ 0 1).toReal - F₁) +
        (c - 1) * ∑ k ∈ s, t17Piece d P₂ 0 1 ε θ k := by
      simp only [b₂, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, ← Finset.mul_sum]
      rw [Finset.sum_coe_sort s (fun k => t17Piece d P₂ 0 1 ε θ k)]
    rw [hsplit, ← hsum₂]
    have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    nlinarith

end LQGMetric.LM
