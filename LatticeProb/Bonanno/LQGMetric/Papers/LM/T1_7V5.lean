/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V4

/-!
# LM Theorem 1.7, packet P-VAR (c): the per-metric product bound, assembled

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Step 2 of the proof of Theorem 1.7 (l. 1038–1055) with D107 §3(ii)–(iv)
(`decisions/DEC-107.md`); see the docstring of `T1_7V4.lean`. `t17v_perD`: for a length metric `d`
and `κ > 0` there is `ε₀ > 0` such that for `ε < ε₀` and a.e. `θ ∈ [0,1]²` (LM Lemma 5.2 for the
two near-geodesics, chosen depending only on `d`), the squared increments `(F(D^S) − F(d))_+²` over
all `D^S` compatible with `d` at `S` (`T17Compat`) are bounded by `b_S` with
`∑_S b_S ≤ C²(η + ε³ + κ)(C²(F + ε³) + ε³ #𝒮)`, `F = d(z,w;B_{n+1})`, `η = d(z,w;B_n) − F`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.LM

open MetricGeometry

/-- **the per-metric product bound** (D107 §3(ii)–(iv)) -/
theorem t17v_perD {d : ContMetric} (hd : d.IsLength) {C : ℝ} (hC : 1 ≤ C) {n : ℕ} {z w : ℂ}
    (hz : ‖z‖ < n) (hw : ‖w‖ < n) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)),
      θ.1 ∈ Icc (0 : ℝ) 1 → θ.2 ∈ Icc (0 : ℝ) 1 →
      ∃ b : t17Box ε ((n : ℝ) + 1) → ℝ, (∀ k, 0 ≤ b k) ∧
        (∀ (k : t17Box ε ((n : ℝ) + 1)) (d'' : ContMetric),
          T17Compat C ε θ (t17Box ε ((n : ℝ) + 1)) d d'' k →
          max ((t17F (n + 1) z w d'').toReal - (t17F (n + 1) z w d).toReal) 0 ^ 2 ≤ b k) ∧
        ∑ k, b k ≤ C ^ 2 * ((t17F n z w d).toReal - (t17F (n + 1) z w d).toReal + ε ^ 3 + κ) *
          (C ^ 2 * ((t17F (n + 1) z w d).toReal + ε ^ 3) +
            ε ^ 3 * (t17Box ε ((n : ℝ) + 1)).card) := by
  have hn1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨r, hr, hnb⟩ := t17_near_bound hd hn1 hκ
  refine ⟨r / 2, by positivity, fun ε hε hεr => ?_⟩
  set c := C ^ 2 with hcdef
  have hc1 : 1 ≤ c := by nlinarith
  have hzn : z ∈ Metric.ball (0 : ℂ) (n : ℝ) := mem_ball_zero_iff.2 hz
  have hwn : w ∈ Metric.ball (0 : ℂ) (n : ℝ) := mem_ball_zero_iff.2 hw
  have hsub : Metric.ball (0 : ℂ) (n : ℝ) ⊆ Metric.ball 0 ((n + 1 : ℕ) : ℝ) :=
    Metric.ball_subset_ball hn1.le
  have hI0 : d.internal (Metric.ball 0 (n : ℝ)) z w ≠ ⊤ :=
    DFGPS.T12.internal_ne_top d hd Metric.isOpen_ball (convex_ball _ _).isPreconnected hzn hwn
  have hI1 : d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w ≠ ⊤ :=
    DFGPS.T12.internal_ne_top d hd Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (hsub hzn) (hsub hwn)
  have e0 : t17F n z w d = d.internal (Metric.ball 0 (n : ℝ)) z w :=
    (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm
  have e1 : t17F (n + 1) z w d = d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w :=
    (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm
  have hε3 : (0 : ℝ) < ε ^ 3 := by positivity
  obtain ⟨P₁, hP₁c, hP₁0, hP₁1, hP₁m, hP₁l⟩ := t17v_near_path d hI0 hε3
  obtain ⟨P₂, hP₂c, hP₂0, hP₂1, hP₂m, hP₂l⟩ := t17v_near_path d hI1 hε3
  have g1 := @t17_grid_null ε hε P₁ hP₁c.measurable (t17LenMeas (d.pt ∘ P₁) 0 1)
    (t17v_sfinite d P₁ 0 1)
  have g2 := @t17_grid_null ε hε P₂ hP₂c.measurable (t17LenMeas (d.pt ∘ P₂) 0 1)
    (t17v_sfinite d P₂ 0 1)
  filter_upwards [g1, g2] with θ hθa hθb hθ1 hθ2
  set s := t17Box ε ((n : ℝ) + 1) with hs
  set F₀ := (t17F n z w d).toReal
  set F₁ := (t17F (n + 1) z w d).toReal
  -- the two curves
  have hfin₁ : d.len P₁ 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI0, ENNReal.ofReal_ne_top⟩) hP₁l
  have hfin₂ : d.len P₂ 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
  have hcb : Metric.ball (0 : ℂ) ((n + 1 : ℕ) : ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by push_cast; rfl))
  have hPR₁ : MapsTo P₁ (Icc 0 1) (Metric.closedBall 0 ((n : ℝ) + 1)) :=
    fun t ht => hcb (hsub (hP₁m ht))
  have hPR₂ : MapsTo P₂ (Icc 0 1) (Metric.closedBall 0 ((n : ℝ) + 1)) :=
    fun t ht => hcb (hP₂m ht)
  have hnull₁ : t17LenMeas (d.pt ∘ P₁) 0 1 (Icc 0 1 ∩ P₁ ⁻¹' t17Grid ε θ) = 0 :=
    measure_mono_null inter_subset_right hθa
  have hnull₂ : t17LenMeas (d.pt ∘ P₂) 0 1 (Icc 0 1 ∩ P₂ ⁻¹' t17Grid ε θ) = 0 :=
    measure_mono_null inter_subset_right hθb
  -- real-valued facts
  have hlen₁ : (d.len P₁ 0 1).toReal ≤ F₀ + ε ^ 3 := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI0, ENNReal.ofReal_ne_top⟩) hP₁l
    rwa [ENNReal.toReal_add hI0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε3.le, ← e0] at this
  have hlen₂ : (d.len P₂ 0 1).toReal ≤ F₁ + ε ^ 3 := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
    rwa [ENNReal.toReal_add hI1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε3.le, ← e1] at this
  have hF₁len₂ : F₁ ≤ (d.len P₂ 0 1).toReal := by
    refine ENNReal.toReal_mono hfin₂ ?_
    rw [e1, ← hP₂0, ← hP₂1]
    exact internalEDist_le_curveLength (X := d.Space) zero_le_one
      (d.continuous_pt.comp_continuousOn hP₂c.continuousOn) (fun t ht => ⟨P₂ t, hP₂m ht, rfl⟩)
  have hF₁F₀ : F₁ ≤ F₀ := ENNReal.toReal_mono (e0 ▸ hI0) (t17_chainInf_succ_le hd n z w)
  have hpiece₁ : ∀ k : ℤ × ℤ, t17Piece d P₁ 0 1 ε θ k ≤ F₀ + ε ^ 3 + κ - F₁ := by
    intro k
    have hnear : d.len P₁ 0 1 ≤ d.internal (Metric.ball 0 (n : ℝ)) (P₁ 0) (P₁ 1) +
        ENNReal.ofReal (ε ^ 3) := by rw [hP₁0, hP₁1]; exact hP₁l
    have := t17v_piece_le hnb hP₁c hfin₁ (fun t ht => Metric.ball_subset_closedBall (hP₁m ht))
      hε3.le hnear (by rw [hP₁0, hP₁1]; exact hI0) hκ.le (show 2 * ε < r by linarith) θ k
    rwa [hP₁0, hP₁1, ← e0, ← e1] at this
  have hsum₂ : (d.len P₂ 0 1).toReal = ∑ k ∈ s, t17Piece d P₂ 0 1 ε θ k :=
    (t17v_resample (d'' := d) zero_le_one (fun x y => by rw [one_mul]) hε hθ1 hθ2 hP₂c
      zero_le_one hfin₂ hPR₂ hnull₂ (k₀ := (0, 0)) (fun _ _ _ _ _ _ _ => rfl)).2.2.2.1
  have hpn : ∀ (P : ℝ → ℂ) k, 0 ≤ t17Piece d P 0 1 ε θ k := fun _ _ => ENNReal.toReal_nonneg
  -- the bounds `b₁, b₂`
  set b₁ : s → ℝ := fun k => (d.len P₁ 0 1).toReal - F₁ + (c - 1) * t17Piece d P₁ 0 1 ε θ k
  set b₂ : s → ℝ := fun k => (d.len P₂ 0 1).toReal - F₁ + (c - 1) * t17Piece d P₂ 0 1 ε θ k
  have hA : ∀ (k : s) (d'' : ContMetric), T17Compat C ε θ s d d'' k →
      max ((t17F (n + 1) z w d'').toReal - F₁) 0 ≤ b₁ k ∧
        max ((t17F (n + 1) z w d'').toReal - F₁) 0 ≤ b₂ k := by
    intro k d'' hcomp
    exact ⟨t17v_A_bound hc1 hcomp.2.1 hε hθ1 hθ2 hP₁c zero_le_one hfin₁ hPR₁
      (fun t ht => hsub (hP₁m ht)) hP₁0 hP₁1 hnull₁ k.2 hcomp.2.2.2,
      t17v_A_bound hc1 hcomp.2.1 hε hθ1 hθ2 hP₂c zero_le_one hfin₂ hPR₂ hP₂m hP₂0 hP₂1 hnull₂
        k.2 hcomp.2.2.2⟩
  set β := c * (F₀ - F₁ + ε ^ 3 + κ)
  have hb₁ : ∀ k, b₁ k ≤ β := by
    intro k
    have h1 := hpiece₁ k
    have h2 := hpn P₁ k
    simp only [b₁, β]
    nlinarith
  have hb₂ : ∀ k, 0 ≤ b₂ k := by
    intro k
    have h2 := hpn P₂ k
    simp only [b₂]
    nlinarith
  have hF₀len₁ : F₀ ≤ (d.len P₁ 0 1).toReal := by
    refine ENNReal.toReal_mono hfin₁ ?_
    rw [e0, ← hP₁0, ← hP₁1]
    exact internalEDist_le_curveLength (X := d.Space) zero_le_one
      (d.continuous_pt.comp_continuousOn hP₁c.continuousOn) (fun t ht => ⟨P₁ t, hP₁m ht, rfl⟩)
  have hb₁0 : ∀ k, 0 ≤ b₁ k := by
    intro k
    have h2 := hpn P₁ k
    simp only [b₁]
    nlinarith
  refine ⟨fun k => b₁ k * b₂ k, fun k => mul_nonneg (hb₁0 k) (hb₂ k), fun k d'' hcomp => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hA k d'' hcomp
    have h0 : 0 ≤ max ((t17F (n + 1) z w d'').toReal - F₁) 0 := le_max_right _ _
    rw [sq]
    exact mul_le_mul h1 h2 h0 (h0.trans h1)
  · have hβ : 0 ≤ β := by
      simp only [β]; nlinarith
    calc ∑ k, b₁ k * b₂ k ≤ ∑ k, β * b₂ k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hb₁ k) (hb₂ k)
      _ = β * ∑ k, b₂ k := (Finset.mul_sum _ _ _).symm
      _ ≤ β * (c * (F₁ + ε ^ 3) + ε ^ 3 * s.card) := by
          refine mul_le_mul_of_nonneg_left ?_ hβ
          have hsplit : ∑ k, b₂ k = s.card * ((d.len P₂ 0 1).toReal - F₁) +
              (c - 1) * ∑ k ∈ s, t17Piece d P₂ 0 1 ε θ k := by
            simp only [b₂, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_coe, nsmul_eq_mul, ← Finset.mul_sum]
            rw [Finset.sum_coe_sort s (fun k => t17Piece d P₂ 0 1 ε θ k)]
          rw [hsplit, ← hsum₂]
          have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
          have hF₁0 : 0 ≤ F₁ := ENNReal.toReal_nonneg
          nlinarith

end LQGMetric.LM
