/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.Deterministic01 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# GM Lemma 3.1, the zero-one step via GM Lemma 2.7 (task P2-M2D, decision D15)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1202–1206: the events `E(z)`, `z ∈ ℂ`, are
determined by `h|_{B_R(z)}` modulo additive constant, have the same probability and are contained
in `{C_* > C}`; GM concludes with tail triviality. Decision D15 (`decisions/DEC-A.md` (d),
proposed DEVIATIONS entry DA6) replaces the tail step by GM Lemma 2.7 (l. 964–971) applied to `n`
translates `E(4kR)`, `k < n`, after rescaling the field by `R`:

* `GM.measure_eq_one_of_L2_7`: if events `E(z)` are (for every random constant `c`) a.s.
  determined by `(h + c)|_{B_R(z)}`, have probability `≥ p₀ > 0` at the points `z = 4kR`, and are
  a.s. contained in `G`, then `P[G] = 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.GM

open Blueprint

/-- the points `4k` (`k < n`): pairwise at distance `≥ 4 = 2(1 + s)` for `s = 1` -/
def detPts (n : ℕ) : Finset ℂ := (Finset.range n).image fun k : ℕ => ((4 * k : ℝ) : ℂ)

lemma card_detPts (n : ℕ) : (detPts n).card = n := by
  rw [detPts, Finset.card_image_of_injective _ (fun a b hab => by
    have := Complex.ofReal_injective hab
    exact_mod_cast (mul_right_inj' (by norm_num : (4 : ℝ) ≠ 0)).1 this), Finset.card_range]

lemma sep_detPts (n : ℕ) : ∀ z ∈ detPts n, ∀ w ∈ detPts n, z ≠ w → 2 * (1 + 1) ≤ ‖z - w‖ := by
  intro z hz w hw hzw
  simp only [detPts, Finset.mem_image] at hz hw
  obtain ⟨k, -, rfl⟩ := hz
  obtain ⟨j, -, rfl⟩ := hw
  have hkj : k ≠ j := fun h => hzw (by rw [h])
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hkj' : ((k : ℤ) - j) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hkj)
  have h1 := Int.one_le_abs hkj'
  have : (1 : ℝ) ≤ |(k : ℝ) - j| := by exact_mod_cast h1
  linarith

/-- **Zero-one step of GM Lemma 3.1 via GM Lemma 2.7** (D15). -/
theorem measure_eq_one_of_L2_7 (hL : L2_7) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {R : ℝ} (hR : 0 < R)
    {G : Set Ω} {E : ℂ → Set Ω} {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hdet : ∀ (z : ℂ) (c : Ω → ℝ), Measurable c →
      AEEventIn P (fieldSigma (fun ω => addConst (h ω) (c ω)) (ballO z R)) (E z))
    (hprob : ∀ k : ℕ, ENNReal.ofReal p₀ ≤ P (E (R • ((4 * k : ℝ) : ℂ))))
    (hsub : ∀ k : ℕ, E (R • ((4 * k : ℝ) : ℂ)) ≤ᵐ[P] G) : P G = 1 := by
  set hR' : Ω → DistC := fun ω => affineComp R 0 (h ω) with hR'_def
  have hhR : IsWholePlaneGFF hR' P := hh.affineComp hR 0
  have key : ∀ q : ℝ, 0 < q → q < 1 → ENNReal.ofReal q ≤ P G := by
    intro q hq0 hq1
    obtain ⟨n₀, hn₀⟩ := hL (s := 1) (p := min p₀ (1 / 2)) (q := q) one_pos
      (lt_min hp₀ (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num)) hq0 hq1
    have hU := hn₀ P hR' hhR (detPts n₀) (card_detPts n₀).ge (sep_detPts n₀)
      (fun w => E (R • w)) ?_ ?_
    · refine hU.trans (measure_mono_ae ?_)
      have hall : ∀ᵐ ω ∂P, ∀ w ∈ detPts n₀, ω ∈ E (R • w) → ω ∈ G := by
        refine (Filter.eventually_all_finset _).2 fun w hw => ?_
        simp only [detPts, Finset.mem_image] at hw
        obtain ⟨k, -, rfl⟩ := hw
        exact hsub k
      filter_upwards [hall] with ω hω hmem
      simp only [mem_iUnion] at hmem
      obtain ⟨w, hw, hωw⟩ := hmem
      exact hω w hw hωw
    · intro w hw
      have hc : Measurable fun ω => -circleAvg (hR' ω) (1 + 1) w :=
        ((measurable_circleAvg_left _ _).comp hhR.measurable).neg
      obtain ⟨F, hF, hEF⟩ := hdet (R • w) _ hc
      refine ⟨F, ?_, hEF⟩
      have hle := fieldSigma_le_affineComp (z := 0) (U := ballO (R • w) R) (V := ballO w 1) hR
        (mem_ballO_iff_scale hR w) (fun ω => addConst (h ω) (-circleAvg (hR' ω) (1 + 1) w))
      simp only [affineComp_addConst hR] at hle
      exact hle _ hF
    · intro w hw
      simp only [detPts, Finset.mem_image] at hw
      obtain ⟨k, -, rfl⟩ := hw
      exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hprob k)
  by_contra hne
  have hlt : P G < 1 := lt_of_le_of_ne prob_le_one hne
  obtain ⟨t, ht0, hGt, ht1⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · rw [← h, ENNReal.ofReal_zero] at hGt; exact absurd hGt (not_lt_zero)
  have ht1' : t < 1 := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos] at ht1
  exact (key t htpos ht1').not_gt hGt

end LQGMetric.GM
