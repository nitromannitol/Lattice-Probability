/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.Deterministic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicRatio
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip

/-!
# GM Lemma 3.1: `c_*` and `C_*` are a.s. deterministic (task P2-M2D, WP-M2d, row 6)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1186–1206 (Lemma 3.1 and proof), with
GM (1.21) (l. 662), Proposition 2.2 (l. 1184: "a.s. `0 < c_* ≤ C_* < ∞`") and decision D15
(GM Lemma 2.7 in place of tail triviality, `decisions/DEC-A.md` (d)).

* `GM.upperRatio_ae_const`: for two weak LQG metrics with bi-Lipschitz bounds, `C_*` is a.s.
  equal to one deterministic constant, the same for every whole-plane GFF on any probability
  space (BP-M2-6). Proof: `P[C_* > C] ∈ {0, 1}` (`ratioEv_zero_one`) and does not depend on the
  GFF (`prob_ratioEv_eq`); `Cs := sup {C > 0 : P[C_* > C] = 1}`.
* `GM.gm_L3_1 (hL : L2_7) (h22 : P2_2) (h38 : DFGPSLem3_8) : L3_1`; the statement for `c_*` is
  "proven in an identical manner" (l. 1189): it is the `C_*` statement for the pair `(D̃, D)`
  (`lowerRatio_eq_inv`).
* `GM.gm_L3_1_of_blueprint`: the same with GM Proposition 2.2 discharged by
  `GM.Bilip.gm_P2_2` (LM Lemma 1.4, LM Theorem 1.6, GM S2.4a, S2.4c).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.GM

open Blueprint

/-- **GM Lemma 3.1 for `C_*`**, under bi-Lipschitz bounds (GM P2.2). -/
theorem upperRatio_ae_const (hL : L2_7) (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {K : ℝ} (hK : 0 < K)
    (hB : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, BiLip (D (h ω)) (D' (h ω)) K)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (h₀ : Ω₀ → DistC) (hh₀ : IsWholePlaneGFF h₀ P₀) :
    ∃ Cs : ℝ, K⁻¹ ≤ Cs ∧ Cs ≤ K ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ᵐ ω ∂P, upperRatio D D' (h ω) = Cs := by
  -- `ratioEv x` is a.s. `{x < C_*}`
  have hrel : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ x : ℝ, 0 ≤ x →
      ∀ᵐ ω ∂P, (ω ∈ ratioEv D D' x h ↔ x < upperRatio D D' (h ω)) := by
    intro Ω _ P _ h hh x hx
    filter_upwards [hB P h hh] with ω hb
    exact (lt_upperRatio_iff hb hx).symm
  have F1 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ x : ℝ, 0 ≤ x → P (ratioEv D D' x h) = 1 →
      ∀ᵐ ω ∂P, x < upperRatio D D' (h ω) := by
    intro Ω _ P _ h hh x hx h1
    have hm : MeasurableSet (ratioEv D D' x h) :=
      hh.measurable (measurableSet_ratioSet hD.measurable hD'.measurable x)
    have hc := measure_eq_zero_iff_ae_notMem.1 ((prob_compl_eq_zero_iff hm).2 h1)
    filter_upwards [hc, hrel P h hh x hx] with ω hω hiff
    exact hiff.1 (not_not.1 hω)
  have F2 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ x : ℝ, 0 ≤ x → P (ratioEv D D' x h) = 0 →
      ∀ᵐ ω ∂P, upperRatio D D' (h ω) ≤ x := by
    intro Ω _ P _ h hh x hx h0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hrel P h hh x hx] with ω hω hiff
    exact not_lt.1 fun hlt => hω (hiff.2 hlt)
  have hIcc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P →
      ∀ᵐ ω ∂P, K⁻¹ ≤ upperRatio D D' (h ω) ∧ upperRatio D D' (h ω) ≤ K := fun P _ h hh =>
    (hB P h hh).mono fun _ hb => upperRatio_mem_Icc hb
  set S : Set ℝ := {x | 0 < x ∧ P₀ (ratioEv D D' x h₀) = 1} with hS
  have hKi : 0 < K⁻¹ := inv_pos.2 hK
  have hne : (K⁻¹ / 2) ∈ S := by
    refine ⟨by positivity, ?_⟩
    rcases ratioEv_zero_one hL h38 hγ hγ2 hD hD' hh₀ (K⁻¹ / 2) with h0 | h1
    · exfalso
      obtain ⟨ω, hω1, hω2⟩ := ((F2 P₀ h₀ hh₀ _ (by positivity) h0).and (hIcc P₀ h₀ hh₀)).exists
      linarith [hω2.1]
    · exact h1
  have hbdd : BddAbove S := by
    refine ⟨K, fun x hx => ?_⟩
    obtain ⟨ω, hω1, hω2⟩ := ((F1 P₀ h₀ hh₀ x hx.1.le hx.2).and (hIcc P₀ h₀ hh₀)).exists
    exact (hω1.trans_le hω2.2).le
  set Cs := sSup S
  have hCs : K⁻¹ / 2 ≤ Cs := le_csSup hbdd hne
  have key : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, upperRatio D D' (h ω) = Cs := by
    intro Ω _ P _ h hh
    have G1 : ∀ y : ℝ, y < Cs → ∀ᵐ ω ∂P, y < upperRatio D D' (h ω) := by
      intro y hy
      obtain ⟨x, ⟨hx0, hx1⟩, hyx⟩ := exists_lt_of_lt_csSup ⟨_, hne⟩ hy
      rw [← prob_ratioEv_eq hD hD' hh hh₀] at hx1
      filter_upwards [F1 P h hh x hx0.le hx1] with ω hω
      exact hyx.trans hω
    have G2 : ∀ y : ℝ, Cs < y → ∀ᵐ ω ∂P, upperRatio D D' (h ω) ≤ y := by
      intro y hy
      have hy0 : 0 < y := by linarith [half_pos hKi]
      have hyS : y ∉ S := fun hyS => (le_csSup hbdd hyS).not_gt hy
      have hne1 : P (ratioEv D D' y h) ≠ 1 := by
        rw [prob_ratioEv_eq hD hD' hh hh₀]; exact fun h1 => hyS ⟨hy0, h1⟩
      rcases ratioEv_zero_one hL h38 hγ hγ2 hD hD' hh y with h0 | h1
      · exact F2 P h hh y hy0.le h0
      · exact absurd h1 hne1
    have A1 : ∀ᵐ ω ∂P, ∀ q : {q : ℚ // (q : ℝ) < Cs}, (q.1 : ℝ) < upperRatio D D' (h ω) :=
      ae_all_iff.2 fun q => G1 _ q.2
    have A2 : ∀ᵐ ω ∂P, ∀ q : {q : ℚ // Cs < (q : ℝ)}, upperRatio D D' (h ω) ≤ (q.1 : ℝ) :=
      ae_all_iff.2 fun q => G2 _ q.2
    filter_upwards [A1, A2] with ω h1 h2
    refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      exact (h2 ⟨q, hq1⟩).not_gt hq2
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      exact (h1 ⟨q, hq2⟩).not_gt hq1
  obtain ⟨ω, hω1, hω2⟩ := ((key P₀ h₀ hh₀).and (hIcc P₀ h₀ hh₀)).exists
  exact ⟨Cs, hω1 ▸ hω2.1, hω1 ▸ hω2.2, key⟩

/-- **GM Lemma 3.1** (l. 1186–1188), with GM.S1.23 / P2.2 (`0 < c_* ≤ C_* < ∞`). -/
theorem gm_L3_1 (hL : L2_7) (h22 : P2_2) (h38 : DFGPSLem3_8) : L3_1 := by
  intro γ D D' c hset
  obtain ⟨hγ, hγ2, hD, hD'⟩ := hset
  obtain ⟨K, hK, hB⟩ := h22 ⟨hγ, hγ2, hD, hD'⟩
  have hB1 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, BiLip (D (h ω)) (D' (h ω)) K :=
    fun P _ h hh => hB P h hh
  have hB2 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, BiLip (D' (h ω)) (D (h ω)) K :=
    fun P _ h hh => (hB P h hh).mono fun _ hb => BiLip.swap hK hb
  by_cases hex : ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀)
      (_ : IsProbabilityMeasure P₀) (h₀ : Ω₀ → DistC), IsWholePlaneGFF h₀ P₀
  · obtain ⟨Ω₀, m₀, P₀, hP₀, h₀, hh₀⟩ := hex
    obtain ⟨Cs, hCs1, -, hCs⟩ := upperRatio_ae_const hL h38 hγ hγ2 hD hD' hK hB1 P₀ h₀ hh₀
    obtain ⟨Cs', hCs'1, hCs'2, hCs'⟩ :=
      upperRatio_ae_const hL h38 hγ hγ2 hD' hD hK hB2 P₀ h₀ hh₀
    have hCs'pos : 0 < Cs' := (inv_pos.2 hK).trans_le hCs'1
    refine ⟨Cs'⁻¹, Cs, inv_pos.2 hCs'pos, ?_, ?_⟩
    · obtain ⟨ω, e1, e2, hb⟩ :=
        ((hCs P₀ h₀ hh₀).and ((hCs' P₀ h₀ hh₀).and (hB1 P₀ h₀ hh₀))).exists
      rw [← e1, ← e2, ← lowerRatio_eq_inv hK hb]
      have p : {p : ℂ × ℂ // p.1 ≠ p.2} := ⟨(0, 1), zero_ne_one⟩
      exact (ciInf_le (bddBelow_ratio hb) p).trans (le_ciSup (bddAbove_ratio hb) p)
    · intro Ω _ P _ h hh
      filter_upwards [hCs P h hh, hCs' P h hh, hB1 P h hh] with ω e1 e2 hb
      exact ⟨by rw [lowerRatio_eq_inv hK hb, e2], e1⟩
  · exact ⟨1, 1, one_pos, le_rfl, fun P _ h hh => (hex ⟨_, _, P, inferInstance, h, hh⟩).elim⟩

end LQGMetric.GM
