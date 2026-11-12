/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicRatio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicTrans
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# GM Lemma 3.1: the zero-one law for `{C_* > C}` and the optimal constants (task P2-M2D)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1186–1206, with GM (1.21) (l. 662):

* `GM.ratioEv_zero_one`: `P[ratioEv C] ∈ {0, 1}` (GM's "Suppose `P[C_* > C] > 0` … we will show
  that in fact `P[C_* > C] = 1`", with D15);
* `GM.prob_ratioEv_eq`: `P[ratioEv C]` is the same for all whole-plane GFFs (law of `h` modulo
  additive constant);
* `GM.lt_upperRatio_iff`: under bi-Lipschitz bounds, `C < C_*(g)` iff some `u, v ∈ Qc` have
  `C D_g(u,v) < D̃_g(u,v)` (the supremum in (1.21) over pairs of rational points, continuity);
* `GM.lowerRatio_eq_inv`: `c_*(g) = (sup D_g/D̃_g)⁻¹` ("the statement for `c_*` is proven in an
  identical manner", l. 1189: we apply the `C_*` statement to the pair `(D̃, D)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.GM

open Blueprint

lemma smul_four_mem_Qc (R k : ℕ) : (R : ℝ) • (((4 * k : ℝ)) : ℂ) ∈ Qc :=
  ⟨((R : ℚ) * (4 * k), 0), by push_cast; simp [Complex.real_smul]⟩

/-- **GM Lemma 3.1, zero-one step** (l. 1190–1206 with D15). -/
theorem ratioEv_zero_one (hL : L2_7) (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C : ℝ) : P (ratioEv D D' C h) = 0 ∨ P (ratioEv D D' C h) = 1 := by
  rcases eq_or_ne (P (ratioEv D D' C h)) 0 with h0 | hne0
  · exact Or.inl h0
  right
  have hpos : 0 < P (ratioEv D D' C h) := pos_iff_ne_zero.2 hne0
  obtain ⟨R, hR, hp⟩ := exists_gmEv_pos h38 hγ hγ2 hD hD' hh C hpos
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hne : P (h ⁻¹' gmEv D D' C R 0) ≠ ⊤ := measure_ne_top _ _
  refine measure_ratioEv_eq_one hL hD hD' hh C hRpos (ENNReal.toReal_pos hp.ne' hne)
    fun k => ?_
  rw [ENNReal.ofReal_toReal hne, ← prob_gmEv_translate hD hD' hh C hRpos (smul_four_mem_Qc R k)]
  exact measure_mono_ae (gmEv_subset_locEv hD hD' hh C hRpos _)

/-- `ratioEv` as an event of the field -/
def ratioSet (D D' : DistC → ContMetric) (C : ℝ) : Set DistC :=
  {g | ∃ u ∈ Qc, ∃ v ∈ Qc,
    ENNReal.ofReal C * edist ((D g).pt u) ((D g).pt v) < edist ((D' g).pt u) ((D' g).pt v)}

theorem measurableSet_ratioSet {D D' : DistC → ContMetric} (hDm : Measurable D)
    (hD'm : Measurable D') (C : ℝ) : MeasurableSet (ratioSet D D' C) := by
  have hm : ∀ (D : DistC → ContMetric), Measurable D → ∀ u v : ℂ,
      Measurable fun g => ENNReal.ofReal ((D g).1 (u, v)) :=
    fun D hD u v => ENNReal.measurable_ofReal.comp (measurable_contMetric_apply hD (u, v))
  have e : ratioSet D D' C = ⋃ u ∈ Qc, ⋃ v ∈ Qc,
      {g | ENNReal.ofReal C * ENNReal.ofReal ((D g).1 (u, v)) < ENNReal.ofReal ((D' g).1 (u, v))} := by
    ext g
    simp only [ratioSet, ContMetric.edist_pt, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [e]
  exact MeasurableSet.biUnion countable_Qc fun u _ => MeasurableSet.biUnion countable_Qc fun v _ =>
    measurableSet_lt ((hm D hDm u v).const_mul _) (hm D' hD'm u v)

/-- `P[ratioEv C]` does not depend on the whole-plane GFF -/
theorem prob_ratioEv_eq {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω Ω' : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') (C : ℝ) :
    P (ratioEv D D' C h) = P' (ratioEv D D' C h') := by
  have hinv : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistC}, IsWholePlaneGFF h P →
      ∀ᵐ ω ∂P, ∀ a : ℝ, addConst (h ω) a ∈ ratioSet D D' C ↔ h ω ∈ ratioSet D D' C := by
    intro Ω _ P _ h hh
    filter_upwards [hD.ae_dist_addConst (detGFFPlusCont hh),
      hD'.ae_dist_addConst (detGFFPlusCont hh)] with ω h1 h2 a
    refine ⟨fun ⟨u, hu, v, hv, hc⟩ => ⟨u, hu, v, hv, ?_⟩,
      fun ⟨u, hu, v, hv, hc⟩ => ⟨u, hu, v, hv, ?_⟩⟩
    · exact (ratio_iff_of_scale (Real.exp_pos _) (h1 a) (h2 a) u v).1 hc
    · exact (ratio_iff_of_scale (Real.exp_pos _) (h1 a) (h2 a) u v).2 hc
  exact prob_eq_of_ae_addConst_iff hh hh' (measurableSet_ratioSet hD.measurable hD'.measurable C)
    (hinv hh) (hinv hh')

lemma dense_Qc : Dense Qc := by
  have h1 : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hg : Continuous fun x : ℝ × ℝ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I := by fun_prop
  have h2 : DenseRange fun x : ℝ × ℝ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I :=
    Function.Surjective.denseRange (f := fun x : ℝ × ℝ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I)
      fun z => ⟨(z.re, z.im), Complex.re_add_im z⟩
  exact h2.comp h1 hg

lemma pos_of_ne (E : ContMetric) {u v : ℂ} (huv : u ≠ v) : 0 < E.1 (u, v) :=
  lt_of_le_of_ne (ContMetric.nonneg E u v) fun h => huv (E.2.eq_of_eq_zero u v h.symm)

/-- bi-Lipschitz bounds `K⁻¹ D_g ≤ D̃_g ≤ K D_g` -/
def BiLip (D D' : ContMetric) (K : ℝ) : Prop :=
  ∀ u v : ℂ, K⁻¹ * D.1 (u, v) ≤ D'.1 (u, v) ∧ D'.1 (u, v) ≤ K * D.1 (u, v)

lemma bddAbove_ratio {D D' : ContMetric} {K : ℝ} (hb : BiLip D D' K) :
    BddAbove (range fun p : {p : ℂ × ℂ // p.1 ≠ p.2} => D'.1 p.1 / D.1 p.1) := by
  refine ⟨K, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact (div_le_iff₀ (pos_of_ne D p.2)).2 (hb _ _).2

lemma bddBelow_ratio {D D' : ContMetric} {K : ℝ} (hb : BiLip D D' K) :
    BddBelow (range fun p : {p : ℂ × ℂ // p.1 ≠ p.2} => D'.1 p.1 / D.1 p.1) := by
  refine ⟨K⁻¹, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact (le_div_iff₀ (pos_of_ne D p.2)).2 (hb _ _).1

instance : Nonempty {p : ℂ × ℂ // p.1 ≠ p.2} := ⟨⟨(0, 1), zero_ne_one⟩⟩

/-- **GM (1.21)**: `C < C_*(g)` iff `C D_g(u,v) < D̃_g(u,v)` for some rational `u, v` -/
theorem lt_upperRatio_iff {D D' : DistC → ContMetric} {g : DistC} {K C : ℝ}
    (hb : BiLip (D g) (D' g) K) (hC : 0 ≤ C) :
    C < upperRatio D D' g ↔ g ∈ ratioSet D D' C := by
  have key : ∀ u v : ℂ, ENNReal.ofReal C * edist ((D g).pt u) ((D g).pt v) <
      edist ((D' g).pt u) ((D' g).pt v) ↔ C * (D g).1 (u, v) < (D' g).1 (u, v) := by
    intro u v
    rw [ContMetric.edist_pt, ContMetric.edist_pt, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hC (ContMetric.nonneg _ _ _))
  constructor
  · intro hlt
    obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hlt
    have hp' : C * (D g).1 p.1 < (D' g).1 p.1 := (lt_div_iff₀ (pos_of_ne _ p.2)).1 hp
    have hO : IsOpen {q : ℂ × ℂ | C * (D g).1 q < (D' g).1 q} :=
      isOpen_lt (continuous_const.mul (D g).1.continuous) (D' g).1.continuous
    obtain ⟨q, hqO, hqQ⟩ := (dense_Qc.prod dense_Qc).inter_open_nonempty _ hO ⟨p.1, hp'⟩
    exact ⟨q.1, hqQ.1, q.2, hqQ.2, (key q.1 q.2).2 hqO⟩
  · rintro ⟨u, -, v, -, hc⟩
    have hc' := (key u v).1 hc
    have huv : u ≠ v := by
      rintro rfl
      rw [(D g).2.self_eq_zero, (D' g).2.self_eq_zero, mul_zero] at hc'
      exact lt_irrefl _ hc'
    have : C < (D' g).1 (u, v) / (D g).1 (u, v) := (lt_div_iff₀ (pos_of_ne _ huv)).2 hc'
    exact this.trans_le (le_ciSup (f := fun p : {p : ℂ × ℂ // p.1 ≠ p.2} =>
      (D' g).1 p.1 / (D g).1 p.1) (bddAbove_ratio hb) ⟨(u, v), huv⟩)

lemma upperRatio_mem_Icc {D D' : DistC → ContMetric} {g : DistC} {K : ℝ}
    (hb : BiLip (D g) (D' g) K) : K⁻¹ ≤ upperRatio D D' g ∧ upperRatio D D' g ≤ K := by
  constructor
  · have h01 : K⁻¹ ≤ (D' g).1 (0, 1) / (D g).1 (0, 1) :=
      (le_div_iff₀ (pos_of_ne _ zero_ne_one)).2 (hb 0 1).1
    exact h01.trans (le_ciSup (f := fun p : {p : ℂ × ℂ // p.1 ≠ p.2} =>
      (D' g).1 p.1 / (D g).1 p.1) (bddAbove_ratio hb) ⟨(0, 1), zero_ne_one⟩)
  · exact ciSup_le fun p => (div_le_iff₀ (pos_of_ne _ p.2)).2 (hb _ _).2

lemma BiLip.swap {D D' : ContMetric} {K : ℝ} (hK : 0 < K) (hb : BiLip D D' K) :
    BiLip D' D K := by
  intro u v
  obtain ⟨h1, h2⟩ := hb u v
  constructor
  · rw [inv_mul_le_iff₀ hK]; exact h2
  · have := mul_le_mul_of_nonneg_left h1 hK.le
    rwa [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at this

/-- `c_*(g) = (C_*` of the swapped pair`)⁻¹` (GM l. 1189: "identical manner") -/
theorem lowerRatio_eq_inv {D D' : DistC → ContMetric} {g : DistC} {K : ℝ} (hK : 0 < K)
    (hb : BiLip (D g) (D' g) K) : lowerRatio D D' g = (upperRatio D' D g)⁻¹ := by
  set f : {p : ℂ × ℂ // p.1 ≠ p.2} → ℝ := fun p => (D' g).1 p.1 / (D g).1 p.1
  have hf : ∀ p : {p : ℂ × ℂ // p.1 ≠ p.2}, (D g).1 p.1 / (D' g).1 p.1 = (f p)⁻¹ := fun p => (inv_div _ _).symm
  have hfpos : ∀ p, 0 < f p := fun p => div_pos (pos_of_ne _ p.2) (pos_of_ne _ p.2)
  have hs := upperRatio_mem_Icc (D := D') (D' := D) (hb.swap hK)
  have hspos : 0 < upperRatio D' D g := (inv_pos.2 hK).trans_le hs.1
  have hu : upperRatio D' D g = ⨆ p, (f p)⁻¹ := by
    simp only [upperRatio, hf]
  have hl : lowerRatio D D' g = ⨅ p, f p := rfl
  have hipos : K⁻¹ ≤ ⨅ p, f p := le_ciInf fun p => (le_div_iff₀ (pos_of_ne _ p.2)).2 (hb _ _).1
  have hbdd' := bddAbove_ratio (hb.swap hK)
  rw [hl]
  refine le_antisymm ?_ ?_
  · rw [le_inv_comm₀ ((inv_pos.2 hK).trans_le hipos) hspos, hu]
    refine ciSup_le fun p => ?_
    exact (inv_le_inv₀ (hfpos p) ((inv_pos.2 hK).trans_le hipos)).2
      (ciInf_le (bddBelow_ratio hb) p)
  · refine le_ciInf fun p => ?_
    rw [inv_le_comm₀ hspos (hfpos p), hu]
    have := le_ciSup (f := fun p : {p : ℂ × ℂ // p.1 ≠ p.2} => (D g).1 p.1 / (D' g).1 p.1)
      hbdd' p
    simp only [hf] at this
    exact this

end LQGMetric.GM
