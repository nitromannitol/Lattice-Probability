/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.P52Bilip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bGeo
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Meas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventStmts
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicGMMeas

/-!
# GM Prop 5.2 (C): the bi-Lipschitz bounds at `h − φ` (task P2-M2M9)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`.
GM use throughout §5 that `c_* D_{h−φ} ≤ D̃_{h−φ} ≤ C_* D_{h−φ}` a.s. for a fixed smooth `φ`
(e.g. l. 3500–3510 in the proof of Lemma 5.11: the bounds (1.21) are applied to the field
`h − φ`), which holds because the law of `h − φ` is absolutely continuous w.r.t. that of `h`
modulo additive constants (GM l. 2808, Cameron–Martin) and the bounds are invariant under adding
constants (Weyl scaling, Axiom III). This file proves it, as `ae_isGeod_sel_addFun`
(Prop43bGeo.lean) does for geodesics:

* `bilipAt_iff_dense` / `measurableSet_bilipAt`: `BilipAt` is a countable intersection of Borel
  conditions (dense sequence `LocalEvent.qd`, `ratio_of_dense`);
* `ae_bilipAt` : a.s. `BilipAt` at `h` (`RatiosAre`, `ratio_of_ratios`);
* `ae_bilipAt_subTest` : a.s. `BilipAt` at `h − φ` (`ae_notMem_addFun_of_ae`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

lemma bilipAt_iff_dense {D D' : DistC → ContMetric} {cs Cs : ℝ} {g : DistC} :
    BilipAt D D' cs Cs g ↔ ∀ i j : ℕ,
      cs * (D g).1 (LocalEvent.qd i, LocalEvent.qd j) ≤ (D' g).1 (LocalEvent.qd i, LocalEvent.qd j) ∧
      (D' g).1 (LocalEvent.qd i, LocalEvent.qd j) ≤ Cs * (D g).1 (LocalEvent.qd i, LocalEvent.qd j) :=
  ⟨fun h _ _ => h _ _, fun h => ratio_of_dense h⟩

lemma measurableSet_bilipAt {D D' : DistC → ContMetric} (hDm : Measurable D)
    (hD'm : Measurable D') (cs Cs : ℝ) : MeasurableSet {g | BilipAt D D' cs Cs g} := by
  have e : {g | BilipAt D D' cs Cs g} = ⋂ i : ℕ, ⋂ j : ℕ,
      ({g | cs * (D g).1 (LocalEvent.qd i, LocalEvent.qd j) ≤
          (D' g).1 (LocalEvent.qd i, LocalEvent.qd j)} ∩
        {g | (D' g).1 (LocalEvent.qd i, LocalEvent.qd j) ≤
          Cs * (D g).1 (LocalEvent.qd i, LocalEvent.qd j)}) := by
    ext g; simp only [mem_setOf_eq, mem_iInter, mem_inter_iff, bilipAt_iff_dense]
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have m1 := measurable_contMetric_apply hDm (LocalEvent.qd i, LocalEvent.qd j)
  have m2 := measurable_contMetric_apply hD'm (LocalEvent.qd i, LocalEvent.qd j)
  exact (measurableSet_le (measurable_const.mul m1) m2).inter
    (measurableSet_le m2 (measurable_const.mul m1))

/-- `BilipAt` is invariant under a common positive rescaling of both metrics -/
lemma bilipAt_iff_of_scale {D D' : DistC → ContMetric} {cs Cs e : ℝ} (he : 0 < e) {g g' : DistC}
    (h1 : ∀ x y : ℂ, (D g').1 (x, y) = e * (D g).1 (x, y))
    (h2 : ∀ x y : ℂ, (D' g').1 (x, y) = e * (D' g).1 (x, y)) :
    BilipAt D D' cs Cs g' ↔ BilipAt D D' cs Cs g := by
  unfold BilipAt
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [h1, h2]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨le_of_mul_le_mul_left (by linarith) he, le_of_mul_le_mul_left (by linarith) he⟩
  · rintro ⟨a, b⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- a.s. `c_* D_h ≤ D̃_h ≤ C_* D_h` (GM (1.21) with `c_*, C_*` deterministic) -/
theorem ae_bilipAt {D D' : DistC → ContMetric} {cs Cs : ℝ} (hRat : RatiosAre D D' cs Cs)
    (hcs : 0 < cs) (hCs : cs ≤ Cs) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, BilipAt D D' cs Cs (h ω) := by
  filter_upwards [hRat P h hh] with ω hω
  exact fun x y => ratio_of_ratios hcs hCs hω.1 hω.2 x y

/-- a.s. `c_* D_{h−φ} ≤ D̃_{h−φ} ≤ C_* D_{h−φ}` for a fixed test function `φ` (Cameron–Martin
transfer, GM l. 2808) -/
theorem ae_bilipAt_subTest {γ : ℝ} {D D' : DistC → ContMetric} {c₀ : ℝ → ℝ}
    (hPS : PairSetting γ D D' c₀) {cs Cs : ℝ} (hRat : RatiosAre D D' cs Cs) (hcs : 0 < cs)
    (hCs : cs ≤ Cs) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (φ : TestC) :
    ∀ᵐ ω ∂P, BilipAt D D' cs Cs (subTest (h ω) φ) := by
  obtain ⟨-, -, hD, hD'⟩ := hPS
  have hρ := GFFLaw.integral_bumpTest 0 0
  set B : Set DistC := {g | ¬ BilipAt D D' cs Cs g} with hBdef
  have hBm : MeasurableSet B := (measurableSet_bilipAt hD.measurable hD'.measurable cs Cs).compl
  have hB : UMeasurableSet B := fun μ _ => hBm.nullMeasurableSet
  have hinv : ∀ {g : Ω → DistC}, IsGFFPlusCont g P → ∀ᵐ ω ∂P,
      (g ω ∈ B ↔ GFFLaw.recenter (bumpTest 0 0) (g ω) ∈ B) := by
    intro g hg
    filter_upwards [hD.ae_dist_addConst hg, hD'.ae_dist_addConst hg] with ω h1 h2
    show ¬ BilipAt D D' cs Cs (g ω) ↔
      ¬ BilipAt D D' cs Cs (addConst (g ω) (-(g ω (bumpTest 0 0))))
    rw [bilipAt_iff_of_scale (Real.exp_pos _) (h1 _) (h2 _)]
  have h0 : ∀ᵐ ω ∂P, h ω ∉ B := by
    filter_upwards [ae_bilipAt hRat hcs hCs hh] with ω hω
    exact fun hb => hb hω
  filter_upwards [ae_notMem_addFun_of_ae hh (-φ) hρ hB h0
    (hinv (Tight.isGFFPlusCont_of_wp hh)) (hinv (isGFFPlusCont_addFun_test hh (-φ)))] with ω hω
  rw [subTest_eq_addFun_neg_cm]
  by_contra hc
  exact hω hc

end LQGMetric.GM
