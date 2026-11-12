/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bGeo

/-!
# Measurability of the event `𝔈_r` (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
GM treat `𝔈_r` (l. 2759–2771) as an event without comment; Lemma 5.3 (l. 2775) and Lemma 5.4
need it to be measurable. Own elementary argument (no source states it): the condition (5.4)
is an open condition (`0 < s < t < 1`, `P(s), P(t) ∈ B_{3r/2}(z)`) and closed conditions in
`(P, D_h, D̃_h, s, t)`; on each compact piece `{s ≥ δ, t ≥ s + δ, t ≤ 1 − δ, |P(·) − z| ≤ 3r/2 − δ}`
the set of good `(P, D_h, D̃_h)` is the projection along the compact `[0,1]²` of a closed set,
hence closed (`isClosedMap_fst_of_compactSpace`); `𝔈_r` is the countable union over `δ = 1/(n+1)`,
pulled back by the measurable map `g ↦ (sel 𝕫 𝕨 g, D_g, D̃_g)`. The `D̃`-distance to `∂B_{3r}(z)`
enters through `∀ w ∈ ∂B_{3r}(z)`, a closed condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `ofReal f ≤ k · D(x, S)` is a closed condition -/
lemma isClosed_le_mul_setDist {Y : Type*} [TopologicalSpace Y] {f : Y → ℝ} (hf : Continuous f)
    {dd : Y → ContMetric} (hdd : Continuous dd) {x : Y → ℂ} (hx : Continuous x) {k : ℝ≥0∞}
    (hk : k ≠ ⊤) (S : Set ℂ) :
    IsClosed {y | ENNReal.ofReal (f y) ≤ k * setDist (dd y) {x y} S} := by
  by_cases hk0 : k = 0
  · simp only [hk0, zero_mul]
    exact isClosed_le (ENNReal.continuous_ofReal.comp hf) continuous_const
  have e : {y | ENNReal.ofReal (f y) ≤ k * setDist (dd y) {x y} S} =
      ⋂ w ∈ S, {y | ENNReal.ofReal (f y) ≤ k * ENNReal.ofReal ((dd y).1 (x y, w))} := by
    ext y
    simp only [mem_ofPred_eq, mem_iInter, setDist_eq_iInf, iInf_singleton,
      ENNReal.mul_iInf_of_ne hk0 hk, le_iInf_iff]
  rw [e]
  refine isClosed_biInter fun w _ => isClosed_le (ENNReal.continuous_ofReal.comp hf) ?_
  refine (ENNReal.continuous_const_mul hk).comp (ENNReal.continuous_ofReal.comp ?_)
  exact continuous_contMetric_apply.comp (hdd.prodMk (hx.prodMk continuous_const))

/-- the compact piece of (5.4) at margin `δ`, in the variables `((P, D, D̃), (s, t))` -/
def frkPiece (cs Cs c₂ b₀ r : ℝ) (z : ℂ) (δ : ℝ) :
    Set ((C(unitInterval, ℂ) × ContMetric × ContMetric) × (unitInterval × unitInterval)) :=
  {q | δ ≤ (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) + δ ≤ q.2.2 ∧ (q.2.2 : ℝ) ≤ 1 - δ ∧
    dist (q.1.1 q.2.1) z ≤ 3 / 2 * r - δ ∧ dist (q.1.1 q.2.2) z ≤ 3 / 2 * r - δ ∧
    b₀ * r ≤ ‖q.1.1 q.2.1 - q.1.1 q.2.2‖ ∧
    q.1.2.2.1 (q.1.1 q.2.1, q.1.1 q.2.2) ≤ c₂ * q.1.2.1.1 (q.1.1 q.2.1, q.1.1 q.2.2) ∧
    ENNReal.ofReal (q.1.2.2.1 (q.1.1 q.2.1, q.1.1 q.2.2)) ≤
      ENNReal.ofReal (cs / Cs) * setDist q.1.2.2 {q.1.1 q.2.1} (Metric.sphere z (3 * r))}

lemma isClosed_frkPiece (cs Cs c₂ b₀ r : ℝ) (z : ℂ) (δ : ℝ) :
    IsClosed (frkPiece cs Cs c₂ b₀ r z δ) := by
  have hs : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => (q.2.1 : ℝ) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have ht : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => (q.2.2 : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hQs : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => q.1.1 q.2.1 :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))
  have hQt : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => q.1.1 q.2.2 :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd))
  have hd : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => q.1.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have hd' : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => q.1.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_fst)
  have hD : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => q.1.2.1.1 (q.1.1 q.2.1, q.1.1 q.2.2) :=
    continuous_contMetric_apply.comp (hd.prodMk (hQs.prodMk hQt))
  have hD' : Continuous fun q : (C(unitInterval, ℂ) × ContMetric × ContMetric) ×
      (unitInterval × unitInterval) => q.1.2.2.1 (q.1.1 q.2.1, q.1.1 q.2.2) :=
    continuous_contMetric_apply.comp (hd'.prodMk (hQs.prodMk hQt))
  refine (isClosed_le continuous_const hs).inter ((isClosed_le (hs.add continuous_const) ht).inter
    ((isClosed_le ht continuous_const).inter ((isClosed_le (hQs.dist continuous_const)
      continuous_const).inter ((isClosed_le (hQt.dist continuous_const) continuous_const).inter
      ((isClosed_le continuous_const (hQs.sub hQt).norm).inter ((isClosed_le hD'
      (continuous_const.mul hD)).inter ?_))))))
  exact isClosed_le_mul_setDist hD' hd' hQs ENNReal.ofReal_ne_top _

/-- (5.4) is the union over `n` of the projections of the compact pieces -/
lemma frkDist_iff_exists_piece {D D' : DistC → ContMetric} {cs Cs c₂ b₀ r : ℝ} {z : ℂ}
    {g : DistC} {Q : C(unitInterval, ℂ)} :
    frkDist D D' cs Cs c₂ b₀ r z g Q ↔ ∃ n : ℕ, ∃ st : unitInterval × unitInterval,
      ((Q, D g, D' g), st) ∈ frkPiece cs Cs c₂ b₀ r z (1 / ((n : ℝ) + 1)) := by
  constructor
  · rintro ⟨s, t, hs0, hst, ht1, hQs, hQt, hb, hc, hd⟩
    have hs0' : (0 : ℝ) < s := hs0
    have hst' : (s : ℝ) < t := hst
    have ht1' : (t : ℝ) < 1 := ht1
    rw [Metric.mem_ball] at hQs hQt
    set m := min (min (s : ℝ) ((t : ℝ) - s)) (min (1 - (t : ℝ))
      (min (3 / 2 * r - dist (Q s) z) (3 / 2 * r - dist (Q t) z))) with hm
    have hmpos : 0 < m := by
      simp only [hm, lt_min_iff]
      exact ⟨⟨hs0', by linarith⟩, by linarith, by linarith, by linarith⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmpos
    have h1 : m ≤ (s : ℝ) := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : m ≤ (t : ℝ) - s := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : m ≤ 1 - (t : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : m ≤ 3 / 2 * r - dist (Q s) z :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have h5 : m ≤ 3 / 2 * r - dist (Q t) z :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨n, (s, t), by linarith, by linarith, by linarith, by linarith, by linarith, hb, hc, hd⟩
  · rintro ⟨n, ⟨s, t⟩, h1, h2, h3, h4, h5, hb, hc, hd⟩
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨s, t, ?_, ?_, ?_, ?_, ?_, hb, hc, hd⟩
    · show (0 : ℝ) < s; linarith
    · show (s : ℝ) < t; linarith
    · show (t : ℝ) < 1; linarith
    · rw [Metric.mem_ball]; linarith
    · rw [Metric.mem_ball]; linarith

/-- **`𝔈_r` is measurable** (for a measurable selector and a finite `𝓖_r`) -/
theorem measurableSet_frkE {D D' : DistC → ContMetric} (hDm : Measurable D)
    (hD'm : Measurable D') {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {a b : ℂ}
    (hselm : Measurable (sel a b)) (cs Cs c₂ b₀ Λ r : ℝ) (G : Finset TestC) (z : ℂ) :
    MeasurableSet (frkE D D' sel cs Cs c₂ b₀ Λ r (G : Set TestC) z a b) := by
  have hΨ : Measurable fun g : DistC => (sel a b g, D g, D' g) :=
    hselm.prodMk (hDm.prodMk hD'm)
  have e : frkE D D' sel cs Cs c₂ b₀ Λ r (G : Set TestC) z a b =
      (⋃ n : ℕ, (fun g : DistC => (sel a b g, D g, D' g)) ⁻¹'
        (Prod.fst '' frkPiece cs Cs c₂ b₀ r z (1 / ((n : ℝ) + 1)))) ∩
      ⋂ φ ∈ G, {g | Real.exp (-dirInner g φ + gradEnergy φ / 2) ≤ Λ} := by
    ext g
    simp only [frkE, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_preimage, mem_image,
      Prod.exists, mem_iInter, Finset.mem_coe, frkDist_iff_exists_piece, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨n, s, t, hst⟩, h2⟩
      exact ⟨⟨n, _, _, _, s, t, hst, rfl, rfl, rfl⟩, h2⟩
    · rintro ⟨⟨n, Q, d, d', s, t, hst, rfl, rfl, rfl⟩, h2⟩
      exact ⟨⟨n, s, t, hst⟩, h2⟩
  rw [e]
  refine (MeasurableSet.iUnion fun n => hΨ ?_).inter
    (Finset.measurableSet_biInter G fun φ _ => ?_)
  · exact ((isClosedMap_fst_of_compactSpace _ (isClosed_frkPiece cs Cs c₂ b₀ r z _))).measurableSet
  · refine measurableSet_le ?_ measurable_const
    exact Real.measurable_exp.comp
      (((GFFInv.measurable_pair (cmTest φ)).neg).add_const _)

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

end LQGMetric.GM
