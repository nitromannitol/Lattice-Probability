/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.WedgeMeasurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.BrownianMotion.Basic

/-!
The reference map of `IsQuantumWedge` is
`ω ↦ canonical γ (wedgeField (lateralPart (X ω)) (A · ω) Q)`, read through `fieldLawFull`
(`coordsFull` jointly with raw test pairings).

* `measurable_dataFull_resc`: the data of `rescale (reconstruct c) Q s` is a *measurable* function
  of `(c, s) ∈ (ℕ → ℝ) × ℝ`.
* `dataFull_canonical`: the data of `canonical γ x` is that function at `(coords x, scaleParam γ x)`,
  and on good samples `scaleParam γ x = scaleG γ (coords x)` with `scaleG` measurable
  (`measurable_scaleParam_global`).
* `aemeasurable_coords_wedgeField`: under `IsWedgeProcess` and measurable coordinates of `X`,
  `ω ↦ coords (wedgeField (lateralPart (X ω)) (A · ω) Q)` is a.e.-measurable. This needs a
  jointly measurable version of the wedge radial process, hence the measurability of `lastZero`
  of a continuous path (`measurable_lastZero`).
* `isProbabilityMeasure_fieldLawFull_wedgeRef`: consequently the reference law is a probability
  measure **provided the reference wedge field is a.s. good** (`IsLQGGood`). This a.s. goodness
  is not available (M4-A5 and the area/boundary existence for wedge fields); it is the only
  missing input.
-/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology NNReal

namespace QuantumZipper

namespace WedgeMeas

open Factorization CoordsFull

/-! ## 1. The data of a rescaled reconstruction is measurable -/

/-! ## 2. `canonical` through coordinates and the scale on good samples -/

/-! ## 3. `lastZero` of a continuous path is measurable -/

/-- `g` has a zero in `[a, b]`. -/
def ZeroIn (g : ℝ → ℝ) (a b : ℝ) : Prop := ∃ s ∈ Icc a b, g s = 0

theorem zeroIn_iff {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) :
    ZeroIn g a b ↔ ∀ m : ℕ, ∃ q : ℚ, a ≤ q ∧ (q : ℝ) ≤ b ∧ |g q| < 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, hs0⟩ m
    have hc := Metric.continuous_iff.1 hg s (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨δ, hδ, hδ'⟩ := hc
    have hlt : max a (s - δ) < min b (s + δ) :=
      max_lt (lt_min hab (by linarith)) (lt_min (by linarith) (by linarith))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, (le_max_left _ _).trans hq1.le, hq2.le.trans (min_le_left _ _), ?_⟩
    have hd : dist (q : ℝ) s < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_right a (s - δ)]
      · linarith [min_le_right b (s + δ)]
    have := hδ' _ hd
    rwa [Real.dist_eq, hs0, sub_zero] at this
  · intro h
    by_contra hno
    obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le)
      (continuous_abs.comp hg).continuousOn
    have hpos : 0 < |g s0| := abs_pos.2 fun h0 => hno ⟨s0, hs0, h0⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    obtain ⟨q, hq1, hq2, hq3⟩ := h m
    have := hmin (show (q : ℝ) ∈ Icc a b from ⟨hq1, hq2⟩)
    simp only [mem_setOf_eq, Function.comp] at this
    linarith

theorem measurable_zeroIn {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ s, Measurable fun ω => f ω s) {a b : ℝ} (hab : a < b) :
    Measurable fun ω => ZeroIn (f ω) a b := by
  have e : (fun ω => ZeroIn (f ω) a b) = fun ω => ∀ m : ℕ, ∃ q : ℚ, a ≤ q ∧ (q : ℝ) ≤ b ∧
      |f ω q| < 1 / ((m : ℝ) + 1) := funext fun ω => propext (zeroIn_iff (hc ω) hab)
  rw [e]
  exact Measurable.forall fun m => Measurable.exists fun q => measurable_const.and
    (measurable_const.and (measurableSet_setOfPred.1 (measurableSet_lt
      (continuous_abs.measurable.comp (hm q)) measurable_const)))

theorem bddAbove_zeros_iff {g : ℝ → ℝ} :
    BddAbove {s | 0 ≤ s ∧ g s = 0} ↔ ∃ N : ℕ, ∀ n : ℕ, ¬ ZeroIn g N (N + n + 1) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨⌈M⌉₊ + 1, fun n => ?_⟩
    rintro ⟨s, ⟨hs1, -⟩, hs0⟩
    have h1 := hM ⟨le_trans (by positivity) hs1, hs0⟩
    have h2 := Nat.le_ceil M
    push_cast at hs1
    linarith
  · rintro ⟨N, hN⟩
    refine ⟨N, fun s hs => ?_⟩
    by_contra h
    push_neg at h
    refine hN ⌈s⌉₊ ⟨s, ⟨h.le, ?_⟩, hs.2⟩
    have := Nat.le_ceil s
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    linarith

theorem exists_zero_gt_iff {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    (∃ s ∈ {s | 0 ≤ s ∧ g s = 0}, c < s) ↔
      ∃ n : ℕ, ZeroIn g (c + 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1) + n + 1) := by
  constructor
  · rintro ⟨s, ⟨-, hs0⟩, hcs⟩
    obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt (sub_pos.2 hcs)
    obtain ⟨n2, hn2⟩ := exists_nat_ge s
    refine ⟨max n1 n2, s, ⟨?_, ?_⟩, hs0⟩
    · have h0 : (n1 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_left n1 n2
      have : 1 / ((max n1 n2 : ℕ) + 1 : ℝ) ≤ 1 / ((n1 : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · have h1 : (n2 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_right n1 n2
      have h2 : 0 < 1 / ((max n1 n2 : ℕ) + 1 : ℝ) := by positivity
      linarith
  · rintro ⟨n, s, ⟨hs1, -⟩, hs0⟩
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨s, ⟨by linarith, hs0⟩, by linarith⟩

theorem lt_lastZero_iff {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    c < lastZero g ↔ BddAbove {s | 0 ≤ s ∧ g s = 0} ∧ ∃ s ∈ {s | 0 ≤ s ∧ g s = 0}, c < s := by
  unfold lastZero
  constructor
  · intro h
    by_cases hb : BddAbove {s | 0 ≤ s ∧ g s = 0}
    · by_cases hne : ({s | 0 ≤ s ∧ g s = 0} : Set ℝ).Nonempty
      · exact ⟨hb, exists_lt_of_lt_csSup hne h⟩
      · rw [not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty] at h; linarith
    · rw [Real.sSup_of_not_bddAbove hb] at h; linarith
  · rintro ⟨hb, s, hs, hcs⟩
    exact lt_csSup_of_lt hb hs hcs

theorem measurable_lastZero {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ s, Measurable fun ω => f ω s) :
    Measurable fun ω => lastZero (f ω) := by
  refine measurable_of_Ioi fun c => ?_
  by_cases hc0 : c < 0
  · have e : (fun ω => lastZero (f ω)) ⁻¹' Ioi c = univ := by
      ext ω
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact hc0.trans_le (Real.sSup_nonneg fun s hs => hs.1)
    rw [e]; exact MeasurableSet.univ
  · push_neg at hc0
    have e : (fun ω => lastZero (f ω)) ⁻¹' Ioi c =
        {ω | (∃ N : ℕ, ∀ n : ℕ, ¬ ZeroIn (f ω) N (N + n + 1)) ∧
          ∃ n : ℕ, ZeroIn (f ω) (c + 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1) + n + 1)} := by
      ext ω
      simp only [mem_preimage, mem_Ioi, mem_setOf_eq]
      rw [lt_lastZero_iff hc0, bddAbove_zeros_iff, exists_zero_gt_iff hc0]
    rw [e]
    refine measurableSet_setOfPred.2 ((Measurable.exists fun N => Measurable.forall fun n =>
      (measurable_zeroIn hc hm ?_).not).and (Measurable.exists fun n => measurable_zeroIn hc hm ?_))
    · linarith
    · linarith

/-! ## 4. A jointly measurable version of the wedge radial process -/

/-- Joint measurability of the wedge path built from paths that are continuous for every `ω`
and measurable for every time. -/
theorem measurable_wedgePath_joint {Ω : Type*} [MeasurableSpace Ω] (α Q : ℝ)
    {B B' : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous fun t => B t ω)
    (hB'c : ∀ ω, Continuous fun t => B' t ω) (hBm : ∀ t, Measurable (B t))
    (hB'm : ∀ t, Measurable (B' t)) :
    Measurable fun q : Ω × ℝ => wedgePath α Q (fun s => B s q.1) (fun s => B' s q.1) q.2 := by
  have hJ : ∀ {C : ℝ≥0 → Ω → ℝ}, (∀ ω, Continuous fun t => C t ω) → (∀ t, Measurable (C t)) →
      Measurable fun q : Ω × ℝ => C q.2.toNNReal q.1 := fun hc hm =>
    (measurable_uncurry_of_continuous_of_measurable hc hm).comp
      ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  set f : Ω → ℝ → ℝ := fun ω s => Real.sqrt 2 * B' s.toNNReal ω - (α - Q) * s with hf
  have hfc : ∀ ω, Continuous (f ω) := fun ω =>
    (continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hfm : ∀ s, Measurable fun ω => f ω s := fun s =>
    ((hB'm _).const_mul _).sub measurable_const
  have hF : Measurable fun q : Ω × ℝ => f q.1 q.2 :=
    ((hJ hB'c hB'm).const_mul _).sub (measurable_snd.const_mul _)
  have hL := measurable_lastZero hfc hfm
  have e : (fun q : Ω × ℝ => wedgePath α Q (fun s => B s q.1) (fun s => B' s q.1) q.2) =
      fun q => if 0 ≤ q.2 then Real.sqrt 2 * B q.2.toNNReal q.1 + (α - Q) * q.2
        else f q.1 (-q.2 + lastZero (f q.1)) := rfl
  rw [e]
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (((hJ hBc hBm).const_mul _).add (measurable_snd.const_mul _)) ?_
  exact hF.comp (measurable_fst.prodMk (measurable_snd.neg.add (hL.comp measurable_fst)))

/-! ## 5. Coordinates of the wedge field -/

/-! ## 6. The reference law -/

end WedgeMeas

end QuantumZipper
