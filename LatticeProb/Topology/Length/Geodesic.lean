/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/Geodesic.lean.
-/
import LatticeProb.Topology.Length.LengthGeodesic
import Mathlib.Analysis.ConstantSpeed

/-!
# Geodesics and their elementary properties

A curve `P : ℝ → X` is a *geodesic* on `[a, b]` when it is continuous there and its length on
`[a, b]` equals the distance between its endpoints, `curveLength P a b = edist (P a) (P b)`. This is
a minimising curve, not a Riemannian geodesic. `IsGeodesicPath γ` is the same condition for a path
`γ : Path x y`. In a length space, `isGeodesicPath_iff_forall_le` shows that geodesic paths are
exactly the paths of minimal length.

The file proves the following elementary facts:
* sub-intervals of a geodesic are minimising (`curveLength_eq_edist_of_subinterval`);
* distances along a geodesic add (`IsGeodesicCurve.edist_add`);
* a geodesic parametrized by length satisfies `d(P s, P t) = |t - s|`
  (`IsGeodesicCurve.dist_eq_of_hasUnitSpeedOn`), and conversely (`isGeodesicCurve_of_edist_eq`);
* concatenation of geodesics is a geodesic (`IsGeodesicCurve.concat`);
* in a proper length space, a geodesic parametrized by length exists between any two points
  (`exists_isGeodesicCurve_unitSpeed`).

Sources: Burago–Burago–Ivanov, *A course in metric geometry*, §2.5.1 (natural parametrization and
shortest paths) and Proposition 2.3.4 (additivity of length); Anton Petrunin, *Pure metric geometry*
(arXiv:2007.09846), §1 (geodesics as distance-preserving curves). The proofs are the standard
arguments: additivity of length and the triangle inequality.
-/

open Set Filter Topology unitInterval
open scoped ENNReal NNReal

namespace LatticeProb.MetricGeometry

section Pseudo

variable {X : Type*} [PseudoEMetricSpace X]

/-- `P : [a, b] → X` is a **geodesic**: a curve whose length equals the distance between its
endpoints. The length is the variation of `P` over `[a, b]`, so this is a minimising curve. -/
def IsGeodesicCurve (P : ℝ → X) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn P (Icc a b) ∧ curveLength P a b = edist (P a) (P b)

/-- If `len(P; [a,b]) = d(P a, P b) < ∞`, the same holds on every subinterval. -/
theorem curveLength_eq_edist_of_subinterval {P : ℝ → X} {a b s t : ℝ}
    (hP : curveLength P a b = edist (P a) (P b)) (hfin : edist (P a) (P b) ≠ ∞)
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) : curveLength P s t = edist (P s) (P t) := by
  have hsplit : curveLength P a s + curveLength P s t + curveLength P t b = curveLength P a b := by
    rw [curveLength_add _ has hst, curveLength_add _ (has.trans hst) htb]
  have htri : edist (P a) (P b) ≤ edist (P a) (P s) + edist (P s) (P t) + edist (P t) (P b) :=
    (edist_triangle _ (P t) _).trans (add_le_add (edist_triangle _ (P s) _) le_rfl)
  have h1 := edist_le_curveLength P has
  have h2 := edist_le_curveLength P htb
  have hLfin : curveLength P a b ≠ ∞ := hP ▸ hfin
  have hfa : curveLength P a s ≠ ∞ :=
    ne_top_of_le_ne_top hLfin (curveLength_mono P le_rfl (hst.trans htb))
  have hfb : curveLength P t b ≠ ∞ :=
    ne_top_of_le_ne_top hLfin (curveLength_mono P (has.trans hst) le_rfl)
  refine le_antisymm ?_ (edist_le_curveLength P hst)
  have key : curveLength P a s + curveLength P t b + curveLength P s t ≤
      curveLength P a s + curveLength P t b + edist (P s) (P t) :=
    calc _ = curveLength P a b := by rw [← hsplit]; ring
      _ = edist (P a) (P b) := hP
      _ ≤ _ := htri
      _ ≤ curveLength P a s + edist (P s) (P t) + curveLength P t b := by gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_left (ENNReal.add_ne_top.2 ⟨hfa, hfb⟩)).1 key

/-- **Distances along a geodesic add**: `d(P s, P t) + d(P t, P u) = d(P s, P u)`. -/
theorem IsGeodesicCurve.edist_add {P : ℝ → X} {a b s t u : ℝ} (hP : IsGeodesicCurve P a b)
    (hfin : edist (P a) (P b) ≠ ∞) (has : a ≤ s) (hst : s ≤ t) (htu : t ≤ u) (hub : u ≤ b) :
    edist (P s) (P t) + edist (P t) (P u) = edist (P s) (P u) := by
  rw [← curveLength_eq_edist_of_subinterval hP.2.2 hfin has hst (htu.trans hub),
    ← curveLength_eq_edist_of_subinterval hP.2.2 hfin (has.trans hst) htu hub,
    ← curveLength_eq_edist_of_subinterval hP.2.2 hfin has (hst.trans htu) hub,
    curveLength_add _ hst htu]

/-- Length of a unit-speed curve on a subinterval of `[0, L]`. -/
theorem curveLength_of_hasUnitSpeedOn {P : ℝ → X} {L s t : ℝ}
    (hu : HasUnitSpeedOn P (Icc 0 L)) (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) :
    curveLength P s t = ENNReal.ofReal (t - s) := by
  have := hu hs ht
  rwa [inter_eq_right.2 (Icc_subset_Icc hs.1 ht.2), NNReal.coe_one, one_mul] at this

/-- A geodesic parametrized by length: `d(P s, P t) = t − s` for `0 ≤ s ≤ t ≤ L`. -/
theorem IsGeodesicCurve.edist_eq_of_hasUnitSpeedOn {P : ℝ → X} {L s t : ℝ}
    (hP : IsGeodesicCurve P 0 L) (hu : HasUnitSpeedOn P (Icc 0 L)) (hs : s ∈ Icc 0 L)
    (ht : t ∈ Icc 0 L) (hst : s ≤ t) : edist (P s) (P t) = ENNReal.ofReal (t - s) := by
  have hL : 0 ≤ L := hP.1
  have hfin : edist (P 0) (P L) ≠ ∞ := by
    rw [← hP.2.2, curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩]
    exact ENNReal.ofReal_ne_top
  rw [← curveLength_eq_edist_of_subinterval hP.2.2 hfin hs.1 hst ht.2,
    curveLength_of_hasUnitSpeedOn hu hs ht]

/-- Conversely, a curve with `d(P s, P t) = |t − s|` on `[0, L]` is a geodesic parametrized by
length. -/
theorem isGeodesicCurve_of_edist_eq {P : ℝ → X} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, edist (P s) (P t) = edist s t) :
    IsGeodesicCurve P 0 L ∧ HasUnitSpeedOn P (Icc 0 L) := by
  have hlip : LipschitzOnWith 1 P (Icc 0 L) := fun s hs t ht => by
    rw [h s hs t ht, ENNReal.coe_one, one_mul]
  have hu : HasUnitSpeedOn P (Icc 0 L) := by
    rw [HasUnitSpeedOn, hasConstantSpeedOnWith_iff_ordered]
    intro s hs t ht hst
    refine le_antisymm ?_ ?_
    · calc eVariationOn P (Icc 0 L ∩ Icc s t) = eVariationOn (P ∘ id) (Icc 0 L ∩ Icc s t) := rfl
        _ ≤ (1 : ℝ≥0) * eVariationOn id (Icc 0 L ∩ Icc s t) :=
          hlip.comp_eVariationOn_le (mapsTo_id _ |>.mono_left inter_subset_left)
        _ = ENNReal.ofReal (1 * (t - s)) := by rw [eVariationOn_id hs ht]; simp
    · have := eVariationOn.edist_le P (s := Icc 0 L ∩ Icc s t) ⟨hs, le_rfl, hst⟩ ⟨ht, hst, le_rfl⟩
      rw [h s hs t ht, edist_dist, Real.dist_eq, abs_of_nonpos (by linarith), neg_sub] at this
      rwa [NNReal.coe_one, one_mul]
  refine ⟨⟨hL, hlip.continuousOn, ?_⟩, hu⟩
  rw [curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩,
    h 0 ⟨le_rfl, hL⟩ L ⟨hL, le_rfl⟩, edist_dist, Real.dist_eq, sub_zero, zero_sub, abs_neg,
    abs_of_nonneg hL]

/-- Length of a concatenation of curves `P` on `[a, b]` and `Q` on `[b, c]` with `P b = Q b`. -/
theorem curveLength_concat {P Q : ℝ → X} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hPQ : P b = Q b) :
    curveLength (fun t => if t ≤ b then P t else Q t) a c =
      curveLength P a b + curveLength Q b c := by
  rw [← curveLength_add _ hab hbc]
  congr 1
  · exact curveLength_congr fun t ht => by simp [ht.2]
  · refine curveLength_congr fun t ht => ?_
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; simp [hPQ]
    · simp [not_le.2 h]

/-- Gluing two curves that are continuous on `[a, b]` and `[b, c]` and agree at `b` gives a curve
that is continuous on `[a, c]`. -/
theorem continuousOn_concat {P Q : ℝ → X} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hPQ : P b = Q b) (hP : ContinuousOn P (Icc a b)) (hQ : ContinuousOn Q (Icc b c)) :
    ContinuousOn (fun t => if t ≤ b then P t else Q t) (Icc a c) := by
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  refine (hP.congr fun t ht => by simp [ht.2]).union_of_isClosed
    (hQ.congr fun t ht => ?_) isClosed_Icc isClosed_Icc
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp [hPQ]
  · simp [not_le.2 h]

/-- **Concatenation of geodesics**: if `P` on `[a, b]` and `Q` on `[b, c]` are geodesics with
`P b = Q b` and `d(P a, P b) + d(Q b, Q c) = d(P a, Q c)`, their concatenation is a geodesic. -/
theorem IsGeodesicCurve.concat {P Q : ℝ → X} {a b c : ℝ} (hP : IsGeodesicCurve P a b)
    (hQ : IsGeodesicCurve Q b c) (hPQ : P b = Q b)
    (hadd : edist (P a) (P b) + edist (Q b) (Q c) = edist (P a) (Q c)) :
    IsGeodesicCurve (fun t => if t ≤ b then P t else Q t) a c := by
  have hc : (if c ≤ b then P c else Q c) = Q c := by
    rcases eq_or_lt_of_le hQ.1 with h | h
    · subst h; simp [hPQ]
    · simp [not_le.2 h]
  refine ⟨hP.1.trans hQ.1, continuousOn_concat hP.1 hQ.1 hPQ hP.2.1 hQ.2.1, ?_⟩
  rw [curveLength_concat hP.1 hQ.1 hPQ, hP.2.2, hQ.2.2, hadd]
  simp only [hP.1, ite_true, hc]

/-- `γ : Path x y` is a geodesic: its length is `d(x, y)`. -/
def IsGeodesicPath {x y : X} (γ : Path x y) : Prop :=
  pathLength γ = edist x y

/-- A path is a geodesic exactly when its extension to `[0, 1]` is a geodesic curve. -/
theorem isGeodesicPath_iff_isGeodesicCurve {x y : X} (γ : Path x y) :
    IsGeodesicPath γ ↔ IsGeodesicCurve γ.extend 0 1 := by
  simp [IsGeodesicCurve, IsGeodesicPath, pathLength, γ.continuous_extend.continuousOn]

/-- The reversal of a geodesic path is a geodesic path. -/
theorem IsGeodesicPath.symm {x y : X} {γ : Path x y} (hγ : IsGeodesicPath γ) :
    IsGeodesicPath γ.symm := by
  rw [IsGeodesicPath, pathLength_symm, hγ, edist_comm]

/-- The concatenation of two geodesic paths is a geodesic path when the lengths add up to the
distance between the outer endpoints. -/
theorem IsGeodesicPath.trans {x y z : X} {γ : Path x y} {γ' : Path y z} (hγ : IsGeodesicPath γ)
    (hγ' : IsGeodesicPath γ') (hadd : edist x y + edist y z = edist x z) :
    IsGeodesicPath (γ.trans γ') := by
  rw [IsGeodesicPath, pathLength_trans, hγ, hγ', hadd]

/-- In a length space, geodesic paths are exactly the paths of minimal length. -/
theorem isGeodesicPath_iff_forall_le (hX : IsLengthSpace X) {x y : X} (γ : Path x y) :
    IsGeodesicPath γ ↔ ∀ γ' : Path x y, pathLength γ ≤ pathLength γ' := by
  refine ⟨fun h γ' => by rw [h]; exact edist_le_pathLength γ', fun h => ?_⟩
  refine le_antisymm ?_ (edist_le_pathLength γ)
  rw [← internalEDist_univ_of_isLengthSpace hX]
  exact le_iInf fun γ' => h γ'.1

end Pseudo

section Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A geodesic parametrized by length satisfies `d(P s, P t) = |t − s|`. -/
theorem IsGeodesicCurve.dist_eq_of_hasUnitSpeedOn {P : ℝ → X} {L s t : ℝ}
    (hP : IsGeodesicCurve P 0 L) (hu : HasUnitSpeedOn P (Icc 0 L)) (hs : s ∈ Icc 0 L)
    (ht : t ∈ Icc 0 L) : dist (P s) (P t) = |t - s| := by
  rcases le_total s t with hst | hst
  · have := hP.edist_eq_of_hasUnitSpeedOn hu hs ht hst
    rw [edist_dist, ENNReal.ofReal_eq_ofReal_iff dist_nonneg (by linarith)] at this
    rw [this, abs_of_nonneg (by linarith)]
  · have := hP.edist_eq_of_hasUnitSpeedOn hu ht hs hst
    rw [edist_dist, ENNReal.ofReal_eq_ofReal_iff dist_nonneg (by linarith)] at this
    rw [dist_comm, this, abs_of_nonpos (by linarith), neg_sub]

end Metric

/-- **Existence of geodesics parametrized by length** (Burago–Burago–Ivanov, *A course in metric
geometry*, Cor. 2.5.20 and §2.5.1): in a proper metric length space, any `x, y` are joined by a
geodesic `P : [0, d(x, y)] → X` with `d(P s, P t) = |t − s|`. -/
theorem exists_isGeodesicCurve_unitSpeed {X : Type*} [MetricSpace X] [ProperSpace X]
    (hX : IsLengthSpace X) (x y : X) :
    ∃ P : ℝ → X, P 0 = x ∧ P (dist x y) = y ∧ IsGeodesicCurve P 0 (dist x y) ∧
      HasUnitSpeedOn P (Icc 0 (dist x y)) ∧
      ∀ s ∈ Icc 0 (dist x y), ∀ t ∈ Icc 0 (dist x y), dist (P s) (P t) = |t - s| := by
  obtain ⟨γ, hγ⟩ := exists_pathLength_eq_edist hX x y
  set Q := γ.extend
  have hc : ContinuousOn Q (Icc 0 1) := γ.continuous_extend.continuousOn
  have hL : curveLength Q 0 1 = edist x y := hγ
  have hfin : curveLength Q 0 1 ≠ ∞ := by rw [hL]; exact edist_ne_top x y
  have hLr : (curveLength Q 0 1).toReal = dist x y := by
    rw [hL, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hu := hasUnitSpeedOn_lengthParam zero_le_one hc hfin
  rw [hLr] at hu
  have h0 : lengthParam Q 0 1 0 = x := by
    have := lengthParam_variationOnFromTo hfin (t := 0) ⟨le_rfl, zero_le_one⟩
    rwa [variationOnFromTo.self, Path.extend_zero] at this
  have h1 : lengthParam Q 0 1 (dist x y) = y := by
    have := lengthParam_variationOnFromTo hfin (t := 1) ⟨zero_le_one, le_rfl⟩
    rw [variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self, Path.extend_one] at this
    rw [← hLr]; exact this
  have hgeo : IsGeodesicCurve (lengthParam Q 0 1) 0 (dist x y) := by
    refine ⟨dist_nonneg, ?_, ?_⟩
    · have := (lipschitzOnWith_lengthParam zero_le_one hc hfin).continuousOn
      rwa [hLr] at this
    · rw [curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, dist_nonneg⟩ ⟨dist_nonneg, le_rfl⟩, h0, h1,
        edist_dist, sub_zero]
  exact ⟨lengthParam Q 0 1, h0, h1, hgeo, hu, fun s hs t ht =>
    hgeo.dist_eq_of_hasUnitSpeedOn hu hs ht⟩

/-! ### Nonvacuity examples -/

namespace GeodesicExample

/-- The identity map on `[0, 1] ⊆ ℝ` is a geodesic: its length on `[0, 1]` is `1 = d(0, 1)`. -/
example : IsGeodesicCurve (fun t : ℝ => t) 0 1 := by
  refine ⟨zero_le_one, continuousOn_id, ?_⟩
  change eVariationOn id (Icc (0 : ℝ) 1) = edist (0 : ℝ) 1
  rw [eVariationOn_id_Icc, edist_dist, Real.dist_eq]
  norm_num

/-- `ℝ` is a length space (the segment from `x` to `y` has length `d(x, y)`). Together with
`ProperSpace ℝ`, this shows that the hypotheses of `exists_isGeodesicCurve_unitSpeed` and
`isGeodesicPath_iff_forall_le` are satisfiable, so their conclusions are not vacuous. -/
example :
    (∀ x y : ℝ, ∃ P : ℝ → ℝ, P 0 = x ∧ P (dist x y) = y ∧ IsGeodesicCurve P 0 (dist x y)) ∧
    ∀ x y : ℝ, ∀ γ : Path x y,
      IsGeodesicPath γ ↔ ∀ γ' : Path x y, pathLength γ ≤ pathLength γ' := by
  have hℝ : IsLengthSpace ℝ := by
    intro x y ε hε
    let γ : Path x y :=
      { toFun := fun t => x + (t : ℝ) • (y - x)
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp }
    have hlip : LipschitzWith ‖y - x‖₊ (fun s : ℝ => x + s • (y - x)) := by
      refine LipschitzWith.of_dist_le_mul fun s t => ?_
      show dist (x + s • (y - x)) (x + t • (y - x)) ≤ (‖y - x‖₊ : ℝ) * dist s t
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq,
        coe_nnnorm]
      exact le_of_eq (mul_comm _ _)
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = x + t • (y - x) := fun t ht =>
      (Path.extend_apply γ ht).trans rfl
    refine ⟨γ, ?_⟩
    calc pathLength γ = curveLength (fun s : ℝ => x + s • (y - x)) 0 1 := by
          unfold pathLength
          exact curveLength_congr fun t ht => hγ t ht
      _ ≤ ‖y - x‖₊ * eVariationOn (id : ℝ → ℝ) (Icc 0 1) := by
          unfold curveLength
          exact hlip.lipschitzOnWith.comp_eVariationOn_le (g := id) (mapsTo_univ _ _)
      _ = edist x y := by
          rw [eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, mul_one, edist_comm,
            edist_eq_enorm_sub, enorm_eq_nnnorm]
      _ ≤ edist x y + ENNReal.ofReal ε := le_self_add
  refine ⟨fun x y => ?_, fun x y γ => isGeodesicPath_iff_forall_le hℝ γ⟩
  obtain ⟨P, h0, h1, hg, -⟩ := exists_isGeodesicCurve_unitSpeed hℝ x y
  exact ⟨P, h0, h1, hg⟩

end GeodesicExample

end LatticeProb.MetricGeometry
