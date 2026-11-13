/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GoodLineOscillation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LineVariation
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Oscillation along a good horizontal line

This module proves the second assertion of the manuscript lemma `s:lem:lines`: at a
non-exceptional offset `y`, the oscillation of `f` over the cells meeting the segment
`[a,b] × {y}` is bounded by the line variation `V_f(y)` of
`ReflectedGMS.horizontalLineVariation`.

The connectivity input is `ReflectedGMS.HorizontalGood F y`, which provides a *finite
walk* inside the segment-induced subgraph between any two cells meeting the segment.
Replacing the walk by `SimpleGraph.Walk.bypass` makes it a simple path, so its darts are
pairwise distinct and no dart occurs together with its reverse.  Consequently the
forward darts and the reversed darts of the path give `2 · (path variation)` distinct
ordered pairs inside the ambient ordered-pair sum, which is exactly the factor `2` that
`horizontalLineVariation` divides out.  No summability, finiteness or integrability
hypothesis is used: both sides live in `ℝ≥0∞`.

The vertical analogue is *not* proved here: `ReflectedGMS.horizontalLineVariation` and
its offset machinery are stated only for horizontal segments, so a vertical statement
needs the vertical counterpart of `ReflectedGMS.Corrector.LineVariation` first.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

variable {V : Type*}

/-! ### Telescoping along a walk -/

/-- **Telescoping along a walk.**  The increment of `f` between the endpoints of a walk is
at most the sum of the absolute increments along its darts. -/
theorem ofReal_abs_sub_le_sum_darts {G : SimpleGraph V} (f : V → ℝ) {v w : V}
    (p : G.Walk v w) :
    ENNReal.ofReal |f w - f v|
      ≤ (p.darts.map fun d : G.Dart => ENNReal.ofReal |f d.toProd.2 - f d.toProd.1|).sum := by
  induction p with
  | nil => simp
  | @cons u x z h q ih =>
    have htri : |f z - f u| ≤ |f x - f u| + |f z - f x| := by
      have h1 : |f z - f u| ≤ |f z - f x| + |f x - f u| := abs_sub_le (f z) (f x) (f u)
      linarith
    calc ENNReal.ofReal |f z - f u|
        ≤ ENNReal.ofReal (|f x - f u| + |f z - f x|) := ENNReal.ofReal_le_ofReal htri
      _ = ENNReal.ofReal |f x - f u| + ENNReal.ofReal |f z - f x| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ ENNReal.ofReal |f x - f u| +
            (q.darts.map fun d : G.Dart =>
              ENNReal.ofReal |f d.toProd.2 - f d.toProd.1|).sum := add_le_add le_rfl ih
      _ = ((SimpleGraph.Walk.cons h q).darts.map fun d : G.Dart =>
            ENNReal.ofReal |f d.toProd.2 - f d.toProd.1|).sum := by
          rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]

/-! ### Symmetry of the edge terms -/

/-- The absolute gradient does not depend on the orientation of the pair. -/
theorem edgeGradAbs_swap (G : ReflectedWalk.ConductanceGraph V) (f : V → ℝ) (p : V × V) :
    edgeGradAbs G f p.swap = edgeGradAbs G f p := by
  by_cases hadj : G.Adj p.1 p.2
  · have hadj' : G.Adj p.swap.1 p.swap.2 := G.adj_symm hadj
    rw [edgeGradAbs, edgeGradAbs, if_pos hadj, if_pos hadj']
    simp [abs_sub_comm]
  · have hadj' : ¬ G.Adj p.swap.1 p.swap.2 := fun h => hadj (G.adj_symm h)
    rw [edgeGradAbs, edgeGradAbs, if_neg hadj, if_neg hadj']

/-- The line edge term does not depend on the orientation of the pair; this is why the
ordered-pair sum defining `horizontalLineVariation` counts each edge twice. -/
theorem horizontalLineEdgeTerm_swap (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) (y : ℝ) :
    horizontalLineEdgeTerm F f a b p.swap y = horizontalLineEdgeTerm F f a b p y := by
  simp only [horizontalLineEdgeTerm, Prod.fst_swap, Prod.snd_swap, edgeGradAbs_swap,
    Set.inter_comm (horizontalHitOffsets F a b p.2) (horizontalHitOffsets F a b p.1)]

/-! ### From a finite simple path to the full edge variation -/

/-- **The finite simple-path bound.**  If every vertex of the path `q` meets the segment
`[a,b] × {y}`, then twice the variation of `f` along the darts of `q` is at most the full
ordered-pair edge sum of the segment.  The factor `2` comes from the reversed darts,
which are distinct ordered pairs because `q` is a simple path. -/
theorem two_mul_sum_darts_le_tsum_horizontalLineEdgeTerm (F : IndexedCells V) (f : V → ℝ)
    (a b y : ℝ) {v w : V} (q : F.graph.toSimpleGraph.Walk v w) (hq : q.IsPath)
    (hhit : ∀ z ∈ q.support, Hits F (horizontal a b y) z) :
    2 * (q.darts.map fun d : F.graph.toSimpleGraph.Dart =>
          ENNReal.ofReal |f d.toProd.2 - f d.toProd.1|).sum
      ≤ ∑' p : V × V, horizontalLineEdgeTerm F f a b p y := by
  classical
  set T : V × V → ℝ≥0∞ := fun p => horizontalLineEdgeTerm F f a b p y with hT
  set L : List (V × V) := q.darts.map SimpleGraph.Dart.toProd with hL
  have hdartsNodup : q.darts.Nodup :=
    SimpleGraph.Walk.darts_nodup_of_support_nodup hq.support_nodup
  have hLnodup : L.Nodup := hdartsNodup.map SimpleGraph.Dart.toProd_injective
  set D : Finset (V × V) := L.toFinset with hD
  -- each dart term is the corresponding line edge term
  have hterm : ∀ d ∈ q.darts,
      (T ∘ SimpleGraph.Dart.toProd) d
        = ENNReal.ofReal |f d.toProd.2 - f d.toProd.1| := by
    intro d hd
    have hadj : F.graph.Adj d.toProd.1 d.toProd.2 := d.adj
    have h1 : Hits F (horizontal a b y) d.toProd.1 :=
      hhit _ (SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts q hd)
    have h2 : Hits F (horizontal a b y) d.toProd.2 :=
      hhit _ (q.dart_snd_mem_support_of_mem_darts hd)
    simp only [hT, Function.comp_apply]
    rw [horizontalLineEdgeTerm_apply, if_pos ⟨hadj, h1, h2⟩]
  have hDsum : ∑ p ∈ D, T p
      = (q.darts.map fun d : F.graph.toSimpleGraph.Dart =>
          ENNReal.ofReal |f d.toProd.2 - f d.toProd.1|).sum := by
    rw [hD, List.sum_toFinset _ hLnodup, hL, List.map_map]
    exact congrArg List.sum (List.map_congr_left hterm)
  -- the reversed darts are distinct ordered pairs
  have hdisj : Disjoint D (D.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [hD, List.mem_toFinset, hL, List.mem_map] at hp
    obtain ⟨d, hd, hdp⟩ := hp
    rw [Finset.mem_image] at hp'
    obtain ⟨p', hp', hswap⟩ := hp'
    rw [hD, List.mem_toFinset, hL, List.mem_map] at hp'
    obtain ⟨d', hd', hd'p⟩ := hp'
    have hdd : d = d'.symm := by
      refine SimpleGraph.Dart.ext _ _ ?_
      rw [SimpleGraph.Dart.symm_toProd, hd'p, hswap, hdp]
    have hnd : (q.darts.map SimpleGraph.Dart.edge).Nodup := hq.isTrail.edges_nodup
    have hedge : d.edge = d'.edge := by
      rw [hdd]
      exact SimpleGraph.Dart.edge_symm d'
    have hdd' : d = d' := List.inj_on_of_nodup_map hnd hd hd' hedge
    exact SimpleGraph.Dart.symm_ne d' (by rw [← hdd, hdd'])
  have himage : ∑ p ∈ D.image Prod.swap, T p = ∑ p ∈ D, T p := by
    rw [Finset.sum_image (Prod.swap_injective.injOn)]
    exact Finset.sum_congr rfl fun p _ => horizontalLineEdgeTerm_swap F f a b p y
  calc 2 * (q.darts.map fun d : F.graph.toSimpleGraph.Dart =>
          ENNReal.ofReal |f d.toProd.2 - f d.toProd.1|).sum
      = ∑ p ∈ D, T p + ∑ p ∈ D, T p := by rw [hDsum, two_mul]
    _ = ∑ p ∈ D ∪ D.image Prod.swap, T p := by rw [Finset.sum_union hdisj, himage]
    _ ≤ ∑' p : V × V, T p := ENNReal.sum_le_tsum _

/-- The increment of `f` between the endpoints of a walk inside the segment subgraph is
bounded by the line variation `V_f(y)`, with the `/2` normalization of
`ReflectedGMS.horizontalLineVariation` intact. -/
theorem ofReal_abs_sub_le_horizontalLineVariation_of_walk (F : IndexedCells V) (f : V → ℝ)
    (a b y : ℝ) {v w : V} (p : F.graph.toSimpleGraph.Walk v w)
    (hp : ∀ z ∈ p.support, Hits F (horizontal a b y) z) :
    ENNReal.ofReal |f w - f v| ≤ horizontalLineVariation F f a b y := by
  classical
  have hpath : p.bypass.IsPath := p.bypass_isPath
  have hhit : ∀ z ∈ p.bypass.support, Hits F (horizontal a b y) z := fun z hz =>
    hp z (p.support_bypass_subset_support hz)
  set S := (p.bypass.darts.map fun d : F.graph.toSimpleGraph.Dart =>
      ENNReal.ofReal |f d.toProd.2 - f d.toProd.1|).sum with hS
  have hkey : 2 * S ≤ ∑' pr : V × V, horizontalLineEdgeTerm F f a b pr y :=
    two_mul_sum_darts_le_tsum_horizontalLineEdgeTerm F f a b y p.bypass hpath hhit
  have htel : ENNReal.ofReal |f w - f v| ≤ S := ofReal_abs_sub_le_sum_darts f p.bypass
  refine htel.trans ?_
  rw [horizontalLineVariation, ENNReal.div_eq_inv_mul]
  calc S = (2 : ℝ≥0∞)⁻¹ * (2 * S) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ∑' pr : V × V, horizontalLineEdgeTerm F f a b pr y :=
        mul_le_mul' le_rfl hkey

/-! ### The oscillation bound at a good offset -/

/-- **Oscillation at a good offset** (manuscript `s:lem:lines`, second assertion).  At a
non-exceptional offset `y`, any two cells meeting the segment `[a,b] × {y}` have
`|f H' - f H| ≤ V_f(y)`. -/
theorem ofReal_abs_sub_le_horizontalLineVariation (F : IndexedCells V) (f : V → ℝ)
    {a b y : ℝ} (hab : a < b) (hy : HorizontalGood F y) {v w : V}
    (hv : Hits F (horizontal a b y) v) (hw : Hits F (horizontal a b y) w) :
    ENNReal.ofReal |f w - f v| ≤ horizontalLineVariation F f a b y := by
  obtain ⟨p, hp⟩ := (horizontalGood_iff_finiteWalk F y).mp hy a b hab v w hv hw
  exact ofReal_abs_sub_le_horizontalLineVariation_of_walk F f a b y p hp

/-- `osc_{ℍ(L_y)} f`: the oscillation of `f` over the cells meeting the horizontal
segment `[a,b] × {y}`. -/
noncomputable def horizontalLineOscillation (F : IndexedCells V) (f : V → ℝ)
    (a b y : ℝ) : ℝ≥0∞ :=
  ⨆ v : {v : V // Hits F (horizontal a b y) v},
    ⨆ w : {w : V // Hits F (horizontal a b y) w}, ENNReal.ofReal |f w.1 - f v.1|

/-- **The oscillation half of the line lemma.**  At a good offset the oscillation over the
segment subgraph is at most the line variation. -/
theorem horizontalLineOscillation_le_horizontalLineVariation (F : IndexedCells V)
    (f : V → ℝ) {a b y : ℝ} (hab : a < b) (hy : HorizontalGood F y) :
    horizontalLineOscillation F f a b y ≤ horizontalLineVariation F f a b y :=
  iSup_le fun v => iSup_le fun w =>
    ofReal_abs_sub_le_horizontalLineVariation F f hab hy v.2 w.2

end ReflectedGMS
