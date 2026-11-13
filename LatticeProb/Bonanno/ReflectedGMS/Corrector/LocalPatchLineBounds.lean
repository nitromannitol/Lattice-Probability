/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.LocalPatchLineBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.VerticalLineVariation
import LatticeProb.Bonanno.ReflectedGMS.Graph.Restriction
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The line estimate localized to a bounded rectangle patch

`ReflectedGMS.Corrector.LineVariation`, `ReflectedGMS.Corrector.GoodLineOscillation` and
`ReflectedGMS.Corrector.VerticalLineVariation` prove the manuscript lemma `s:lem:lines`
with the *whole-plane* geometric mass `∑_H d_H ^ 2 π*(H)` and the *whole-plane* energy
`ℰ(f)` on the right-hand side.  Both of these are typically infinite: the manuscript
statement is about the restricted graph `G_{Q_R}` on the rectangle patch `Q_R` and about
the patch sums `∑_{H ∈ ℍ(Q_R)} d_H ^ 2 π*(H)` and `ℰ_{G_{Q_R}}(f)`.

This module supplies that localization.  The patch is described by an arbitrary vertex
set `A ⊆ V`; the geometric hypothesis is only that *every cell meeting the segment lies
in `A`*, which for `A = ℍ(Q)` is immediate once the segment is contained in `Q`.

The central observation is `ReflectedGMS.horizontalLineVariation_restrictIndexedCells`:
for such a segment the line variation of the restricted cell family
`ReflectedGMS.restrictIndexedCells F A` *equals* the whole-plane line variation, because
the whole-plane ordered-pair sum is already supported on `A × A`.  Feeding this into the
existing estimate gives the localized bound

`∫⁻ y in s, V_f(y) ≤ (∑_{H ∈ A} d_H ^ 2 π*(H)) ^ (1/2) · ℰ_{G_A}(f) ^ (1/2)`,

in which *both* factors are patch quantities.  No finiteness of the whole-plane energy,
of the whole-plane mass, or of the cell count is used anywhere: every quantity lives in
`ℝ≥0∞`.

The offset integral is then converted by Markov's inequality into the *good-line
selection* step the uniform-sublinearity proof actually consumes: as soon as the patch
bound is smaller than `t · |s|`, the offset window `s` contains an offset which is
simultaneously outside the exceptional null set and has oscillation at most `t`.

Everything is proved for both directions, with the ordered-edge `/2` normalization of
`ReflectedGMS.horizontalLineVariation` intact and with the almost-everywhere offset
statements still holding simultaneously for *all* endpoint pairs `a < b`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

variable {V : Type*}

/-! ### The restricted cell family -/

/-- The cell family restricted to a vertex subset `A`: the cells are unchanged and the
conductance graph is the induced one, `ReflectedGMS.restrictGraph`.  For
`A = {v | Hits F Q v}` this is the manuscript's restricted graph `G_Q` together with its
cells `ℍ(Q)`. -/
def restrictIndexedCells (F : IndexedCells V) (A : Set V) : IndexedCells A where
  cell v := F.cell v.1
  graph := restrictGraph F.graph A

@[simp]
theorem restrictIndexedCells_graph (F : IndexedCells V) (A : Set V) :
    (restrictIndexedCells F A).graph = restrictGraph F.graph A := rfl

@[simp]
theorem restrictIndexedCells_cell (F : IndexedCells V) (A : Set V) (v : A) :
    (restrictIndexedCells F A).cell v = F.cell v.1 := rfl

@[simp]
theorem cellDiameter_restrictIndexedCells (F : IndexedCells V) (A : Set V) (v : A) :
    cellDiameter (restrictIndexedCells F A) v = cellDiameter F v.1 := rfl

@[simp]
theorem horizontalHitOffsets_restrictIndexedCells (F : IndexedCells V) (A : Set V)
    (a b : ℝ) (v : A) :
    horizontalHitOffsets (restrictIndexedCells F A) a b v
      = horizontalHitOffsets F a b v.1 := rfl

/-! ### Edge data of the restricted graph -/

theorem adj_restrictGraph (G : ReflectedWalk.ConductanceGraph V) (A : Set V) (x y : A) :
    (restrictGraph G A).Adj x y ↔ G.Adj x.1 y.1 := Iff.rfl

theorem edgeGradAbs_restrictGraph (G : ReflectedWalk.ConductanceGraph V) (f : V → ℝ)
    (A : Set V) (p : A × A) :
    edgeGradAbs (restrictGraph G A) (fun v => f v.1) p = edgeGradAbs G f (p.1.1, p.2.1) := by
  by_cases h : G.Adj p.1.1 p.2.1
  · rw [edgeGradAbs, edgeGradAbs, if_pos h, if_pos ((adj_restrictGraph G A p.1 p.2).mpr h)]
  · rw [edgeGradAbs, edgeGradAbs, if_neg h,
      if_neg fun hh => h ((adj_restrictGraph G A p.1 p.2).mp hh)]

theorem reciprocalConductance_restrictGraph (G : ReflectedWalk.ConductanceGraph V)
    (A : Set V) (p : A × A) :
    reciprocalConductance (restrictGraph G A) p = reciprocalConductance G (p.1.1, p.2.1) := by
  by_cases h : G.Adj p.1.1 p.2.1
  · rw [reciprocalConductance, reciprocalConductance, if_pos h,
      if_pos ((adj_restrictGraph G A p.1 p.2).mpr h)]
    rfl
  · rw [reciprocalConductance, reciprocalConductance, if_neg h,
      if_neg fun hh => h ((adj_restrictGraph G A p.1 p.2).mp hh)]

/-- The reciprocal-conductance mass of the restricted graph is at most the whole-plane
one: restriction only deletes edges. -/
theorem reciprocalConductanceMass_restrictGraph_le (G : ReflectedWalk.ConductanceGraph V)
    (A : Set V) (v : A) :
    reciprocalConductanceMass (restrictGraph G A) v ≤ reciprocalConductanceMass G v.1 := by
  rw [reciprocalConductanceMass, reciprocalConductanceMass]
  calc ∑' w : A, reciprocalConductance (restrictGraph G A) (v, w)
      = ∑' w : A, reciprocalConductance G (v.1, w.1) :=
        tsum_congr fun w => reciprocalConductance_restrictGraph G A (v, w)
    _ ≤ ∑' w : V, reciprocalConductance G (v.1, w) :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := (Subtype.val : A → V))
          Subtype.val_injective fun w => reciprocalConductance G (v.1, w)

/-! ### The two patch quantities -/

/-- The patch geometric mass `∑_{H ∈ A} d_H ^ 2 π*(H)` of the manuscript, with the
*whole-plane* reciprocal-conductance mass `π*` and the sum taken only over the patch
cells.  It is finite under the manuscript's `W`-bound even though the whole-plane mass
`ReflectedGMS.diameterReciprocalConductanceMass` is not. -/
noncomputable def patchDiameterReciprocalConductanceMass (F : IndexedCells V) (A : Set V) :
    ℝ≥0∞ :=
  ∑' v : A, cellDiameter F v.1 ^ (2 : ℝ) * reciprocalConductanceMass F.graph v.1

/-- The patch energy `ℰ_{G_A}(f)`: the extended energy of `f` for the restricted graph.
It is finite under the manuscript's residual estimate even when the whole-plane energy
is infinite. -/
noncomputable def patchEnergyENN (F : IndexedCells V) (A : Set V) (f : V → ℝ) : ℝ≥0∞ :=
  energyENN (restrictGraph F.graph A) fun v => f v.1

@[simp]
theorem patchEnergyENN_swapIndexedCells (F : IndexedCells V) (A : Set V) (f : V → ℝ) :
    patchEnergyENN (swapIndexedCells F) A f = patchEnergyENN F A f := rfl

theorem patchDiameterReciprocalConductanceMass_swapIndexedCells (F : IndexedCells V)
    (A : Set V) :
    patchDiameterReciprocalConductanceMass (swapIndexedCells F) A
      = patchDiameterReciprocalConductanceMass F A := by
  simp only [patchDiameterReciprocalConductanceMass, cellDiameter_swapIndexedCells,
    swapIndexedCells_graph]

/-- The geometric mass of the restricted family is bounded by the patch mass with the
whole-plane `π*`; this is the inequality `∑_e λ_e ^ 2 / c(e) ≤ ∑_{H ∈ ℍ(Q)} d_H ^ 2 π*(H)`
of the manuscript proof, now with the sum restricted to the patch. -/
theorem diameterReciprocalConductanceMass_restrictIndexedCells_le (F : IndexedCells V)
    (A : Set V) :
    diameterReciprocalConductanceMass (restrictIndexedCells F A)
      ≤ patchDiameterReciprocalConductanceMass F A := by
  rw [diameterReciprocalConductanceMass, patchDiameterReciprocalConductanceMass]
  exact ENNReal.tsum_le_tsum fun v =>
    mul_le_mul' le_rfl (reciprocalConductanceMass_restrictGraph_le F.graph A v)

/-! ### The whole-plane edge sum is already supported on the patch -/

/-- A pair can contribute to the variation along the segment `[a,b] × {y}` only if both
of its cells meet that segment. -/
theorem hits_of_horizontalLineEdgeTerm_ne_zero (F : IndexedCells V) (f : V → ℝ) (a b y : ℝ)
    {p : V × V} (hp : horizontalLineEdgeTerm F f a b p y ≠ 0) :
    Hits F (horizontal a b y) p.1 ∧ Hits F (horizontal a b y) p.2 := by
  by_contra hcon
  refine hp ?_
  rw [horizontalLineEdgeTerm,
    Set.indicator_of_notMem fun hy =>
      hcon ⟨mem_horizontalHitOffsets.mp hy.1, mem_horizontalHitOffsets.mp hy.2⟩]

/-- **The localization identity for the edge sum.**  If every cell meeting the segment
`[a,b] × {y}` lies in `A`, then the ordered-pair edge sum of the restricted family is the
whole-plane ordered-pair edge sum: the whole-plane sum has no support outside `A × A`.
Countably many edges and infinitely many cells are allowed. -/
theorem tsum_horizontalLineEdgeTerm_restrictIndexedCells (F : IndexedCells V) (f : V → ℝ)
    (A : Set V) (a b y : ℝ) (hA : ∀ v, Hits F (horizontal a b y) v → v ∈ A) :
    (∑' p : A × A, horizontalLineEdgeTerm (restrictIndexedCells F A) (fun v => f v.1) a b p y)
      = ∑' p : V × V, horizontalLineEdgeTerm F f a b p y := by
  classical
  have hginj : Function.Injective fun p : A × A => ((p.1 : V), (p.2 : V)) := by
    rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.injEq _ _ _ _ ▸ h
    subst h₁
    subst h₂
    rfl
  have hsupp : Function.support (fun p : V × V => horizontalLineEdgeTerm F f a b p y)
      ⊆ Set.range fun p : A × A => ((p.1 : V), (p.2 : V)) := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := hits_of_horizontalLineEdgeTerm_ne_zero F f a b y hp
    exact ⟨(⟨p.1, hA _ h₁⟩, ⟨p.2, hA _ h₂⟩), rfl⟩
  have hterm : ∀ p : A × A,
      horizontalLineEdgeTerm (restrictIndexedCells F A) (fun v => f v.1) a b p y
        = horizontalLineEdgeTerm F f a b ((p.1 : V), (p.2 : V)) y := by
    intro p
    simp only [horizontalLineEdgeTerm, horizontalHitOffsets_restrictIndexedCells,
      restrictIndexedCells_graph, edgeGradAbs_restrictGraph]
  rw [tsum_congr hterm]
  exact hginj.tsum_eq hsupp

/-- **The localization identity for the line variation.**  For a segment all of whose
cells lie in the patch, the patch line variation *is* the whole-plane line variation; in
particular the ordered-edge `/2` normalization is preserved. -/
theorem horizontalLineVariation_restrictIndexedCells (F : IndexedCells V) (f : V → ℝ)
    (A : Set V) (a b y : ℝ) (hA : ∀ v, Hits F (horizontal a b y) v → v ∈ A) :
    horizontalLineVariation (restrictIndexedCells F A) (fun v => f v.1) a b y
      = horizontalLineVariation F f a b y := by
  rw [horizontalLineVariation, horizontalLineVariation,
    tsum_horizontalLineEdgeTerm_restrictIndexedCells F f A a b y hA]

/-! ### The localized integral estimate -/

/-- **Energy controls the average line variation, localized to a patch** (manuscript
`s:lem:lines`, first assertion, on the restricted graph `G_{Q_R}`).  Over any measurable
offset window `s` all of whose segments have their cells inside the patch `A`, the offset
integral of the line variation is bounded by the square root of the *patch* geometric
mass times the square root of the *patch* energy.  No finiteness of the whole-plane mass
or energy and no finiteness of the cell count is assumed. -/
theorem setLIntegral_horizontalLineVariation_le_patch [Countable V] (F : IndexedCells V)
    (f : V → ℝ) (A : Set V) (a b : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hA : ∀ y ∈ s, ∀ v, Hits F (horizontal a b y) v → v ∈ A) :
    ∫⁻ y in s, horizontalLineVariation F f a b y
      ≤ patchDiameterReciprocalConductanceMass F A ^ (2⁻¹ : ℝ) *
        patchEnergyENN F A f ^ (2⁻¹ : ℝ) := by
  have hcongr : ∫⁻ y in s, horizontalLineVariation F f a b y
      = ∫⁻ y in s, horizontalLineVariation (restrictIndexedCells F A) (fun v => f v.1) a b y :=
    setLIntegral_congr_fun hs fun y hy =>
      (horizontalLineVariation_restrictIndexedCells F f A a b y (hA y hy)).symm
  rw [hcongr]
  refine le_trans (lintegral_mono' Measure.restrict_le_self le_rfl) ?_
  refine le_trans
    (lintegral_horizontalLineVariation_le (restrictIndexedCells F A) (fun v => f v.1) a b) ?_
  exact mul_le_mul'
    (ENNReal.rpow_le_rpow (diameterReciprocalConductanceMass_restrictIndexedCells_le F A)
      (by norm_num)) le_rfl

/-- The vertical localized integral estimate, with the same patch constants. -/
theorem setLIntegral_verticalLineVariation_le_patch [Countable V] (F : IndexedCells V)
    (f : V → ℝ) (A : Set V) (a b : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hA : ∀ x ∈ s, ∀ v, Hits F (vertical x a b) v → v ∈ A) :
    ∫⁻ x in s, verticalLineVariation F f a b x
      ≤ patchDiameterReciprocalConductanceMass F A ^ (2⁻¹ : ℝ) *
        patchEnergyENN F A f ^ (2⁻¹ : ℝ) := by
  have hswap : ∀ x ∈ s, ∀ v, Hits (swapIndexedCells F) (horizontal a b x) v → v ∈ A := by
    intro x hx v hv
    exact hA x hx v ((hits_swapIndexedCells_horizontal F a b x v).mp hv)
  have h := setLIntegral_horizontalLineVariation_le_patch (swapIndexedCells F) f A a b hs hswap
  rw [patchDiameterReciprocalConductanceMass_swapIndexedCells, patchEnergyENN_swapIndexedCells]
    at h
  simpa only [verticalLineVariation_eq_horizontal] using h

/-! ### Measurability of the line variations -/

theorem measurable_horizontalLineVariation [Countable V] (F : IndexedCells V) (f : V → ℝ)
    (a b : ℝ) : Measurable (horizontalLineVariation F f a b) := by
  have h : Measurable fun y => ∑' p : V × V, horizontalLineEdgeTerm F f a b p y :=
    Measurable.ennreal_tsum fun p => measurable_horizontalLineEdgeTerm F f a b p
  have heq : horizontalLineVariation F f a b
      = fun y => (2 : ℝ≥0∞)⁻¹ * ∑' p : V × V, horizontalLineEdgeTerm F f a b p y := by
    funext y
    rw [horizontalLineVariation, ENNReal.div_eq_inv_mul]
  rw [heq]
  exact h.const_mul _

theorem measurable_verticalLineVariation [Countable V] (F : IndexedCells V) (f : V → ℝ)
    (a b : ℝ) : Measurable (verticalLineVariation F f a b) := by
  have h : Measurable fun x => ∑' p : V × V, verticalLineEdgeTerm F f a b p x :=
    Measurable.ennreal_tsum fun p => measurable_verticalLineEdgeTerm F f a b p
  have heq : verticalLineVariation F f a b
      = fun x => (2 : ℝ≥0∞)⁻¹ * ∑' p : V × V, verticalLineEdgeTerm F f a b p x := by
    funext x
    rw [verticalLineVariation, ENNReal.div_eq_inv_mul]
  rw [heq]
  exact h.const_mul _

/-! ### Good-offset selection -/

/-- **Markov selection of a good offset.**  If a nonnegative measurable offset function
has offset integral at most `c` over the window `s`, and `c` is strictly smaller than
`t · |s|`, then some offset of `s` lies outside the null exceptional set `N` and has
value at most `t`.  This is the manuscript's "each interval of length `αR` contains a
coordinate outside both the variation-bad set and `N_h`" step, in a form that never
needs `t` to be finite or nonzero. -/
theorem exists_notMem_and_le_of_setLIntegral_lt (W : ℝ → ℝ≥0∞) (hW : Measurable W)
    {s N : Set ℝ} (hN : volume N = 0) {t c : ℝ≥0∞}
    (hbound : ∫⁻ y in s, W y ≤ c) (hlt : c < t * volume s) :
    ∃ y ∈ s, y ∉ N ∧ W y ≤ t := by
  classical
  have hmk : MeasurableSet {y : ℝ | t ≤ W y} := hW measurableSet_Ici
  have hmarkov : t * volume ({y : ℝ | t ≤ W y} ∩ s) ≤ c := by
    have h := mul_meas_ge_le_lintegral (μ := volume.restrict s) hW t
    rw [Measure.restrict_apply hmk] at h
    exact h.trans hbound
  have hsubB : {y : ℝ | t < W y} ∩ s ⊆ {y : ℝ | t ≤ W y} ∩ s := by
    rintro y ⟨hy, hys⟩
    refine ⟨?_, hys⟩
    simp only [Set.mem_setOf_eq] at hy ⊢
    exact hy.le
  have hBle : t * volume ({y : ℝ | t < W y} ∩ s) ≤ c :=
    le_trans (mul_le_mul' (le_refl t) (measure_mono hsubB)) hmarkov
  by_contra hcon
  push_neg at hcon
  have hsub : s \ N ⊆ {y : ℝ | t < W y} ∩ s := fun y hy => ⟨hcon y hy.1 hy.2, hy.1⟩
  have hvol : volume s ≤ volume ({y : ℝ | t < W y} ∩ s) := by
    rw [← measure_diff_null (μ := volume) (s := s) hN]
    exact measure_mono hsub
  exact absurd (le_trans (mul_le_mul' (le_refl t) hvol) hBle) (not_le.mpr hlt)

/-- **The usable finite good-line bound, horizontal case.**  Once the patch mass and
patch energy are small enough compared with the length of the offset window, that window
contains an offset which is outside the exceptional null set and along which the
oscillation of `f` over the cells meeting the segment is at most `t`.  The exceptional
set is the manuscript's `N_h`: it works simultaneously for all endpoint pairs. -/
theorem exists_good_offset_horizontalLineOscillation_le [Countable V] (F : IndexedCells V)
    (f : V → ℝ) (A : Set V) {a b : ℝ} (hab : a < b) {s : Set ℝ} (hs : MeasurableSet s)
    (hA : ∀ y ∈ s, ∀ v, Hits F (horizontal a b y) v → v ∈ A)
    {N : Set ℝ} (hN : volume N = 0) (hNgood : ∀ y ∉ N, HorizontalGood F y) {t : ℝ≥0∞}
    (hlt : patchDiameterReciprocalConductanceMass F A ^ (2⁻¹ : ℝ) *
        patchEnergyENN F A f ^ (2⁻¹ : ℝ) < t * volume s) :
    ∃ y ∈ s, y ∉ N ∧ horizontalLineOscillation F f a b y ≤ t := by
  obtain ⟨y, hys, hyN, hyle⟩ :=
    exists_notMem_and_le_of_setLIntegral_lt (horizontalLineVariation F f a b)
      (measurable_horizontalLineVariation F f a b) hN
      (setLIntegral_horizontalLineVariation_le_patch F f A a b hs hA) hlt
  exact ⟨y, hys, hyN,
    (horizontalLineOscillation_le_horizontalLineVariation F f hab (hNgood y hyN)).trans hyle⟩

/-- **The usable finite good-line bound, vertical case.** -/
theorem exists_good_offset_verticalLineOscillation_le [Countable V] (F : IndexedCells V)
    (f : V → ℝ) (A : Set V) {a b : ℝ} (hab : a < b) {s : Set ℝ} (hs : MeasurableSet s)
    (hA : ∀ x ∈ s, ∀ v, Hits F (vertical x a b) v → v ∈ A)
    {N : Set ℝ} (hN : volume N = 0) (hNgood : ∀ x ∉ N, VerticalGood F x) {t : ℝ≥0∞}
    (hlt : patchDiameterReciprocalConductanceMass F A ^ (2⁻¹ : ℝ) *
        patchEnergyENN F A f ^ (2⁻¹ : ℝ) < t * volume s) :
    ∃ x ∈ s, x ∉ N ∧ verticalLineOscillation F f a b x ≤ t := by
  obtain ⟨x, hxs, hxN, hxle⟩ :=
    exists_notMem_and_le_of_setLIntegral_lt (verticalLineVariation F f a b)
      (measurable_verticalLineVariation F f a b) hN
      (setLIntegral_verticalLineVariation_le_patch F f A a b hs hA) hlt
  exact ⟨x, hxs, hxN,
    (verticalLineOscillation_le_verticalLineVariation F f hab (hNgood x hxN)).trans hxle⟩

/-! ### The rectangle patch -/

/-- `ℍ(Q)`: the cells meeting a patch `Q`.  Together with `restrictGraph` this is the
manuscript's restricted graph `G_Q`. -/
def hittingVertices (F : IndexedCells V) (Q : Set Plane) : Set V := {v | Hits F Q v}

theorem mem_hittingVertices {F : IndexedCells V} {Q : Set Plane} {v : V} :
    v ∈ hittingVertices F Q ↔ Hits F Q v := Iff.rfl

/-- Every cell meeting a subset of `Q` is a patch cell. -/
theorem mem_hittingVertices_of_hits_subset (F : IndexedCells V) {Q S : Set Plane}
    (hSQ : S ⊆ Q) {v : V} (hv : Hits F S v) : v ∈ hittingVertices F Q := by
  obtain ⟨z, hzcell, hzS⟩ := hv
  exact ⟨z, hzcell, hSQ hzS⟩

/-- **The localized good-grid input.**  Under AE line connectivity, if the patch mass and
patch energy of `f` on `Q` satisfy the smallness condition relative to the length of the
offset window `s`, then `s` contains *both* a horizontal offset and a vertical offset —
each outside its own exceptional null set, and also outside an arbitrary further null set
`Ne` supplied by the caller — along which the oscillation of `f` over the cells meeting the
corresponding segment is at most `t`.  This is the pair of good coordinates the
uniform-sublinearity grid construction selects in each interval, now justified by patch
quantities only.

The extra null set `Ne` is what the weakened covering clause of `Geometry` needs: taking it
to contain the coordinate projections of the uncovered set makes the whole selected line
lie in the union of the cells, which is what the crossing-cell argument of
`ReflectedGMS.exists_hits_horizontal_and_vertical` consumes. -/
theorem exists_good_offsets_lineOscillation_le_rectanglePatch [Countable V]
    (F : IndexedCells V) (f : V → ℝ) (Q : Set Plane) (hF : AELineConnected F)
    {Ne : Set ℝ} (hNe : volume Ne = 0) {a b : ℝ}
    (hab : a < b) {s : Set ℝ} (hs : MeasurableSet s)
    (hsh : ∀ y ∈ s, horizontal a b y ⊆ Q) (hsv : ∀ x ∈ s, vertical x a b ⊆ Q) {t : ℝ≥0∞}
    (hlt : patchDiameterReciprocalConductanceMass F (hittingVertices F Q) ^ (2⁻¹ : ℝ) *
        patchEnergyENN F (hittingVertices F Q) f ^ (2⁻¹ : ℝ) < t * volume s) :
    (∃ y ∈ s, y ∉ Ne ∧ horizontalLineOscillation F f a b y ≤ t) ∧
      ∃ x ∈ s, x ∉ Ne ∧ verticalLineOscillation F f a b x ≤ t := by
  obtain ⟨Nh, Nv, -, hNhNull, -, hNvNull, hNh, hNv⟩ :=
    (aeLineConnected_iff_exists_measurable_null_sets F).mp hF
  constructor
  · obtain ⟨y, hys, hyN, hy⟩ :=
      exists_good_offset_horizontalLineOscillation_le F f (hittingVertices F Q) hab hs
        (fun y hy v hv => mem_hittingVertices_of_hits_subset F (hsh y hy) hv)
        (measure_union_null hNhNull hNe)
        (fun y hy => hNh y fun hc => hy (Or.inl hc)) hlt
    exact ⟨y, hys, fun hc => hyN (Or.inr hc), hy⟩
  · obtain ⟨x, hxs, hxN, hx⟩ :=
      exists_good_offset_verticalLineOscillation_le F f (hittingVertices F Q) hab hs
        (fun x hx v hv => mem_hittingVertices_of_hits_subset F (hsv x hx) hv)
        (measure_union_null hNvNull hNe)
        (fun x hx => hNv x fun hc => hx (Or.inl hc)) hlt
    exact ⟨x, hxs, fun hc => hxN (Or.inr hc), hx⟩

end ReflectedGMS
