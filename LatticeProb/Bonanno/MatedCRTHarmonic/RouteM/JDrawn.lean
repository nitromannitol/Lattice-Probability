/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.JDrawn at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Core.CellInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.ArcUnion
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.JWinding
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.JExtract

/-!
# Route M: drawn walks of a monotone drawing, and the winding lemmas W1–W4

The drawing construction ("Drawn walks") and §7, on the abstract Core
interface `CellularEmbedding.MonotoneDrawing` (`Core/CellInterfaces.lean`). For a monotone drawing `D`:

* `drawnPath D w`: the drawn path `D(W)` of a walk, the concatenation of its arcs from `pt a` to `pt b`;
  `drawnLoop D w := Ψ ∘ D(W)` as a curve `C(I, ℂ)`;
* `mem_range_drawnPath`: a point of `D(W)` is `pt a` or lies on the arc of a dart of `W`; `drawnLoop_mem_cell`:
  every point of `Ψ ∘ D(W)` lies in the cell of a vertex of `W`;
* `exists_mem_support_of_mem_range` (TF3's (SV)): if `D(W)` and `D(W')` meet, `W` and `W'` share a vertex;
* `injective_drawnPath` (W4, first half): the drawn path of a non-empty graph path is injective (an arc);
* `isJordanCurve_range_drawnPath` (W4): the drawn path of a cycle is a Jordan curve (landed arc-union lemma
  `Planar.ArcUnion.jordanCurve_union_of_arcs`);
* `dartIncr`, `walkIncr`: TF3's `2πi Δ` per dart and its sum along a walk; `logIncr_drawnLoop` (W1),
  `dartIncr_symm` (W2), `loopDeg_drawnLoop_mul` (W1 for closed walks);
* `exists_isCycle_loopDeg_ne_zero` (W1 + W3): a closed walk whose drawn loop has non-zero degree about `z`
  contains a cycle with the same property, whose darts, vertices and drawn image are among those of the walk.
-/

set_option autoImplicit false

noncomputable section

open Set Function SimpleGraph SimpleGraph.Walk
open scoped unitInterval
open QuantumZipper.CA.Topo

namespace MatedCRTHarmonic.RouteM

/-- Concatenating two injective paths that meet only at the junction point gives an injective path. -/
theorem JAux.path_trans_injective {X : Type*} [TopologicalSpace X] {x y w : X} {γ : Path x y} {γ' : Path y w}
    (hγ : Injective γ) (hγ' : Injective γ') (h : ∀ s t, γ s = γ' t → s = 1 ∧ t = 0) :
    Injective (γ.trans γ') := by
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have := congrArg Subtype.val (hγ hst)
    simp only at this
    exact Subtype.ext (by linarith)
  · have h1 := (h _ _ hst).2
    have := congrArg Subtype.val h1
    simp only [Set.Icc.coe_zero] at this
    exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  · have h1 := (h _ _ hst.symm).2
    have := congrArg Subtype.val h1
    simp only [Set.Icc.coe_zero] at this
    exact absurd (by linarith : (s : ℝ) ≤ 1 / 2) hs
  · have := congrArg Subtype.val (hγ' hst)
    simp only at this
    exact Subtype.ext (by linarith)

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}

section Drawn

variable (D : H.MonotoneDrawing)

/-- The arc of a dart. -/
def dartArc (d : G.adj.Dart) : Path (D.pt d.fst) (D.pt d.snd) := D.arc d.fst d.snd d.adj

/-- The drawn path `D(W)` of a walk (TF3 §5.2): the concatenation of its arcs, from `pt a` to `pt b`; the constant
path for the empty walk. (The last arc is not followed by a constant path, so drawn paths of graph paths are
injective, `injective_drawnPath`.) -/
def drawnPath : {a b : V} → G.adj.Walk a b → Path (D.pt a) (D.pt b)
  | _, _, .nil => Path.refl _
  | _, _, .cons h .nil => D.arc _ _ h
  | _, _, .cons h (.cons h' p) => (D.arc _ _ h).trans (drawnPath (.cons h' p))

@[simp]
theorem drawnPath_nil {a : V} : drawnPath D (nil : G.adj.Walk a a) = Path.refl _ := rfl

@[simp]
theorem drawnPath_cons_nil {a b : V} (h : G.adj.Adj a b) : drawnPath D (cons h nil) = D.arc a b h := rfl

theorem drawnPath_cons_cons {a b c d : V} (h : G.adj.Adj a b) (h' : G.adj.Adj b c) (p : G.adj.Walk c d) :
    drawnPath D (cons h (cons h' p)) = (D.arc a b h).trans (drawnPath D (cons h' p)) := rfl

/-- The range of `D(h :: p)` is the arc of `h` together with the range of `D(p)`. -/
theorem range_drawnPath_cons {a b c : V} (h : G.adj.Adj a b) (p : G.adj.Walk b c) :
    range (drawnPath D (cons h p)) = range (D.arc a b h) ∪ range (drawnPath D p) := by
  cases p with
  | nil =>
    have hb : D.pt b ∈ range (D.arc a b h) := ⟨1, (D.arc a b h).target⟩
    rw [drawnPath_cons_nil, drawnPath_nil, Path.refl_range]
    exact (union_eq_left.mpr (singleton_subset_iff.mpr hb)).symm
  | cons h' p => rw [drawnPath_cons_cons, Path.trans_range]

/-- **Points of a drawn path**: a point of `D(W)` is `pt a` or lies on the arc of a dart of `W`. -/
theorem mem_range_drawnPath {a b : V} (w : G.adj.Walk a b) {q : ℂ} :
    q ∈ range (drawnPath D w) ↔ q = D.pt a ∨ ∃ d ∈ w.darts, q ∈ range (dartArc D d) := by
  induction w with
  | nil => simp [drawnPath_nil]
  | @cons a b c h p ih =>
    rw [range_drawnPath_cons, mem_union, ih]
    have hsrc : D.pt a ∈ range (D.arc a b h) := ⟨0, (D.arc a b h).source⟩
    have htgt : D.pt b ∈ range (D.arc a b h) := ⟨1, (D.arc a b h).target⟩
    simp only [darts_cons, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (hq | rfl | hq)
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inl htgt)
      · exact Or.inr (Or.inr hq)
    · rintro (rfl | hq | hq)
      · exact Or.inl hsrc
      · exact Or.inl hq
      · exact Or.inr (Or.inr hq)

/-- On a non-empty walk every point of the drawn path lies on the arc of one of its darts. -/
theorem exists_dart_of_mem_range {a b : V} {w : G.adj.Walk a b} (hw : ¬ w.Nil) {q : ℂ}
    (hq : q ∈ range (drawnPath D w)) : ∃ d ∈ w.darts, q ∈ range (dartArc D d) := by
  rcases (mem_range_drawnPath D w).mp hq with rfl | hd
  · cases w with
    | nil => exact absurd Nil.nil hw
    | cons h p => exact ⟨_, by simp only [darts_cons]; exact List.mem_cons_self, ⟨0, Path.source _⟩⟩
  · exact hd

/-- The arc of a dart of `W` lies in `D(W)`. -/
theorem range_dartArc_subset {a b : V} {w : G.adj.Walk a b} {d : G.adj.Dart} (hd : d ∈ w.darts) :
    range (dartArc D d) ⊆ range (drawnPath D w) := fun _ hq => (mem_range_drawnPath D w).mpr (Or.inr ⟨d, hd, hq⟩)

/-- If the darts of a non-empty walk are darts of `W`, its drawn path lies in `D(W)`. -/
theorem range_drawnPath_subset_of_darts_subset {a b a' b' : V} {C : G.adj.Walk a b} (hC : ¬ C.Nil)
    {W : G.adj.Walk a' b'} (h : ∀ d ∈ C.darts, d ∈ W.darts) : range (drawnPath D C) ⊆ range (drawnPath D W) := by
  intro q hq
  obtain ⟨d, hd, hqd⟩ := exists_dart_of_mem_range D hC hq
  exact range_dartArc_subset D (h d hd) hqd

/-- **(SV)** (TF3 §5.2): if the drawn paths of two walks meet, the walks share a vertex. -/
theorem exists_mem_support_of_mem_range {a b a' b' : V} (w : G.adj.Walk a b) (w' : G.adj.Walk a' b') {q : ℂ}
    (hq : q ∈ range (drawnPath D w)) (hq' : q ∈ range (drawnPath D w')) : ∃ y ∈ w.support, y ∈ w'.support := by
  have key : ∀ (d : G.adj.Dart) {x y : V} (W : G.adj.Walk x y), d ∈ W.darts → ∀ v, (v = d.fst ∨ v = d.snd) →
      v ∈ W.support := by
    rintro d x y W hd v (rfl | rfl)
    · exact dart_fst_mem_support_of_mem_darts W hd
    · exact dart_snd_mem_support_of_mem_darts W hd
  rcases (mem_range_drawnPath D w).mp hq with rfl | ⟨d, hd, hqd⟩ <;>
    rcases (mem_range_drawnPath D w').mp hq' with hq'' | ⟨d', hd', hqd'⟩
  · exact ⟨a, start_mem_support w, (D.pt_injective hq'') ▸ start_mem_support w'⟩
  · exact ⟨a, start_mem_support w, key d' w' hd' a (D.pt_mem_arc a _ _ _ hqd')⟩
  · subst hq''
    exact ⟨a', key d w hd a' (D.pt_mem_arc a' _ _ _ hqd), start_mem_support w'⟩
  · by_cases h1 : d.fst = d'.fst ∧ d.snd = d'.snd
    · exact ⟨d.fst, key d w hd _ (Or.inl rfl), key d' w' hd' _ (Or.inl h1.1)⟩
    by_cases h2 : d.fst = d'.snd ∧ d.snd = d'.fst
    · exact ⟨d.fst, key d w hd _ (Or.inl rfl), key d' w' hd' _ (Or.inr h2.1)⟩
    obtain ⟨y, ⟨hy, hy'⟩, -⟩ := D.arc_inter _ _ _ _ d.adj d'.adj h1 h2 ⟨hqd, hqd'⟩
    exact ⟨y, key d w hd y hy, key d' w' hd' y hy'⟩

/-- A point of `D(p)` on the arc of a dart `(a, b)` with `a ∉ p` is `pt b`, if `p` starts at `b`. -/
theorem eq_pt_of_mem_arc_of_not_mem {a b c : V} (h : G.adj.Adj a b) {p : G.adj.Walk b c} (ha : a ∉ p.support)
    {q : ℂ} (hq : q ∈ range (D.arc a b h)) (hq' : q ∈ range (drawnPath D p)) : q = D.pt b := by
  rcases (mem_range_drawnPath D p).mp hq' with hq'' | ⟨d', hd', hqd'⟩
  · exact hq''
  have hf := dart_fst_mem_support_of_mem_darts p hd'
  have hs := dart_snd_mem_support_of_mem_darts p hd'
  have h1 : ¬ (a = d'.fst ∧ b = d'.snd) := fun h1 => ha (h1.1 ▸ hf)
  have h2 : ¬ (a = d'.snd ∧ b = d'.fst) := fun h2 => ha (h2.1 ▸ hs)
  obtain ⟨y, ⟨hy, hy'⟩, rfl⟩ := D.arc_inter _ _ _ _ h d'.adj h1 h2 ⟨hq, hqd'⟩
  rcases hy with rfl | rfl
  · rcases hy' with rfl | rfl
    · exact absurd hf ha
    · exact absurd hs ha
  · rfl

/-- **W4, first half**: the drawn path of a non-empty graph path is injective (an arc). -/
theorem injective_drawnPath {a b : V} {w : G.adj.Walk a b} (hw : w.IsPath) (hne : ¬ w.Nil) :
    Injective (drawnPath D w) := by
  induction w with
  | nil => exact absurd Nil.nil hne
  | @cons a b c h p ih =>
    cases p with
    | nil => exact D.arc_injective a b h
    | cons h' p =>
      rw [drawnPath_cons_cons]
      have hp := hw.of_cons
      have ha : a ∉ (cons h' p).support := ((cons_isPath_iff h _).mp hw).2
      refine JAux.path_trans_injective (D.arc_injective a b h) (ih hp not_nil_cons) fun s t hst => ?_
      have hq := eq_pt_of_mem_arc_of_not_mem D h ha ⟨s, rfl⟩ ⟨t, hst.symm⟩
      constructor
      · exact D.arc_injective a b h (hq.trans (D.arc a b h).target.symm)
      · exact ih hp not_nil_cons ((hst.symm.trans hq).trans (drawnPath D (cons h' p)).source.symm)

/-- **W4** (TF3 §7): the drawn path of a cycle is a Jordan curve. -/
theorem isJordanCurve_range_drawnPath {c : V} {C : G.adj.Walk c c} (hC : C.IsCycle) :
    LQGMetric.JordanMap.IsJordanCurve (range (drawnPath D C)) := by
  cases C with
  | nil => exact absurd hC not_isCycle_nil
  | @cons _ c₁ _ h p =>
    obtain ⟨hp, hedge⟩ := (cons_isCycle_iff p h).mp hC
    have hpne : ¬ p.Nil := fun hnil => G.adj.loopless.irrefl c (hnil.eq ▸ h)
    have hrange : range (drawnPath D (cons h p)) = range (D.arc c c₁ h) ∪ range (drawnPath D p).symm := by
      rw [range_drawnPath_cons, Path.symm_range]
    rw [hrange]
    refine Planar.ArcUnion.jordanCurve_union_of_arcs (D.arc c c₁ h).continuous (D.arc_injective c c₁ h)
      (drawnPath D p).symm.continuous ?_ ?_ ?_ ?_
    · intro s t hst
      have := injective_drawnPath D hp hpne hst
      exact unitInterval.symm_involutive.injective this
    · rw [Path.source, Path.source]
    · rw [Path.target, Path.target]
    · apply Subset.antisymm
      · rintro q ⟨hq, hq'⟩
        rw [Path.symm_range] at hq'
        rw [Path.source, Path.target]
        obtain ⟨d', hd', hqd'⟩ := exists_dart_of_mem_range D hpne hq'
        have hmem : ∀ x y : V, s(x, y) = s(c, c₁) → d'.fst = x → d'.snd = y → False := by
          intro x y hxy hx hy
          apply hedge
          rw [← hxy, edges_eq_map_darts]
          refine List.mem_map.mpr ⟨d', hd', ?_⟩
          rw [Dart.edge, hx, hy]
        have h1 : ¬ (c = d'.fst ∧ c₁ = d'.snd) := fun h1 => hmem c c₁ rfl h1.1.symm h1.2.symm
        have h2 : ¬ (c = d'.snd ∧ c₁ = d'.fst) := fun h2 => hmem c₁ c Sym2.eq_swap h2.2.symm h2.1.symm
        obtain ⟨y, ⟨hy, -⟩, rfl⟩ := D.arc_inter _ _ _ _ h d'.adj h1 h2 ⟨hq, hqd'⟩
        rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro q (rfl | rfl)
        · rw [Path.source]
          exact ⟨⟨0, (D.arc c c₁ h).source⟩, by rw [Path.symm_range]; exact ⟨1, (drawnPath D p).target⟩⟩
        · rw [Path.target]
          exact ⟨⟨1, (D.arc c c₁ h).target⟩, by rw [Path.symm_range]; exact ⟨0, (drawnPath D p).source⟩⟩

/-! ### Drawn loops and dart increments -/

/-- The image `Ψ ∘ D(W)` of the drawn path of a walk, as a curve (`drawnLoop` of TF3 Details (a); a loop when `W`
is closed). -/
def drawnLoop {a b : V} (w : G.adj.Walk a b) : C(I, ℂ) := ((drawnPath D w).map D.continuous_Ψ).toContinuousMap

theorem drawnLoop_apply {a b : V} (w : G.adj.Walk a b) (t : I) : drawnLoop D w t = D.Ψ (drawnPath D w t) := rfl

theorem drawnLoop_zero {a b : V} (w : G.adj.Walk a b) : drawnLoop D w 0 = D.Ψ (D.pt a) := by
  rw [drawnLoop_apply, Path.source]

theorem drawnLoop_one {a b : V} (w : G.adj.Walk a b) : drawnLoop D w 1 = D.Ψ (D.pt b) := by
  rw [drawnLoop_apply, Path.target]

/-- The drawn loop of a closed walk is closed. -/
theorem drawnLoop_closed {a : V} (w : G.adj.Walk a a) : drawnLoop D w 0 = drawnLoop D w 1 := by
  rw [drawnLoop_zero, drawnLoop_one]

theorem range_drawnLoop {a b : V} (w : G.adj.Walk a b) : range (drawnLoop D w) = D.Ψ '' range (drawnPath D w) := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

/-- If the darts of a non-empty walk are darts of `W`, its drawn loop lies in that of `W`. -/
theorem range_drawnLoop_subset_of_darts_subset {a b a' b' : V} {C : G.adj.Walk a b} (hC : ¬ C.Nil)
    {W : G.adj.Walk a' b'} (h : ∀ d ∈ C.darts, d ∈ W.darts) : range (drawnLoop D C) ⊆ range (drawnLoop D W) := by
  rw [range_drawnLoop, range_drawnLoop]
  exact image_mono (range_drawnPath_subset_of_darts_subset D hC h)

/-- The image under `Ψ` of the arc of a dart. -/
def dartImage (d : G.adj.Dart) : Path (D.Ψ (D.pt d.fst)) (D.Ψ (D.pt d.snd)) := (dartArc D d).map D.continuous_Ψ

/-- TF3's `2πi Δ(x, y)` for a dart: the logarithmic increment about `z` of the image of its arc. -/
def dartIncr (z : ℂ) (d : G.adj.Dart) : ℂ := logIncr (dartImage D d).toContinuousMap z

/-- The sum of the dart increments along a walk. -/
def walkIncr (z : ℂ) {a b : V} (w : G.adj.Walk a b) : ℂ := dartSum (dartIncr D z) w

theorem dartImage_symm_apply (d : G.adj.Dart) (t : I) : dartImage D d.symm t = (dartImage D d).symm t := by
  change D.Ψ (D.arc d.snd d.fst d.adj.symm t) = D.Ψ (D.arc d.fst d.snd d.adj (σ t))
  rw [D.arc_symm d.fst d.snd d.adj]
  rfl

/-- **W2 (reversal)**: `Δ(y, x) = -Δ(x, y)`. -/
theorem dartIncr_symm (z : ℂ) (d : G.adj.Dart) : dartIncr D z d.symm = -dartIncr D z d := by
  unfold dartIncr
  rw [logIncr_congr (dartImage_symm_apply D d) z]
  by_cases hz : ∀ t, dartImage D d t ≠ z
  · exact logIncr_symm (dartImage D d) hz
  · simp only [not_forall, not_not] at hz
    obtain ⟨t, ht⟩ := hz
    rw [logIncr_eq_zero_of_mem (γ := (dartImage D d).toContinuousMap) ht,
      logIncr_eq_zero_of_mem (γ := (dartImage D d).symm.toContinuousMap) (t := σ t)
        (by simp only [Path.coe_toContinuousMap, Path.symm_apply, Function.comp_apply,
          unitInterval.symm_symm]; exact ht), neg_zero]

/-- **W1 (additivity)**: for a walk whose drawn loop avoids `z`, the increment of the drawn loop is the sum of the
dart increments. -/
theorem logIncr_drawnLoop {z : ℂ} {a b : V} (w : G.adj.Walk a b) (hz : ∀ t, drawnLoop D w t ≠ z) :
    logIncr (drawnLoop D w) z = walkIncr D z w := by
  induction w with
  | @nil a =>
    simp only [walkIncr, dartSum_nil]
    exact (logIncr_congr (γ := drawnLoop D (nil : G.adj.Walk a a))
      (γ' := ContinuousMap.const I (D.Ψ (D.pt a))) (fun t => rfl) z).trans (logIncr_const _ z)
  | @cons a b c h p ih =>
    have hzp : ∀ t, drawnLoop D p t ≠ z := by
      intro t ht
      have hmem : drawnLoop D p t ∈ range (drawnLoop D (cons h p)) := by
        rw [range_drawnLoop, range_drawnPath_cons, image_union]
        exact Or.inr ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨s, hs⟩ := hmem
      exact hz s (hs.trans ht)
    have hza : ∀ t, ((D.arc a b h).map D.continuous_Ψ) t ≠ z := by
      intro t ht
      have hmem : D.Ψ (D.arc a b h t) ∈ range (drawnLoop D (cons h p)) := by
        rw [range_drawnLoop, range_drawnPath_cons, image_union]
        exact Or.inl ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨s, hs⟩ := hmem
      exact hz s (hs.trans ht)
    simp only [walkIncr, dartSum_cons] at ih ⊢
    rw [← ih hzp]
    cases p with
    | nil =>
      rw [logIncr_congr (fun t => rfl : ∀ t, drawnLoop D (cons h nil) t = dartImage D ⟨(a, b), h⟩ t) z]
      rw [show drawnLoop D (nil : G.adj.Walk b b) = ContinuousMap.const I (D.Ψ (D.pt b)) from rfl,
        logIncr_const, add_zero]
      rfl
    | cons h' p =>
      have heq : drawnLoop D (cons h (cons h' p)) =
          (((D.arc a b h).map D.continuous_Ψ).trans
            ((drawnPath D (cons h' p)).map D.continuous_Ψ)).toContinuousMap := by
        rw [drawnLoop, drawnPath_cons_cons, Path.map_trans]
      rw [heq, logIncr_trans _ _ hza hzp]
      rfl

/-- **W1 for closed walks**: the degree of the drawn loop about `z` times `2πi` is the sum of dart increments. -/
theorem loopDeg_drawnLoop_mul {z : ℂ} {a : V} (w : G.adj.Walk a a)
    (h : ∀ t, (drawnLoop D w - ContinuousMap.const I z) t ≠ 0) :
    (loopDeg (drawnLoop D w - ContinuousMap.const I z) h : ℂ) * (2 * Real.pi * Complex.I) = walkIncr D z w := by
  rw [loopDeg_mul_eq_logIncr _ z (drawnLoop_closed D w) h]
  refine logIncr_drawnLoop D w fun t ht => h t ?_
  simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, ht, sub_self]

/-- **W1 + W3** (TF3 §7): a closed walk whose drawn loop has non-zero degree about `z` contains a cycle `C` whose
drawn loop has non-zero degree about `z`; the darts and vertices of `C` are among those of the walk, and the drawn
loop of `C` lies in that of the walk. -/
theorem exists_isCycle_loopDeg_ne_zero {u : V} (W : G.adj.Walk u u) {z : ℂ}
    (hW : ∀ t, (drawnLoop D W - ContinuousMap.const I z) t ≠ 0)
    (hdeg : loopDeg (drawnLoop D W - ContinuousMap.const I z) hW ≠ 0) :
    ∃ (c : V) (C : G.adj.Walk c c), C.IsCycle ∧ (∀ d ∈ C.darts, d ∈ W.darts) ∧
      (∀ y ∈ C.support, y ∈ W.support) ∧ range (drawnLoop D C) ⊆ range (drawnLoop D W) ∧
      ∃ hC : ∀ t, (drawnLoop D C - ContinuousMap.const I z) t ≠ 0,
        loopDeg (drawnLoop D C - ContinuousMap.const I z) hC ≠ 0 := by
  have hsumW : walkIncr D z W ≠ 0 := by
    rw [← loopDeg_drawnLoop_mul D W hW]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hdeg) two_pi_I_ne_zero'
  obtain ⟨c, C, hC, hCd, hCs⟩ := exists_isCycle_dartSum_ne_zero (dartIncr D z) (dartIncr_symm D z) W hsumW
  have hCne : ¬ C.Nil := hC.not_nil
  have hrange := range_drawnLoop_subset_of_darts_subset D hCne hCd
  have hCz : ∀ t, (drawnLoop D C - ContinuousMap.const I z) t ≠ 0 := by
    intro t ht
    obtain ⟨s, hs⟩ := hrange ⟨t, rfl⟩
    apply hW s
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply] at ht ⊢
    rw [hs, ht]
  refine ⟨c, C, hC, hCd, JAux.support_subset_of_darts_subset hCne hCd, hrange, hCz, fun h0 => hCs ?_⟩
  have := loopDeg_drawnLoop_mul D C hCz
  rw [h0, Int.cast_zero, zero_mul] at this
  exact this.symm

end Drawn

end MatedCRTHarmonic.RouteM
