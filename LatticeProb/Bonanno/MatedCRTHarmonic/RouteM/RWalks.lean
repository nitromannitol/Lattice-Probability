/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RWalks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.JDrawn
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RItinerary

/-!
# Route M,: walks along sequences, telescoping dart sums, locations of drawn loops

on top drawn walks
(`RouteM/JDrawn.lean`: `drawnLoop`, `dartIncr`, `walkIncr`, `dartSum`):

* `walkAlongSeq v hadj m i h`: the walk `v i → v (i+1) → ⋯ → v (i+m)` of a sequence with consecutive adjacencies, its
  support (`mem_support_walkAlongSeq`) and its dart sums (`dartSum_walkAlongSeq`);
* `dartSum_eq_sub_of_forall`: a dart sum whose terms are differences `F (d.snd) - F (d.fst)` telescopes;
* `drawnLoop_mem_of_forall_cell`: a property of all points of the cells of the vertices of a walk holds along its drawn loop
  (TF3 §5.2: `Ψ ∘ D(W)` lies in the union of the cells of `W`);
* `dartIncr_eq_log_sub_log_of_cells`: TFJ's sector rule `logIncr_eq_log_sub_log` for the arc of one dart, with the slit-plane
  condition checked on the two end cells.
-/

set_option autoImplicit false

noncomputable section

open Set SimpleGraph SimpleGraph.Walk

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}

/-! ### Walks along sequences -/

section SeqWalk

variable (v : ℕ → V) {N : ℕ} (hadj : ∀ j < N, G.adj.Adj (v j) (v (j + 1)))

/-- The walk `v i → v (i+1) → ⋯ → v (i+m)` along a sequence with consecutive adjacencies (`i + m ≤ N`). -/
def walkAlongSeq : (m i : ℕ) → i + m ≤ N → G.adj.Walk (v i) (v (i + m))
  | 0, _, _ => nil
  | m + 1, i, h =>
      cons (hadj i (by omega))
        ((walkAlongSeq m (i + 1) (by omega)).copy rfl (congrArg v (Nat.add_right_comm i 1 m)))

/-- The vertices of `walkAlongSeq v hadj m i h` are the `v (i + t)`, `t ≤ m`. -/
theorem mem_support_walkAlongSeq : ∀ (m i : ℕ) (h : i + m ≤ N) {y : V},
    y ∈ (walkAlongSeq v hadj m i h).support → ∃ t ≤ m, y = v (i + t)
  | 0, i, h, y, hy => by
    simp only [walkAlongSeq, support_nil, List.mem_singleton] at hy
    exact ⟨0, le_rfl, by rw [hy, Nat.add_zero]⟩
  | m + 1, i, h, y, hy => by
    simp only [walkAlongSeq, support_cons, support_copy, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨0, by omega, by rw [Nat.add_zero]⟩
    · obtain ⟨t, ht, rfl⟩ := mem_support_walkAlongSeq m (i + 1) (by omega) hy
      exact ⟨t + 1, by omega, by rw [Nat.add_right_comm i 1 t, Nat.add_assoc]⟩

/-- Dart sums along `walkAlongSeq`: the sum of the values at the consecutive pairs `(v t, v (t+1))`, `i ≤ t < i + m`. -/
theorem dartSum_walkAlongSeq {M : Type*} [AddCommMonoid M] (f : G.adj.Dart → M) (g : ℕ → M) (m : ℕ) :
    ∀ (i : ℕ) (h : i + m ≤ N),
      (∀ t, i ≤ t → t < i + m → ∀ ht : t < N, f ⟨(v t, v (t + 1)), hadj t ht⟩ = g t) →
      dartSum f (walkAlongSeq v hadj m i h) = ∑ t ∈ Finset.range m, g (i + t) := by
  have hcopy : ∀ {a b a' b' : V} (p : G.adj.Walk a b) (ha : a = a') (hb : b = b'),
      dartSum f (p.copy ha hb) = dartSum f p := by
    intro a b a' b' p ha hb
    subst ha hb
    rfl
  induction m with
  | zero => intro i h _; simp [walkAlongSeq]
  | succ m ih =>
    intro i h hg
    rw [walkAlongSeq, dartSum_cons, hcopy,
      ih (i + 1) (by omega) (fun t ht1 ht2 ht => hg t (by omega) (by omega) ht),
      Finset.sum_range_succ', hg i le_rfl (by omega) (by omega), Nat.add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Nat.add_right_comm i 1 t, Nat.add_assoc]

end SeqWalk

/-- **Telescoping**: a dart sum whose terms are the differences `F d.snd - F d.fst` is `F b - F a`. -/
theorem dartSum_eq_sub_of_forall {M : Type*} [AddCommGroup M] {G' : SimpleGraph V} (f : G'.Dart → M) (F : V → M) :
    ∀ {a b : V} (w : G'.Walk a b), (∀ d ∈ w.darts, f d = F d.snd - F d.fst) → dartSum f w = F b - F a
  | _, _, nil, _ => by simp
  | _, _, cons h p, hf => by
    rw [dartSum_cons, dartSum_eq_sub_of_forall f F p fun d hd => hf d (by simp [hd]),
      hf _ (by simp only [darts_cons, List.mem_cons, true_or])]
    abel

/-! ### Locations of drawn loops and dart images -/

/-- `Ψ ∘ D(W)` lies in the union of the cells of the vertices of `W` (TF3 §5.2). -/
theorem drawnLoop_mem_of_forall_cell (D : H.MonotoneDrawing) {a b : V} (w : G.adj.Walk a b) (P : ℂ → Prop)
    (hP : ∀ x ∈ w.support, ∀ q ∈ H.cell x, P q) (t : unitInterval) : P (drawnLoop D w t) := by
  rw [drawnLoop_apply]
  rcases (mem_range_drawnPath D w).mp ⟨t, rfl⟩ with h | ⟨d, hd, s, hs⟩
  · rw [h]
    exact hP a (start_mem_support w) _ (D.Ψ_pt a)
  · rw [← hs]
    rcases D.Ψ_arc d.fst d.snd d.adj s with h1 | h1
    · exact hP _ (dart_fst_mem_support_of_mem_darts w hd) _ h1
    · exact hP _ (dart_snd_mem_support_of_mem_darts w hd) _ h1

/-- The image of the arc of a dart lies in the two end cells. -/
theorem dartImage_mem_cell_union (D : H.MonotoneDrawing) (d : G.adj.Dart) (t : unitInterval) :
    dartImage D d t ∈ H.cell d.fst ∪ H.cell d.snd :=
  D.Ψ_arc d.fst d.snd d.adj t

/-- TFJ's **sector rule** (`logIncr_eq_log_sub_log`) for one dart: if `c (q - z)` lies in the slit plane for every
point `q` of the two end cells, the dart increment is `log (c (Ψ(pt y) - z)) - log (c (Ψ(pt x) - z))`. -/
theorem dartIncr_eq_log_sub_log_of_cells (D : H.MonotoneDrawing) (z : ℂ) (d : G.adj.Dart) {c : ℂ} (hc : c ≠ 0)
    (hslit : ∀ q ∈ H.cell d.fst ∪ H.cell d.snd, c * (q - z) ∈ Complex.slitPlane) :
    dartIncr D z d =
      Complex.log (c * (D.Ψ (D.pt d.snd) - z)) - Complex.log (c * (D.Ψ (D.pt d.fst) - z)) := by
  unfold dartIncr
  rw [logIncr_eq_log_sub_log _ z hc (fun t => hslit _ (dartImage_mem_cell_union D d t))]
  simp only [Path.coe_toContinuousMap, Path.target, Path.source]

end MatedCRTHarmonic.RouteM
