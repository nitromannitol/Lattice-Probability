/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.JExtract at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto

/-!
# Route M, winding lemma W3: extracting a cycle with non-zero dart sum

The winding argument, W3. For an antisymmetric function `f` on the darts
of a simple graph (`f d.symm = -f d`, TF3's W2), a closed walk with non-zero dart sum contains a cycle (length
`≥ 3`, darts among those of the walk) with non-zero dart sum (`exists_isCycle_dartSum_ne_zero`).

Proof (TF3 §7, strong induction on the length `m`): `m = 0` and the back-and-forth walks `x → y → x` have sum `0`
(W2), `m = 1` is impossible (no loops); if the vertices after the start are distinct the walk is a cycle;
otherwise a repeated vertex splits it into two shorter closed walks whose dart lists partition its darts, and one
of them has non-zero sum.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.RouteM

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G' : SimpleGraph V}

/-- The sum of a dart function along a walk. -/
def dartSum {M : Type*} [AddCommMonoid M] (f : G'.Dart → M) {u v : V} (w : G'.Walk u v) : M :=
  (w.darts.map f).sum

section DartSum

variable {M : Type*} [AddCommMonoid M] (f : G'.Dart → M)

@[simp]
theorem dartSum_nil {u : V} : dartSum f (nil : G'.Walk u u) = 0 := rfl

@[simp]
theorem dartSum_cons {u v w : V} (h : G'.Adj u v) (p : G'.Walk v w) :
    dartSum f (cons h p) = f ⟨(u, v), h⟩ + dartSum f p := by
  simp only [dartSum, darts_cons, List.map_cons, List.sum_cons]

theorem dartSum_append {u v w : V} (p : G'.Walk u v) (q : G'.Walk v w) :
    dartSum f (p.append q) = dartSum f p + dartSum f q := by
  simp only [dartSum, darts_append, List.map_append, List.sum_append]

end DartSum

/-- The support of a non-nil closed walk lies in the support of any walk containing its darts. -/
theorem JAux.support_subset_of_darts_subset {u v w : V} {C : G'.Walk u u} (hC : ¬ C.Nil) {W : G'.Walk v w}
    (h : ∀ d ∈ C.darts, d ∈ W.darts) : ∀ y ∈ C.support, y ∈ W.support := by
  intro y hy
  rw [← map_fst_darts_append, List.mem_append, List.mem_map, List.mem_singleton] at hy
  rcases hy with ⟨d, hd, rfl⟩ | rfl
  · exact dart_fst_mem_support_of_mem_darts W (h d hd)
  · cases C with
    | nil => exact absurd Nil.nil hC
    | cons h' p =>
      exact dart_fst_mem_support_of_mem_darts W (h _ (by simp only [darts_cons]; exact List.mem_cons_self))

/-- A repeated vertex in a walk: the walk splits as `q ++ (h' :: s) ++ t` with `h' :: s` a closed walk. -/
theorem JAux.exists_split_of_not_isPath {v u : V} {p : G'.Walk v u} (hp : ¬ p.IsPath) :
    ∃ (x y : V) (q : G'.Walk v x) (h' : G'.Adj x y) (s : G'.Walk y x) (t : G'.Walk x u),
      p = q.append (cons h' (s.append t)) := by
  classical
  rw [isPath_def, List.nodup_iff_count_le_one] at hp
  simp only [not_forall, not_le] at hp
  obtain ⟨x, hx⟩ := hp
  have hxmem : x ∈ p.support := List.count_pos_iff.mp (by omega)
  have hsupp : p.support = (p.takeUntil x hxmem).support ++ (p.dropUntil x hxmem).support.tail := by
    conv_lhs => rw [← p.take_spec hxmem]
    exact support_append _ _
  have h1 := p.count_support_takeUntil_eq_one hxmem
  have hxr : x ∈ (p.dropUntil x hxmem).support.tail := by
    rw [hsupp, List.count_append, h1] at hx
    exact List.count_pos_iff.mp (by omega)
  have hspec := p.take_spec hxmem
  revert hxr hspec
  generalize p.dropUntil x hxmem = r
  generalize p.takeUntil x hxmem = q
  intro hxr hspec
  cases r with
  | nil => simp at hxr
  | cons h' r' =>
    rw [support_cons, List.tail_cons] at hxr
    obtain ⟨s, t, rfl⟩ := mem_support_iff_exists_append.mp hxr
    exact ⟨x, _, q, h', s, t, hspec.symm⟩

/-- **W3 (extraction).** For an antisymmetric dart function, a closed walk with non-zero dart sum contains a
cycle with non-zero dart sum, all of whose darts are darts of the walk. -/
theorem exists_isCycle_dartSum_ne_zero {M : Type*} [AddCommGroup M] (f : G'.Dart → M)
    (hf : ∀ d, f d.symm = -f d) {u : V} (W : G'.Walk u u) (hW : dartSum f W ≠ 0) :
    ∃ (c : V) (C : G'.Walk c c), C.IsCycle ∧ (∀ d ∈ C.darts, d ∈ W.darts) ∧ dartSum f C ≠ 0 := by
  suffices key : ∀ n : ℕ, ∀ {u : V} (W : G'.Walk u u), W.length ≤ n → dartSum f W ≠ 0 →
      ∃ (c : V) (C : G'.Walk c c), C.IsCycle ∧ (∀ d ∈ C.darts, d ∈ W.darts) ∧ dartSum f C ≠ 0 from
    key _ W le_rfl hW
  intro n
  induction n with
  | zero =>
    intro u W hlen hW
    cases W with
    | nil => exact absurd (dartSum_nil f) hW
    | cons h p => simp at hlen
  | succ n ih =>
    intro u W hlen hW
    cases W with
    | nil => exact absurd (dartSum_nil f) hW
    | @cons _ v _ h p =>
      by_cases hp : p.IsPath
      · by_cases h3 : 3 ≤ (cons h p).length
        · refine ⟨u, cons h p, ?_, fun d hd => hd, hW⟩
          refine isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, h3⟩
          refine IsPath.mk' ?_
          rw [support_tail_of_not_nil _ not_nil_cons, support_cons, List.tail_cons]
          exact hp.support_nodup
        · exfalso
          cases p with
          | nil => exact G'.loopless.irrefl _ h
          | cons h' p' =>
            cases p' with
            | nil =>
              apply hW
              have hd : (⟨(v, u), h'⟩ : G'.Dart) = (⟨(u, v), h⟩ : G'.Dart).symm := rfl
              rw [dartSum_cons, dartSum_cons, dartSum_nil, hd, hf]
              abel
            | cons h'' p'' => simp only [length_cons] at h3; omega
      · obtain ⟨x, y, q, h', s, t, rfl⟩ := JAux.exists_split_of_not_isPath hp
        have hsum : dartSum f (cons h (q.append (cons h' (s.append t)))) =
            dartSum f (cons h' s) + dartSum f (cons h (q.append t)) := by
          simp only [dartSum_cons, dartSum_append]
          abel
        have hlenL : (cons h' s).length ≤ n := by
          simp only [length_cons, length_append] at hlen ⊢
          omega
        have hlenR : (cons h (q.append t)).length ≤ n := by
          simp only [length_cons, length_append] at hlen ⊢
          omega
        by_cases hL : dartSum f (cons h' s) = 0
        · have hR : dartSum f (cons h (q.append t)) ≠ 0 := by
            intro hR
            exact hW (by rw [hsum, hL, hR, add_zero])
          obtain ⟨c, C, hC, hCd, hCs⟩ := ih _ hlenR hR
          refine ⟨c, C, hC, fun d hd => ?_, hCs⟩
          have := hCd d hd
          simp only [darts_cons, darts_append, List.mem_cons, List.mem_append] at this ⊢
          tauto
        · obtain ⟨c, C, hC, hCd, hCs⟩ := ih _ hlenL hL
          refine ⟨c, C, hC, fun d hd => ?_, hCs⟩
          have := hCd d hd
          simp only [darts_cons, darts_append, List.mem_cons, List.mem_append] at this ⊢
          tauto

end MatedCRTHarmonic.RouteM
