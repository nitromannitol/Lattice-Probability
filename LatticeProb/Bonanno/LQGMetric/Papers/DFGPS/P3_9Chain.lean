/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_9Chain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Neg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.9: chaining the squares covering `K` (deterministic part)

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.9 assuming Proposition 3.10 (T:1767–1775): "We can cover `K` by finitely
many Euclidean squares `S_1, …, S_n` which are contained in `U` … " and deduce the bound for
`sup_{z,w∈𝕣K} D_h(z,w;𝕣U)` from the bounds for `sup_{z,w∈𝕣S_k} D_h(z,w;𝕣S_k)`. The paper leaves
the deterministic step implicit; we prove it here (own elementary argument, proposed DEVIATIONS
entry): since `K` is connected and covered by the open sets `S_k ⊆ V`, every point of `K` is
reached from a fixed `z ∈ K` through a chain of overlapping `S_k`, whence
`sup_{u,v∈K} D(u,v;V) ≤ 2 Σ_k sup_{x,y∈S_k} D(x,y;S_k)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

/-- the indices reachable from `z` in at most `m` overlap steps -/
def reachIdx (s : Finset ι) (S : ι → Set ℂ) (z : ℂ) : ℕ → Finset ι
  | 0 => {i ∈ s | z ∈ S i}
  | m + 1 => reachIdx s S z m ∪ {i ∈ s | ∃ j ∈ reachIdx s S z m, (S i ∩ S j).Nonempty}

lemma reachIdx_subset (s : Finset ι) (S : ι → Set ℂ) (z : ℂ) : ∀ m, reachIdx s S z m ⊆ s
  | 0 => Finset.filter_subset _ _
  | m + 1 => Finset.union_subset (reachIdx_subset s S z m) (Finset.filter_subset _ _)

lemma internal_le_internalDiam (D : ContMetric) {A V : Set ℂ} {x y : ℂ} (hx : x ∈ A)
    (hy : y ∈ A) : D.internal V x y ≤ internalDiam D A V :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)

lemma internal_anti (D : ContMetric) {A B : Set ℂ} (hAB : A ⊆ B) (x y : ℂ) :
    D.internal B x y ≤ D.internal A x y :=
  MetricGeometry.internalEDist_anti (image_mono hAB) _ _

lemma reach_bound (D : ContMetric) {V : Set ℂ} (s : Finset ι) (S : ι → Set ℂ)
    (hSV : ∀ i ∈ s, S i ⊆ V) (z : ℂ) :
    ∀ m, ∀ i ∈ reachIdx s S z m, ∀ u ∈ S i,
      D.internal V z u ≤ ∑ j ∈ reachIdx s S z m, internalDiam D (S j) (S j) := by
  intro m
  induction m with
  | zero =>
    intro i hi u hu
    have hi' := Finset.mem_filter.1 hi
    exact (internal_anti D (hSV i hi'.1) z u).trans ((internal_le_internalDiam D hi'.2 hu).trans
      (Finset.single_le_sum (f := fun j => internalDiam D (S j) (S j)) (fun _ _ => zero_le) hi))
  | succ m ih =>
    intro i hi u hu
    have hsub : reachIdx s S z m ⊆ reachIdx s S z (m + 1) := Finset.subset_union_left
    by_cases him : i ∈ reachIdx s S z m
    · exact (ih i him u hu).trans (Finset.sum_le_sum_of_subset hsub)
    · have hi' : i ∈ {i ∈ s | ∃ j ∈ reachIdx s S z m, (S i ∩ S j).Nonempty} := by
        rcases Finset.mem_union.1 hi with h | h
        · exact absurd h him
        · exact h
      obtain ⟨his, j, hj, v, hvi, hvj⟩ := Finset.mem_filter.1 hi'
      calc D.internal V z u ≤ D.internal V z v + D.internal V v u := internal_triangle D V z v u
        _ ≤ ∑ j ∈ reachIdx s S z m, internalDiam D (S j) (S j) + internalDiam D (S i) (S i) :=
            add_le_add (ih j hj v hvj) ((internal_anti D (hSV i his) v u).trans
              (internal_le_internalDiam D hvi hu))
        _ = ∑ j ∈ insert i (reachIdx s S z m), internalDiam D (S j) (S j) := by
            rw [Finset.sum_insert him, add_comm]
        _ ≤ ∑ j ∈ reachIdx s S z (m + 1), internalDiam D (S j) (S j) := by
            refine Finset.sum_le_sum_of_subset (Finset.insert_subset hi hsub)

/-- **Chaining over a finite open cover of a connected set** (deterministic step of the proof of
DFGPS Prop 3.9, T:1767–1775; own elementary argument) -/
theorem internalDiam_le_two_sum (D : ContMetric) {K V : Set ℂ} (hK : IsPreconnected K)
    (s : Finset ι) (S : ι → Set ℂ) (hSo : ∀ i, IsOpen (S i)) (hSV : ∀ i ∈ s, S i ⊆ V)
    (hcov : K ⊆ ⋃ i ∈ s, S i) :
    internalDiam D K V ≤ 2 * ∑ i ∈ s, internalDiam D (S i) (S i) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · simp [internalDiam]
  set T : ℕ → Finset ι := reachIdx s S z
  set R : Finset ι := {i ∈ s | ∃ m, i ∈ T m}
  set M := ∑ i ∈ s, internalDiam D (S i) (S i)
  have hbd : ∀ i ∈ R, ∀ u ∈ S i, D.internal V z u ≤ M := by
    intro i hi u hu
    obtain ⟨-, m, hm⟩ := Finset.mem_filter.1 hi
    exact (reach_bound D s S hSV z m i hm u hu).trans
      (Finset.sum_le_sum_of_subset (reachIdx_subset s S z m))
  -- every point of `K` lies in a reachable square
  have hreach : K ⊆ ⋃ i ∈ R, S i := by
    by_contra hne
    obtain ⟨x, hxK, hxR⟩ := not_subset.1 hne
    obtain ⟨i₀, hi₀s, hzi₀⟩ := mem_iUnion₂.1 (hcov hz)
    have hi₀R : i₀ ∈ R := Finset.mem_filter.2 ⟨hi₀s, 0, Finset.mem_filter.2 ⟨hi₀s, hzi₀⟩⟩
    obtain ⟨i₁, hi₁s, hxi₁⟩ := mem_iUnion₂.1 (hcov hxK)
    have hi₁R : i₁ ∉ R := fun h => hxR (mem_iUnion₂.2 ⟨i₁, h, hxi₁⟩)
    have hopen1 : IsOpen (⋃ i ∈ R, S i) := isOpen_biUnion fun i _ => hSo i
    have hopen2 : IsOpen (⋃ i ∈ s.filter (· ∉ R), S i) := isOpen_biUnion fun i _ => hSo i
    have hcov' : K ⊆ (⋃ i ∈ R, S i) ∪ ⋃ i ∈ s.filter (· ∉ R), S i := by
      intro y hy
      obtain ⟨i, his, hyi⟩ := mem_iUnion₂.1 (hcov hy)
      by_cases hiR : i ∈ R
      · exact Or.inl (mem_iUnion₂.2 ⟨i, hiR, hyi⟩)
      · exact Or.inr (mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨his, hiR⟩, hyi⟩)
    obtain ⟨y, -, hy1, hy2⟩ := hK _ _ hopen1 hopen2 hcov' ⟨z, hz, mem_iUnion₂.2 ⟨i₀, hi₀R, hzi₀⟩⟩
      ⟨x, hxK, mem_iUnion₂.2 ⟨i₁, Finset.mem_filter.2 ⟨hi₁s, hi₁R⟩, hxi₁⟩⟩
    obtain ⟨i, hiR, hyi⟩ := mem_iUnion₂.1 hy1
    obtain ⟨j, hjs, hyj⟩ := mem_iUnion₂.1 hy2
    obtain ⟨hjs', hjR⟩ := Finset.mem_filter.1 hjs
    obtain ⟨-, m, hm⟩ := Finset.mem_filter.1 hiR
    refine hjR (Finset.mem_filter.2 ⟨hjs', m + 1, Finset.mem_union_right _ ?_⟩)
    exact Finset.mem_filter.2 ⟨hjs', i, hm, y, hyj, hyi⟩
  have hK' : ∀ u ∈ K, D.internal V z u ≤ M := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := mem_iUnion₂.1 (hreach hu)
    exact hbd i hi u hui
  refine iSup₂_le fun u hu => iSup₂_le fun w hw => ?_
  calc D.internal V u w ≤ D.internal V u z + D.internal V z w := internal_triangle D V u z w
    _ = D.internal V z u + D.internal V z w := by
        rw [ContMetric.internal, ContMetric.internal, MetricGeometry.internalEDist_comm]; rfl
    _ ≤ M + M := add_le_add (hK' u hu) (hK' w hw)
    _ = 2 * M := (two_mul M).symm

end LQGMetric.DFGPS
