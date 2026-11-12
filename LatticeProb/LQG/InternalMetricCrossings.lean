import LatticeProb.LQG.LQGMetricMeasurable
import LatticeProb.LQG.WeylChainLower
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet

/-!
# Crossings of closed rectangles and the internal metric

Deterministic lemmas for the "#"-shape step in the proof of Dubédat-Falconet-Gwynne-Pfeffer-Sun
(arXiv:1905.00380, Proposition 3.10, Step 2): a closed rectangle `R = [x₀, x₁] × [y₀, y₁]` carrying two left-right
crossings and two top-bottom crossings of `D`-length at most `L` has any two points of the union of the four crossings
at `D(·, ·; U)`-distance at most `3 L`, for every set `U ⊇ R`, since every left-right crossing of `R` meets every
top-bottom crossing of `R`.

## Main statements

* `curveLength_mono_Icc`: the length of a curve on `[a, b]` is at most its length on `[a', b'] ⊇ [a, b]`.
* `IsEuclideanLengthMetric.internalMetric_le_pathLength_of_mem`: two points of a path in `U` are at internal distance
  in `U` at most the length of the path.
* `IsEuclideanLengthMetric.internalMetric_le_add_of_meet`, `internalMetric_le_add_add_of_meet`: chains of two or three
  paths in `U` which meet.
* `IsLeftRightCrossing`, `IsTopBottomCrossing`: a path in a closed rectangle joining its vertical sides, respectively
  its horizontal sides; `IsLeftRightCrossing.exists_eq` (a left-right crossing meets a top-bottom crossing), from the
  planar crossing lemma `LQGMetric.RectMeet.rect_crossings_meet`.
* `IsEuclideanLengthMetric.internalMetric_le_of_crossings`: the bound `3 L` on the union of the four crossings.
-/

namespace LatticeProb.LQG

open Set
open scoped ENNReal unitInterval

/-- The length of a curve on a subinterval is at most its length on a larger interval. -/
theorem curveLength_mono_Icc (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    curveLength D p a b ≤ curveLength D p a' b' := by
  unfold curveLength
  refine iSup_le fun q => ?_
  exact le_iSup_of_le (⟨q.1, q.2.1, q.2.2.1, fun i => ⟨ha.trans (q.2.2.2 i).1, (q.2.2.2 i).2.trans hb⟩⟩ :
    ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a' b' }) le_rfl

/-- Two points of a path with range in `U` are at internal distance in `U` at most the `D`-length of the path. -/
theorem IsEuclideanLengthMetric.internalMetric_le_pathLength_of_mem {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ U) (s t : I) :
    internalMetric D U (P s) (P t) ≤ pathLength D P := by
  have key : ∀ s t : I, (s : ℝ) ≤ t → internalMetric D U (P s) (P t) ≤ pathLength D P := by
    intro s t hst
    have hW : P.extend '' Icc (s : ℝ) t ⊆ U := by
      rintro _ ⟨r, -, rfl⟩
      obtain ⟨r', hr'⟩ : P.extend r ∈ range P := by
        rw [← Path.extend_range]; exact mem_range_self r
      rw [← hr']; exact hP r'
    have h := internalMetric_le_curveLength_of_image_subset hD P hst hW
    rw [Path.extend_extends', Path.extend_extends'] at h
    exact h.trans (curveLength_mono_Icc D P.extend s.2.1 t.2.2)
  rcases le_total (s : ℝ) t with h | h
  · exact key s t h
  · rw [hD.internalMetric_symm]; exact key t s h

/-- Two paths in `U` which meet: a point of the first and a point of the second are at internal distance in `U` at most
the sum of the lengths of the paths. -/
theorem IsEuclideanLengthMetric.internalMetric_le_add_of_meet {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} {x y x' y' : ℂ} {P : Path x y} {Q : Path x' y'}
    (hP : ∀ t, P t ∈ U) (hQ : ∀ t, Q t ∈ U) (hPQ : ∃ s₀ t₀, P s₀ = Q t₀) (s t : I) :
    internalMetric D U (P s) (Q t) ≤ pathLength D P + pathLength D Q := by
  obtain ⟨s₀, t₀, h⟩ := hPQ
  calc internalMetric D U (P s) (Q t)
      ≤ internalMetric D U (P s) (P s₀) + internalMetric D U (P s₀) (Q t) := hD.internalMetric_triangle U _ _ _
    _ ≤ pathLength D P + pathLength D Q := by
        refine add_le_add (hD.internalMetric_le_pathLength_of_mem P hP s s₀) ?_
        rw [h]; exact hD.internalMetric_le_pathLength_of_mem Q hQ t₀ t

/-- Three paths in `U`, the first meeting the second and the second meeting the third: a point of the first and a point
of the third are at internal distance in `U` at most the sum of the three lengths. -/
theorem IsEuclideanLengthMetric.internalMetric_le_add_add_of_meet {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} {x y x' y' x'' y'' : ℂ} {P : Path x y} {Q : Path x' y'}
    {R : Path x'' y''} (hP : ∀ t, P t ∈ U) (hQ : ∀ t, Q t ∈ U) (hR : ∀ t, R t ∈ U)
    (hPQ : ∃ s₀ t₀, P s₀ = Q t₀) (hQR : ∃ s₀ t₀, Q s₀ = R t₀) (s t : I) :
    internalMetric D U (P s) (R t) ≤ pathLength D P + pathLength D Q + pathLength D R := by
  obtain ⟨s₀, t₀, h⟩ := hPQ
  calc internalMetric D U (P s) (R t)
      ≤ internalMetric D U (P s) (P s₀) + internalMetric D U (P s₀) (R t) := hD.internalMetric_triangle U _ _ _
    _ ≤ pathLength D P + (pathLength D Q + pathLength D R) := by
        refine add_le_add (hD.internalMetric_le_pathLength_of_mem P hP s s₀) ?_
        rw [h]; exact hD.internalMetric_le_add_of_meet hQ hR hQR t₀ t
    _ = pathLength D P + pathLength D Q + pathLength D R := (add_assoc _ _ _).symm

/-- `P` is a left-right crossing of the closed rectangle `[x₀, x₁] × [y₀, y₁]`: its range lies in the rectangle, it
starts on the left side and ends on the right side. -/
def IsLeftRightCrossing (x₀ x₁ y₀ y₁ : ℝ) {a b : ℂ} (P : Path a b) : Prop :=
  (∀ t, P t ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁) ∧ a.re = x₀ ∧ b.re = x₁

/-- `P` is a top-bottom crossing of the closed rectangle `[x₀, x₁] × [y₀, y₁]`: its range lies in the rectangle, it
starts on the top side and ends on the bottom side. -/
def IsTopBottomCrossing (x₀ x₁ y₀ y₁ : ℝ) {a b : ℂ} (P : Path a b) : Prop :=
  (∀ t, P t ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁) ∧ a.im = y₁ ∧ b.im = y₀

/-- A left-right crossing of a rectangle is a left-right crossing of every taller rectangle with the same vertical
sides. -/
theorem IsLeftRightCrossing.mono {x₀ x₁ y₀ y₁ y₀' y₁' : ℝ} {a b : ℂ} {P : Path a b}
    (h : IsLeftRightCrossing x₀ x₁ y₀ y₁ P) (h₀ : y₀' ≤ y₀) (h₁ : y₁ ≤ y₁') :
    IsLeftRightCrossing x₀ x₁ y₀' y₁' P := by
  refine ⟨fun t => ?_, h.2⟩
  have ht := Complex.mem_reProdIm.1 (h.1 t)
  exact Complex.mem_reProdIm.2 ⟨ht.1, h₀.trans ht.2.1, ht.2.2.trans h₁⟩

/-- A top-bottom crossing of a rectangle is a top-bottom crossing of every wider rectangle with the same horizontal
sides. -/
theorem IsTopBottomCrossing.mono {x₀ x₁ y₀ y₁ x₀' x₁' : ℝ} {a b : ℂ} {P : Path a b}
    (h : IsTopBottomCrossing x₀ x₁ y₀ y₁ P) (h₀ : x₀' ≤ x₀) (h₁ : x₁ ≤ x₁') :
    IsTopBottomCrossing x₀' x₁' y₀ y₁ P := by
  refine ⟨fun t => ?_, h.2⟩
  have ht := Complex.mem_reProdIm.1 (h.1 t)
  exact Complex.mem_reProdIm.2 ⟨⟨h₀.trans ht.1.1, ht.1.2.trans h₁⟩, ht.2⟩

/-- A left-right crossing and a top-bottom crossing of the same closed rectangle meet. This is the planar crossing
lemma `LQGMetric.RectMeet.rect_crossings_meet`, for paths. -/
theorem IsLeftRightCrossing.exists_eq {x₀ x₁ y₀ y₁ : ℝ} {a b c d : ℂ} {P : Path a b} {Q : Path c d}
    (hP : IsLeftRightCrossing x₀ x₁ y₀ y₁ P) (hQ : IsTopBottomCrossing x₀ x₁ y₀ y₁ Q) : ∃ s t, P s = Q t := by
  have hmaps : ∀ {u v : ℂ} (R : Path u v), (∀ t, R t ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁) →
      MapsTo R.extend (Icc 0 1) (LQGMetric.RectCross.rect x₀ x₁ y₀ y₁) := by
    intro u v R hR r hr
    rw [Path.extend_apply R hr]
    exact Complex.mem_reProdIm.1 (hR _)
  obtain ⟨s, hs, t, ht, h⟩ := LQGMetric.RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ P.extend Q.extend
    P.continuous_extend.continuousOn Q.continuous_extend.continuousOn (hmaps P hP.1) (hmaps Q hQ.1)
    (by simpa using hP.2.1) (by simpa using hP.2.2) (by simpa using hQ.2.1) (by simpa using hQ.2.2)
  refine ⟨⟨s, hs⟩, ⟨t, ht⟩, ?_⟩
  rwa [Path.extend_apply P hs, Path.extend_apply Q ht] at h

/-- The "#"-shape bound: two left-right crossings `P₁, P₂` and two top-bottom crossings `Q₁, Q₂` of a closed rectangle
`R ⊆ U`, each of `D`-length at most `L`. Any two points of the union of the four crossings are at internal distance in
`U` at most `3 L`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_crossings {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {x₀ x₁ y₀ y₁ : ℝ} {U : Set ℂ} (hU : Icc x₀ x₁ ×ℂ Icc y₀ y₁ ⊆ U)
    {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℂ} {P₁ : Path a₁ b₁} {P₂ : Path a₂ b₂} {Q₁ : Path c₁ d₁} {Q₂ : Path c₂ d₂}
    (hP₁ : IsLeftRightCrossing x₀ x₁ y₀ y₁ P₁) (hP₂ : IsLeftRightCrossing x₀ x₁ y₀ y₁ P₂)
    (hQ₁ : IsTopBottomCrossing x₀ x₁ y₀ y₁ Q₁) (hQ₂ : IsTopBottomCrossing x₀ x₁ y₀ y₁ Q₂) {L : ℝ≥0∞}
    (hLP₁ : pathLength D P₁ ≤ L) (hLP₂ : pathLength D P₂ ≤ L) (hLQ₁ : pathLength D Q₁ ≤ L)
    (hLQ₂ : pathLength D Q₂ ≤ L) {z w : ℂ} (hz : z ∈ range P₁ ∪ range P₂ ∪ range Q₁ ∪ range Q₂)
    (hw : w ∈ range P₁ ∪ range P₂ ∪ range Q₁ ∪ range Q₂) :
    internalMetric D U z w ≤ 3 * L := by
  rw [show (3 : ℝ≥0∞) * L = L + L + L by ring]
  have hHV : ∀ {u v u' v' : ℂ} {A : Path u v} {B : Path u' v'} {z w : ℂ}, z ∈ range A → w ∈ range B →
      IsLeftRightCrossing x₀ x₁ y₀ y₁ A → IsTopBottomCrossing x₀ x₁ y₀ y₁ B → pathLength D A ≤ L →
      pathLength D B ≤ L → internalMetric D U z w ≤ L + L + L := by
    rintro u v u' v' A B _ _ ⟨s, rfl⟩ ⟨t, rfl⟩ hA hB hLA hLB
    refine (hD.internalMetric_le_add_of_meet (fun r => hU (hA.1 r)) (fun r => hU (hB.1 r)) (hA.exists_eq hB) s t).trans ?_
    exact (add_le_add hLA hLB).trans le_self_add
  have hVH : ∀ {u v u' v' : ℂ} {A : Path u v} {B : Path u' v'} {z w : ℂ}, z ∈ range A → w ∈ range B →
      IsTopBottomCrossing x₀ x₁ y₀ y₁ A → IsLeftRightCrossing x₀ x₁ y₀ y₁ B → pathLength D A ≤ L →
      pathLength D B ≤ L → internalMetric D U z w ≤ L + L + L := by
    intro u v u' v' A B z w hz hw hA hB hLA hLB
    rw [hD.internalMetric_symm]
    exact hHV hw hz hB hA hLB hLA
  have hHH : ∀ {u v u' v' : ℂ} {A : Path u v} {B : Path u' v'} {z w : ℂ}, z ∈ range A → w ∈ range B →
      IsLeftRightCrossing x₀ x₁ y₀ y₁ A → IsLeftRightCrossing x₀ x₁ y₀ y₁ B → pathLength D A ≤ L →
      pathLength D B ≤ L → internalMetric D U z w ≤ L + L + L := by
    rintro u v u' v' A B _ _ ⟨s, rfl⟩ ⟨t, rfl⟩ hA hB hLA hLB
    obtain ⟨s₁, t₁, h₁⟩ := hB.exists_eq hQ₁
    refine (hD.internalMetric_le_add_add_of_meet (fun r => hU (hA.1 r)) (fun r => hU (hQ₁.1 r))
      (fun r => hU (hB.1 r)) (hA.exists_eq hQ₁) ⟨t₁, s₁, h₁.symm⟩ s t).trans ?_
    exact add_le_add (add_le_add hLA hLQ₁) hLB
  have hVV : ∀ {u v u' v' : ℂ} {A : Path u v} {B : Path u' v'} {z w : ℂ}, z ∈ range A → w ∈ range B →
      IsTopBottomCrossing x₀ x₁ y₀ y₁ A → IsTopBottomCrossing x₀ x₁ y₀ y₁ B → pathLength D A ≤ L →
      pathLength D B ≤ L → internalMetric D U z w ≤ L + L + L := by
    rintro u v u' v' A B _ _ ⟨s, rfl⟩ ⟨t, rfl⟩ hA hB hLA hLB
    obtain ⟨s₁, t₁, h₁⟩ := hP₁.exists_eq hA
    refine (hD.internalMetric_le_add_add_of_meet (fun r => hU (hA.1 r)) (fun r => hU (hP₁.1 r))
      (fun r => hU (hB.1 r)) ⟨t₁, s₁, h₁.symm⟩ (hP₁.exists_eq hB) s t).trans ?_
    exact add_le_add (add_le_add hLA hLP₁) hLB
  rcases hz with ((hz | hz) | hz) | hz <;> rcases hw with ((hw | hw) | hw) | hw
  all_goals first
    | exact hHH hz hw ‹_› ‹_› ‹_› ‹_›
    | exact hHV hz hw ‹_› ‹_› ‹_› ‹_›
    | exact hVH hz hw ‹_› ‹_› ‹_› ‹_›
    | exact hVV hz hw ‹_› ‹_› ‹_› ‹_›

end LatticeProb.LQG
