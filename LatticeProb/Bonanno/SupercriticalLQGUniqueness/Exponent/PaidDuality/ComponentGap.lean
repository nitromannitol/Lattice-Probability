/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.ComponentGap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.ComponentToPath




 



set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set Metric
open scoped ENNReal Convex

 
theorem compact_disjoint_dist_gap {U V : Set ℂ}
    (hU : IsCompact U) (hV : IsClosed V) (hdisj : Disjoint U V) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ U, ∀ y ∈ V, d ≤ dist x y := by
  obtain ⟨r, hr, hgap⟩ := exists_pos_forall_lt_edist hU hV hdisj
  refine ⟨(r : ℝ), hr, ?_⟩
  intro x hx y hy
  have hxy := hgap x hx y hy
  rw [edist_dist] at hxy
  have hxy' : ENNReal.ofReal (r : ℝ) < ENNReal.ofReal (dist x y) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hxy
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hxy')

 
theorem finite_uniform_radius {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → ℝ → Prop)
    (hpos : ∀ i ∈ s, ∃ r : ℝ, 0 < r ∧ P i r)
    (hmono : ∀ i ∈ s, ∀ r r' : ℝ, 0 < r' → r' ≤ r → P i r → P i r') :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, P i r := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨r, hr, hir⟩ := hpos i (Finset.mem_insert_self i s)
      obtain ⟨r', hr', hrest⟩ := ih
        (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
        (fun j hj q q' hq' hle hP =>
          hmono j (Finset.mem_insert_of_mem hj) q q' hq' hle hP)
      refine ⟨min r r', lt_min hr hr', ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact hmono j (Finset.mem_insert_self j s) r (min r r')
          (lt_min hr hr') (min_le_left _ _) hir
      · exact hmono j (Finset.mem_insert_of_mem hjs) r' (min r r')
          (lt_min hr hr') (min_le_right _ _) (hrest j hjs)

 
theorem finite_compact_pairwise_gap (t : Finset (Set ℂ))
    (hcompact : ∀ U ∈ t, IsCompact U)
    (hdisj : ∀ U ∈ t, ∀ V ∈ t, U ≠ V → Disjoint U V) :
    ∃ d : ℝ, 0 < d ∧ ∀ U ∈ t, ∀ V ∈ t, U ≠ V →
      ∀ x ∈ U, ∀ y ∈ V, d ≤ dist x y := by
  classical
  let P : Set ℂ × Set ℂ → ℝ → Prop := fun p r =>
    ∀ x ∈ p.1, ∀ y ∈ p.2, r ≤ dist x y
  have hpair : ∀ p ∈ t.offDiag, ∃ r : ℝ, 0 < r ∧ P p r := by
    intro p hp
    obtain ⟨hU, hV, hne⟩ := Finset.mem_offDiag.mp hp
    exact compact_disjoint_dist_gap (hcompact p.1 hU) (hcompact p.2 hV).isClosed
      (hdisj p.1 hU p.2 hV hne)
  have hmono : ∀ p ∈ t.offDiag, ∀ r r' : ℝ, 0 < r' → r' ≤ r → P p r → P p r' := by
    intro p hp r r' hr' hle hP x hx y hy
    exact hle.trans (hP x hx y hy)
  obtain ⟨d, hd, hall⟩ := finite_uniform_radius t.offDiag P hpair hmono
  refine ⟨d, hd, ?_⟩
  intro U hU V hV hne x hx y hy
  exact hall (U, V) (Finset.mem_offDiag.mpr ⟨hU, hV, hne⟩) x hx y hy

 
noncomputable def graphComponentLabels {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ) : Finset (Set ℂ) := by
  classical
  exact s.image (graphComponent s C)

theorem graphComponentLabels_cover {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ) :
    (⋃ i ∈ s, C i) ⊆ ⋃ V ∈ graphComponentLabels s C, V := by
  classical
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  refine Set.mem_iUnion₂.mpr ⟨graphComponent s C i, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · change x ∈ ⋃ j ∈ s.filter (fun j => Relation.ReflTransGen
      (fun k l => k ∈ s ∧ l ∈ s ∧ (C k ∩ C l).Nonempty) i j), C j
    exact Set.mem_iUnion₂.mpr ⟨i,
      Finset.mem_filter.mpr ⟨hi, Relation.ReflTransGen.refl⟩, hxi⟩

theorem graphComponentLabels_compact {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hcompact : ∀ i ∈ s, IsCompact (C i)) :
    ∀ V ∈ graphComponentLabels s C, IsCompact V := by
  classical
  intro V hV
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
  exact graphComponent_isCompact s C hcompact i

theorem graphComponentLabels_disjoint {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hpre : ∀ i ∈ s, IsPreconnected (C i)) :
    ∀ U ∈ graphComponentLabels s C, ∀ V ∈ graphComponentLabels s C,
      U ≠ V → Disjoint U V := by
  classical
  intro U hU V hV hne
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hU
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hV
  exact graphComponent_disjoint_of_ne s C
    (fun k hk => (hcompact k hk).isClosed) hpre hi hj hne

theorem graphComponentLabels_gap {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Set ℂ)
    (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hpre : ∀ i ∈ s, IsPreconnected (C i)) :
    ∃ d : ℝ, 0 < d ∧
      ∀ U ∈ graphComponentLabels s C,
      ∀ V ∈ graphComponentLabels s C, U ≠ V →
        ∀ x ∈ U, ∀ y ∈ V, d ≤ dist x y :=
  finite_compact_pairwise_gap (graphComponentLabels s C)
    (graphComponentLabels_compact s C hcompact)
    (graphComponentLabels_disjoint s C hcompact hpre)

end SupercriticalLQGUniqueness.Exponent.PaidDuality

