/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112L1b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L1

/-!
# D112 packet L1, part 1b: connectedness, boundedness and finiteness of `(K_C, W_C)`

Side conditions of `zb_step2_of_tight` and `exists_tight_family` (S3D108P2D) for the family of
decision D112 (`decisions/DEC-112.md` §2) in CONF Lemma 3.3, Step 2 (arXiv:1905.00381,
C:1217–1234): `isPreconnected_confFatW` (the spine of a grid component is connected, mathlib
`IsPreconnected.biUnion_of_reflTransGen`), `isBounded_confFatW`, `finite_confFree`,
`finite_confCtrs`, `confCtrs_subset_confFatW`. Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-! ## Connectedness, boundedness, finiteness -/

theorem isPreconnected_confSpine (ε : ℝ) (z : ℂ) (F : Set (ℤ × ℤ)) {k₀ : ℤ × ℤ}
    (hk₀ : k₀ ∈ F) : IsPreconnected (confSpine ε z (confComp F k₀)) := by
  set C := confComp F k₀
  set t : Set ((ℤ × ℤ) × (ℤ × ℤ)) := {e | e.1 ∈ C ∧ e.2 ∈ C ∧ (e.1 = e.2 ∨ SqAdj e.1 e.2)}
  set s : (ℤ × ℤ) × (ℤ × ℤ) → Set ℂ := fun e => segment ℝ (confCtr ε z e.1) (confCtr ε z e.2)
  have eq : confSpine ε z C = ⋃ e ∈ t, s e := by
    ext x; simp only [confSpine, mem_iUnion, t, s, mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, k', hk', h, hx⟩; exact ⟨(k, k'), ⟨hk, hk', h⟩, hx⟩
    · rintro ⟨⟨k, k'⟩, ⟨hk, hk', h⟩, hx⟩; exact ⟨k, hk, k', hk', h, hx⟩
  rw [eq]
  set R : (ℤ × ℤ) × (ℤ × ℤ) → (ℤ × ℤ) × (ℤ × ℤ) → Prop :=
    fun i j => (s i ∩ s j).Nonempty ∧ i ∈ t ∧ j ∈ t
  have hRs : ∀ i j, R i j → R j i := fun i j h => ⟨by rw [inter_comm]; exact h.1, h.2.2, h.2.1⟩
  have hsym : ∀ {x y}, Relation.ReflTransGen R x y → Relation.ReflTransGen R y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hRs _ _ hbc) ih
  have hk₀C : k₀ ∈ C := Relation.ReflTransGen.refl
  have diag : ∀ a ∈ C, Relation.ReflTransGen R (k₀, k₀) (a, a) := by
    intro a ha
    induction ha with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hb hbc ih =>
      have hcC : c ∈ C := Relation.ReflTransGen.tail hb hbc
      have h1 : R (b, b) (b, c) := ⟨⟨confCtr ε z b, left_mem_segment _ _ _,
        left_mem_segment _ _ _⟩, ⟨hb, hb, Or.inl rfl⟩, ⟨hb, hcC, Or.inr hbc.1⟩⟩
      have h2 : R (b, c) (c, c) := ⟨⟨confCtr ε z c, right_mem_segment _ _ _,
        left_mem_segment _ _ _⟩, ⟨hb, hcC, Or.inr hbc.1⟩, ⟨hcC, hcC, Or.inl rfl⟩⟩
      exact (ih.tail h1).tail h2
  have toAll : ∀ e ∈ t, Relation.ReflTransGen R (k₀, k₀) e := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    exact (diag a ha).tail ⟨⟨confCtr ε z a, left_mem_segment _ _ _, left_mem_segment _ _ _⟩,
      ⟨ha, ha, Or.inl rfl⟩, ⟨ha, hb, hab⟩⟩
  refine IsPreconnected.biUnion_of_reflTransGen (fun e _ => (convex_segment _ _).isPreconnected)
    fun i hi j hj => ?_
  have hij : Relation.ReflTransGen R i j :=
    (hsym (toAll i hi)).trans (toAll j hj)
  clear toAll diag hj
  induction hij with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, hbc.2.1⟩

theorem isPreconnected_confFatW (ε : ℝ) (z : ℂ) (F : Set (ℤ × ℤ)) {k₀ : ℤ × ℤ}
    (hk₀ : k₀ ∈ F) : IsPreconnected (confFatW ε z (confComp F k₀)) := by
  set S := confSpine ε z (confComp F k₀)
  have hS := isPreconnected_confSpine ε z F hk₀
  by_cases hε : 0 < ε / 4
  · have hx₀ : confCtr ε z k₀ ∈ S := by
      simp only [S, confSpine, mem_iUnion]
      exact ⟨k₀, Relation.ReflTransGen.refl, k₀, Relation.ReflTransGen.refl, Or.inl rfl,
        left_mem_segment _ _ _⟩
    have eq : confFatW ε z (confComp F k₀) = ⋃ x ∈ S, (S ∪ ball x (ε / 4)) := by
      ext y
      simp only [confFatW, mem_iUnion, mem_union, mem_thickening_iff]
      constructor
      · rintro ⟨x, hx, hd⟩; exact ⟨x, hx, Or.inr (mem_ball.2 hd)⟩
      · rintro ⟨x, hx, h | h⟩
        · exact ⟨y, h, by simpa using hε⟩
        · exact ⟨x, hx, mem_ball.1 h⟩
    rw [eq, biUnion_eq_iUnion]
    refine isPreconnected_iUnion ⟨confCtr ε z k₀, mem_iInter.2 fun x => Or.inl hx₀⟩
      fun x => IsPreconnected.union x.1 x.2 (mem_ball_self hε) hS (convex_ball _ _).isPreconnected
  · have : confFatW ε z (confComp F k₀) = ∅ := by
      rw [confFatW]; exact thickening_of_nonpos (not_lt.1 hε) _
    rw [this]; exact isPreconnected_empty

theorem isBounded_confFatW {ε r : ℝ} (hε : 0 < ε) (hεr : 8 * ε ≤ r) (z : ℂ)
    {C : Set (ℤ × ℤ)} (hC : C ⊆ confFull ε z r) : Bornology.IsBounded (confFatW ε z C) := by
  refine (isBounded_ball (x := z) (r := 5 * r)).subset fun p hp => ?_
  have := confFatW_subset_annulus hε hεr z hC hp
  rw [mem_ball, dist_eq_norm]; exact this.2

theorem finite_confSqIdx_annulus {ε : ℝ} (hε : 0 < ε) (z : ℂ) (a b : ℝ) :
    (confSqIdx ε z (annulus z a b)).Finite := by
  set N : ℤ := ⌈|b| / ε⌉ + 1
  refine (((Finset.Icc (-N) N) ×ˢ (Finset.Icc (-N) N) : Finset (ℤ × ℤ)).finite_toSet).subset ?_
  rintro k ⟨u, ⟨h1, h2, h3, h4⟩, hu⟩
  have hn : ‖u - z‖ < |b| := lt_of_lt_of_le hu.2 (le_abs_self b)
  have hre : |u.re - z.re| ≤ |b| := by
    rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hn.le
  have him : |u.im - z.im| ≤ |b| := by
    rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans hn.le
  rw [abs_le] at hre him
  have hc : |b| / ε ≤ (⌈|b| / ε⌉ : ℝ) := Int.le_ceil _
  have hc' : |b| ≤ (⌈|b| / ε⌉ : ℝ) * ε := by rwa [div_le_iff₀ hε] at hc
  have k1u : (k.1 : ℝ) < N := by
    simp only [N]; push_cast; by_contra hh; push_neg at hh; nlinarith
  have k1l : (-N : ℝ) ≤ k.1 := by
    simp only [N]; push_cast; by_contra hh; push_neg at hh; nlinarith
  have k2u : (k.2 : ℝ) < N := by
    simp only [N]; push_cast; by_contra hh; push_neg at hh; nlinarith
  have k2l : (-N : ℝ) ≤ k.2 := by
    simp only [N]; push_cast; by_contra hh; push_neg at hh; nlinarith
  simp only [Finset.coe_product, Finset.coe_Icc, mem_prod, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact_mod_cast k1l
  · exact_mod_cast k1u.le
  · exact_mod_cast k2l
  · exact_mod_cast k2u.le

theorem finite_confFree {ε r : ℝ} (hε : 0 < ε) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    (confFree ε z r T).Finite :=
  (finite_confSqIdx_annulus hε z (3 * r) (4 * r)).subset
    ((confFree_subset_full).trans (confFull_subset_idx hε z))

theorem finite_confCtrs {ε : ℝ} (z : ℂ) {C : Set (ℤ × ℤ)} (hC : C.Finite) :
    (confCtrs ε z C).Finite := hC.image _

theorem confCtrs_subset_confFatW {ε : ℝ} (hε : 0 < ε) (z : ℂ) (C : Set (ℤ × ℤ)) :
    confCtrs ε z C ⊆ confFatW ε z C := by
  rintro _ ⟨k, hk, rfl⟩
  refine self_subset_thickening (by linarith) _ ?_
  simp only [confSpine, mem_iUnion]
  exact ⟨k, hk, k, hk, Or.inl rfl, left_mem_segment _ _ _⟩

end LQGMetric.CONF
