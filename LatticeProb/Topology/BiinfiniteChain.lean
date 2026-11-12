import Mathlib
import LatticeProb.Topology.PolygonalRay

/-!
# Parametrising a bi-infinite polygonal chain

A sequence `u : ℤ → E` with `u n → a` as `n → -∞` and `u n → b` as `n → +∞` determines the bi-infinite polygonal
chain `⋃ n, [u n, u (n + 1)]` from `a` to `b`. Running the polygonal ray through `u 0, u (-1), u (-2), …` towards
`a` backwards on `[0, 1/2]` and the polygonal ray through `u 0, u 1, u 2, …` towards `b` on `[1/2, 1]` gives a
parametrisation `f` that is continuous on `[0, 1]`, with `f 0 = a`, `f 1 = b`, and `f` traces the chain on `(0, 1)`.
It is injective on `[0, 1]` when the chain is simple, avoids `a` and `b`, and `a ≠ b`.

## Main statements

* `IsBiinfiniteChainParam u a b f`: the two halves of `f` are polygonal ray parametrisations.
* `exists_biinfiniteChain_param`: existence of a parametrisation continuous on `[0, 1]`.
* `IsBiinfiniteChainParam.image_Ioo`, `IsBiinfiniteChainParam.image_Icc`: the traced sets.
* `IsBiinfiniteChainParam.injOn`: injectivity for simple chains.
-/

open Set Filter Metric
open scoped Topology

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsPolygonalRayParam

variable {v : ℕ → E} {x : E} {β β' : ℝ → E}

/-- The `n`-th interval of the dyadic time grid lies in `[0, 1)`. -/
theorem grid_subset_Ico (n : ℕ) : Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)) ⊆ Ico 0 1 := by
  intro t ht
  have h1 : (2⁻¹ : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- A polygonal ray parametrisation only depends on the values on `[0, 1]`. -/
theorem congr (hβ : IsPolygonalRayParam v x β) (h : ∀ s ∈ Icc (0 : ℝ) 1, β' s = β s) :
    IsPolygonalRayParam v x β' := by
  refine ⟨by rw [h 1 ⟨zero_le_one, le_rfl⟩, hβ.1], fun n t ht => ?_⟩
  rw [h t (Ico_subset_Icc_self (grid_subset_Ico n ht)), hβ.2 n t ht]

/-- The ray starts at `v 0`. -/
theorem apply_zero (hβ : IsPolygonalRayParam v x β) : β 0 = v 0 := by
  simpa using hβ.apply_grid 0

/-- Before time `1` the ray traces exactly the union of its segments. -/
theorem image_Ico (hβ : IsPolygonalRayParam v x β) :
    β '' Ico 0 1 = ⋃ n, segment ℝ (v n) (v (n + 1)) := by
  refine Subset.antisymm ?_ (iUnion_subset fun n => ?_)
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨n, hn⟩ := hβ.exists_mem_segment ht
    exact mem_iUnion.2 ⟨n, hn⟩
  · rw [← hβ.image_Icc_grid n]
    exact image_mono (grid_subset_Ico n)

end IsPolygonalRayParam

/-- `f` parametrises the bi-infinite polygonal chain through `u` from `a` to `b`: `s ↦ f ((1 - s) / 2)` is the
polygonal ray through `u 0, u (-1), u (-2), …` towards `a`, and `s ↦ f ((1 + s) / 2)` is the polygonal ray through
`u 0, u 1, u 2, …` towards `b`. -/
def IsBiinfiniteChainParam (u : ℤ → E) (a b : E) (f : ℝ → E) : Prop :=
  IsPolygonalRayParam (fun n : ℕ => u (-(n : ℤ))) a (fun s => f ((1 - s) / 2)) ∧
    IsPolygonalRayParam (fun n : ℕ => u n) b (fun s => f ((1 + s) / 2))

/-- **Bi-infinite chain parametrisation.** If `u n → a` as `n → -∞` and `u n → b` as `n → +∞`, the bi-infinite
polygonal chain through `u` has a parametrisation that is continuous on `[0, 1]`. -/
theorem exists_biinfiniteChain_param {u : ℤ → E} {a b : E} (ha : Tendsto u atBot (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) :
    ∃ f : ℝ → E, ContinuousOn f (Icc 0 1) ∧ IsBiinfiniteChainParam u a b f := by
  obtain ⟨βm, hcm, hm⟩ := exists_polygonalRay_param (v := fun n : ℕ => u (-(n : ℤ))) (x := a)
    (ha.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  obtain ⟨βp, hcp, hp⟩ := exists_polygonalRay_param (v := fun n : ℕ => u n) (x := b)
    (hb.comp tendsto_natCast_atTop_atTop)
  have h0 : βm 0 = βp 0 := by rw [hm.apply_zero, hp.apply_zero]; simp
  set f : ℝ → E := fun t => if t ≤ 1 / 2 then βm (1 - 2 * t) else βp (2 * t - 1) with hf_def
  have hfm : ∀ t, t ≤ 1 / 2 → f t = βm (1 - 2 * t) := fun t ht => ite_eq_left ht
  have hfp : ∀ t, 1 / 2 ≤ t → f t = βp (2 * t - 1) := by
    intro t ht
    rcases ht.lt_or_eq with ht | rfl
    · exact ite_eq_right (not_le.2 ht)
    · rw [hfm _ le_rfl]
      norm_num [h0]
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [← Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine ContinuousOn.congr (f := βm ∘ fun t : ℝ => 1 - 2 * t) ?_ fun t ht => hfm t ht.2
      refine hcm.comp (by fun_prop) fun t ht => ?_
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · refine ContinuousOn.congr (f := βp ∘ fun t : ℝ => 2 * t - 1) ?_ fun t ht => hfp t ht.1
      refine hcp.comp (by fun_prop) fun t ht => ?_
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · refine hm.congr fun s hs => ?_
    rw [hfm _ (by linarith [hs.1])]
    congr 1
    ring
  · refine hp.congr fun s hs => ?_
    rw [hfp _ (by linarith [hs.1])]
    congr 1
    ring

namespace IsBiinfiniteChainParam

variable {u : ℤ → E} {a b : E} {f : ℝ → E}

theorem apply_zero (hf : IsBiinfiniteChainParam u a b f) : f 0 = a := by
  simpa using hf.1.1

theorem apply_one (hf : IsBiinfiniteChainParam u a b f) : f 1 = b := by
  simpa using hf.2.1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The two rays read off `f` on `[0, 1]`. -/
theorem eq_or_eq (f : ℝ → E) (t : ℝ) :
    (t ≤ 1 / 2 ∧ f t = (fun s => f ((1 - s) / 2)) (1 - 2 * t)) ∨
      (1 / 2 ≤ t ∧ f t = (fun s => f ((1 + s) / 2)) (2 * t - 1)) := by
  rcases le_total t (1 / 2) with ht | ht
  · exact Or.inl ⟨ht, by simp only; congr 1; ring⟩
  · exact Or.inr ⟨ht, by simp only; congr 1; ring⟩

/-- The segments of the ray towards `a`, re-indexed over the negative integers. -/
theorem iUnion_segment_neg :
    (⋃ n : ℕ, segment ℝ (u (-(n : ℤ))) (u (-((n + 1 : ℕ) : ℤ)))) =
      ⋃ m : ℤ, ⋃ (_ : m < 0), segment ℝ (u m) (u (m + 1)) := by
  ext y
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-(n : ℤ) - 1, by omega, ?_⟩
    rw [segment_symm] at hn
    convert hn using 3 <;> push_cast <;> ring
  · rintro ⟨m, hm, hy⟩
    refine ⟨(-m - 1).toNat, ?_⟩
    rw [segment_symm]
    convert hy using 3 <;> push_cast <;> omega

/-- **Trace of the open chain.** On `(0, 1)` the parametrisation traces exactly the union of the segments. -/
theorem image_Ioo (hf : IsBiinfiniteChainParam u a b f) :
    f '' Ioo 0 1 = ⋃ n : ℤ, segment ℝ (u n) (u (n + 1)) := by
  have hsplit : f '' Ioo 0 1 =
      (fun s => f ((1 - s) / 2)) '' Ico 0 1 ∪ (fun s => f ((1 + s) / 2)) '' Ico 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases eq_or_eq f t with ⟨h, he⟩ | ⟨h, he⟩
      · exact Or.inl ⟨1 - 2 * t, ⟨by linarith, by linarith [ht.1]⟩, he.symm⟩
      · exact Or.inr ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, he.symm⟩
    · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨(1 - s) / 2, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
      · exact ⟨(1 + s) / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
  rw [hsplit, hf.1.image_Ico, hf.2.image_Ico, iUnion_segment_neg]
  ext y
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (⟨m, -, hy⟩ | ⟨n, hy⟩)
    · exact ⟨m, hy⟩
    · exact ⟨n, by exact_mod_cast hy⟩
  · rintro ⟨m, hy⟩
    rcases lt_or_ge m 0 with hm | hm
    · exact Or.inl ⟨m, hm, hy⟩
    · refine Or.inr ⟨m.toNat, ?_⟩
      have hm' : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
      push_cast
      rw [hm']
      exact hy

/-- **Trace of the closed chain.** -/
theorem image_Icc (hf : IsBiinfiniteChainParam u a b f) :
    f '' Icc 0 1 = insert a (insert b (⋃ n : ℤ, segment ℝ (u n) (u (n + 1)))) := by
  rw [← Ico_insert_right (zero_le_one' ℝ), ← Ioo_insert_left (zero_lt_one' ℝ), image_insert_eq,
    image_insert_eq, hf.image_Ioo, hf.apply_zero, hf.apply_one, insert_comm]

/-- **Injectivity for simple chains.** If consecutive vertices are distinct, consecutive segments meet only in
their common vertex, segments two or more apart are disjoint, `a` and `b` lie on no segment and `a ≠ b`, then the
parametrisation is injective on `[0, 1]`. -/
theorem injOn (hf : IsBiinfiniteChainParam u a b f) (hne : ∀ n, u n ≠ u (n + 1))
    (hadj : ∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)})
    (hfar : ∀ n m : ℤ, n + 2 ≤ m → Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1))))
    (haγ : ∀ n, a ∉ segment ℝ (u n) (u (n + 1))) (hbγ : ∀ n, b ∉ segment ℝ (u n) (u (n + 1)))
    (hab : a ≠ b) : InjOn f (Icc 0 1) := by
  have hsegm : ∀ n : ℕ, segment ℝ (u (-(n : ℤ))) (u (-((n + 1 : ℕ) : ℤ))) =
      segment ℝ (u (-(n : ℤ) - 1)) (u (-(n : ℤ) - 1 + 1)) := by
    intro n
    rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by push_cast; ring,
      show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring, segment_symm]
  have hinjm : InjOn (fun s => f ((1 - s) / 2)) (Icc 0 1) := by
    refine hf.1.injOn (fun n => ?_) (fun n => ?_) (fun n m hnm => ?_) (fun n => ?_)
    · show u (-(n : ℤ)) ≠ u (-((n + 1 : ℕ) : ℤ))
      have h := hne (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at h
      rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by push_cast; ring]
      exact h.symm
    · show segment ℝ (u (-(n : ℤ))) (u (-((n + 1 : ℕ) : ℤ))) ∩
          segment ℝ (u (-((n + 1 : ℕ) : ℤ))) (u (-((n + 2 : ℕ) : ℤ))) ⊆ {u (-((n + 1 : ℕ) : ℤ))}
      have h := hadj (-(n : ℤ) - 2)
      rw [show -(n : ℤ) - 2 + 1 = -(n : ℤ) - 1 by ring, show -(n : ℤ) - 2 + 2 = -(n : ℤ) by ring] at h
      rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by push_cast; ring,
        show -((n + 2 : ℕ) : ℤ) = -(n : ℤ) - 2 by push_cast; ring, inter_comm,
        segment_symm ℝ (u (-(n : ℤ) - 1)), segment_symm ℝ (u (-(n : ℤ)))]
      exact h
    · show Disjoint (segment ℝ (u (-(n : ℤ))) (u (-((n + 1 : ℕ) : ℤ))))
        (segment ℝ (u (-(m : ℤ))) (u (-((m + 1 : ℕ) : ℤ))))
      rw [hsegm n, hsegm m]
      exact (hfar (-(m : ℤ) - 1) (-(n : ℤ) - 1) (by omega)).symm
    · show a ∉ segment ℝ (u (-(n : ℤ))) (u (-((n + 1 : ℕ) : ℤ)))
      rw [hsegm n]
      exact haγ _
  have hinjp : InjOn (fun s => f ((1 + s) / 2)) (Icc 0 1) := by
    refine hf.2.injOn (fun n => ?_) (fun n => ?_) (fun n m hnm => ?_) (fun n => ?_)
    · show u (n : ℤ) ≠ u ((n + 1 : ℕ) : ℤ)
      push_cast
      exact hne n
    · show segment ℝ (u (n : ℤ)) (u ((n + 1 : ℕ) : ℤ)) ∩ segment ℝ (u ((n + 1 : ℕ) : ℤ)) (u ((n + 2 : ℕ) : ℤ)) ⊆
        {u ((n + 1 : ℕ) : ℤ)}
      push_cast
      exact hadj n
    · show Disjoint (segment ℝ (u (n : ℤ)) (u ((n + 1 : ℕ) : ℤ))) (segment ℝ (u (m : ℤ)) (u ((m + 1 : ℕ) : ℤ)))
      push_cast
      exact hfar n m (by omega)
    · show b ∉ segment ℝ (u (n : ℤ)) (u ((n + 1 : ℕ) : ℤ))
      push_cast
      exact hbγ n
  have hhalf : f (1 / 2) = u 0 := by
    simpa only [sub_zero, Nat.cast_zero, neg_zero] using hf.1.apply_zero
  -- a point on a segment of each ray is the common vertex `u 0`
  have hcross : ∀ m₁ m₂ : ℤ, m₁ < 0 → 0 ≤ m₂ → ∀ p, p ∈ segment ℝ (u m₁) (u (m₁ + 1)) →
      p ∈ segment ℝ (u m₂) (u (m₂ + 1)) → p = u 0 := by
    intro m₁ m₂ hm₁ hm₂ p hp₁ hp₂
    by_cases hfar' : m₁ + 2 ≤ m₂
    · exact absurd hp₂ (disjoint_left.1 (hfar _ _ hfar') hp₁)
    · obtain rfl : m₁ = -1 := by omega
      obtain rfl : m₂ = 0 := by omega
      have h := hadj (-1)
      have e1 : (-1 : ℤ) + 1 = 0 := by norm_num
      have e2 : (-1 : ℤ) + 2 = 0 + 1 := by norm_num
      rw [e1, e2] at h
      rw [e1] at hp₁
      exact h ⟨hp₁, hp₂⟩
  have hmix : ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, f ((1 - s₁) / 2) = f ((1 + s₂) / 2) →
      s₁ = 0 ∧ s₂ = 0 := by
    intro s₁ hs₁ s₂ hs₂ h
    have hp : f ((1 - s₁) / 2) = u 0 := by
      rcases hs₁.2.lt_or_eq with hs₁' | rfl
      · obtain ⟨n, hn⟩ := hf.1.exists_mem_segment ⟨hs₁.1, hs₁'⟩
        have hn1 : f ((1 - s₁) / 2) ∈ segment ℝ (u (-(n : ℤ))) (u (-((n + 1 : ℕ) : ℤ))) := hn
        rw [hsegm n] at hn1
        rcases hs₂.2.lt_or_eq with hs₂' | rfl
        · obtain ⟨n', hn'⟩ := hf.2.exists_mem_segment ⟨hs₂.1, hs₂'⟩
          have hn2 : f ((1 + s₂) / 2) ∈ segment ℝ (u (n' : ℤ)) (u ((n' : ℤ) + 1)) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hn'
          rw [← h] at hn2
          exact hcross _ _ (by omega) (by omega) _ hn1 hn2
        · have hb1 : f ((1 + 1) / 2) = b := hf.2.1
          rw [h, hb1] at hn1
          exact absurd hn1 (hbγ _)
      · have ha1 : f ((1 - 1) / 2) = a := hf.1.1
        rcases hs₂.2.lt_or_eq with hs₂' | rfl
        · obtain ⟨n', hn'⟩ := hf.2.exists_mem_segment ⟨hs₂.1, hs₂'⟩
          have hn2 : f ((1 + s₂) / 2) ∈ segment ℝ (u (n' : ℤ)) (u ((n' : ℤ) + 1)) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hn'
          rw [← h, ha1] at hn2
          exact absurd hn2 (haγ _)
        · exact absurd (ha1.symm.trans (h.trans hf.2.1)) hab
    refine ⟨hinjm hs₁ ⟨le_rfl, zero_le_one⟩ ?_, hinjp hs₂ ⟨le_rfl, zero_le_one⟩ ?_⟩
    · show f ((1 - s₁) / 2) = f ((1 - 0) / 2)
      rw [hp, sub_zero, hhalf]
    · show f ((1 + s₂) / 2) = f ((1 + 0) / 2)
      rw [← h, hp, add_zero, hhalf]
  intro t₁ ht₁ t₂ ht₂ h
  rcases eq_or_eq f t₁ with ⟨h₁, e₁⟩ | ⟨h₁, e₁⟩ <;> rcases eq_or_eq f t₂ with ⟨h₂, e₂⟩ | ⟨h₂, e₂⟩
  · have := hinjm ⟨by linarith, by linarith [ht₁.1]⟩ ⟨by linarith, by linarith [ht₂.1]⟩
      (e₁.symm.trans (h.trans e₂))
    linarith
  · obtain ⟨h0, h0'⟩ := hmix _ ⟨by linarith, by linarith [ht₁.1]⟩ _ ⟨by linarith, by linarith [ht₂.2]⟩
      (e₁.symm.trans (h.trans e₂))
    linarith
  · obtain ⟨h0, h0'⟩ := hmix _ ⟨by linarith, by linarith [ht₂.1]⟩ _ ⟨by linarith, by linarith [ht₁.2]⟩
      (e₂.symm.trans (h.symm.trans e₁))
    linarith
  · have := hinjp ⟨by linarith, by linarith [ht₁.2]⟩ ⟨by linarith, by linarith [ht₂.2]⟩
      (e₁.symm.trans (h.trans e₂))
    linarith

end IsBiinfiniteChainParam

end LatticeProb.Topology
