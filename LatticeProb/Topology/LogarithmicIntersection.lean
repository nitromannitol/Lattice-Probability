import LatticeProb.Topology.Unicoherence

/-! A logarithmic criterion for connected intersections of plane sets. -/

namespace LatticeProb.Topology

open Set Complex

/-- Closed preconnected plane sets have preconnected intersection when every continuous
nonvanishing function on their union has a continuous logarithm there. -/
theorem isPreconnected_inter_of_hasLogOn_union {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hAc : IsPreconnected A) (hBc : IsPreconnected B)
    (hlog : ∀ f : ℂ → ℂ, ContinuousOn f (A ∪ B) → (∀ z ∈ A ∪ B, f z ≠ 0) →
      ∃ F : ℂ → ℂ, ContinuousOn F (A ∪ B) ∧ ∀ z ∈ A ∪ B, exp (F z) = f z) :
    IsPreconnected (A ∩ B) := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsub hne
  by_contra hcon
  obtain ⟨hnu, hnv⟩ := not_or.1 hcon
  obtain ⟨q, hqAB, hqu⟩ := not_subset.1 hnu
  obtain ⟨p, hpAB, hpv⟩ := not_subset.1 hnv
  have hqv : q ∈ v := (hsub hqAB).resolve_left hqu
  have hpu : p ∈ u := (hsub hpAB).resolve_right hpv
  have hPQ : Disjoint (A ∩ B ∩ u) (A ∩ B ∩ v) := disjoint_left.2 fun z hzP hzQ => by
    have : z ∈ A ∩ B ∩ (u ∩ v) := ⟨hzP.1, hzP.2, hzQ.2⟩
    rw [hne] at this
    exact this
  obtain ⟨φ, hφP, hφQ, -⟩ :=
    exists_continuous_zero_one_of_isClosed ((hA.inter hB).inter hu) ((hA.inter hB).inter hv) hPQ
  have hφp : φ p = 0 := hφP ⟨hpAB, hpu⟩
  have hφq : φ q = 1 := hφQ ⟨hqAB, hqv⟩
  have hagree : ∀ z ∈ A ∩ B,
      exp (((Real.pi * φ z : ℝ) : ℂ) * I) = exp (((-(Real.pi * φ z) : ℝ) : ℂ) * I) := by
    intro z hz
    rcases hsub hz with h | h
    · rw [show φ z = 0 from hφP ⟨hz, h⟩]
      simp
    · rw [show φ z = 1 from hφQ ⟨hz, h⟩]
      simp [neg_mul, exp_neg]
  let e : ℂ → ℂ := fun z =>
    if z ∈ A then exp (((Real.pi * φ z : ℝ) : ℂ) * I) else exp (((-(Real.pi * φ z) : ℝ) : ℂ) * I)
  have hecont : ContinuousOn e (A ∪ B) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hA hB
    · refine (show ContinuousOn (fun z : ℂ => exp (((Real.pi * φ z : ℝ) : ℂ) * I)) A by
        fun_prop).congr ?_
      intro z hz
      simp [e, hz]
    · refine (show ContinuousOn (fun z : ℂ => exp (((-(Real.pi * φ z) : ℝ) : ℂ) * I)) B by
        fun_prop).congr ?_
      intro z hz
      by_cases hzA : z ∈ A
      · simpa [e, hzA] using (hagree z ⟨hzA, hz⟩)
      · simp [e, hzA]
  have he0 : ∀ z ∈ A ∪ B, e z ≠ 0 := by
    intro z hz
    simp only [e]
    split_ifs <;> exact exp_ne_zero _
  obtain ⟨F, hFc, hF⟩ := hlog e hecont he0
  have hmA : MapsTo (fun z => (F z).im - Real.pi * φ z) A (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) :=
    fun z hz => im_sub_mem_zmultiples_of_exp_eq (by rw [hF z (Or.inl hz)]; simp only [e, hz, ↓reduceIte])
  have hmB : MapsTo (fun z => (F z).im - (-(Real.pi * φ z))) B
      (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) := by
    intro z hz
    refine im_sub_mem_zmultiples_of_exp_eq ?_
    rw [hF z (Or.inr hz)]
    simp only [e]
    split_ifs with hzA
    · exact hagree z ⟨hzA, hz⟩
    · rfl
  have hT : IsDiscrete (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) :=
    SetLike.isDiscrete_iff_discreteTopology.2 inferInstance
  have hFA : ContinuousOn F A := hFc.mono subset_union_left
  have hFB : ContinuousOn F B := hFc.mono subset_union_right
  have hc1 : ContinuousOn (fun z => (F z).im - Real.pi * φ z) A := by
    exact (continuous_im.comp_continuousOn hFA).sub (by fun_prop)
  have hc2 : ContinuousOn (fun z => (F z).im - (-(Real.pi * φ z))) B := by
    exact (continuous_im.comp_continuousOn hFB).sub (by fun_prop)
  have h1 := hAc.constant_of_mapsTo hT hc1 hmA hpAB.1 hqAB.1
  have h2 := hBc.constant_of_mapsTo hT hc2 hmB hpAB.2 hqAB.2
  simp only [hφp, hφq] at h1 h2
  linarith [Real.pi_pos]


end LatticeProb.Topology
