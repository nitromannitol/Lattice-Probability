import LatticeProb.Topology.FirstExitBallArea

/-! # Rooted first-exit traces under increasing time changes -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace LatticeProb

/-- An increasing bijection fixing the root preserves both rooted exit traces,
including when an exit set is empty. -/
theorem rooted_exit_traces_comp_orderIso {X : Type*} (f : ℝ → X) (U : Set X)
    (e : ℝ ≃o ℝ) (he : e 0 = 0) :
    ((f ∘ e) '' Icc (sSup {t : ℝ | t ≤ 0 ∧ (f ∘ e) t ∉ U}) 0 =
      f '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f t ∉ U}) 0) ∧
    ((f ∘ e) '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ (f ∘ e) t ∉ U}) =
      f '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f t ∉ U})) := by
  let A : Set ℝ := {t | t ≤ 0 ∧ (f ∘ e) t ∉ U}
  let B : Set ℝ := {t | 0 ≤ t ∧ (f ∘ e) t ∉ U}
  have hA : e '' A = {t : ℝ | t ≤ 0 ∧ f t ∉ U} := by
    ext t
    constructor
    · rintro ⟨s, ⟨hs, hf⟩, rfl⟩
      exact ⟨by simpa only [he] using e.monotone hs, hf⟩
    · rintro ⟨ht, hf⟩
      refine ⟨e.symm t, ⟨?_, ?_⟩, e.apply_symm_apply t⟩
      · apply e.le_iff_le.mp
        simpa only [e.apply_symm_apply, he] using ht
      · simpa only [Function.comp_apply, e.apply_symm_apply] using hf
  have hB : e '' B = {t : ℝ | 0 ≤ t ∧ f t ∉ U} := by
    ext t
    constructor
    · rintro ⟨s, ⟨hs, hf⟩, rfl⟩
      exact ⟨by simpa only [he] using e.monotone hs, hf⟩
    · rintro ⟨ht, hf⟩
      refine ⟨e.symm t, ⟨?_, ?_⟩, e.apply_symm_apply t⟩
      · apply e.le_iff_le.mp
        simpa only [e.apply_symm_apply, he] using ht
      · simpa only [Function.comp_apply, e.apply_symm_apply] using hf
  have hsup : e (sSup A) = sSup (e '' A) := by
    by_cases h : A.Nonempty
    · exact e.map_csSup' h ⟨0, fun _ ht => ht.1⟩
    · have hz : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp only [hz, Set.image_empty, Real.sSup_empty, he]
  have hinf : e (sInf B) = sInf (e '' B) := by
    by_cases h : B.Nonempty
    · exact e.map_csInf' h ⟨0, fun _ ht => ht.1⟩
    · have hz : B = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp only [hz, Set.image_empty, Real.sInf_empty, he]
  constructor
  · change (f ∘ e) '' Icc (sSup A) 0 = _
    rw [Set.image_comp, e.image_Icc, hsup, hA, he]
  · change (f ∘ e) '' Icc 0 (sInf B) = _
    rw [Set.image_comp, e.image_Icc, hinf, hB, he]

/-- A first-exit area bound for a curve transfers to its rooted increasing
reparametrization. -/
theorem first_exit_trace_area_comp_orderIso
    {β : Type*} (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (ω : β)
    (η : ℝ → ℂ) (hη : ∀ t, f ω t = Complex.orthonormalBasisOneI.repr (η t))
    (e : ℝ ≃o ℝ) (he : e 0 = 0) {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hgood : ω ∉ firstExitBallFailure f ε k) :
    ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / (4 / (Real.pi * ε ^ 2))) ≤
      min (volume ((η ∘ e) '' Icc
        (sSup {t : ℝ | t ≤ 0 ∧ (η ∘ e) t ∉ ball 0 (Real.exp k)}) 0))
        (volume ((η ∘ e) '' Icc 0
          (sInf {t : ℝ | 0 ≤ t ∧ (η ∘ e) t ∉ ball 0 (Real.exp k)}))) := by
  obtain ⟨hl, hr⟩ := rooted_exit_traces_comp_orderIso η (ball 0 (Real.exp k)) e he
  rw [hl, hr]
  exact first_exit_trace_area_of_not_mem_firstExitBallFailure f ω η hη hε k hgood

end LatticeProb
