import Mathlib

/-! # Endpoint minima on moving intervals -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A continuous path attaining its minimum at the right endpoint of a
nonempty closed interval is a closed condition jointly in the path and endpoints. -/
theorem isClosed_moving_endpoint_minimum :
    IsClosed {p : (C(ℝ, ℝ) × ℝ) × ℝ |
      p.1.2 ≤ p.2 ∧ ∀ v ∈ Icc p.1.2 p.2, p.1.1 p.2 ≤ p.1.1 v} := by
  let A : Set ((C(ℝ, ℝ) × ℝ) × ℝ) :=
    {p | p.1.2 ≤ p.2 ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      p.1.1 p.2 ≤ p.1.1 (p.1.2 + s * (p.2 - p.1.2))}
  have hA : IsClosed A := by
    change IsClosed ({p : (C(ℝ, ℝ) × ℝ) × ℝ | p.1.2 ≤ p.2} ∩
      {p : (C(ℝ, ℝ) × ℝ) × ℝ | ∀ s ∈ Icc (0 : ℝ) 1,
        p.1.1 p.2 ≤ p.1.1 (p.1.2 + s * (p.2 - p.1.2))})
    apply IsClosed.inter (isClosed_le
      (show Continuous (fun p : (C(ℝ, ℝ) × ℝ) × ℝ => p.1.2) by fun_prop)
      (show Continuous (fun p : (C(ℝ, ℝ) × ℝ) × ℝ => p.2) by fun_prop))
    simp only [ofPred_forall]
    refine isClosed_iInter fun (s : ℝ) => isClosed_iInter fun (_ : s ∈ Icc (0 : ℝ) 1) => ?_
    apply isClosed_le
    · exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    · exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
        (show Continuous (fun p : (C(ℝ, ℝ) × ℝ) × ℝ =>
          p.1.2 + s * (p.2 - p.1.2)) by fun_prop))
  have heq : A = {p : (C(ℝ, ℝ) × ℝ) × ℝ |
      p.1.2 ≤ p.2 ∧ ∀ v ∈ Icc p.1.2 p.2, p.1.1 p.2 ≤ p.1.1 v} := by
    ext p
    have himg (h : p.1.2 ≤ p.2) :
        (fun s : ℝ => p.1.2 + s * (p.2 - p.1.2)) '' Icc 0 1 = Icc p.1.2 p.2 := by
      rw [show (fun s : ℝ => p.1.2 + s * (p.2 - p.1.2)) =
            (fun s : ℝ => p.1.2 + s) ∘ (fun s : ℝ => s * (p.2 - p.1.2)) from rfl,
          image_comp, image_mul_right_Icc zero_le_one (sub_nonneg.mpr h), image_const_add_Icc]
      simp
    simp only [A, mem_ofPred_eq]
    constructor
    · rintro ⟨hab, h⟩
      refine ⟨hab, ?_⟩
      intro v hv
      obtain ⟨s, hs, rfl⟩ := ((himg hab).symm ▸ hv)
      exact h s hs
    · rintro ⟨hab, h⟩
      exact ⟨hab, fun s hs => h _ (himg hab ▸ mem_image_of_mem _ hs)⟩
  rwa [heq] at hA

/-- For two continuous paths, the common endpoint-minimum condition on an
interval with a fixed left endpoint and a strictly later right endpoint is Borel. -/
theorem measurableSet_two_endpoint_minima (a : ℝ) :
    MeasurableSet {p : (C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ |
      a < p.2 ∧ ∀ v ∈ Icc a p.2,
        p.1.1 p.2 ≤ p.1.1 v ∧ p.1.2 p.2 ≤ p.1.2 v} := by
  have h₁ : IsClosed {p : (C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ |
      a ≤ p.2 ∧ ∀ v ∈ Icc a p.2, p.1.1 p.2 ≤ p.1.1 v} :=
    isClosed_moving_endpoint_minimum.preimage
      (show Continuous (fun p : (C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ => ((p.1.1, a), p.2)) by fun_prop)
  have h₂ : IsClosed {p : (C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ |
      a ≤ p.2 ∧ ∀ v ∈ Icc a p.2, p.1.2 p.2 ≤ p.1.2 v} :=
    isClosed_moving_endpoint_minimum.preimage
      (show Continuous (fun p : (C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ => ((p.1.2, a), p.2)) by fun_prop)
  have hlt : MeasurableSet {p : (C(ℝ, ℝ) × C(ℝ, ℝ)) × ℝ | a < p.2} :=
    (isOpen_lt continuous_const continuous_snd).measurableSet
  convert hlt.inter (h₁.measurableSet.inter h₂.measurableSet) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, ⟨h.le, fun v hv => (hh v hv).1⟩, h.le, fun v hv => (hh v hv).2⟩
  · rintro ⟨h, ⟨_, h₁⟩, _, h₂⟩
    exact ⟨h, fun v hv => ⟨h₁ v hv, h₂ v hv⟩⟩

end LatticeProb
