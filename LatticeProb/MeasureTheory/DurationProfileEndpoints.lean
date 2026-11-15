import LatticeProb.MeasureTheory.BoundedAEProfileRun
import LatticeProb.MeasureTheory.FiniteAbsorbedIntervalCover
import LatticeProb.MeasureTheory.FiniteIntervalTilingEndpoints

/-! # Endpoints determined by almost-everywhere duration profiles -/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace LatticeProb

/-- Two interval families with almost-everywhere equal duration profiles have the
same endpoints at a common interior point. -/
theorem duration_profile_endpoint_unique
    {ι κ : Type*} (a u b : ℝ)
    (A B : ι → ℝ) (C D : κ → ℝ) (f g : ℝ → ℝ)
    (hAB : ∀ i, a ≤ A i ∧ A i < B i ∧ B i ≤ b)
    (hCD : ∀ j, a ≤ C j ∧ C j < D j ∧ D j ≤ b)
    (hdisAB : Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j)))
    (hdisCD : Pairwise fun i j => Disjoint (Ioo (C i) (D i)) (Ioo (C j) (D j)))
    (hcoverAB : volume (Ioo a b \ ⋃ i, Ioo (A i) (B i)) = 0)
    (hcoverCD : volume (Ioo a b \ ⋃ j, Ioo (C j) (D j)) = 0)
    (hprofileAB : ∀ i, ∀ᵐ t ∂(volume.restrict (Ioo (A i) (B i))), f t = B i - A i)
    (hprofileCD : ∀ j, ∀ᵐ t ∂(volume.restrict (Ioo (C j) (D j))), g t = D j - C j)
    (hfg : ∀ᵐ t ∂(volume.restrict (Ioo a b)), f t = g t)
    (i : ι) (j : κ) (hi : u ∈ Ioo (A i) (B i)) (hj : u ∈ Ioo (C j) (D j)) :
    A i = C j ∧ B i = D j := by
  have hsubAB : ∀ k, Ioo (A k) (B k) ⊆ Ioo a b := fun k =>
    Ioo_subset_Ioo (hAB k).1 (hAB k).2.2
  have hsubCD : ∀ k, Ioo (C k) (D k) ⊆ Ioo a b := fun k =>
    Ioo_subset_Ioo (hCD k).1 (hCD k).2.2
  have hprofileCD' : ∀ k, ∀ᵐ t ∂(volume.restrict (Ioo (C k) (D k))),
      f t = D k - C k := by
    intro k
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsubCD k) hfg,
      hprofileCD k] with t h₁ h₂
    exact h₁.trans h₂
  obtain ⟨l, r, hal, hlu, hur, hrb, _, hmax⟩ :=
    exists_bounded_ae_profile_run f (B i - A i) a b u
      ⟨Ioo (A i) (B i), isOpen_Ioo, hi, hsubAB i, hprofileAB i⟩
  have habsAB : ∀ k, (Ioo l r ∩ Ioo (A k) (B k)).Nonempty →
      Ioo (A k) (B k) ⊆ Ioo l r ∧ B k - A k = B i - A i := by
    intro k hk
    obtain ⟨heq, hsub⟩ := hmax (A k) (B k) (hsubAB k) hk _ (hprofileAB k)
    exact ⟨hsub, heq⟩
  have habsCD : ∀ k, (Ioo l r ∩ Ioo (C k) (D k)).Nonempty →
      Ioo (C k) (D k) ⊆ Ioo l r ∧ D k - C k = B i - A i := by
    intro k hk
    obtain ⟨heq, hsub⟩ := hmax (C k) (D k) (hsubCD k) hk _ (hprofileCD' k)
    exact ⟨hsub, heq⟩
  let S : Set ι := {k | (Ioo l r ∩ Ioo (A k) (B k)).Nonempty}
  let T : Set κ := {k | (Ioo l r ∩ Ioo (C k) (D k)).Nonempty}
  have hℓ : 0 < B i - A i := sub_pos.mpr (hAB i).2.1
  obtain ⟨hSf, hSb, _, hSc⟩ := finite_cover_of_absorbed_intervals a b l r
    (B i - A i) A B hal (lt_trans hlu hur) hrb hℓ (fun k => (hAB k).2.1)
    hdisAB hcoverAB habsAB
  obtain ⟨hTf, hTb, _, hTc⟩ := finite_cover_of_absorbed_intervals a b l r
    (B i - A i) C D hal (lt_trans hlu hur) hrb hℓ (fun k => (hCD k).2.1)
    hdisCD hcoverCD habsCD
  let : Finite S := hSf.to_subtype
  let : Finite T := hTf.to_subtype
  have hiS : i ∈ S := ⟨u, ⟨hlu, hur⟩, hi⟩
  have hjT : j ∈ T := ⟨u, ⟨hlu, hur⟩, hj⟩
  exact interval_endpoints_eq_of_common_interior_point l r (B i - A i)
    (fun k : S => A k) (fun k : S => B k) (fun k : T => C k) (fun k : T => D k)
    hℓ (fun k => (hSb k k.property).1) (fun k => (hTb k k.property).1)
    (fun k => (hSb k k.property).2.2) (fun k => (hTb k k.property).2.2)
    (fun k m hkm => hdisAB (fun h => hkm (Subtype.ext h)))
    (fun k m hkm => hdisCD (fun h => hkm (Subtype.ext h)))
    hSc hTc ⟨i, hiS⟩ ⟨j, hjT⟩ (hSb i hiS).2.1 (hTb j hjT).2.1 u hi hj

end LatticeProb
