/-
Reading finitely many coordinates of an independent family.

Every application of a concentration inequality in the papers is to a function
of the field that reads only a finite box, and the inequalities are stated for
`Measure.pi` over a finite index type.  What connects the two is that reading an
independent family along a finite injective family of indices gives exactly the
finite product of the corresponding laws.  Nothing here needs the index type to
be the lattice.
-/
import LatticeProb.IID

noncomputable section

namespace LatticeProb

open MeasureTheory

/-- **The finite-dimensional marginals of an independent family.**  Reading
`Measure.infinitePi` along a finite injective family of indices gives the finite
product of the corresponding laws. -/
theorem infinitePi_map_comp {ι α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {κ : Type*} [Fintype κ] (v : κ → ι)
    (hv : Function.Injective v) :
    (Measure.infinitePi fun _ : ι => ν).map (fun ω k => ω (v k))
      = Measure.pi fun _ : κ => ν := by
  classical
  have hmeas : Measurable (fun (ω : ι → α) (k : κ) => ω (v k)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (v k)
  refine (Measure.pi_eq (μ := fun _ : κ => ν) fun t ht => ?_).symm
  set T : ι → Set α := fun i => ⋂ k : κ, (if v k = i then t k else Set.univ) with hTdef
  have hTmeas : ∀ i, MeasurableSet (T i) := by
    intro i
    refine MeasurableSet.iInter fun k => ?_
    by_cases h : v k = i <;> simp [h, ht k]
  have hTv : ∀ k, T (v k) = t k := by
    intro k
    ext x
    simp only [hTdef, Set.mem_iInter]
    constructor
    · intro h
      simpa using h k
    · intro hx k'
      by_cases h : v k' = v k
      · rw [if_pos h]
        have hk : k' = k := hv h
        subst hk
        exact hx
      · simp [h]
  have hpre : (fun (ω : ι → α) (k : κ) => ω (v k)) ⁻¹' (Set.univ.pi t)
      = Set.pi (↑(Finset.univ.image v)) T := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    constructor
    · rintro h i ⟨k, rfl⟩
      rw [hTv k]
      exact h k
    · intro h k
      have hk := h (v k) ⟨k, rfl⟩
      rwa [hTv k] at hk
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht), hpre,
    Measure.infinitePi_pi _ (fun i _ => hTmeas i),
    Finset.prod_image (fun k _ k' _ h => hv h)]
  exact Finset.prod_congr rfl fun k _ => by rw [hTv k]

/-- The marginal of an i.i.d. field on a finite injective family of sites is the
finite product of copies of the one-site law. -/
theorem iidLaw_map_comp (d : ℕ) {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {κ : Type*} [Fintype κ] (v : κ → Site d)
    (hv : Function.Injective v) :
    (iidLaw d ν).map (fun ω k => ω (v k)) = Measure.pi fun _ : κ => ν :=
  infinitePi_map_comp ν v hv

/-- The restriction of an i.i.d. field to a finite set of sites. -/
theorem iidLaw_map_restrict (d : ℕ) {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (s : Finset (Site d)) :
    (iidLaw d ν).map s.restrict = Measure.pi fun _ : s => ν :=
  Measure.infinitePi_map_restrict _

/-- Reading a finite injective family of sites of an i.i.d. field is measure preserving onto
the finite product of copies of the one-site law. -/
theorem measurePreserving_pick (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {κ : Type*} [Fintype κ] (v : κ → Site d) (hv : Function.Injective v) :
    MeasurePreserving (fun ω : Site d → ℝ => fun k => ω (v k))
      (iidLaw d ν) (Measure.pi fun _ : κ => ν) :=
  ⟨measurable_pi_lambda _ fun k => measurable_pi_apply (v k), iidLaw_map_comp d ν v hv⟩

/-- **The integral of a function of finitely many distinct sites.**  For an i.i.d. field
and a finite injective family of sites, the integral of a function of those sites is the
integral against the finite product of copies of the one-site law. -/
theorem integral_pick (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {κ : Type*} [Fintype κ] (v : κ → Site d) (hv : Function.Injective v)
    (F : (κ → ℝ) → ℝ) (hF : Integrable F (Measure.pi fun _ : κ => ν)) :
    (∫ ω : Site d → ℝ, F (fun k => ω (v k)) ∂(iidLaw d ν))
      = ∫ x : κ → ℝ, F x ∂(Measure.pi fun _ : κ => ν) := by
  have hmp := measurePreserving_pick d ν v hv
  rw [← hmp.map_eq]
  rw [← hmp.map_eq] at hF
  exact (integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable).symm

/-- **The integral of a function of a finite set of sites.**  For an i.i.d. field and a
finite set of sites, the integral of a function of the restriction to that set is the
integral against the finite product of copies of the one-site law. -/
theorem integral_restrict (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Finset (Site d)) (F : (s → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi fun _ : s => ν)) :
    (∫ ω : Site d → ℝ, F (s.restrict ω) ∂(iidLaw d ν))
      = ∫ x : s → ℝ, F x ∂(Measure.pi fun _ : s => ν) := by
  have hmp := measurePreserving_pick d ν (fun k : s => (k : Site d))
    (fun a b h => Subtype.ext h)
  rw [← hmp.map_eq]
  rw [← hmp.map_eq] at hF
  exact (integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable).symm

end LatticeProb

end
