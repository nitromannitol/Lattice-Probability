import LatticeProb.Prob.Strassen.MarginalWeights

/-!
# D. The discrete coupling on the full space

`ext F ω` extends a pattern `ω : F → Bool` to `S → Bool` by `false` off `F`; it is order-preserving
and its restriction to `F` recovers `ω`, so cylinder membership only sees `F`-coordinates and the
mass of a cylinder event is a sum of pattern weights (`measure_cylinder_toReal_eq_sum_wt`). Given
a transport plan `k : (F → Bool) → (F → Bool) → ℕ` with total mass `D`, `cplMeasure F D k` places
mass `k y x / D` at `(ext F x, ext F y)`: it is a probability measure when `k` sums to `D`
(`isProbabilityMeasure_cplMeasure_of_sum_eq`), supported on `couplingSupport S` when `k`'s support
lies in `{(y, x) | y ≤ x}` (`cplMeasure_compl_couplingSupport_eq_zero`), and its marginals on a
measurable set `A` are column and row sums of `k` over the patterns landing in `A`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- Extend a pattern on `F` by `false`. -/
noncomputable def ext {S : Type} (F : Finset S) (ω : F → Bool) : S → Bool :=
  fun s => if h : s ∈ F then ω ⟨s, h⟩ else false

/-- Restricting the zero-extension of a pattern recovers the pattern. -/
private theorem restrict_ext_eq {S : Type} (F : Finset S) (ω : F → Bool) : F.restrict (ext F ω) = ω
    := by
  funext i
  simp [Finset.restrict, ext, i.2]


/-- Extending by `false` preserves the pointwise order: `ω ≤ ω'` gives `ext F ω ≤ ext F ω'`. -/
private theorem forall_apply_ext_true_imp_of_le {S : Type} (F : Finset S) (ω ω' : F → Bool)
    (h : ω ≤ ω') :
    ∀ s, ext F ω s = true → ext F ω' s = true := by
  intro s hs
  have hle : ∀ t, ω t ≤ ω' t := (Pi.le_def.mp h)
  rw [ext] at hs ⊢
  by_cases hF : s ∈ F
  · rw [dif_pos hF] at hs ⊢
    exact (Bool.le_iff_imp.mp (hle ⟨s, hF⟩)) hs
  · rw [dif_neg hF] at hs
    exact absurd hs (by simp)


/-- Membership in a cylinder over `G ⊆ F` only sees the `F`-coordinates: `ω ∈ cylinder G T ↔ ext F
(F.restrict ω) ∈ cylinder G T`. -/
private theorem mem_cylinder_iff_ext_restrict_mem {S : Type} (F G : Finset S) (hGF : G ⊆ F)
    (T : Set (G → Bool))
    (ω : S → Bool) : ω ∈ cylinder G T ↔ ext F (F.restrict ω) ∈ cylinder G T := by
  have h : G.restrict (ext F (F.restrict ω)) = G.restrict ω := funext fun i => by
    simp only [StrassenAux.ext, Finset.restrict_def]
    exact dif_pos (hGF i.2)
  simp only [cylinder, Set.mem_preimage, h]


/-- The real mass of a cylinder event is a sum of pattern weights over the patterns on `F` extending
into it. -/
theorem measure_cylinder_toReal_eq_sum_wt {S : Type} (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ]
    (F G : Finset S) (hGF : G ⊆ F) (T : Set (G → Bool)) :
    (μ (cylinder G T)).toReal
      = ∑ x ∈ Finset.univ.filter (fun x : F → Bool => ext F x ∈ cylinder G T), wt μ F x := by
  have h26 := sum_wt_eq_measure_preimage_restrict_toReal μ F
      (Finset.univ.filter (fun x : F → Bool => ext F x ∈ cylinder G T))
  rw [h26]
  apply congrArg (fun s => (μ s).toReal)
  apply Set.ext
  intro ω
  simp only [MeasureTheory.cylinder, Set.mem_preimage, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact mem_cylinder_iff_ext_restrict_mem F G hGF T ω


/-- The discrete coupling: mass `k y x / D` at `(ext x, ext y)` (first coordinate = large law). -/
noncomputable def cplMeasure {S : Type} (F : Finset S) (D : ℕ) (k : (F → Bool) → (F → Bool) → ℕ) :
    Measure ((S → Bool) × (S → Bool)) :=
  ∑ y, ∑ x, ((k y x : ENNReal) / D) • Measure.dirac (ext F x, ext F y)

/-- The discrete coupling `cplMeasure F D k` has total mass `∑_y ∑_x k y x / D`. -/
private theorem cplMeasure_univ_eq_sum_div {S : Type} (F : Finset S) (D : ℕ)
    (k : (F → Bool) → (F → Bool) → ℕ) :
    cplMeasure F D k Set.univ = ∑ y, ∑ x, (k y x : ENNReal) / D := by
  simp only [cplMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]

/-- `∑_y ∑_x (k y x : ENNReal) / D = (∑_y ∑_x k y x : ENNReal) / D`. -/
private theorem sum_div_eq_cast_sum_div {ι κ : Type} [Fintype ι] [Fintype κ] (k : ι → κ → ℕ)
    (D : ℕ) :
    ∑ y, ∑ x, (k y x : ENNReal) / D = ((∑ y, ∑ x, k y x : ℕ) : ENNReal) / D := by
  simp only [ENNReal.div_eq_inv_mul, ← Finset.mul_sum, ← Nat.cast_sum]

/-- If the transport plan `k` has total mass `D`, then `cplMeasure F D k` is a probability measure.
-/
theorem isProbabilityMeasure_cplMeasure_of_sum_eq {S : Type} (F : Finset S) (D : ℕ)
    (hD : D ≠ 0)
    (k : (F → Bool) → (F → Bool) → ℕ) (hk : ∑ y, ∑ x, k y x = D) :
    IsProbabilityMeasure (cplMeasure F D k) := by
  constructor
  rw [cplMeasure_univ_eq_sum_div, sum_div_eq_cast_sum_div, hk]
  exact ENNReal.div_self (Nat.cast_ne_zero.mpr hD) (ENNReal.natCast_ne_top D)

/-- If `k`'s support lies in `{(y, x) | y ≤ x}`, then `cplMeasure F D k` puts no mass off
`couplingSupport S`. -/
theorem cplMeasure_compl_couplingSupport_eq_zero {S : Type} [Countable S] (F : Finset S)
    (D : ℕ) (k : (F → Bool) → (F → Bool) → ℕ)
    (hk : ∀ y x, k y x ≠ 0 → y ≤ x) : cplMeasure F D k (couplingSupport S)ᶜ = 0 := by
  rw [cplMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x _ => ?_
  by_cases hkxy : k y x = 0
  · simp [hkxy]
  · have hle : y ≤ x := hk y x hkxy
    have hmem : (ext F x, ext F y) ∈ couplingSupport S := by
      intro s hs
      simp only [ext] at hs ⊢
      by_cases hF : s ∈ F
      · rw [dif_pos hF] at hs ⊢
        exact Bool.le_iff_imp.mp (Pi.le_def.mp hle ⟨s, hF⟩) hs
      · rw [dif_neg hF] at hs
        exact absurd hs (by simp)
    simp [Set.mem_compl_iff, hmem]

/-- The first marginal of `cplMeasure F D k` on a measurable set `A` is a sum of column sums of `k`
over patterns landing in `A`, divided by `D`. -/
theorem cplMeasure_prod_univ_eq_sum_div {S : Type} (F : Finset S) (D : ℕ)
    (k : (F → Bool) → (F → Bool) → ℕ)
    (A : Set (S → Bool)) (hA : MeasurableSet A) :
    cplMeasure F D k (A ×ˢ Set.univ)
      = ∑ x ∈ Finset.univ.filter (fun x => ext F x ∈ A), ((∑ y, k y x : ℕ) : ENNReal) / D := by
  rw [cplMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hA.prod MeasurableSet.univ), Set.indicator_apply,
    Set.mem_prod, Set.mem_univ, and_true, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ext F x ∈ A
  · simp only [hx, if_true, ENNReal.div_eq_inv_mul, ← Finset.mul_sum, ← Nat.cast_sum]
  · simp only [hx, if_false, Finset.sum_const_zero]


/-- The second marginal of `cplMeasure F D k` on a measurable set `A` is a sum of row sums of `k`
over patterns landing in `A`, divided by `D`. -/
theorem cplMeasure_univ_prod_eq_sum_div {S : Type} (F : Finset S) (D : ℕ)
    (k : (F → Bool) → (F → Bool) → ℕ)
    (A : Set (S → Bool)) (hA : MeasurableSet A) :
    cplMeasure F D k (Set.univ ×ˢ A)
      = ∑ y ∈ Finset.univ.filter (fun y => ext F y ∈ A), ((∑ x, k y x : ℕ) : ENNReal) / D := by
  classical
  have hprod : MeasurableSet (Set.univ ×ˢ A : Set ((S → Bool) × (S → Bool))) :=
    MeasurableSet.univ.prod hA
  have hterm : ∀ (y x : F → Bool),
      (((k y x : ENNReal) / D) • Measure.dirac (ext F x, ext F y)) (Set.univ ×ˢ A)
        = (if ext F y ∈ A then ((k y x : ENNReal) / D) else 0) := fun y x => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hprod, Set.indicator_apply]
    by_cases hy : ext F y ∈ A
    · simp [hy, Set.mem_prod]
    · simp [hy]
  unfold cplMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Measure.coe_finsetSum, Finset.sum_apply, hterm]
  split_ifs with hy
  · simp only [ENNReal.div_eq_inv_mul]
    rw [← Finset.mul_sum, ← Nat.cast_sum]
  · simp

end StrassenAux

end LatticeProb
