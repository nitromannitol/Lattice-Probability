/-
# The coordinate carrier map between `ℤ × ℤ` and `Site 2`, and its transports

The planar carrier `ℤ × ℤ` and the two-dimensional lattice carrier `Fin 2 → ℤ` are the same set
of coordinates under the standard identification `p ↦ ![p.1, p.2]`.  This module records that
identification and transports the thin-form bridge data across it: the finite-range dependence
predicate `KDependent` at range `2` and the one-site probability of a field.  It is the carrier
lemma that connects the planar instantiation of the complement bridge to the `Site d`
formulation of the bridge.

The domination half is never touched; no `Prop` is frozen, no cited statement is assumed, and
nothing is claimed about `Rotor.External.LSS`.
-/

import LatticeProb.Prob.Percolation.LSSThinInstantiation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-! ### The coordinate identification -/

/-- The planar pair `(a, b)` read as the two-coordinate site `![a, b]`. -/
def toSite2 (p : PlanarCarrier) : LatticeProb.Site 2 := ![p.1, p.2]

/-- The two-coordinate site read as the planar pair of its two coordinates. -/
def ofSite2 (z : LatticeProb.Site 2) : PlanarCarrier := (z 0, z 1)

theorem ofSite2_toSite2 (p : PlanarCarrier) : ofSite2 (toSite2 p) = p := by
  ext <;> simp [ofSite2, toSite2]

theorem toSite2_ofSite2 (z : LatticeProb.Site 2) : toSite2 (ofSite2 z) = z := by
  funext i
  fin_cases i <;> simp [ofSite2, toSite2]

/-- The coordinate equivalence between the planar carrier and the two-dimensional lattice
carrier. -/
def planarSiteEquiv : PlanarCarrier ≃ LatticeProb.Site 2 where
  toFun := toSite2
  invFun := ofSite2
  left_inv := ofSite2_toSite2
  right_inv := toSite2_ofSite2

/-- The induced bijection on `{0,1}`-fields, by reading a planar field at the site coordinates. -/
def fieldEquivPlanar : (PlanarCarrier → Bool) ≃ (LatticeProb.Site 2 → Bool) where
  toFun ω z := ω (ofSite2 z)
  invFun η p := η (toSite2 p)
  left_inv ω := by funext p; simp [ofSite2_toSite2]
  right_inv η := by funext z; simp [toSite2_ofSite2]

theorem fieldEquivPlanar_toFun_apply (ω : PlanarCarrier → Bool) (z : LatticeProb.Site 2) :
    fieldEquivPlanar.toFun ω z = ω (ofSite2 z) :=
  rfl

theorem measurable_toSite2Field : Measurable fieldEquivPlanar.toFun := by
  refine measurable_pi_lambda _ fun z => ?_
  exact measurable_pi_apply (ofSite2 z)

theorem measurable_ofSite2Field : Measurable fieldEquivPlanar.invFun := by
  refine measurable_pi_lambda _ fun p => ?_
  exact measurable_pi_apply (toSite2 p)

/-! ### The finite-range dependence correspondence -/

/-- The planar `ℓ^∞` dependence range at `Fin 2` is the "separated in one coordinate" range of
the lattice statement. -/
theorem site2_max_lt_iff {a b : LatticeProb.Site 2} {k : ℕ} :
    (k : ℤ) < max |a 0 - b 0| |a 1 - b 1| ↔ ∃ l : Fin 2, (k : ℤ) < |a l - b l| := by
  constructor
  · intro h
    rcases lt_max_iff.mp h with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  · rintro ⟨l, hl⟩
    fin_cases l
    · exact lt_of_lt_of_le hl (le_max_left _ _)
    · exact lt_of_lt_of_le hl (le_max_right _ _)

/-! ### One-site transport -/

/-- The one-site probability of a planar field is read at the corresponding site. -/
theorem fieldEquivPlanar_oneSite (μ : Measure (PlanarCarrier → Bool))
    (z : LatticeProb.Site 2) :
    (μ.map fieldEquivPlanar.toFun) {η | η z = true} =
      μ {ω | ω (ofSite2 z) = true} := by
  have hs : MeasurableSet {η : LatticeProb.Site 2 → Bool | η z = true} := by
    have h : {η : LatticeProb.Site 2 → Bool | η z = true} =
        (fun f : LatticeProb.Site 2 → Bool => f z) ⁻¹' ({true} : Set Bool) := by
      ext η; simp
    rw [h]
    exact (measurable_pi_apply z) (measurableSet_singleton true)
  rw [Measure.map_apply measurable_toSite2Field hs]
  rfl

/-! ### Transport of `KDependent` across the coordinate identification -/

theorem measurable_imageRestrict (I : Finset (LatticeProb.Site 2)) :
    Measurable (fun f : (I.image ofSite2 → Bool) => fun a : I =>
      f ⟨ofSite2 a, Finset.mem_image.mpr ⟨a, a.2, rfl⟩⟩) :=
  measurable_pi_lambda _ fun a =>
    measurable_pi_apply
      (⟨ofSite2 a, Finset.mem_image.mpr ⟨a, a.2, rfl⟩⟩ : ↥(I.image ofSite2))

/-- **Finite-range dependence transports across the coordinate identification.**  A planar field
that is `k`-dependent for the `ℓ^∞` range is `k`-dependent as a `Fin 2`-indexed lattice field. -/
theorem kDependentPlanar_map_fieldEquivPlanar (k : ℕ) {μ : Measure (PlanarCarrier → Bool)}
    [IsFiniteMeasure μ] (h : KDependentPlanar k μ) :
    KDependent k (μ.map fieldEquivPlanar.toFun) := by
  intro I J hfar
  have hfar' : ∀ p ∈ I.image ofSite2, ∀ q ∈ J.image ofSite2,
      (k : ℤ) < max |p.1 - q.1| |p.2 - q.2| := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    simpa [ofSite2] using
      (site2_max_lt_iff (a := a) (b := b) (k := k)).mpr (hfar a ha b hb)
  have hKDp := h (I.image ofSite2) (J.image ofSite2) hfar'
  refine (indepFun_map_iff_of_measurable (T := fieldEquivPlanar.toFun)
    measurable_toSite2Field (measurable_finsetRestrict (d := 2) I)
    (measurable_finsetRestrict (d := 2) J) μ).mpr ?_
  have hcomp := hKDp.comp (measurable_imageRestrict I) (measurable_imageRestrict J)
  have hI : ((fun ω : LatticeProb.Site 2 → Bool => fun i : I => ω i) ∘ fieldEquivPlanar.toFun)
      = ((fun f : (I.image ofSite2 → Bool) => fun a : I =>
            f ⟨ofSite2 a, Finset.mem_image.mpr ⟨a, a.2, rfl⟩⟩) ∘
          (fun ω : PlanarCarrier → Bool => fun p : I.image ofSite2 => ω p)) := by
    funext ω a; rfl
  have hJ : ((fun ω : LatticeProb.Site 2 → Bool => fun j : J => ω j) ∘ fieldEquivPlanar.toFun)
      = ((fun f : (J.image ofSite2 → Bool) => fun b : J =>
            f ⟨ofSite2 b, Finset.mem_image.mpr ⟨b, b.2, rfl⟩⟩) ∘
          (fun ω : PlanarCarrier → Bool => fun q : J.image ofSite2 => ω q)) := by
    funext ω b; rfl
  rw [hI, hJ]
  exact hcomp

end LatticeProb.Percolation
