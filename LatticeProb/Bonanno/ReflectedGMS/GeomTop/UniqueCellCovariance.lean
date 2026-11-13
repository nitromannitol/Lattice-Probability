/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.UniqueCellCovariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.Statement
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import Mathlib.Util.AssertNoSorry

/-!
# (1.10) wherever `H_u` is uniquely defined, by renormalizing a harmonic coordinate

Rule (1.10) of the geometric-topology revision (manuscript lines 177–179) asserts
`Φ_{C(H−u)}(C(H−u)) = C(Φ_H(H) − Φ_H(H_u))` "where `H_u` is uniquely defined", `H_u` being the unique
cell containing `u` when it is unique (line 122) — a point of a cell boundary lying in no other cell
included.  The reused clause `HarmonicLawIngredients.NormalizedCovariant` asserts it only where the
masked root `rootAt (decode e) u` is defined, i.e. off every cell boundary.

This file upgrades any harmonic coordinate to one satisfying `UniqueCellCovariant`, for an arbitrary
law `ν` on `Env` (nothing here depends on the geometric topology):

* `renormalizedField Φ` subtracts, in every environment, the constant `originConstant Φ e`, the value
  of `Φ` at the unique cell containing the origin when there is one (and `0` otherwise).  The constant
  is measurable because membership of the origin in a compact cell is a closed condition and the
  uniqueness is a countable intersection (`measurable_originConstant`).
* Gradients are unchanged in every environment, so gradient covariance persists, and together with
  similarity invariance of "the unique cell containing the point" it gives `UniqueCellCovariant`
  (`uniqueCellCovariant_renormalizedField`), hence also `NormalizedCovariant`.
* Almost surely the origin is off the boundary mask and `Φ` vanishes at the root; there the unique
  cell containing the origin is the root, so the constant is `0` and the two fields coincide
  (`ae_renormalizedField_at_eq`).  Every remaining clause of `IsHarmonicCoordinate`, of
  `ReflectedInvarianceConclusions` and of the process conclusions consumes the field only through
  `Φ.at e` at almost every environment, and transfers.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace ReflectedGMS.GeomTop

open Code EnvironmentLaws EnvironmentFields HarmonicLawIngredients HarmonicMainStatement
open InvarianceMainStatement StatementIngredients RootedFiniteEnergyDensityMeasurable
open DyadicApproximation

/-! ### The unique cell containing the origin -/

/-- Label `n` is active and is the unique cell of `e` containing the origin. -/
def OriginUniqueCell (e : Env) (n : ℕ) : Prop :=
  (e.val.1 n).isSome ∧ (0 : Plane) ∈ (slotCell e n : Set Plane) ∧
    ∀ m : ℕ, (e.val.1 m).isSome → (0 : Plane) ∈ (slotCell e m : Set Plane) → m = n

theorem measurableSet_slotIsSome_env (n : ℕ) : MeasurableSet {e : Env | (e.val.1 n).isSome} :=
  ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion))
    Spatial.measurableSet_slotIsSome

theorem measurable_slotIsSome_env (n : ℕ) : Measurable fun e : Env => (e.val.1 n).isSome = true :=
  measurableSet_setOfPred.1 (measurableSet_slotIsSome_env n)

theorem measurable_zero_mem_slotCell (n : ℕ) :
    Measurable fun e : Env => (0 : Plane) ∈ (slotCell e n : Set Plane) :=
  measurableSet_setOfPred.1 ((measurable_slotCell_env n) (Spatial.measurableSet_mem_cell 0))

theorem measurableSet_originUniqueCell (n : ℕ) : MeasurableSet {e : Env | OriginUniqueCell e n} :=
  measurableSet_setOfPred.2 ((measurable_slotIsSome_env n).and
    ((measurable_zero_mem_slotCell n).and (Measurable.forall fun m =>
      (measurable_slotIsSome_env m).imp ((measurable_zero_mem_slotCell m).imp measurable_const))))

/-- A cell containing the origin and no other cell containing it gives `OriginUniqueCell`. -/
theorem originUniqueCell_of_unique {e : Env} {r : Vertex e.val}
    (h0 : (0 : Plane) ∈ ((decode e).cell r : Set Plane))
    (huniq : ∀ w : Vertex e.val, (0 : Plane) ∈ ((decode e).cell w : Set Plane) → w = r) :
    OriginUniqueCell e r.val := by
  refine ⟨r.property, ?_, fun m hm hm0 => ?_⟩
  · rw [slotCell_eq_cell]
    exact h0
  · have hc : slotCell e m = (decode e).cell ⟨m, hm⟩ := slotCell_eq_cell e ⟨m, hm⟩
    rw [hc] at hm0
    exact congrArg Subtype.val (huniq ⟨m, hm⟩ hm0)

/-- `n` is the unique origin cell, or there is none (a total selector). -/
def OriginCellSelector (e : Env) (n : ℕ) : Prop :=
  OriginUniqueCell e n ∨ ¬ ∃ m, OriginUniqueCell e m

theorem exists_originCellSelector (e : Env) : ∃ n, OriginCellSelector e n := by
  by_cases h : ∃ m, OriginUniqueCell e m
  · obtain ⟨m, hm⟩ := h
    exact ⟨m, Or.inl hm⟩
  · exact ⟨0, Or.inr h⟩

open Classical in
/-- The value of `Φ` at label `n` if `n` is the unique origin cell, and `0` otherwise. -/
noncomputable def originCellValue (Φ : CellField) (n : ℕ) (e : Env) : Plane :=
  if OriginUniqueCell e n then Φ.value e n else 0

open Classical in
/-- **The root constant**: the value of `Φ` at the unique cell containing the origin, when there is
one, and `0` otherwise. -/
noncomputable def originConstant (Φ : CellField) (e : Env) : Plane :=
  originCellValue Φ (Nat.find (exists_originCellSelector e)) e

open Classical in
theorem measurable_originConstant (Φ : CellField) : Measurable (originConstant Φ) := by
  have hf : ∀ n, Measurable (originCellValue Φ n) := fun n =>
    Measurable.ite (measurableSet_originUniqueCell n) (Φ.measurable_label n) measurable_const
  have hO : ∀ n, Measurable fun e : Env => OriginUniqueCell e n := fun n =>
    measurableSet_setOfPred.1 (measurableSet_originUniqueCell n)
  have hp : ∀ n, MeasurableSet {e : Env | OriginCellSelector e n} := fun n =>
    measurableSet_setOfPred.2 ((hO n).or (Measurable.exists hO).not)
  exact Measurable.find (p := fun n e => OriginCellSelector e n) hf hp exists_originCellSelector

theorem originConstant_eq_of_originUniqueCell {Φ : CellField} {e : Env} {n : ℕ}
    (hn : OriginUniqueCell e n) : originConstant Φ e = Φ.value e n := by
  classical
  unfold originConstant
  rcases Nat.find_spec (exists_originCellSelector e) with hk | hk
  · have hkn := hn.2.2 _ hk.1 hk.2.1
    rw [originCellValue, if_pos hk, hkn]
  · exact absurd ⟨n, hn⟩ hk

/-! ### The renormalized field -/

/-- **The renormalized field** `Φ − Φ(unique origin cell)`, extended by zero at absent labels. -/
noncomputable def renormalizedField (Φ : CellField) : CellField where
  value e n := if (e.val.1 n).isSome then Φ.value e n - originConstant Φ e else 0
  measurable_value := Measurable.of_eval fun n =>
    Measurable.ite (measurableSet_slotIsSome_env n)
      ((Φ.measurable_label n).sub (measurable_originConstant Φ)) measurable_const
  absent_zero e n hn := by simp [hn]

theorem renormalizedField_at (Φ : CellField) (e : Env) (v : Vertex e.val) :
    (renormalizedField Φ).at e v = Φ.at e v - originConstant Φ e := by
  show (if (e.val.1 v.val).isSome then Φ.value e v.val - originConstant Φ e else 0) = _
  rw [if_pos v.property]
  rfl

/-- Gradients are unchanged in every environment. -/
theorem gradient_renormalizedField (Φ : CellField) (e : Env) (v w : Vertex e.val) :
    (renormalizedField Φ).gradient e v w = Φ.gradient e v w := by
  unfold CellField.gradient
  rw [renormalizedField_at, renormalizedField_at, sub_sub_sub_cancel_right]

theorem gradientCovariant_renormalizedField {Φ : CellField} (hΦ : GradientCovariant Φ) :
    GradientCovariant (renormalizedField Φ) := by
  intro s u hs e e' relabel hrel v w
  rw [gradient_renormalizedField, gradient_renormalizedField]
  exact hΦ s u hs e e' relabel hrel v w

/-- A similarity sends `u` to the origin. -/
theorem zero_mem_transformCell_iff (s : ℝ) (u : Plane) (hs : 0 < s) (K : CompactCell) :
    (0 : Plane) ∈ (transformCell s u hs K : Set Plane) ↔ u ∈ (K : Set Plane) := by
  rw [coe_transformCell]
  constructor
  · rintro ⟨z, hz, hz0⟩
    rw [positiveSimilarity_apply] at hz0
    have hzu : z - u = 0 := (smul_eq_zero.1 hz0).resolve_left hs.ne'
    rwa [sub_eq_zero.1 hzu] at hz
  · intro hu
    exact ⟨u, hu, by simp⟩

/-- **(1.10) wherever `H_u` is uniquely defined**, for the renormalized field. -/
theorem uniqueCellCovariant_renormalizedField {Φ : CellField} (hΦ : GradientCovariant Φ) :
    UniqueCellCovariant (renormalizedField Φ) := by
  intro s u hs e e' relabel hrel r hur huniq v
  have hc : originConstant Φ e' = Φ.at e' (relabel r) := by
    refine originConstant_eq_of_originUniqueCell (originUniqueCell_of_unique ?_ ?_)
    · rw [hrel.1 r, zero_mem_transformCell_iff]
      exact hur
    · intro w' hw'
      have hw := hrel.1 (relabel.symm w')
      rw [Equiv.apply_symm_apply] at hw
      rw [hw, zero_mem_transformCell_iff] at hw'
      rw [← huniq _ hw', Equiv.apply_symm_apply]
  rw [renormalizedField_at, renormalizedField_at, renormalizedField_at, sub_sub_sub_cancel_right,
    hc]
  exact hΦ s u hs e e' relabel hrel r v

/-- A defined masked root is the unique cell containing the point. -/
theorem mem_cell_and_unique_of_rootAt {e : Env} {u : Plane} {r : Vertex e.val}
    (h : RootDensities.rootAt (decode e) u = some r) :
    u ∈ ((decode e).cell r : Set Plane) ∧
      ∀ w : Vertex e.val, u ∈ ((decode e).cell w : Set Plane) → w = r := by
  obtain ⟨hmask, hint⟩ :=
    (RootDensities.rootAt_eq_some_iff (decode e) (decode_geometry e) u r).1 h
  refine ⟨interior_subset hint, fun w hw => ?_⟩
  have hwint : RootDensities.IsInteriorRoot (decode e) u w := by
    have hfr : u ∉ frontier ((decode e).cell w : Set Plane) := fun hf =>
      hmask (Set.mem_union_left _ (Set.mem_iUnion.2 ⟨w, hf⟩))
    have hclosed : IsClosed ((decode e).cell w : Set Plane) :=
      ((decode e).cell w).isCompact.isClosed
    rw [frontier, hclosed.closure_eq] at hfr
    exact Classical.byContradiction fun hn => hfr ⟨hw, hn⟩
  exact (RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask (decode e)
    (decode_geometry e) hmask).unique hwint hint

theorem normalizedCovariant_renormalizedField {Φ : CellField} (hΦ : GradientCovariant Φ) :
    NormalizedCovariant (renormalizedField Φ) := by
  intro s u hs e e' relabel hrel r hr v
  obtain ⟨h1, h2⟩ := mem_cell_and_unique_of_rootAt hr
  exact uniqueCellCovariant_renormalizedField hΦ s u hs e e' relabel hrel r h1 h2 v

/-- Where the origin is off the mask and `Φ` vanishes at the root, nothing changes. -/
theorem renormalizedField_at_eq_of_rootNormalized {Φ : CellField} {e : Env}
    (hmask : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) (hroot : RootNormalized Φ e) :
    (renormalizedField Φ).at e = Φ.at e := by
  obtain ⟨r, hr, _⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) (decode_geometry e) hmask
  obtain ⟨h1, h2⟩ := mem_cell_and_unique_of_rootAt hr
  have hc : originConstant Φ e = 0 := by
    rw [originConstant_eq_of_originUniqueCell (originUniqueCell_of_unique h1 h2)]
    exact hroot r hr
  funext v
  rw [renormalizedField_at, hc, sub_zero]

theorem ae_renormalizedField_at_eq {ν : Measure Env} {Φ : CellField}
    (hΦ : IsHarmonicCoordinate ν Φ) : ∀ᵐ e ∂ν, (renormalizedField Φ).at e = Φ.at e := by
  filter_upwards [hΦ.2.2.2.2.1] with e he
  exact renormalizedField_at_eq_of_rootNormalized he.1 he.2.1

/-! ### Transfer of the clauses that read the field at one environment -/

section Congr

variable {Φ Ψ : CellField}

theorem rootNormalized_congr {e : Env} (h : Ψ.at e = Φ.at e) (hΦ : RootNormalized Φ e) :
    RootNormalized Ψ e := by
  intro v hv
  rw [h]
  exact hΦ v hv

theorem fullSpatialHarmonicity_congr {e : Env} (h : Ψ.at e = Φ.at e)
    (hΦ : FullSpatialHarmonicity Φ e) : FullSpatialHarmonicity Ψ e := by
  unfold FullSpatialHarmonicity at hΦ ⊢
  rw [h]
  exact hΦ

theorem discreteHarmonicity_congr {e : Env} (h : Ψ.at e = Φ.at e)
    (hΦ : DiscreteHarmonicity Φ e) : DiscreteHarmonicity Ψ e := by
  unfold DiscreteHarmonicity CellField.gradient at hΦ ⊢
  rw [h]
  exact hΦ

theorem sublinearCorrector_congr {e : Env} (h : Ψ.at e = Φ.at e)
    (hΦ : SublinearCorrector Φ e) : SublinearCorrector Ψ e := by
  unfold SublinearCorrector at hΦ ⊢
  rw [h]
  exact hΦ

theorem graphNeighborhoodError_congr {ω : MarkedEnvironment} (h : Ψ.at ω.1 = Φ.at ω.1)
    (radius m : ℕ) : graphNeighborhoodError Ψ radius m ω = graphNeighborhoodError Φ radius m ω := by
  unfold graphNeighborhoodError
  rw [h]

theorem specificGradientError_congr {ω : MarkedEnvironment} (h : Ψ.at ω.1 = Φ.at ω.1) (m : ℕ) :
    specificGradientError Ψ m ω = specificGradientError Φ m ω := by
  unfold specificGradientError
  rw [h]

theorem spatialPatchError_congr {ω : MarkedEnvironment} (h : Ψ.at ω.1 = Φ.at ω.1) (m : ℕ)
    (A : Set Plane) : spatialPatchError Ψ m ω A = spatialPatchError Φ m ω A := by
  unfold spatialPatchError
  rw [h]

theorem environmentProcessConclusions_congr {e : Env} {target : AnisotropicBrownianTarget}
    (h : Ψ.at e = Φ.at e) (hΦ : EnvironmentProcessConclusions e Φ target) :
    EnvironmentProcessConclusions e Ψ target := by
  unfold EnvironmentProcessConclusions FixedStartConclusions CanonicalBracket at hΦ ⊢
  rw [h]
  exact hΦ

/-- The approximation conclusions transfer along almost-sure agreement of the fields. -/
theorem approximationConclusions_congr {ν : Measure Env} {σ : Measure Grid} [SFinite σ]
    (hae : ∀ᵐ e ∂ν, Ψ.at e = Φ.at e) (hΦ : ApproximationConclusions ν σ Φ) :
    ApproximationConclusions ν σ Ψ := by
  have haeP : ∀ᵐ ω : MarkedEnvironment ∂ν.prod σ, Ψ.at ω.1 = Φ.at ω.1 :=
    (Measure.quasiMeasurePreserving_fst :
      Measure.QuasiMeasurePreserving Prod.fst (ν.prod σ) ν).ae hae
  obtain ⟨h1, h2, h3, h4, ⟨h5a, h5b, h5c⟩, ⟨sub, hsub, h6⟩⟩ := hΦ
  have hGN : ∀ radius m, graphNeighborhoodError Φ radius m =ᵐ[ν.prod σ]
      graphNeighborhoodError Ψ radius m := fun radius m => by
    filter_upwards [haeP] with ω hω
    exact (graphNeighborhoodError_congr hω radius m).symm
  have hSG : ∀ m, specificGradientError Φ m =ᵐ[ν.prod σ] specificGradientError Ψ m := fun m => by
    filter_upwards [haeP] with ω hω
    exact (specificGradientError_congr hω m).symm
  refine ⟨h1, h2, fun radius m => (h3 radius m).congr (hGN radius m),
    fun radius => (h4 radius).congr_left (hGN radius), ⟨h5a, fun m => (h5b m).congr (hSG m), ?_⟩,
    ⟨sub, hsub, ?_⟩⟩
  · have hfun : (fun m => ∫⁻ ω : MarkedEnvironment, specificGradientError Ψ m ω ∂ν.prod σ) =
        fun m => ∫⁻ ω : MarkedEnvironment, specificGradientError Φ m ω ∂ν.prod σ :=
      funext fun m => (lintegral_congr_ae (hSG m)).symm
    rw [hfun]
    exact h5c
  · filter_upwards [h6, haeP] with ω hω hωeq
    refine ⟨fun A hA => ?_, fun r hr v => ?_⟩
    · simp only [spatialPatchError_congr hωeq]
      exact hω.1 A hA
    · rw [hωeq]
      exact hω.2 r hr v

end Congr

/-! ### The harmonic-coordinate and reflected-invariance transfers -/

theorem isHarmonicCoordinate_renormalizedField {ν : Measure Env} {Φ : CellField}
    (hΦ : IsHarmonicCoordinate ν Φ) : IsHarmonicCoordinate ν (renormalizedField Φ) := by
  have hae := ae_renormalizedField_at_eq hΦ
  obtain ⟨hgrad, _, hmeas, hfin, has, hσ, happrox⟩ := hΦ
  have hρ : (fun e : Env => RootDensities.rootedSpecificEnergyDensity (decode e) (Φ.at e) 0) =ᵐ[ν]
      fun e => RootDensities.rootedSpecificEnergyDensity (decode e)
        ((renormalizedField Φ).at e) 0 := by
    filter_upwards [hae] with e he
    rw [he]
  refine ⟨gradientCovariant_renormalizedField hgrad, normalizedCovariant_renormalizedField hgrad,
    hmeas.congr hρ, ?_, ?_, hσ, fun σ hσ' => ?_⟩
  · unfold FiniteSpecificEnergy at hfin ⊢
    rw [← lintegral_congr_ae hρ]
    exact hfin
  · filter_upwards [has, hae] with e he heq
    obtain ⟨h0, hroot, hfull, hdisc, hsub⟩ := he
    exact ⟨h0, rootNormalized_congr heq hroot, fullSpatialHarmonicity_congr heq hfull,
      discreteHarmonicity_congr heq hdisc, sublinearCorrector_congr heq hsub⟩
  · have := hσ'.1
    exact approximationConclusions_congr hae (happrox σ hσ')

/-- **Every harmonic coordinate can be renormalized to satisfy (1.10) wherever `H_u` is uniquely
defined**, keeping every conclusion of `IsHarmonicCoordinate` and agreeing with the original field
at almost every environment. -/
theorem exists_uniqueCellCovariant_of_isHarmonicCoordinate {ν : Measure Env} {Φ : CellField}
    (hΦ : IsHarmonicCoordinate ν Φ) :
    ∃ Ψ : CellField, IsHarmonicCoordinate ν Ψ ∧ UniqueCellCovariant Ψ ∧
      ∀ᵐ e ∂ν, Ψ.at e = Φ.at e :=
  ⟨renormalizedField Φ, isHarmonicCoordinate_renormalizedField hΦ,
    uniqueCellCovariant_renormalizedField hΦ.1, ae_renormalizedField_at_eq hΦ⟩

/-- The strengthened harmonic-coordinate conclusions follow from the reused ones. -/
theorem geomHarmonicCoordinateConclusions_of_harmonicCoordinateConclusions {ν : Measure Env}
    (h : HarmonicCoordinateConclusions ν) : GeomHarmonicCoordinateConclusions ν := by
  obtain ⟨Φ, hΦ⟩ := h
  obtain ⟨Ψ, hΨ, hcov, _⟩ := exists_uniqueCellCovariant_of_isHarmonicCoordinate hΦ
  exact ⟨Ψ, hΨ, hcov⟩

/-- The strengthened reflected-invariance conclusions follow from the reused ones: the same target,
bracket and representative, with the renormalized coordinate. -/
theorem geomReflectedInvarianceConclusions_of_reflectedInvarianceConclusions {ν : Measure Env}
    (h : ReflectedInvarianceConclusions ν) : GeomReflectedInvarianceConclusions ν := by
  obtain ⟨Φ, target, hΦ, hint, hcov, hz, hproc⟩ := h
  obtain ⟨Ψ, hΨ, hunique, hae⟩ := exists_uniqueCellCovariant_of_isHarmonicCoordinate hΦ
  have hΓ : ∀ i j, (fun e : Env => RootDensities.rootedGamma (decode e) (Φ.at e) 0 i j) =ᵐ[ν]
      fun e => RootDensities.rootedGamma (decode e) (Ψ.at e) 0 i j := fun i j => by
    filter_upwards [hae] with e he
    rw [he]
  refine ⟨Ψ, target, ⟨hΨ, hunique⟩, fun i j => (hint i j).congr (hΓ i j), ?_, hz, ?_⟩
  · rw [hcov]
    ext i j
    exact integral_congr_ae (hΓ i j)
  · filter_upwards [hproc, hae] with e he heq
    exact environmentProcessConclusions_congr heq he

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.uniqueCellCovariant_renormalizedField
assert_no_sorry ReflectedGMS.GeomTop.exists_uniqueCellCovariant_of_isHarmonicCoordinate
assert_no_sorry ReflectedGMS.GeomTop.geomHarmonicCoordinateConclusions_of_harmonicCoordinateConclusions
assert_no_sorry
  ReflectedGMS.GeomTop.geomReflectedInvarianceConclusions_of_reflectedInvarianceConclusions
#print axioms ReflectedGMS.GeomTop.uniqueCellCovariant_renormalizedField
#print axioms ReflectedGMS.GeomTop.exists_uniqueCellCovariant_of_isHarmonicCoordinate
#print axioms ReflectedGMS.GeomTop.geomHarmonicCoordinateConclusions_of_harmonicCoordinateConclusions
#print axioms
  ReflectedGMS.GeomTop.geomReflectedInvarianceConclusions_of_reflectedInvarianceConclusions
