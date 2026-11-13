/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.InvarianceAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.QuenchedFormulation
import LatticeProb.Bonanno.ReflectedGMS.Limit.CovarianceRootPropagation
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoercivitySmallJumps
import LatticeProb.Bonanno.ReflectedGMS.Analysis.BracketSpecificEnergy
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootedBracketMeasurability
import LatticeProb.Bonanno.BouRabeeGwynne.StandardBrownianProbabilityMeasure
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Assembly of the reflected invariance conclusions from named inputs

This file reduces `InvarianceMainStatement.ReflectedInvarianceConclusions` to a
short list of *named* mathematical inputs, discharging every clause the project
can already prove.  It proves no main theorem: the final statement is an
implication whose hypotheses are still open, and nothing here certifies them.

What is actually discharged here, from already checked results:

* `IntegrableBracket ν Φ` follows from the finite specific energy clause of
  `IsHarmonicCoordinate` together with entrywise measurability of the rooted
  bracket in the environment, which is itself discharged from mass transport by
  `RootedBracketMeasurability.aestronglyMeasurable_rootedGamma`.  The key
  deterministic step is `abs_rootedGamma_le_trace`: every
  entry of the rooted bracket density is dominated in absolute value by its
  trace, which by `RootDensities.ofReal_trace_rootedGamma_eq_two_mul_rootedSpecificEnergyDensity`
  is twice the rooted specific energy density.
* `SymmetricPositiveDefinite (meanCovariance ν Φ)`: symmetry is proved here,
  and strict positivity is the checked
  `CovarianceRootPropagation.quadraticForm_meanCovariance_pos`.
* The `AnisotropicBrownianTarget` with the prescribed covariance is built by an
  explicit `2 × 2` Cholesky factorisation of a symmetric positive definite
  matrix; its standard `2`-dimensional Brownian law is supplied unconditionally
  by the sibling project's checked
  `BouRabeeGwynne.exists_standardBrownianProbabilityMeasure`, so no Brownian
  input is carried as a hypothesis.
* The submacroscopic-diameter hypothesis of the positive-definiteness producer
  is discharged from mass transport and the finite-energy moment through
  `Spatial.ae_finite_scaledNear_of_finiteEnergyMoment` and
  `CoercivitySmallJumps.submacroscopicDiameters_of_finite_scaledNear`.
* The passage from per-starting-label almost-sure statements to one
  probability-one set of environments is the checked
  `QuenchedFormulation.ae_environmentProcessConclusions_of_ae_fixedStartConclusions`.

Everything else is carried as an explicit hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.InvarianceAssembly

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open RootDensities DirectionalNondegeneracy
open InvarianceMainStatement QuenchedFormulation

/-! ## Entrywise control of the ordinary-edge bracket by its trace -/

section BracketEntries

variable {V : Type*}

/-- The ordinary-edge bracket density is a symmetric matrix. -/
theorem bracketDensity_symm (F : IndexedCells V) (Phi : V → Plane) (v : V)
    (i j : Fin 2) :
    bracketDensity F Phi v i j = bracketDensity F Phi v j i := by
  simp only [StatementIngredients.bracketDensity]
  refine congrArg _ (tsum_congr fun w => ?_)
  ring

/-- The rooted bracket density is a symmetric matrix. -/
theorem rootedGamma_symm (F : IndexedCells V) (Phi : V → Plane) (z : Plane)
    (i j : Fin 2) :
    rootedGamma F Phi z i j = rootedGamma F Phi z j i := by
  generalize hroot : rootAt F z = root
  cases root with
  | none => simp [rootedGamma, hroot]
  | some v =>
      have hG : rootedGamma F Phi z = bracketDensity F Phi v := by
        simp [rootedGamma, hroot]
      rw [hG]
      exact bracketDensity_symm F Phi v i j

/-- A `2 × 2` real symmetric matrix whose quadratic form is nonnegative has each
entry dominated in absolute value by its trace. -/
theorem abs_entry_le_trace (G : Matrix (Fin 2) (Fin 2) ℝ) (hsymm : G 1 0 = G 0 1)
    (hq : ∀ ξ : Fin 2 → ℝ, 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ξ i * G i j * ξ j)
    (i j : Fin 2) :
    |G i j| ≤ Matrix.trace G := by
  have key : ∀ a b : ℝ, 0 ≤ a ^ 2 * G 0 0 + 2 * (a * b) * G 0 1 + b ^ 2 * G 1 1 := by
    intro a b
    have h := hq ![a, b]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [hsymm] at h
    nlinarith [h]
  have h00 : 0 ≤ G 0 0 := by nlinarith [key 1 0]
  have h11 : 0 ≤ G 1 1 := by nlinarith [key 0 1]
  have hplus : 0 ≤ G 0 0 + 2 * G 0 1 + G 1 1 := by nlinarith [key 1 1]
  have hminus : 0 ≤ G 0 0 - 2 * G 0 1 + G 1 1 := by nlinarith [key 1 (-1)]
  have htrace : Matrix.trace G = G 0 0 + G 1 1 := Matrix.trace_fin_two G
  have e00 : |G 0 0| ≤ Matrix.trace G := by
    rw [htrace, abs_le]; constructor <;> linarith
  have e01 : |G 0 1| ≤ Matrix.trace G := by
    rw [htrace, abs_le]; constructor <;> linarith
  have e10 : |G 1 0| ≤ Matrix.trace G := by rw [hsymm]; exact e01
  have e11 : |G 1 1| ≤ Matrix.trace G := by
    rw [htrace, abs_le]; constructor <;> linarith
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

/-- Every entry of the rooted bracket density is dominated in absolute value by
its trace.  This is pure `2 × 2` positive-semidefiniteness: the quadratic form
of `rootedGamma` is nonnegative in every direction
(`DirectionalNondegeneracy.quadraticForm_rootedGamma_nonneg`) and the matrix is
symmetric. -/
theorem abs_rootedGamma_le_trace [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Phi : V → Plane) (z : Plane) (i j : Fin 2) :
    |rootedGamma F Phi z i j| ≤ Matrix.trace (rootedGamma F Phi z) :=
  abs_entry_le_trace _ (rootedGamma_symm F Phi z 1 0)
    (fun ξ => quadraticForm_rootedGamma_nonneg F hF Phi z ξ) i j

end BracketEntries

/-! ## Integrability of the bracket -/

/-- **`IntegrableBracket` from measurability alone.**  Given entrywise
measurability of the rooted bracket, its integrability is a consequence of the
finite specific energy clause already contained in `IsHarmonicCoordinate`. -/
theorem integrableBracket_of_aestronglyMeasurable (ν : Measure Env) (Φ : CellField)
    (hmeas : ∀ i j, AEStronglyMeasurable
      (fun e : Env => rootedGamma (decode e) (Φ.at e) 0 i j) ν)
    (hfin : FiniteSpecificEnergy ν Φ) :
    IntegrableBracket ν Φ := by
  intro i j
  refine ⟨hmeas i j, ?_⟩
  have hbound : ∀ e : Env, ‖rootedGamma (decode e) (Φ.at e) 0 i j‖ₑ
      ≤ 2 * rootedSpecificEnergyDensity (decode e) (Φ.at e) 0 := by
    intro e
    have h1 := abs_rootedGamma_le_trace (decode e) (decode_geometry e) (Φ.at e) 0 i j
    have h2 := ofReal_trace_rootedGamma_eq_two_mul_rootedSpecificEnergyDensity
      (decode e) (decode_geometry e) (Φ.at e) 0
    calc ‖rootedGamma (decode e) (Φ.at e) 0 i j‖ₑ
        = ENNReal.ofReal |rootedGamma (decode e) (Φ.at e) 0 i j| :=
          Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (Matrix.trace (rootedGamma (decode e) (Φ.at e) 0)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = 2 * rootedSpecificEnergyDensity (decode e) (Φ.at e) 0 := h2
  have hle : (∫⁻ e : Env, ‖rootedGamma (decode e) (Φ.at e) 0 i j‖ₑ ∂ν)
      ≤ 2 * ∫⁻ e : Env, rootedSpecificEnergyDensity (decode e) (Φ.at e) 0 ∂ν := by
    calc (∫⁻ e : Env, ‖rootedGamma (decode e) (Φ.at e) 0 i j‖ₑ ∂ν)
        ≤ ∫⁻ e : Env, 2 * rootedSpecificEnergyDensity (decode e) (Φ.at e) 0 ∂ν :=
          lintegral_mono hbound
      _ = 2 * ∫⁻ e : Env, rootedSpecificEnergyDensity (decode e) (Φ.at e) 0 ∂ν :=
          lintegral_const_mul' _ _ (by norm_num)
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (by norm_num) hfin)

/-! ## Symmetry and positive definiteness of the mean covariance -/

/-- The deterministic mean covariance is symmetric. -/
theorem meanCovariance_symm (ν : Measure Env) (Φ : CellField) (i j : Fin 2) :
    meanCovariance ν Φ i j = meanCovariance ν Φ j i := by
  show (∫ e : Env, rootedGamma (decode e) (Φ.at e) 0 i j ∂ν)
      = ∫ e : Env, rootedGamma (decode e) (Φ.at e) 0 j i ∂ν
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun e => rootedGamma_symm (decode e) (Φ.at e) 0 i j)

/-- **The full `SymmetricPositiveDefinite` clause for the mean covariance**,
combining the symmetry above with the checked directional positivity
`CovarianceRootPropagation.quadraticForm_meanCovariance_pos`. -/
theorem symmetricPositiveDefinite_meanCovariance (ν : Measure Env) (hνne : ν ≠ 0)
    (hmt : MassTransport ν) (Φ : CellField) (hcov : GradientCovariant Φ)
    (hint : IntegrableBracket ν Φ)
    (hsub : ∀ᵐ e ∂ν, UniformlySublinearCorrector (decode e) (Φ.at e))
    (hdiam : ∀ᵐ e ∂ν, SubmacroscopicDiameters (decode e)) :
    SymmetricPositiveDefinite (meanCovariance ν Φ) :=
  ⟨meanCovariance_symm ν Φ, fun ξ hξ =>
    CovarianceRootPropagation.quadraticForm_meanCovariance_pos ν hνne hmt Φ hcov hint
      hsub hdiam hξ⟩

/-- Almost-sure submacroscopic cell diameters from the manuscript's own
environment assumptions: mass transport and the finite (FE) moment. -/
theorem ae_submacroscopicDiameters (ν : Measure Env) (hmt : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ e ∂ν, SubmacroscopicDiameters (decode e) := by
  filter_upwards [Spatial.ae_finite_scaledNear_of_finiteEnergyMoment ν hmt hFE.ne] with e he
  exact CoercivitySmallJumps.submacroscopicDiameters_of_finite_scaledNear (decode e) he

/-! ## An anisotropic Brownian target with a prescribed covariance -/

/-- The entries of `A Aᵀ` in dimension two. -/
theorem covarianceOfBrownianFactor_apply (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    covarianceOfBrownianFactor M i j = M i 0 * M j 0 + M i 1 * M j 1 := by
  show (M * M.transpose) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  rfl

/-- `A Aᵀ` for a lower triangular `2 × 2` matrix. -/
theorem covarianceOfBrownianFactor_lower (a b c : ℝ) :
    covarianceOfBrownianFactor (Matrix.of ![![a, 0], ![b, c]])
      = Matrix.of ![![a * a, a * b], ![b * a, b * b + c * c]] := by
  ext i j
  rw [covarianceOfBrownianFactor_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Reading off a lower-triangular factorisation entrywise. -/
theorem eq_covarianceOfBrownianFactor_lower (C : Matrix (Fin 2) (Fin 2) ℝ) (a b c : ℝ)
    (h00 : C 0 0 = a * a) (h01 : C 0 1 = a * b) (h10 : C 1 0 = b * a)
    (h11 : C 1 1 = b * b + c * c) :
    C = covarianceOfBrownianFactor (Matrix.of ![![a, 0], ![b, c]]) := by
  rw [covarianceOfBrownianFactor_lower]
  conv_lhs => rw [Matrix.eta_fin_two C, h00, h01, h10, h11]

/-- **Explicit `2 × 2` Cholesky factorisation.**  A symmetric positive definite
`2 × 2` real matrix is `A Aᵀ` for a lower triangular `A`. -/
theorem exists_factor_of_symmetricPositiveDefinite
    (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : SymmetricPositiveDefinite C) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, C = covarianceOfBrownianFactor A := by
  obtain ⟨hsymm, hpos⟩ := hC
  have hs : C 1 0 = C 0 1 := hsymm 1 0
  have h00 : 0 < C 0 0 := by
    have hne : (![(1 : ℝ), 0]) ≠ 0 := by
      intro h
      have h1 : (![(1 : ℝ), 0]) 0 = (0 : Fin 2 → ℝ) 0 := by rw [h]
      simp at h1
    have h := hpos _ hne
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    nlinarith [h]
  have hdet : 0 < C 0 0 * C 1 1 - C 0 1 ^ 2 := by
    have hne : (![-(C 0 1), C 0 0]) ≠ 0 := by
      intro h
      have h1 : (![-(C 0 1), C 0 0]) 1 = (0 : Fin 2 → ℝ) 1 := by rw [h]
      simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
      exact (ne_of_gt h00) h1
    have h := hpos _ hne
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hs] at h
    nlinarith [h, h00]
  obtain ⟨a, ha0, hasq⟩ : ∃ a : ℝ, 0 < a ∧ a * a = C 0 0 :=
    ⟨Real.sqrt (C 0 0), Real.sqrt_pos.mpr h00, Real.mul_self_sqrt h00.le⟩
  obtain ⟨c, hcsq⟩ : ∃ c : ℝ, c * c = (C 0 0 * C 1 1 - C 0 1 ^ 2) / C 0 0 :=
    ⟨Real.sqrt ((C 0 0 * C 1 1 - C 0 1 ^ 2) / C 0 0),
      Real.mul_self_sqrt (div_pos hdet h00).le⟩
  have hane : a ≠ 0 := ne_of_gt ha0
  have h00ne : C 0 0 ≠ 0 := ne_of_gt h00
  refine ⟨Matrix.of ![![a, 0], ![C 0 1 / a, c]],
    eq_covarianceOfBrownianFactor_lower C a (C 0 1 / a) c hasq.symm ?_ ?_ ?_⟩
  · field_simp
  · rw [hs]; field_simp
  · rw [hcsq, div_mul_div_comm, hasq]
    field_simp
    ring

/-- **A genuine anisotropic Brownian target with prescribed covariance**, from a
supplied standard `2`-dimensional Brownian law.  The unconditional form, which
supplies that law from the sibling project's checked Euclidean Wiener law, is
`exists_anisotropicBrownianTarget_of_symmetricPositiveDefinite` below. -/
theorem exists_anisotropicBrownianTarget_covariance_eq
    (μBM : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (hBM : BouRabeeGwynne.IsStandardBrownianLaw (d := 2)
      (μBM : Measure (BouRabeeGwynne.BrownianPath 2)))
    (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : SymmetricPositiveDefinite C) :
    ∃ target : AnisotropicBrownianTarget, target.covariance = C := by
  obtain ⟨A, hA⟩ := exists_factor_of_symmetricPositiveDefinite C hC
  exact ⟨{ standardLaw := μBM
           isStandard := hBM
           covariance := C
           factor := A
           covariance_eq := hA
           positiveDefinite := hC }, rfl⟩

/-- **Unconditional existence of an anisotropic Brownian target with prescribed
covariance.**  The standard `2`-dimensional Brownian law is no longer an input:
it is the checked Euclidean Wiener law of the sibling project, bundled by
`BouRabeeGwynne.exists_standardBrownianProbabilityMeasure`. -/
theorem exists_anisotropicBrownianTarget_of_symmetricPositiveDefinite
    (C : Matrix (Fin 2) (Fin 2) ℝ) (hC : SymmetricPositiveDefinite C) :
    ∃ target : AnisotropicBrownianTarget, target.covariance = C := by
  obtain ⟨μBM, hBM⟩ := BouRabeeGwynne.exists_standardBrownianProbabilityMeasure 2
  exact exists_anisotropicBrownianTarget_covariance_eq μBM hBM C hC

/-! ## A measurable, similarity-covariant choice of cell representatives

The witness is the *lexicographic minimum* of the cell: the point of the cell
whose first coordinate is least, and among those the one whose second
coordinate is least.  It lies in the cell by compactness, it is exactly
covariant under `positiveSimilarity s u` because that map is strictly
increasing in each coordinate for `s > 0`, and it is Borel measurable in the
Hausdorff topology on `NonemptyCompacts Plane`. -/

section CellRepresentative

/-- `p` is the lexicographic minimum of the planar set `K`. -/
def IsLexMin (K : Set Plane) (p : Plane) : Prop :=
  p ∈ K ∧ ∀ x ∈ K, p 0 < x 0 ∨ (p 0 = x 0 ∧ p 1 ≤ x 1)

theorem IsLexMin.coord_zero_le {K : Set Plane} {p x : Plane} (h : IsLexMin K p)
    (hx : x ∈ K) : p 0 ≤ x 0 := by
  rcases h.2 x hx with h' | h'
  · exact h'.le
  · exact h'.1.le

theorem isLexMin_unique {K : Set Plane} {p q : Plane} (hp : IsLexMin K p)
    (hq : IsLexMin K q) : p = q := by
  have h0 : p 0 = q 0 := le_antisymm (hp.coord_zero_le hq.1) (hq.coord_zero_le hp.1)
  have h1 : p 1 = q 1 := by
    rcases hp.2 q hq.1 with h | h
    · exact absurd h0 (ne_of_lt h)
    · rcases hq.2 p hp.1 with h' | h'
      · exact absurd h0.symm (ne_of_lt h')
      · exact le_antisymm h.2 h'.2
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem exists_isLexMin {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ p, IsLexMin K p := by
  obtain ⟨a, haK, hamin⟩ := hK.exists_isMinOn hne
    (Continuous.continuousOn (by fun_prop : Continuous fun x : Plane => x 0))
  have hKc : IsCompact (K ∩ {x : Plane | x 0 = a 0}) :=
    hK.inter_right (isClosed_eq (by fun_prop) continuous_const)
  obtain ⟨b, hbK, hbmin⟩ := hKc.exists_isMinOn ⟨a, haK, rfl⟩
    (Continuous.continuousOn (by fun_prop : Continuous fun x : Plane => x 1))
  have hb0 : b 0 = a 0 := hbK.2
  refine ⟨b, hbK.1, fun x hx => ?_⟩
  have hax : a 0 ≤ x 0 := hamin hx
  rcases lt_or_eq_of_le hax with hlt | heq
  · exact Or.inl (by rw [hb0]; exact hlt)
  · have hbx : b 1 ≤ x 1 := hbmin ⟨hx, heq.symm⟩
    exact Or.inr ⟨by rw [hb0]; exact heq, hbx⟩

/-- The lexicographic minimum of a nonempty compact cell. -/
noncomputable def lexMin (K : CompactCell) : Plane :=
  (exists_isLexMin K.isCompact K.nonempty).choose

theorem isLexMin_lexMin (K : CompactCell) : IsLexMin (K : Set Plane) (lexMin K) :=
  (exists_isLexMin K.isCompact K.nonempty).choose_spec

theorem lexMin_mem (K : CompactCell) : lexMin K ∈ (K : Set Plane) :=
  (isLexMin_lexMin K).1

theorem positiveSimilarity_coord (s : ℝ) (u z : Plane) (i : Fin 2) :
    positiveSimilarity s u z i = s * (z i - u i) := by
  simp [positiveSimilarity]

/-- A positive similarity is strictly increasing in each coordinate, hence it
transports lexicographic minima. -/
theorem isLexMin_positiveSimilarity {K : Set Plane} {p : Plane} (h : IsLexMin K p)
    {s : ℝ} (hs : 0 < s) (u : Plane) :
    IsLexMin (positiveSimilarity s u '' K) (positiveSimilarity s u p) := by
  refine ⟨⟨p, h.1, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rcases h.2 x hx with hlt | ⟨heq, hle⟩
  · refine Or.inl ?_
    rw [positiveSimilarity_coord, positiveSimilarity_coord]
    exact mul_lt_mul_of_pos_left (by linarith) hs
  · refine Or.inr ⟨?_, ?_⟩
    · rw [positiveSimilarity_coord, positiveSimilarity_coord, heq]
    · rw [positiveSimilarity_coord, positiveSimilarity_coord]
      exact mul_le_mul_of_nonneg_left (by linarith) hs.le

theorem lexMin_transformCell (s : ℝ) (u : Plane) (hs : 0 < s) (K : CompactCell) :
    lexMin (transformCell s u hs K) = positiveSimilarity s u (lexMin K) :=
  isLexMin_unique (isLexMin_lexMin (transformCell s u hs K))
    (isLexMin_positiveSimilarity (isLexMin_lexMin K) hs u)

/-- Meeting a fixed open set is an open condition on nonempty compact sets. -/
theorem isOpen_meets {U : Set Plane} (hU : IsOpen U) :
    IsOpen {K : CompactCell | ((K : Set Plane) ∩ U).Nonempty} := by
  rw [Metric.isOpen_iff]
  rintro K ⟨x, hxK, hxU⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  refine ⟨ε, hε, fun L hL => ?_⟩
  have hfin : Metric.hausdorffEDist (K : Set Plane) (L : Set Plane) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded K.nonempty L.nonempty
      K.isCompact.isBounded L.isCompact.isBounded
  have hdist : Metric.hausdorffDist (K : Set Plane) (L : Set Plane) < ε := by
    have hLK : dist L K < ε := Metric.mem_ball.mp hL
    rw [TopologicalSpace.NonemptyCompacts.dist_eq, Metric.hausdorffDist_comm] at hLK
    exact hLK
  obtain ⟨y, hyL, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hxK hdist hfin
  exact ⟨y, hyL, hball (by rw [Metric.mem_ball, dist_comm]; exact hxy)⟩

theorem measurable_lexMin_coord_zero :
    Measurable fun K : CompactCell => lexMin K 0 := by
  refine measurable_of_Iio fun c => ?_
  have hset : (fun K : CompactCell => lexMin K 0) ⁻¹' Iio c
      = {K : CompactCell | ((K : Set Plane) ∩ {x : Plane | x 0 < c}).Nonempty} := by
    ext K
    constructor
    · intro hK
      exact ⟨lexMin K, lexMin_mem K, hK⟩
    · rintro ⟨x, hxK, hxc⟩
      exact lt_of_le_of_lt ((isLexMin_lexMin K).coord_zero_le hxK) hxc
  rw [hset]
  exact (isOpen_meets (isOpen_lt (by fun_prop) continuous_const)).measurableSet

/-- The second coordinate of the lexicographic minimum is determined by an
approximation criterion; the compactness argument is here. -/
theorem lexMin_coord_one_le_of_approx {K : CompactCell} {c : ℝ}
    (h : ∀ n : ℕ, ∃ x ∈ (K : Set Plane),
      x 0 < lexMin K 0 + 1 / ((n : ℝ) + 1) ∧ x 1 < c + 1 / ((n : ℝ) + 1)) :
    lexMin K 1 ≤ c := by
  choose u hu h1 h2 using h
  obtain ⟨a, haK, φ, hφ, hconv⟩ := K.isCompact.tendsto_subseq hu
  have hδ : Filter.Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hc0 : Continuous fun x : Plane => x 0 := by fun_prop
  have hc1 : Continuous fun x : Plane => x 1 := by fun_prop
  have hlim0 : Filter.Tendsto (fun n => u (φ n) 0) Filter.atTop (nhds (a 0)) :=
    (hc0.tendsto a).comp hconv
  have hlim1 : Filter.Tendsto (fun n => u (φ n) 1) Filter.atTop (nhds (a 1)) :=
    (hc1.tendsto a).comp hconv
  have ha0 : a 0 ≤ lexMin K 0 := by
    refine le_of_tendsto_of_tendsto' hlim0 ?_ fun n => (h1 (φ n)).le
    simpa using
      (Filter.Tendsto.add
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => lexMin K 0) Filter.atTop (nhds (lexMin K 0))) hδ)
  have ha1 : a 1 ≤ c := by
    refine le_of_tendsto_of_tendsto' hlim1 ?_ fun n => (h2 (φ n)).le
    simpa using
      (Filter.Tendsto.add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c)) hδ)
  rcases (isLexMin_lexMin K).2 a haK with hlt | ⟨-, hle⟩
  · exact absurd hlt (not_lt.mpr ha0)
  · exact le_trans hle ha1

theorem measurable_lexMin_coord_one :
    Measurable fun K : CompactCell => lexMin K 1 := by
  refine measurable_of_Iic fun c => ?_
  have hset : (fun K : CompactCell => lexMin K 1) ⁻¹' Iic c
      = ⋂ n : ℕ, ⋃ q : ℚ,
          ({K : CompactCell | (q : ℝ) - 1 / ((n : ℝ) + 1) < lexMin K 0} ∩
            {K : CompactCell | ((K : Set Plane) ∩
              {x : Plane | x 0 < (q : ℝ) ∧ x 1 < c + 1 / ((n : ℝ) + 1)}).Nonempty}) := by
    ext K
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hK n
      have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨q, hq1, hq2⟩ :=
        exists_rat_btwn (show lexMin K 0 < lexMin K 0 + 1 / ((n : ℝ) + 1) by linarith)
      exact ⟨q, by linarith, ⟨lexMin K, lexMin_mem K, hq1, by linarith⟩⟩
    · intro hK
      refine lexMin_coord_one_le_of_approx fun n => ?_
      obtain ⟨q, hq, x, hxK, hx1, hx2⟩ := hK n
      exact ⟨x, hxK, by linarith, hx2⟩
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_
  refine MeasurableSet.inter
    (measurableSet_lt measurable_const measurable_lexMin_coord_zero) ?_
  have h1 : IsOpen {x : Plane | x 0 < (q : ℝ)} :=
    isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {x : Plane | x 1 < c + 1 / ((n : ℝ) + 1)} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopen : IsOpen {x : Plane | x 0 < (q : ℝ) ∧ x 1 < c + 1 / ((n : ℝ) + 1)} :=
    h1.inter h2
  exact (isOpen_meets hopen).measurableSet

theorem measurable_lexMin : Measurable (lexMin : CompactCell → Plane) := by
  have hrw : (lexMin : CompactCell → Plane)
      = fun K => WithLp.toLp 2 (fun i : Fin 2 => lexMin K i) := by
    funext K
    apply WithLp.ofLp_injective 2
    funext i
    rfl
  rw [hrw]
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
    (Measurable.of_eval fun i => ?_)
  fin_cases i
  · exact measurable_lexMin_coord_zero
  · exact measurable_lexMin_coord_one

/-- The representative rule at the level of a raw code slot: the lexicographic
minimum of a present cell, and `0` at an absent label. -/
noncomputable def slotLexMin (o : Option CompactCell) : Plane :=
  Set.indicator {o : Option CompactCell | o.isSome}
    (fun o => lexMin (o.getD Spatial.referenceCell)) o

theorem measurable_slotLexMin : Measurable slotLexMin :=
  (measurable_lexMin.comp Spatial.measurable_slotCell).indicator
    Spatial.measurableSet_slotIsSome

/-- **The canonical measurable cell-representative field.** -/
noncomputable def lexMinField : CellField where
  value := fun e n => slotLexMin (e.val.1 n)
  measurable_value :=
    Measurable.of_eval fun n =>
      measurable_slotLexMin.comp
        ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion))
  absent_zero := fun e n hn => by
    show slotLexMin (e.val.1 n) = 0
    rw [hn, slotLexMin, Set.indicator_of_notMem (by simp)]

theorem lexMinField_at (e : Env) (v : Vertex e.val) :
    lexMinField.at e v = lexMin ((decode e).cell v) := by
  have hv : (e.val.1 v.val).isSome := v.property
  show slotLexMin (e.val.1 v.val) = lexMin ((e.val.1 v.val).get hv)
  generalize hgen : e.val.1 v.val = o at hv ⊢
  cases o with
  | none => exact absurd hv (by simp)
  | some K =>
      rw [slotLexMin, Set.indicator_of_mem
        (show (some K : Option CompactCell) ∈ {o : Option CompactCell | o.isSome} by simp)]
      rfl

theorem isCellRepresentative_lexMinField : IsCellRepresentative lexMinField := by
  intro e v
  rw [lexMinField_at]
  exact lexMin_mem _

theorem representativeCovariant_lexMinField : RepresentativeCovariant lexMinField := by
  intro s u hs e e' relabel hrel v
  rw [lexMinField_at, lexMinField_at, hrel.1 v, lexMin_transformCell]

/-- **Answer to the inhabitation question for the representative clause.**  The
cell-representative existential of `ReflectedInvarianceConclusions` is
satisfiable, with an explicit witness. -/
theorem exists_cellRepresentative_covariant :
    ∃ z : CellField, IsCellRepresentative z ∧ RepresentativeCovariant z :=
  ⟨lexMinField, isCellRepresentative_lexMinField, representativeCovariant_lexMinField⟩

end CellRepresentative

/-! ## The pathwise clauses of `FixedStartConclusions`, isolated -/

/-- The almost-sure pathwise clauses of
`InvarianceMainStatement.FixedStartConclusions` for one fixed choice of the two
lifted end-labelled paths and of the harmonic spatial extension.  The clauses
are copied verbatim from that definition. -/
def PathwiseClockClauses (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (Φ : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane) : Prop :=
  ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
    (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
    (∀ t, collapse (Xexact t ω) = exactAreaPath (decode e) D t ω) ∧
    IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
    IsEndLabeling (decode e) (fun t => Xexact t ω) ∧
    AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω) ∧
    AvoidsSpatialInfinity (decode e) (fun t => Xexact t ω) ∧
    IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
      (fun t => canonicalFastPath (decode e) D hG t ω) ∧
    IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
      (fun t => exponentialAreaPath (decode e) D t ω) ∧
    (∀ v w s t, IsHoldingInterval (decode e) (fun t => Xexact t ω) v w s t →
      (t : ℝ) - s = areaHoldingLength (decode e) v) ∧
    RegularSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
      (fun t => M t ω)

/-- `FixedStartConclusions` is exactly the pathwise clauses, the two recurrence
clauses, the bracket clause and the representative-limit clause, for one common
choice of lifts. -/
theorem fixedStartConclusions_of_parts (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (Φ : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    {Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)}
    {M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane}
    (h1 : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (h2 : ReturnsToEveryVertex (areaSampleLaw (decode e) D hG start)
      (exponentialAreaPath (decode e) D))
    (h3 : ReturnsToEveryVertex (areaSampleLaw (decode e) D hG start)
      (exactAreaPath (decode e) D))
    (h4 : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M)
    (h5 : ∀ z : CellField, IsCellRepresentative z →
      RepresentativePathConclusions e z (areaSampleLaw (decode e) D hG start)
        target Xexp Xexact) :
    FixedStartConclusions e D hG Φ target start :=
  ⟨Xexp, Xexact, M, h1, h2, h3, h4, h5⟩

/-! ## The reduction -/

/-- **Reduction of `ReflectedInvarianceConclusions` to named inputs.**

This is an implication, not a proof of the reflected invariance principle: the
hypotheses `hΦ`, `hdata`, `hlift`, `hreturn`, `hbracket` and `hlimit` are open,
and nothing below certifies any of them.

Two former inputs are **no longer** hypotheses:

* the standard `2`-dimensional Brownian law needed by the target, discharged
  from the sibling project's checked
  `BouRabeeGwynne.exists_standardBrownianProbabilityMeasure` via
  `exists_anisotropicBrownianTarget_of_symmetricPositiveDefinite`;
* entrywise measurability of the rooted bracket in the environment, discharged
  from `hmt` by
  `RootedBracketMeasurability.aestronglyMeasurable_rootedGamma`.

The inputs are, in order:

* `hmt`, `hFE` — the manuscript's own environment hypotheses (mass transport
  and the finite (FE) moment); these are hypotheses of the main theorem itself,
  not open obligations.
* `hΦ` — the harmonic coordinate clause, owned elsewhere.
* `hdata` — almost surely, the canonical construction is a reflected walk for
  both the area clock and the admissible fast clock.
* `hlift` — existence of the end-labelled lifts of both clocks, of the harmonic
  spatial extension, of the two clock homeomorphisms and of the exact holding
  lengths.
* `hreturn` — recurrence at every vertex for both clocks.
* `hbracket` — the ordinary-edge predictable bracket of the harmonic
  martingale, for any lift satisfying the pathwise clauses.
* `hlimit` — the quenched invariance principle: for any lifts satisfying the
  pathwise clauses and any Brownian target whose covariance is the mean
  covariance, the two interpolations converge to that target. -/
theorem reflectedInvarianceConclusions_of_named_inputs
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ)
    (hdata : ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG)
    (hlift : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M)
    (hreturn : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ReturnsToEveryVertex (areaSampleLaw (decode e) D hG ⟨n, hn⟩)
              (exponentialAreaPath (decode e) D) ∧
            ReturnsToEveryVertex (areaSampleLaw (decode e) D hG ⟨n, hn⟩)
              (exactAreaPath (decode e) D))
    (hbracket : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG ⟨n, hn⟩) M)
    (hlimit : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            ∀ target : AnisotropicBrownianTarget,
              target.covariance = meanCovariance ν Φ →
              ∀ z : CellField, IsCellRepresentative z →
                RepresentativePathConclusions e z
                  (areaSampleLaw (decode e) D hG ⟨n, hn⟩) target Xexp Xexact) :
    ReflectedInvarianceConclusions ν := by
  have hνne : ν ≠ 0 := by
    intro h
    have hu : ν Set.univ = 1 := measure_univ
    rw [h] at hu
    simp at hu
  have hsub : ∀ᵐ e ∂ν, UniformlySublinearCorrector (decode e) (Φ.at e) := by
    filter_upwards [hΦ.2.2.2.2.1] with e he using he.2.2.2.2.1
  have hdiam : ∀ᵐ e ∂ν, SubmacroscopicDiameters (decode e) :=
    ae_submacroscopicDiameters ν hmt hFE
  have hint : IntegrableBracket ν Φ :=
    integrableBracket_of_aestronglyMeasurable ν Φ
      (fun i j =>
        RootedBracketMeasurability.aestronglyMeasurable_rootedGamma ν hmt Φ i j)
      hΦ.2.2.2.1
  have hSPD : SymmetricPositiveDefinite (meanCovariance ν Φ) :=
    symmetricPositiveDefinite_meanCovariance ν hνne hmt Φ hΦ.1 hint hsub hdiam
  obtain ⟨target, htarget⟩ :=
    exists_anisotropicBrownianTarget_of_symmetricPositiveDefinite _ hSPD
  refine ⟨Φ, target, hΦ, hint, htarget, exists_cellRepresentative_covariant, ?_⟩
  refine ae_environmentProcessConclusions_of_ae_fixedStartConclusions hdata ?_
  intro n
  filter_upwards [hlift n, hreturn n, hbracket n, hlimit n] with e h1 h2 h3 h4
  intro hn hnt D hG hdat
  haveI : Nontrivial (Vertex e.val) := hnt
  obtain ⟨Xexp, Xexact, M, hP⟩ := h1 hn hnt D hG hdat
  exact fixedStartConclusions_of_parts e D hG Φ target ⟨n, hn⟩ hP
    (h2 hn hnt D hG hdat).1 (h2 hn hnt D hG hdat).2
    (h3 hn hnt D hG hdat Xexp Xexact M hP)
    (h4 hn hnt D hG hdat Xexp Xexact M hP target htarget)

end ReflectedGMS.InvarianceAssembly
