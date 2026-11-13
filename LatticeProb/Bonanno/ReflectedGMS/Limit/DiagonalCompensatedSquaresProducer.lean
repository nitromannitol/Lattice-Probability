/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.DiagonalCompensatedSquaresProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.DiagonalCompensatedSquares
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoordinateLocallySquareIntegrableWeld
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedDomainDensity

/-!
# Bracket atom 2 DISCHARGED: `DiagonalCompensatedSquares` from `MassTransport`, (FE) and `hΦ`

`ae_diagonalCompensatedSquares` proves `BracketClausesScalarReduction.DiagonalCompensatedSquares`
almost surely in the environment, for every exhaustion, connectivity witness, start and pinned
lift satisfying the pathwise clock clauses, from `MassTransport ν`, the (FE) moment and
`IsHarmonicCoordinate ν Φ` alone — in the exact shape of the `hsq` binder of
`CoordinateLocallySquareIntegrableWeld.hbracket_of_ae_diagonalCompensatedSquares`.  Hence
`hbracket_of_isHarmonicCoordinate`: **the `hbracket` input of the invariance assembly is proved.**

The environment step is `DiagonalCompensatedSquaresProof.compensatedSquareClause_of_radii`, fed
with atom 1's radii, comparison constants and log-cutoff boundedness (copied from
`CoordinateLocallySquareIntegrable.ae_coordinateLocallySquareIntegrable`), the occupation
finiteness `CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite`, and **globally
bounded cutoffs**:

* `exists_bounded_cutoff` — the step-(a) cutoff truncated at height `⌈K'⌉` (`boundedTruncation`, a
  normal contraction, so it stays in the fast Hilbert domain); it still agrees with `Φ · i` on
  `{‖z‖ ≤ R}` (where `|Φ · i| ≤ K'`), hence still satisfies the variational test by
  `LocalHarmonicClock.hU_of_fullRectangleOrthogonality`, which reads only that agreement;
* `sum_cutoff` — the cutoff of `Φ · i + Φ · j` is the sum of the two cutoffs; the test is linear
  (`dirichletForm_add_left`).

No hypothesis is `Summable (cellArea …)` or a global `HasFiniteEnergy`; the only summable speed is
the canonical `fastSpeed`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.DiagonalCompensatedSquaresProof

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk FullNetworkForm
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.BracketClausesScalarReduction
open ReflectedGMS.CoordinateLocallySquareIntegrableProof

/-! ## Bounded cutoffs -/

/-- Truncation at a height above `|x|` does nothing. -/
theorem boundedTruncation_eq_of_abs_le {n : ℕ} {x : ℝ} (hx : |x| ≤ n) :
    boundedTruncation n x = x := by
  have hxi := abs_le.1 hx
  simp [boundedTruncation, Set.coe_projIcc, hxi.1, hxi.2]

/-- The decoded value of a sum of Hilbert-domain vectors. -/
theorem unweight_valueInclusion_add {V : Type*} {G : ConductanceGraph V} {m : V → ℝ}
    (U W : hilbertDomain G m) :
    unweight m (valueInclusion G m (U + W)) =
      unweight m (valueInclusion G m U) + unweight m (valueInclusion G m W) := by
  funext x
  simp only [map_add, unweight, lp.coeFn_add, Pi.add_apply]
  ring

/-- **A globally bounded cutoff.**  Truncating a cutoff of `Φ · i` at radius `r` at a height above
the bound `K'` of `Φ` on `{‖z‖ ≤ r}` keeps the agreement there, keeps the variational test, and
makes the cutoff globally bounded. -/
theorem exists_bounded_cutoff (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (i : Fin 2) {r : ℝ} (hr : 0 < r)
    (hD : ∀ v : Vertex e.val, Hits (decode e) (Metric.closedBall (0 : Plane) r) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ r / 100)
    (hΦo : FullRectangleOrthogonality (decode e) (Φ.at e))
    {K' : ℝ} (hΦB : ∀ v : Vertex e.val, ‖lexMinField.at e v‖ ≤ r → ‖Φ.at e v‖ ≤ K')
    (U : hilbertDomain (decode e).graph (fastSpeed e D hG))
    (hUeq : Set.EqOn (unweight (fastSpeed e D hG)
        (valueInclusion (decode e).graph (fastSpeed e D hG) U))
      (fun v => (Φ.at e) v i) (region e r)) :
    ∃ U' : hilbertDomain (decode e).graph (fastSpeed e D hG), ∃ C : ℝ,
      Set.EqOn (unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U'))
        (fun v => (Φ.at e) v i) (region e r) ∧
      (∀ x, |unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U') x| ≤ C) ∧
      ∀ w : hilbertDomain (decode e).graph (fastSpeed e D hG),
        (∀ x ∉ region e (r / 2),
          unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) w) x = 0) →
        (decode e).graph.dirichletForm
          (unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U'))
          (unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) w)) = 0 := by
  have hm : ∀ v, 0 < fastSpeed e D hG v := (summableFastRate_spec e D hG).2.2.1
  have hqL2 : HasSpeedL2 (fastSpeed e D hG) (unweight (fastSpeed e D hG)
      (valueInclusion (decode e).graph (fastSpeed e D hG) U)) :=
    hasSpeedL2_unweight _ hm _
  have hqE : (decode e).graph.HasFiniteEnergy (unweight (fastSpeed e D hG)
      (valueInclusion (decode e).graph (fastSpeed e D hG) U)) :=
    hilbertDomain_hasFiniteEnergy _ _ U
  have hL2 := boundedTruncation_hasSpeedL2 (fastSpeed e D hG) _ hqL2 ⌈K'⌉₊
  have hE := boundedTruncation_hasFiniteEnergy (decode e).graph _ hqE ⌈K'⌉₊
  have hU' : unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG)
      (inHilbertDomain (decode e).graph (fastSpeed e D hG) hm
        (boundedTruncation ⌈K'⌉₊ ∘ unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U)) hL2 hE)) =
      boundedTruncation ⌈K'⌉₊ ∘ unweight (fastSpeed e D hG)
        (valueInclusion (decode e).graph (fastSpeed e D hG) U) :=
    unweight_weightedValue (fastSpeed e D hG) hm _ hL2
  have hEq' : Set.EqOn (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph
      (fastSpeed e D hG) (inHilbertDomain (decode e).graph (fastSpeed e D hG) hm
        (boundedTruncation ⌈K'⌉₊ ∘ unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U)) hL2 hE)))
      (fun v => (Φ.at e) v i) (region e r) := by
    intro v hv
    rw [hU']
    have hqv : unweight (fastSpeed e D hG)
        (valueInclusion (decode e).graph (fastSpeed e D hG) U) v = (Φ.at e) v i := hUeq hv
    have habs : |unweight (fastSpeed e D hG)
        (valueInclusion (decode e).graph (fastSpeed e D hG) U) v| ≤ (⌈K'⌉₊ : ℝ) := by
      rw [hqv]
      calc |(Φ.at e) v i| ≤ ‖(Φ.at e) v‖ := by
            have := PiLp.norm_apply_le (p := 2) ((Φ.at e) v) i
            simpa [Real.norm_eq_abs] using this
        _ ≤ K' := hΦB v hv
        _ ≤ (⌈K'⌉₊ : ℝ) := Nat.le_ceil K'
    show boundedTruncation ⌈K'⌉₊ (unweight (fastSpeed e D hG)
      (valueInclusion (decode e).graph (fastSpeed e D hG) U) v) = (Φ.at e) v i
    rw [boundedTruncation_eq_of_abs_le habs, hqv]
  refine ⟨inHilbertDomain (decode e).graph (fastSpeed e D hG) hm
      (boundedTruncation ⌈K'⌉₊ ∘ unweight (fastSpeed e D hG)
        (valueInclusion (decode e).graph (fastSpeed e D hG) U)) hL2 hE,
    (⌈K'⌉₊ : ℝ), hEq', fun x => ?_, ?_⟩
  · rw [hU']
    exact abs_boundedTruncation_le _ _
  · exact LocalHarmonicClock.hU_of_fullRectangleOrthogonality (decode_geometry e)
      (isCellRepresentative_lexMinField e) hΦo hr hD (fastSpeed e D hG) i _ hEq'

/-- **The cutoff of a sum is the sum of the cutoffs**: agreement, bound and the (linear)
variational test all add. -/
theorem sum_cutoff {V : Type*} {G : ConductanceGraph V} {m : V → ℝ} {A B : Set V}
    {u₁ u₂ : V → ℝ} (U₁ U₂ : hilbertDomain G m) {C₁ C₂ : ℝ}
    (h₁ : Set.EqOn (unweight m (valueInclusion G m U₁)) u₁ B)
    (h₂ : Set.EqOn (unweight m (valueInclusion G m U₂)) u₂ B)
    (hb₁ : ∀ x, |unweight m (valueInclusion G m U₁) x| ≤ C₁)
    (hb₂ : ∀ x, |unweight m (valueInclusion G m U₂) x| ≤ C₂)
    (hU₁ : ∀ w : hilbertDomain G m, (∀ x ∉ A, unweight m (valueInclusion G m w) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U₁))
        (unweight m (valueInclusion G m w)) = 0)
    (hU₂ : ∀ w : hilbertDomain G m, (∀ x ∉ A, unweight m (valueInclusion G m w) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U₂))
        (unweight m (valueInclusion G m w)) = 0) :
    Set.EqOn (unweight m (valueInclusion G m (U₁ + U₂))) (u₁ + u₂) B ∧
      (∀ x, |unweight m (valueInclusion G m (U₁ + U₂)) x| ≤ C₁ + C₂) ∧
      ∀ w : hilbertDomain G m, (∀ x ∉ A, unweight m (valueInclusion G m w) x = 0) →
        G.dirichletForm (unweight m (valueInclusion G m (U₁ + U₂)))
          (unweight m (valueInclusion G m w)) = 0 := by
  rw [unweight_valueInclusion_add]
  refine ⟨fun x hx => ?_, fun x => ?_, fun w hw => ?_⟩
  · simp only [Pi.add_apply]
    rw [h₁ hx, h₂ hx]
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hb₁ x) (hb₂ x))
  · rw [G.dirichletForm_add_left (hilbertDomain_hasFiniteEnergy G m U₁)
      (hilbertDomain_hasFiniteEnergy G m U₂) (hilbertDomain_hasFiniteEnergy G m w),
      hU₁ w hw, hU₂ w hw, add_zero]

/-! ## The ν-level producer -/

/-- **Bracket atom 2, from the manuscript's hypotheses alone.**  Almost surely in the environment,
for every exhaustion, connectivity witness and start carrying the environment walk data, and every
pinned lift `M` satisfying the pathwise clock clauses, the diagonal compensated squares of the
coordinates and of their sums are local martingales of the completed area filtration.  The inputs
are `MassTransport ν`, the (FE) moment and `IsHarmonicCoordinate ν Φ`. -/
theorem ae_diagonalCompensatedSquares (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          DiagonalCompensatedSquares e D hG Φ start M := by
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [LocalHarmonicClockEnvironment.ae_exists_cutoff_and_hU_of_isHarmonicCoordinate
      ν hmt hFE Φ hΦ,
    AlmostSureCutoffBounds.ae_exists_diameter_bound ν hmt hFE.ne,
    AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax,
    hΦ.2.2.2.2.1,
    CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite ν hmt hFE Φ hΦ]
    with e hcutE hdiam hlog hΦe hoccE
  intro hnt D hG hdat start Xexp Xexact M hpcc
  letI := hnt
  obtain ⟨Rc, -, hcutR⟩ := hcutE
  obtain ⟨Rd, -, hdiamR⟩ := hdiam
  obtain ⟨Rs, -, hsub⟩ := hΦe.2.2.2.2.2 (lexMinField.at e) (isCellRepresentative_lexMinField e)
    (1 / 10) (by norm_num)
  obtain ⟨hmin, hrate, hwalkA, -⟩ := id hdat
  obtain ⟨r₀, C, hr₀, hC, ho, hD0, hW⟩ := hlog (lexMinField.at e) start
  have hbdd := LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime
    (decode e) (decode_geometry e) (lexMinField.at e) (isCellRepresentative_lexMinField e)
    (areaPF e D hG) hwalkA hrate start hr₀ hC ho hD0 hW
  have hz : CellRepresentatives (decode e) (lexMinField.at e) :=
    isCellRepresentative_lexMinField e
  have hocc := hoccE hnt D hG hdat start
  -- the radii (atom 1's)
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = max (max Rc Rd) (max (2 * Rs)
      (max 6 (2 * ‖lexMinField.at e start‖))) := ⟨_, rfl⟩
  have hXc : Rc ≤ X := by rw [hXdef]; exact le_max_of_le_left (le_max_left _ _)
  have hXd : Rd ≤ X := by rw [hXdef]; exact le_max_of_le_left (le_max_right _ _)
  have hXs : 2 * Rs ≤ X := by rw [hXdef]; exact le_max_of_le_right (le_max_left _ _)
  have hX6 : 6 ≤ X := by
    rw [hXdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hXo : 2 * ‖lexMinField.at e start‖ ≤ X := by
    rw [hXdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  obtain ⟨Rf, hRf⟩ : ∃ Rf : ℕ → ℝ, ∀ n, Rf n = ((⌈X⌉₊ + 1 + n : ℕ) : ℝ) :=
    ⟨fun n => ((⌈X⌉₊ + 1 + n : ℕ) : ℝ), fun _ => rfl⟩
  have hRge : ∀ n : ℕ, X ≤ Rf n := by
    intro n
    rw [hRf n]
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : ((⌈X⌉₊ : ℕ) : ℝ) ≤ ((⌈X⌉₊ + 1 + n : ℕ) : ℝ) := by
      exact_mod_cast (by omega : ⌈X⌉₊ ≤ ⌈X⌉₊ + 1 + n)
    linarith
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ℕ → ℝ, ∀ n, Kf n = Rf n / 2 + Rf n / 20 :=
    ⟨fun n => Rf n / 2 + Rf n / 20, fun _ => rfl⟩
  obtain ⟨Kf', hKf'⟩ : ∃ Kf' : ℕ → ℝ, ∀ n, Kf' n = Rf n + Rf n / 10 :=
    ⟨fun n => Rf n + Rf n / 10, fun _ => rfl⟩
  have hsubv : ∀ (ρ : ℝ), Rs ≤ ρ → ∀ v : Vertex e.val, ‖lexMinField.at e v‖ ≤ ρ →
      ‖(Φ.at e) v - lexMinField.at e v‖ ≤ 1 / 10 * ρ := by
    intro ρ hρ v hv
    refine hsub ρ hρ v ⟨lexMinField.at e v, hz v, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  -- the radius hypotheses of the environment step
  have hRpos : ∀ n, 0 < Rf n := fun n => by have := hRge n; linarith
  have hRmono : Monotone Rf := fun a b hab => by
    rw [hRf a, hRf b]
    exact_mod_cast (by omega : ⌈X⌉₊ + 1 + a ≤ ⌈X⌉₊ + 1 + b)
  have hRtop : ∀ b : ℝ, ∃ n, b ≤ Rf n := fun b => ⟨⌈b⌉₊, by
    rw [hRf]
    have h1 : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    have h2 : ((⌈b⌉₊ : ℕ) : ℝ) ≤ ((⌈X⌉₊ + 1 + ⌈b⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast (by omega : ⌈b⌉₊ ≤ ⌈X⌉₊ + 1 + ⌈b⌉₊)
    linarith⟩
  have hDn : ∀ (n : ℕ) (v : Vertex e.val),
      Hits (decode e) (Metric.closedBall (0 : Plane) (Rf n)) v →
        Metric.diam ((decode e).cell v : Set Plane) ≤ Rf n / 100 :=
    fun n v hv => hdiamR (Rf n) (by have := hRge n; linarith) v hv
  have hzΦ : ∀ (n : ℕ) (v : Vertex e.val),
      ‖Φ.at e v‖ ≤ Kf n + 2 → ‖lexMinField.at e v‖ ≤ Rf n := by
    intro n v hv
    rw [hKf n] at hv
    have hRn := hRge n
    by_cases hsmall : ‖lexMinField.at e v‖ ≤ Rs
    · linarith
    · push Not at hsmall
      have h1 := hsubv (‖lexMinField.at e v‖) hsmall.le v le_rfl
      have h2 := norm_sub_norm_le (lexMinField.at e v) ((Φ.at e) v)
      rw [norm_sub_rev] at h2
      linarith
  have hΦA : ∀ (n : ℕ) (v : Vertex e.val),
      ‖lexMinField.at e v‖ ≤ Rf n / 2 → ‖Φ.at e v‖ ≤ Kf n := by
    intro n v hv
    rw [hKf n]
    have hRn := hRge n
    have h1 := hsubv (Rf n / 2) (by linarith) v hv
    have h2 := norm_sub_norm_le ((Φ.at e) v) (lexMinField.at e v)
    linarith
  have hΦB : ∀ (n : ℕ) (v : Vertex e.val),
      ‖lexMinField.at e v‖ ≤ Rf n → ‖Φ.at e v‖ ≤ Kf' n := by
    intro n v hv
    rw [hKf' n]
    have hRn := hRge n
    have h1 := hsubv (Rf n) (by linarith) v hv
    have h2 := norm_sub_norm_le ((Φ.at e) v) (lexMinField.at e v)
    linarith
  have hstart : ‖lexMinField.at e start‖ ≤ Rf 0 / 2 := by
    have hR0 := hRge 0
    linarith
  -- globally bounded cutoffs of each coordinate
  have hcutB : ∀ (i : Fin 2) (n : ℕ),
      ∃ U : hilbertDomain (decode e).graph (fastSpeed e D hG), ∃ Cb : ℝ,
        Set.EqOn (unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U))
          (fun v => (Φ.at e) v i) (region e (Rf n)) ∧
        (∀ x, |unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U) x| ≤ Cb) ∧
        ∀ w : hilbertDomain (decode e).graph (fastSpeed e D hG),
          (∀ x ∉ region e (Rf n / 2),
            unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) w) x = 0) →
          (decode e).graph.dirichletForm
            (unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) U))
            (unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) w)) = 0 := by
    intro i n
    have hcut0 : ∃ U : hilbertDomain (decode e).graph (fastSpeed e D hG),
        Set.EqOn (unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U))
          (fun v => (Φ.at e) v i) (region e (Rf n)) := by
      have hRn := hRge n
      rw [hRf n] at hRn ⊢
      obtain ⟨U, hU1, -⟩ := hcutR hnt D hG hdat i (⌈X⌉₊ + 1 + n) (by linarith)
      exact ⟨U, hU1⟩
    obtain ⟨U, hUeq⟩ := hcut0
    exact exists_bounded_cutoff e D hG Φ i (hRpos n) (hDn n) hΦe.2.2.1.1 (hΦB n) U hUeq
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · exact compensatedSquareClause_of_radii e D hG hdat Φ start Xexp Xexact M hpcc
      (ℓ := fun x : Plane => x i) (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i)
      (u := fun v => (Φ.at e) v i) (fun v => rfl) (hocc.1 i)
      Rf hRpos hRmono hRtop hDn Kf hzΦ hΦA hstart (hcutB i) hbdd
  · refine compensatedSquareClause_of_radii e D hG hdat Φ start Xexp Xexact M hpcc
      (ℓ := fun x : Plane => x i + x j)
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).add
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j))
      (u := (fun v => (Φ.at e) v i) + (fun v => (Φ.at e) v j)) (fun v => rfl) (hocc.2 i j)
      Rf hRpos hRmono hRtop hDn Kf hzΦ hΦA hstart (fun n => ?_) hbdd
    obtain ⟨U₁, C₁, h₁, hb₁, hU₁⟩ := hcutB i n
    obtain ⟨U₂, C₂, h₂, hb₂, hU₂⟩ := hcutB j n
    exact ⟨U₁ + U₂, C₁ + C₂, sum_cutoff U₁ U₂ h₁ h₂ hb₁ hb₂ hU₁ hU₂⟩

/-! ## `hbracket` is proved -/

end ReflectedGMS.DiagonalCompensatedSquaresProof
