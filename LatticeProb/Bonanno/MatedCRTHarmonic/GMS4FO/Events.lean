/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.Events at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.BridgeOut
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaLimit
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.OpenSupport
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift

/-!
# The localized failure event as a set of local data

Source: [18], Lemma 4.3: the localized quantities at `z`
are a.s. determined by `h|_V` (and the space-filling SLE) on the event `B̄^ε_z ⊂ V`.

`failSet γ V ε D f A tol R r ⊆ DistOn V × C(ℝ, ℂ)` is the set of pairs `(h|_V, c)` (restricted field, Lebesgue-time
curve) such that the dyadic GMC approximations of (some field with this restriction) have a vague limit `ν` on `V`
and the localized good event `LocalGood ν c ε D f A tol R r` fails. Deterministic facts:

* `mem_failSet_of_globalFail` (the γ-cone side): if `c ∘ ψ` is parametrized by the area `μ` of `h` (`BridgeHyp`),
  failure of the geometric good event puts `(h|_V, c)` in `failSet` (the witness is `h`, the bridge
  `localGood_iff_globalGood`);
* `mem_failSet_translate` (recentring): if `(h(· + z₀)|_V, c(τ_{z₀} + ·) − z₀) ∈ failSet` for `(D, f, R)`, then
  `(h|_{V+z₀}, c) ∈ failSet` for `(D + z₀, f(· − z₀), R + z₀)` (translate the witness: exact identities
  `lqgAreaApprox_affineComp_one`, `restrictTo_affineComp_neg`, and `localGood_shiftCurve_iff`);
* `globalFail_of_mem_failSet` (the 0-cone side): conversely, a witness with the restriction of a field whose area
  `μ` parametrizes `c ∘ ψ` has the local limit `μ|_V` (`isVagueLimitOn_eq_restrict`), so the geometric good event
  fails.
The measurability of `failSet` under the bundle laws is the measurable form of Lemma 4.3 (named input, see
`GMS4FO/Assembly.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic LQGMetric

/-- **The localized failure set** of [18] Lemma 4.3: restricted field and Lebesgue-time curve for which the
GMC on `V` (vague limit of the dyadic approximations of a field with this restriction) fails the localized good
event (4.39)–(4.40). -/
def failSet (γ : ℝ) (V : Opens ℂ) (ε : ℝ) (D : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ) :
    Set (DistOn V × C(ℝ, ℂ)) :=
  {p | ∃ h : DistC, restrictTo V h = p.1 ∧ ∃ ν : Measure ℂ,
    QuantumZipper.IsVagueLimitOn (V : Set ℂ) (CellScaling.lqgAreaApprox γ h) ν ∧
      ¬ LocalGood ν p.2 ε D f A tol R r}

/-! ### Approximations and restrictions under translation -/

/-- The translation `x ↦ x − b` as a homeomorphism. -/
def subHomeo (b : ℂ) : ℂ ≃ₜ ℂ := Homeomorph.subRight b

@[simp] theorem subHomeo_apply (b x : ℂ) : subHomeo b x = x - b := rfl

/-- **The dyadic GMC approximations of `h(· + b)` are those of `h` translated by `−b`** (exact). -/
theorem lqgAreaApprox_affineComp_one (γ : ℝ) (h : DistC) (b : ℂ) (k : ℕ) :
    CellScaling.lqgAreaApprox γ (affineComp 1 b h) k = (CellScaling.lqgAreaApprox γ h k).map (subHomeo b) := by
  ext A hA
  rw [Measure.map_apply (subHomeo b).measurable hA, CellScaling.lqgAreaApprox, CellScaling.lqgAreaApprox,
    withDensity_apply _ hA, withDensity_apply _ ((subHomeo b).measurable hA)]
  simp only [GM.circleAvg_affineComp_one_at]
  have h1 := setLIntegral_translate (-b) ((subHomeo b) ⁻¹' A) (fun z => ENNReal.ofReal
    (CellScaling.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg h (CellScaling.dyadicScale k) z)))
  have hset : (fun z => z + -b) '' ((subHomeo b) ⁻¹' A) = A := by
    ext u
    simp only [mem_image, mem_preimage, subHomeo_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [sub_eq_add_neg] using hx
    · intro hu
      exact ⟨u + b, by simpa using hu, by ring⟩
  rw [hset] at h1
  rw [h1]
  congr 1
  funext w
  congr 3
  ring

/-- Restrictions commute with translations. -/
theorem restrictTo_affineComp_neg {U V : Opens ℂ} {z₀ : ℂ} (hUV : ∀ y : ℂ, y ∈ V ↔ y + z₀ ∈ U)
    {h h' : DistC} (heq : restrictTo V h' = restrictTo V (affineComp 1 z₀ h)) :
    restrictTo U (affineComp 1 (-z₀) h') = restrictTo U h := by
  have hUV' : ∀ y : ℂ, y ∈ V ↔ (1 : ℝ) • y + z₀ ∈ U := by simpa using hUV
  refine DFunLike.ext _ _ fun ψ => ?_
  rw [GM.restrictTo_apply_eq_scale one_pos hUV' h ψ,
    GM.restrictTo_apply_eq_scale one_pos hUV' (affineComp 1 (-z₀) h') ψ]
  have hcomp : affineComp 1 z₀ (affineComp 1 (-z₀) h') = h' := by
    rw [GM.affineComp_comp one_ne_zero one_ne_zero]
    simpa using GM.affineComp_one_zero h'
  rw [hcomp, heq]

/-- A global vague limit restricts to a vague limit on `V`. -/
theorem isVagueLimitOn_restrict_of_global {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hμ : CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) (V : Opens ℂ) :
    QuantumZipper.IsVagueLimitOn (V : Set ℂ) (CellScaling.lqgAreaApprox γ h) (μ.restrict V) := by
  have hglob := LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mp hμ
  have := QuantumZipper.AtomlessUncond.isVagueLimitOn_restrict V.isOpen (subset_univ _) hglob
  have e : MoTPort.areaApproxC γ h = CellScaling.lqgAreaApprox γ h :=
    funext fun k => (LQGCone.lqgAreaApprox_eq_areaApproxC γ h k).symm
  rwa [e] at this

/-! ### The γ-cone side -/

/-- **Failure of the geometric good event puts the local data in `failSet`.** -/
theorem mem_failSet_of_globalFail {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hμ : CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) {c : C(ℝ, ℂ)} {ψ : ℝ ≃o ℝ}
    {V : Opens ℂ} (H : BridgeHyp μ c ψ V) {ε : ℝ} (hε : 0 < ε) {D R : Set ℂ} {f : ℂ → ℝ}
    {A tol r : ℝ} (hr : 0 ≤ r) (hDR : D ⊆ R) (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V)
    (hD : MeasurableSet D) (hfail : ¬ GlobalGood (c ∘ ψ) ε D f A tol R r) :
    (restrictTo V h, c) ∈ failSet γ V ε D f A tol R r := by
  refine ⟨h, rfl, μ.restrict V, isVagueLimitOn_restrict_of_global hμ V, ?_⟩
  rwa [H.localGood_iff_globalGood hε hr hDR hRV hD]

/-! ### Recentring -/

/-- **Recentring of the failure set.** -/
theorem mem_failSet_translate {γ : ℝ} {U V : Opens ℂ} {z₀ : ℂ}
    (hUV : ∀ y : ℂ, y ∈ V ↔ y + z₀ ∈ U) {h : DistC} {c : C(ℝ, ℂ)} (hc : HasFirstVisits c)
    {ε : ℝ} {D R : Set ℂ} {f : ℂ → ℝ} {A tol r : ℝ}
    (hmem : (restrictTo V (affineComp 1 z₀ h), MatedCRT.affineReroot z₀ 1 0 c) ∈
      failSet γ V ε D f A tol R r) :
    (restrictTo U h, c) ∈ failSet γ U ε ((fun z => z + z₀) '' D) (fun w => f (w - z₀)) A tol
      ((fun z => z + z₀) '' R) r := by
  obtain ⟨h', hres, ν, hν, hfail⟩ := hmem
  refine ⟨affineComp 1 (-z₀) h', restrictTo_affineComp_neg hUV hres, ν.map (subHomeo (-z₀)), ?_, ?_⟩
  · have hT := LQGCone.isVagueLimitOn_map_homeomorph V.isOpen hν (subHomeo (-z₀))
    have himg : (subHomeo (-z₀)) '' (V : Set ℂ) = (U : Set ℂ) := by
      ext u
      simp only [mem_image, subHomeo_apply, sub_neg_eq_add, SetLike.mem_coe]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hUV y).1 hy
      · intro hu
        exact ⟨u - z₀, (hUV _).2 (by simpa using hu), by ring⟩
    rw [himg] at hT
    have happrox : (fun k => (CellScaling.lqgAreaApprox γ h' k).map (subHomeo (-z₀))) =
        CellScaling.lqgAreaApprox γ (affineComp 1 (-z₀) h') :=
      funext fun k => (lqgAreaApprox_affineComp_one γ h' (-z₀) k).symm
    rwa [happrox] at hT
  · intro hgood
    apply hfail
    have hmap : (ν.map (subHomeo (-z₀))).map (subEquiv z₀) = ν := by
      rw [Measure.map_map (subEquiv z₀).measurable (subHomeo (-z₀)).measurable]
      convert Measure.map_id
      funext x
      simp
    have := (localGood_shiftCurve_iff (ν.map (subHomeo (-z₀))) hc (GMS4b.hitTime c z₀) z₀ ε D f A tol
      R r).2 hgood
    rw [hmap] at this
    rwa [affineReroot_one_eq_shiftCurve]

/-! ### The 0-cone side -/

/-- Equal restrictions to `V` give equal restrictions to any smaller open set. -/
theorem restrictTo_eq_of_le {V W : Opens ℂ} (hWV : W ≤ V) {a b : DistC}
    (hab : restrictTo V a = restrictTo V b) : restrictTo W a = restrictTo W b := by
  refine DFunLike.ext _ _ fun ψ => ?_
  have e : TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := ⊤) ψ =
      TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤)
        (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := V) ψ) := by
    ext x
    simp [TestFunction.monoCLM_apply, hWV]
  change a (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := ⊤) ψ) =
    b (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := ⊤) ψ)
  rw [e]
  exact DFunLike.congr_fun hab _

/-- A vague limit on `V` of the approximations of a field with the restriction of `h` is the restriction of the
global limit of `h`. -/
theorem isVagueLimitOn_eq_restrict {γ : ℝ} {V : Opens ℂ} {h h' : DistC}
    (hres : restrictTo V h' = restrictTo V h) {μ ν : Measure ℂ}
    (hμ : CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ)
    (hν : QuantumZipper.IsVagueLimitOn (V : Set ℂ) (CellScaling.lqgAreaApprox γ h') ν) :
    ν = μ.restrict V := by
  have hlimμ := isVagueLimitOn_restrict_of_global hμ V
  refine QuantumZipper.isVagueLimitOn_unique V.isOpen ⟨hν.1, hν.2.1, fun g hg hgc hgV => ?_⟩ hlimμ
  -- the approximations of `h` and `h'` agree on a thickening of the support of `g`
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨δ, hδ, hδV⟩ : ∃ δ > 0, thickening (2 * δ) (tsupport g) ⊆ V := by
    rcases (tsupport g).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by rw [he, thickening_empty]; exact empty_subset _⟩
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open V.isOpen hgV
    exact ⟨δ / 2, by positivity, by rw [show 2 * (δ / 2) = δ by ring]; exact hsub⟩
  set W : Opens ℂ := ⟨thickening δ (tsupport g), isOpen_thickening⟩
  have hWδ : (GMS4c.thickOpen W δ : Set ℂ) ⊆ V := by
    intro x hx
    apply hδV
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    obtain ⟨w, hw, hyw⟩ := mem_thickening_iff.1 hy
    exact mem_thickening_iff.2 ⟨w, hw, by
      calc dist x w ≤ dist x y + dist y w := dist_triangle _ _ _
        _ < δ + δ := add_lt_add hxy hyw
        _ = 2 * δ := by ring⟩
  have hres' : restrictTo (GMS4c.thickOpen W δ) h' = restrictTo (GMS4c.thickOpen W δ) h :=
    restrictTo_eq_of_le hWδ hres
  obtain ⟨K, hKk⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt hδ
  have happrox : ∀ k, K ≤ k →
      (CellScaling.lqgAreaApprox γ h' k).restrict W = (CellScaling.lqgAreaApprox γ h k).restrict W := by
    intro k hk
    have hsmall : CellScaling.dyadicScale k < δ := by
      rw [LQGCone.dyadicScale_eq_radius]
      exact hKk k hk
    rw [← GMS4c.localAreaApprox_restrictTo γ W δ h' k hsmall,
      ← GMS4c.localAreaApprox_restrictTo γ W δ h k hsmall, hres']
  have hgW : tsupport g ⊆ (W : Set ℂ) := self_subset_thickening hδ _
  have hg0 : ∀ z ∉ (W : Set ℂ), g z = 0 :=
    fun z hz => image_eq_zero_of_notMem_tsupport fun hzs => hz (hgW hzs)
  have hevent : (fun k => ∫ z, g z ∂(CellScaling.lqgAreaApprox γ h' k)) =ᶠ[atTop]
      (fun k => ∫ z, g z ∂(CellScaling.lqgAreaApprox γ h k)) := by
    filter_upwards [eventually_ge_atTop K] with k hk
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := CellScaling.lqgAreaApprox γ h' k) hg0,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := CellScaling.lqgAreaApprox γ h k) hg0,
      happrox k hk]
  exact (hν.2.2 g hg hgc hgV).congr' hevent

/-- **The 0-cone side**: membership in `failSet` of the local data of a field whose area parametrizes `c ∘ ψ`
means failure of the geometric good event. -/
theorem globalFail_of_mem_failSet {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hμ : CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) {c : C(ℝ, ℂ)} {ψ : ℝ ≃o ℝ}
    {V : Opens ℂ} (H : BridgeHyp μ c ψ V) {ε : ℝ} (hε : 0 < ε) {D R : Set ℂ} {f : ℂ → ℝ}
    {A tol r : ℝ} (hr : 0 ≤ r) (hDR : D ⊆ R) (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V)
    (hD : MeasurableSet D) (hmem : (restrictTo V h, c) ∈ failSet γ V ε D f A tol R r) :
    ¬ GlobalGood (c ∘ ψ) ε D f A tol R r := by
  obtain ⟨h', hres, ν, hν, hfail⟩ := hmem
  have hνeq := isVagueLimitOn_eq_restrict hres hμ hν
  rw [hνeq] at hfail
  rwa [H.localGood_iff_globalGood hε hr hDR hRV hD] at hfail

end MatedCRTHarmonic.GMS4FO
