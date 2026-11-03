/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4M1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InRep
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer3B
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LM Lemma 3.1, canonical nesting: the two Gaussian-space interfaces (task P2-LM34c)

Source: MQ arXiv:1812.03913 `lqg_geodesics.tex`, proof of Prop 4.3 (l. 693–700): nested Markov
decompositions of `h` on `B_{r_0} ⊃ B_{r_1} ⊃ …`; LM arXiv:1905.00379 Lemma 2.1 (l. 425–429).
In Gaussian-space form the zero-boundary part of `h|_{B_{r_j}}` is the orthogonal projection of
the field onto the Cameron–Martin image `cmIso (B_{r_j})` (GMSh arXiv:1807.07511 Lemma 2.2, the
proof formalized in `Field/Markov*.lean`).

* `laplacian_comp_smul`, `testAffinePull_cmTest`, `lmScaled_cmTest`: `Δ(f(c·)) = c² (Δf)(c·)` and
  the scaling of the Dirichlet pairings of `lmScaled h r`.
* **Interface (a)** `range_cmIso_lmScaled`: the Cameron–Martin image of `H₀¹(B_1)` for
  `lmScaled h (r c)` equals that of `H₀¹(B_c)` for `lmScaled h r` (scale invariance of the
  Dirichlet inner product; implicit in MQ l. 693–700, "by scaling").
* **Interface (b)** `exists_lmRep_zbExt`: a decomposition `IsLMRep` at scale `r` whose
  zero-boundary part is (pairing-wise a.s.) the Cameron–Martin projection `zbExt`;
  `inner_pairVec_sub_extVec`: `[⟨h, φ⟩] − zbExt φ ⊥ cmIso(H₀¹(U))`, i.e. `zbExt φ` is the
  orthogonal projection of `[⟨h, φ⟩]` onto `range cmIso U`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace Laplacian
open scoped RealInnerProductSpace

namespace LQGMetric.LM

open Blueprint QuantumZipper QuantumZipper.K3 MarkovZB MarkovExt MarkovGauss

/-- `Δ (f(c ·)) = c² (Δ f)(c ·)` -/
lemma laplacian_comp_smul {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : ℂ) :
    Δ (fun y => f (c • y)) x = c ^ 2 * Δ f (c • x) := by
  set L : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ with hL
  have hT : (fun y => f (c • y)) = f ∘ L := by funext y; simp [hL]
  rw [hT, laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [L.iteratedFDeriv_comp_right hf x (by norm_num)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have e : ∀ v : ℂ, (fun i : Fin 2 => L (![v, v] i)) = fun i => c • ![v, v] i := by
    intro v; funext i; simp [hL]
  rw [e, e, ContinuousMultilinearMap.map_smul_univ, ContinuousMultilinearMap.map_smul_univ]
  have hLx : L x = c • x := by simp [hL]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hLx]
  ring

lemma testAffinePull_zero_apply {a : ℝ} (ha : a ≠ 0) (φ : TestC) (x : ℂ) :
    testAffinePull a 0 φ x = φ (a⁻¹ • x) := by
  rw [testAffinePull_apply a 0 ha, sub_zero]
  congr 1
  rw [Complex.real_smul, div_eq_inv_mul]; push_cast; rfl

/-- `(cmTest φ)((·)/a) = a² cmTest (φ((·)/a))` -/
lemma testAffinePull_cmTest {a : ℝ} (ha : a ≠ 0) (φ : TestC) :
    testAffinePull a 0 (cmTest φ) = (a ^ 2) • cmTest (testAffinePull a 0 φ) := by
  ext x
  rw [testAffinePull_zero_apply ha]
  change -(2 * Real.pi)⁻¹ * Δ (⇑φ) (a⁻¹ • x) =
    a ^ 2 * (-(2 * Real.pi)⁻¹ * Δ (⇑(testAffinePull a 0 φ)) x)
  have e : (⇑(testAffinePull a 0 φ)) = fun y => φ (a⁻¹ • y) := by
    funext y; exact testAffinePull_zero_apply ha φ y
  rw [e, laplacian_comp_smul (φ.contDiff.of_le (by simp)) a⁻¹ x]
  field_simp

lemma testAffinePull_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (φ : TestC) :
    testAffinePull (a * b) 0 φ = testAffinePull a 0 (testAffinePull b 0 φ) := by
  ext x
  rw [testAffinePull_zero_apply (mul_ne_zero ha hb), testAffinePull_zero_apply ha,
    testAffinePull_zero_apply hb, smul_smul, mul_inv, mul_comm a⁻¹]

/-- `⟨h(r ·) − c, cmTest ψ⟩ = ⟨h, cmTest (ψ(·/r))⟩` (pathwise) -/
lemma lmScaled_cmTest {Ω : Type} (h : Ω → DistC) {r : ℝ} (hr : 0 < r) (ψ : TestC) (ω : Ω) :
    lmScaled h r ω (cmTest ψ) = h ω (cmTest (testAffinePull r 0 ψ)) := by
  simp only [lmScaled, recentre]
  rw [GFFInv.affineComp_apply, testAffinePull_cmTest hr.ne', map_smul, GFFInv.addConst_apply,
    integral_cmTest, zero_mul, add_zero, smul_eq_mul]
  field_simp

lemma lmScaled_mul_cmTest {Ω : Type} (h : Ω → DistC) {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (ψ : TestC) (ω : Ω) :
    lmScaled h (r * c) ω (cmTest ψ) = lmScaled h r ω (cmTest (testAffinePull c 0 ψ)) := by
  rw [lmScaled_cmTest h (mul_pos hr hc), lmScaled_cmTest h hr,
    testAffinePull_mul hr.ne' hc.ne']

/-- `f ∈ C_c^∞(U)` ⇒ `f((·)/a) ∈ C_c^∞(V)` when `x ∈ V ⇐ a⁻¹ x ∈ U` -/
lemma testAffinePull_mem_zeroSpace {a : ℝ} (ha : a ≠ 0) {U V : Set ℂ}
    (hUV : ∀ x, a⁻¹ • x ∈ U → x ∈ V) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    ⇑(testAffinePull a 0 (zsTest hf)) ∈ zeroSpace V := by
  have e : ⇑(testAffinePull a 0 (zsTest hf)) = fun y => f (a⁻¹ • y) := by
    funext y; exact testAffinePull_zero_apply ha _ y
  refine ⟨(testAffinePull a 0 (zsTest hf)).contDiff,
    (testAffinePull a 0 (zsTest hf)).hasCompactSupport, ?_⟩
  rw [e]
  refine (tsupport_comp_subset_preimage f (continuous_const_smul a⁻¹)).trans ?_
  intro x hx
  exact hUV x (hf.2.2 hx)

/-- the Cameron–Martin image is determined by the Dirichlet pairings -/
lemma range_cmIso_subset {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → DistC} (hY : IsWholePlaneGFF Y P) (hX : IsWholePlaneGFF X P) (U V : Opens ℂ)
    (hT : ∀ f (hf : f ∈ zeroSpace (U : Set ℂ)), ∃ f' : ℂ → ℝ, ∃ hf' : f' ∈ zeroSpace (V : Set ℂ),
      ∀ ω, Y ω (cmTest (zsTest hf)) = X ω (cmTest (zsTest hf'))) :
    Set.range (cmIso hY U) ⊆ Set.range (cmIso hX V) := by
  rintro _ ⟨v, rfl⟩
  have hcl : IsClosed (Set.range (cmIso hX V)) :=
    (cmIso hX V).isometry.isClosedEmbedding.isClosed_range
  refine (denseRange_gradLin U).induction_on v (hcl.preimage (cmIso hY U).continuous)
    fun f => ?_
  obtain ⟨f', hf', he⟩ := hT f.1 f.2
  refine ⟨gradLin V ⟨f', hf'⟩, ?_⟩
  rw [cmIso_gradLin, cmIso_gradLin]
  simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => ?_)
  simp only [pairProc, cmTest0]
  exact (he ω).symm

lemma mem_ballO_iff (x : ℂ) (a : ℝ) : x ∈ (ballO (0 : ℂ) a : Set ℂ) ↔ ‖x‖ < a := by
  simp [ballO, mem_ball, dist_zero_right]

/-- **Interface (a): scaling of `cmIso`.** `range cmIso_{lmScaled h (r c)}(H₀¹(B_1)) =
range cmIso_{lmScaled h r}(H₀¹(B_c))`. -/
theorem range_cmIso_lmScaled {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r c : ℝ} (hr : 0 < r)
    (hc : 0 < c) :
    Set.range (cmIso (isWholePlaneGFF_lmScaled hh (mul_pos hr hc)) (ballO 0 1)) =
      Set.range (cmIso (isWholePlaneGFF_lmScaled hh hr) (ballO 0 c)) := by
  refine subset_antisymm (range_cmIso_subset _ _ _ _ fun f hf => ?_)
    (range_cmIso_subset _ _ _ _ fun f hf => ?_)
  · refine ⟨_, testAffinePull_mem_zeroSpace hc.ne' (fun x hx => ?_) hf, fun ω => ?_⟩
    · rw [mem_ballO_iff] at hx ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc] at hx
      rwa [inv_mul_lt_iff₀ hc, mul_one] at hx
    · rw [lmScaled_mul_cmTest h hr hc]; rfl
  · refine ⟨_, testAffinePull_mem_zeroSpace (inv_ne_zero hc.ne') (fun x hx => ?_) hf,
      fun ω => ?_⟩
    · rw [mem_ballO_iff] at hx ⊢
      rw [inv_inv, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hx
      rwa [← lt_div_iff₀' hc, div_self hc.ne'] at hx
    · rw [lmScaled_mul_cmTest h hr hc]
      congr 2
      ext x
      rw [testAffinePull_zero_apply hc.ne', zsTest_apply]
      show f x = testAffinePull c⁻¹ 0 (zsTest hf) (c⁻¹ • x)
      rw [testAffinePull_zero_apply (inv_ne_zero hc.ne'), zsTest_apply, inv_inv,
        smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

lemma isNormalizedWPGFF_lmScaled {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) :
    IsNormalizedWPGFF (lmScaled h r) P :=
  ⟨isWholePlaneGFF_lmScaled hh hr, ae_circleAvg_lmScaled hh hr⟩

lemma disjoint_ballO_sphere {a : ℝ} (ha : a ≤ 1) :
    Disjoint ((ballO (0 : ℂ) a : Opens ℂ) : Set ℂ) (sphere (0 : ℂ) 1) :=
  Set.disjoint_left.2 fun y hy hs => by
    have h1 : ‖y‖ < a := (mem_ballO_iff y a).1 hy
    have h2 : ‖y‖ = 1 := by simpa using hs
    linarith

/-- **Interface (b), first half: a decomposition at scale `r` whose zero-boundary part is the
Cameron–Martin projection** (LM Lemma 2.1 via `MarkovAsm.markov_decomp_ae`, keeping the
identification `⟨h̊, φ⟩ = zbExt φ` a.s. from `exists_dist_version_zbExt`). -/
theorem exists_lmRep_zbExt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) :
    ∃ hh0 hz G : Ω → DistC, IsLMRep P h r hh0 hz G ∧ Measurable hz ∧
      (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P]
        zbExt (isWholePlaneGFF_lmScaled hh hr) (ballO 0 1) φ) ∧
      ∀ ω, restrictTo (toOpens (closure ((ballO (0 : ℂ) 1 : Opens ℂ) : Set ℂ))ᶜ
        isClosed_closure.isOpen_compl) (hz ω) = 0 := by
  have hN := isNormalizedWPGFF_lmScaled hh hr
  have hV := disjoint_ballO_sphere (le_refl (1 : ℝ))
  have hVb : Bornology.IsBounded ((ballO (0 : ℂ) 1 : Opens ℂ) : Set ℂ) := by
    simpa [ballO] using (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1))
  obtain ⟨hz, hzm, hzae, hzv⟩ := MarkovVer2.exists_dist_version_zbExt hN hV
  obtain ⟨G, hGm, hhG⟩ := MarkovAsm.exists_germ_dist_version hN hzae
    (MarkovGermVer.exists_germ_version_harm_of_bdd hN hV hVb)
  refine ⟨fun ω => lmScaled h r ω - hz ω, hz, G,
    ⟨fun ω => (sub_add_cancel _ _).symm, hhG, ?_, MarkovAsm.ae_harmonic_sub hN hV hz hzae,
      MarkovAsm.isZeroBoundaryGFF_restrict hN hV hzm hzae,
      MarkovAsm.indep_dist_fieldSigmaClosed hN hV hzae⟩, hzm, hzae, hzv⟩
  have e : (((ballO (0 : ℂ) 1 : Opens ℂ) : Set ℂ))ᶜ = (ball (0 : ℂ) 1)ᶜ := rfl
  rw [e] at hGm
  exact hGm

/-- **Interface (b), second half: `zbExt φ` is the orthogonal projection of `[⟨h, φ⟩]` onto
`range cmIso U`** (bounded `U` with `U ∩ ∂𝔻 = ∅`). -/
theorem inner_pairVec_sub_extVec {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) (hUb : Bornology.IsBounded (U : Set ℂ))
    (φ : TestC) (v : gradClosure (U : Set ℂ) (zeroSpace U)) :
    ⟪MarkovNorm.pairVec hh φ - extVec hh.1 U ((U : Set ℂ).indicator φ), cmIso hh.1 U v⟫ = 0 := by
  rw [inner_sub_left, MarkovNorm.inner_pairVec_cmIso hh hU hUb φ v, extVec,
    LinearIsometry.inner_map_map, Submodule.coe_inner, sub_self]

end LQGMetric.LM
