import LatticeProb.Analysis.Elliptic.HolderClosureJets
import LatticeProb.Analysis.Elliptic.HolderReflectionGlue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Reflection across a coordinate hyperplane

The higher-order reflection in Gilbarg–Trudinger Lemma 6.37 extends a function
with Hölder-continuous second derivatives across a coordinate hyperplane.
-/

namespace LatticeProb.Elliptic.HolderExtension

open Set
open scoped ContDiff

noncomputable section

/-- Reflect a coordinate with an inverse scaling factor. -/
def reflect {d : ℕ} (i : Fin d) (a : ℝ) (x : E d) : E d :=
  Function.update x i (-x i / a)

private theorem contDiff_reflect {d : ℕ} (i : Fin d) (a : ℝ) :
    ContDiff ℝ 2 (reflect i a) := by
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa [reflect] using ((contDiff_apply ℝ ℝ i).neg.div_const a)
  · simpa [reflect, Function.update_of_ne h] using (contDiff_apply ℝ ℝ j)

private theorem reflect_mem_halfSpace {d : ℕ} (i : Fin d) {a : ℝ} (ha : 0 < a)
    {x : E d} (hx : x i < 0) : reflect i a x ∈ halfSpace i := by
  simp only [halfSpace, mem_ofPred_eq, reflect, Function.update_self]
  exact div_pos (neg_pos.mpr hx) ha

private theorem contDiffOn_reflection {d : ℕ} (i : Fin d) (u : E d → ℝ)
    (hu : ContDiffOn ℝ 2 u (halfSpace i)) :
    ContDiffOn ℝ 2 (fun x => 6 * u (reflect i 1 x) - 32 * u (reflect i 2 x) +
      27 * u (reflect i 3 x)) {x : E d | x i < 0} := by
  have hcomp (a : ℝ) (ha : 0 < a) :
      ContDiffOn ℝ 2 (fun x => u (reflect i a x)) {x : E d | x i < 0} :=
    hu.comp (contDiff_reflect i a).contDiffOn (fun _ hx => reflect_mem_halfSpace i ha hx)
  exact ((contDiffOn_const.mul (hcomp 1 (by norm_num))).sub
    (contDiffOn_const.mul (hcomp 2 (by norm_num)))).add
    (contDiffOn_const.mul (hcomp 3 (by norm_num)))

private def normalProjection {d : ℕ} (i : Fin d) : E d →L[ℝ] E d :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).comp (ContinuousLinearMap.proj i)

private def reflectionCLM {d : ℕ} (i : Fin d) (a : ℝ) : E d →L[ℝ] E d :=
  ContinuousLinearMap.id ℝ (E d) + (-1 / a - 1) • normalProjection i

private theorem reflectionCLM_eq_reflect {d : ℕ} (i : Fin d) (a : ℝ) (x : E d) :
    reflectionCLM i a x = reflect i a x := by
  ext j
  by_cases h : j = i
  · subst j
    simp [reflectionCLM, normalProjection, reflect]
    ring
  · simp [reflectionCLM, normalProjection, reflect, h]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem reflection_first_jet (L : V →L[ℝ] ℝ) (v n : V) :
    6 * L (v - (2 : ℝ) • n) - 32 * L (v - (3 / 2 : ℝ) • n) +
      27 * L (v - (4 / 3 : ℝ) • n) = L v := by
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

private theorem reflection_second_jet (B : V →L[ℝ] V →L[ℝ] ℝ) (v w n m : V) :
    6 * B (v - (2 : ℝ) • n) (w - (2 : ℝ) • m) -
      32 * B (v - (3 / 2 : ℝ) • n) (w - (3 / 2 : ℝ) • m) +
      27 * B (v - (4 / 3 : ℝ) • n) (w - (4 / 3 : ℝ) • m) = B v w := by
  simp only [map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]
  ring

private def secondCompose (A : V →L[ℝ] V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V V ℝ).flip A).comp (B.comp A)

private theorem secondCompose_apply (A : V →L[ℝ] V) (B : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    secondCompose A B v w = B (A v) (A w) := by
  rfl

private theorem compose_deriv {s t : Set V} {F : V → ℝ} {D : V → V →L[ℝ] ℝ}
    (A : V →L[ℝ] V) (hmap : MapsTo A s t)
    (hF : ∀ y ∈ t, HasFDerivWithinAt F (D y) t y)
    {x : V} (hx : x ∈ s) :
    HasFDerivWithinAt (fun y => F (A y)) ((D (A x)).comp A) s x := by
  exact (hF (A x) (hmap hx)).comp x A.hasFDerivAt.hasFDerivWithinAt hmap

private theorem compose_deriv_field {s t : Set V} {D : V → V →L[ℝ] ℝ}
    {B : V → V →L[ℝ] V →L[ℝ] ℝ}
    (A : V →L[ℝ] V) (hmap : MapsTo A s t)
    (hD : ∀ y ∈ t, HasFDerivWithinAt D (B y) t y)
    {x : V} (hx : x ∈ s) :
    HasFDerivWithinAt (fun y => (D (A y)).comp A) (secondCompose A (B (A x))) s x := by
  have h := (hD (A x) (hmap hx)).comp x A.hasFDerivAt.hasFDerivWithinAt hmap
  exact (((ContinuousLinearMap.compL ℝ V V ℝ).flip A).hasFDerivAt.comp_hasFDerivWithinAt x h)

private theorem halfSpace_closure_eq {d : ℕ} (i : Fin d) :
    closure (halfSpace i) = {x : E d | 0 ≤ x i} := by
  change closure ((fun x : E d => x i) ⁻¹' Ioi (0 : ℝ)) = _
  rw [← (isOpenMap_eval i).preimage_closure_eq_closure_preimage (continuous_apply i), closure_Ioi]
  rfl

private theorem uniqueDiffOn_upper {d : ℕ} (i : Fin d) :
    UniqueDiffOn ℝ {x : E d | 0 ≤ x i} := by
  have hconv : Convex ℝ {x : E d | 0 ≤ x i} := by
    change Convex ℝ ((LinearMap.proj i : E d →ₗ[ℝ] ℝ) ⁻¹' Ici 0)
    exact (convex_Ici (0 : ℝ)).linear_preimage (LinearMap.proj i : E d →ₗ[ℝ] ℝ)
  have hint : (interior {x : E d | 0 ≤ x i}).Nonempty := by
    refine ⟨Pi.single i 1, ?_⟩
    have hsub : halfSpace i ⊆ {x : E d | 0 ≤ x i} := by
      intro x hx
      change 0 < x i at hx
      exact le_of_lt hx
    apply interior_mono hsub
    have hopen : IsOpen (halfSpace i) := isOpen_lt continuous_const (continuous_apply i)
    rw [hopen.interior_eq]
    simp [halfSpace]
  exact uniqueDiffOn_convex hconv hint

private theorem reflectionCLM_one {d : ℕ} (i : Fin d) (v : E d) :
    reflectionCLM i 1 v = v - (2 : ℝ) • normalProjection i v := by
  ext j
  simp [reflectionCLM]
  ring

private theorem reflectionCLM_two {d : ℕ} (i : Fin d) (v : E d) :
    reflectionCLM i 2 v = v - (3 / 2 : ℝ) • normalProjection i v := by
  ext j
  simp [reflectionCLM]
  ring

private theorem reflectionCLM_three {d : ℕ} (i : Fin d) (v : E d) :
    reflectionCLM i 3 v = v - (4 / 3 : ℝ) • normalProjection i v := by
  ext j
  simp [reflectionCLM]
  ring

private theorem reflection_first_jet_eq {d : ℕ} (i : Fin d) (D : E d →L[ℝ] ℝ) :
    (6 : ℝ) • D.comp (reflectionCLM i 1) - (32 : ℝ) • D.comp (reflectionCLM i 2) +
      (27 : ℝ) • D.comp (reflectionCLM i 3) = D := by
  ext v
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  simpa only [reflectionCLM_one, reflectionCLM_two, reflectionCLM_three] using
    reflection_first_jet D v (normalProjection i v)

private theorem reflection_second_jet_eq {d : ℕ} (i : Fin d)
    (B : E d →L[ℝ] E d →L[ℝ] ℝ) :
    (6 : ℝ) • secondCompose (reflectionCLM i 1) B - (32 : ℝ) • secondCompose (reflectionCLM i 2) B +
      (27 : ℝ) • secondCompose (reflectionCLM i 3) B = B := by
  ext v w
  simp only [sub_apply, add_apply, smul_apply, secondCompose_apply, smul_eq_mul]
  simpa only [reflectionCLM_one, reflectionCLM_two, reflectionCLM_three] using
    reflection_second_jet B v w (normalProjection i v) (normalProjection i w)

private theorem reflect_mem_upper {d : ℕ} (i : Fin d) {a : ℝ} (ha : 0 < a)
    {x : E d} (hx : x i ≤ 0) : 0 ≤ (reflect i a x) i := by
  simp only [reflect, Function.update_self]
  exact div_nonneg (neg_nonneg.mpr hx) (le_of_lt ha)

private theorem reflect_of_zero {d : ℕ} (i : Fin d) (a : ℝ) {x : E d} (hx : x i = 0) :
    reflect i a x = x := by
  ext j
  by_cases h : j = i
  · subst j
    simp [reflect, hx]
  · simp [reflect, h]

private theorem upper_jets {d : ℕ} (i : Fin d) (F : E d → ℝ)
    (hF : ContDiffOn ℝ 2 F (closure (halfSpace i))) :
    ∃ D : E d → E d →L[ℝ] ℝ, ∃ B : E d → E d →L[ℝ] E d →L[ℝ] ℝ,
      ContinuousOn B {x | 0 ≤ x i} ∧
      (∀ x ∈ {x | 0 ≤ x i}, HasFDerivWithinAt D (B x) {x | 0 ≤ x i} x) ∧
      (∀ x ∈ {x | 0 ≤ x i}, HasFDerivWithinAt F (D x) {x | 0 ≤ x i} x) := by
  rw [halfSpace_closure_eq] at hF
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (uniqueDiffOn_upper i)] at hF
  obtain ⟨_, D, hD, hFD⟩ := hF
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (uniqueDiffOn_upper i)] at hD
  obtain ⟨_, B, hB, hDB⟩ := hD
  exact ⟨D, B, contDiffOn_zero.mp hB, hDB, hFD⟩


private def reflectedValue {d : ℕ} (i : Fin d) (F : E d → ℝ) (x : E d) : ℝ :=
  6 * F (reflectionCLM i 1 x) - 32 * F (reflectionCLM i 2 x) +
    27 * F (reflectionCLM i 3 x)

private def reflectedFirst {d : ℕ} (i : Fin d) (D : E d → E d →L[ℝ] ℝ)
    (x : E d) : E d →L[ℝ] ℝ :=
  (6 : ℝ) • (D (reflectionCLM i 1 x)).comp (reflectionCLM i 1) -
    (32 : ℝ) • (D (reflectionCLM i 2 x)).comp (reflectionCLM i 2) +
    (27 : ℝ) • (D (reflectionCLM i 3 x)).comp (reflectionCLM i 3)

private def reflectedSecond {d : ℕ} (i : Fin d)
    (B : E d → E d →L[ℝ] E d →L[ℝ] ℝ) (x : E d) : E d →L[ℝ] E d →L[ℝ] ℝ :=
  (6 : ℝ) • secondCompose (reflectionCLM i 1) (B (reflectionCLM i 1 x)) -
    (32 : ℝ) • secondCompose (reflectionCLM i 2) (B (reflectionCLM i 2 x)) +
    (27 : ℝ) • secondCompose (reflectionCLM i 3) (B (reflectionCLM i 3 x))

private theorem reflection_maps_upper {d : ℕ} (i : Fin d) {a : ℝ} (ha : 0 < a) :
    MapsTo (reflectionCLM i a) {x : E d | x i ≤ 0} {x : E d | 0 ≤ x i} := by
  intro x hx
  change 0 ≤ (reflectionCLM i a x) i
  rw [reflectionCLM_eq_reflect]
  exact reflect_mem_upper i ha hx

private theorem reflectedValue_deriv {d : ℕ} (i : Fin d) (F : E d → ℝ)
    (D : E d → E d →L[ℝ] ℝ)
    (hF : ∀ x ∈ {x : E d | 0 ≤ x i},
      HasFDerivWithinAt F (D x) {x : E d | 0 ≤ x i} x) :
    ∀ x ∈ {x : E d | x i ≤ 0}, HasFDerivWithinAt (reflectedValue i F)
      (reflectedFirst i D x) {x : E d | x i ≤ 0} x := by
  intro x hx
  have hd (a : ℝ) (ha : 0 < a) :=
    compose_deriv (reflectionCLM i a) (reflection_maps_upper i ha) hF hx
  convert (((hd 1 (by norm_num)).const_smul (6 : ℝ)).sub
      ((hd 2 (by norm_num)).const_smul (32 : ℝ))).add
      ((hd 3 (by norm_num)).const_smul (27 : ℝ)) using 1 <;>
    ext y <;> simp [reflectedValue, reflectedFirst, smul_eq_mul]

private theorem reflectedFirst_deriv {d : ℕ} (i : Fin d)
    (D : E d → E d →L[ℝ] ℝ) (B : E d → E d →L[ℝ] E d →L[ℝ] ℝ)
    (hD : ∀ x ∈ {x : E d | 0 ≤ x i},
      HasFDerivWithinAt D (B x) {x : E d | 0 ≤ x i} x) :
    ∀ x ∈ {x : E d | x i ≤ 0}, HasFDerivWithinAt (reflectedFirst i D)
      (reflectedSecond i B x) {x : E d | x i ≤ 0} x := by
  intro x hx
  have hd (a : ℝ) (ha : 0 < a) :=
    compose_deriv_field (reflectionCLM i a) (reflection_maps_upper i ha) hD hx
  convert (((hd 1 (by norm_num)).const_smul (6 : ℝ)).sub
      ((hd 2 (by norm_num)).const_smul (32 : ℝ))).add
      ((hd 3 (by norm_num)).const_smul (27 : ℝ)) using 1 <;>
    ext y <;> simp [reflectedFirst, reflectedSecond]

private theorem reflectedSecond_continuousOn {d : ℕ} (i : Fin d)
    (B : E d → E d →L[ℝ] E d →L[ℝ] ℝ)
    (hB : ContinuousOn B {x : E d | 0 ≤ x i}) :
    ContinuousOn (reflectedSecond i B) {x : E d | x i ≤ 0} := by
  have hc (a : ℝ) (ha : 0 < a) :
      ContinuousOn (fun x => secondCompose (reflectionCLM i a) (B (reflectionCLM i a x)))
        {x : E d | x i ≤ 0} := by
    unfold secondCompose
    exact continuousOn_const.clm_comp
      ((hB.comp (reflectionCLM i a).continuous.continuousOn
        (reflection_maps_upper i ha)).clm_comp continuousOn_const)
  let : Add (E d →L[ℝ] E d →L[ℝ] ℝ) := inferInstance
  let : ContinuousAdd (E d →L[ℝ] E d →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E d →L[ℝ] E d →L[ℝ] ℝ)).toContinuousAdd
  let : ContinuousNeg (E d →L[ℝ] E d →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E d →L[ℝ] E d →L[ℝ] ℝ)).toContinuousNeg
  let : ContinuousSub (E d →L[ℝ] E d →L[ℝ] ℝ) := ⟨by
    have heq : (fun p : (E d →L[ℝ] E d →L[ℝ] ℝ) ×
        (E d →L[ℝ] E d →L[ℝ] ℝ) => p.1 - p.2) =
        (fun p => p.1 + -p.2) := by
      funext p
      ext v w
      simp only [sub_apply, add_apply, neg_apply, sub_eq_add_neg]
    rw [heq]
    exact continuous_add.comp (continuous_fst.prodMk (continuous_neg.comp continuous_snd))⟩
  exact (((hc 1 (by norm_num)).const_smul (6 : ℝ)).sub
    ((hc 2 (by norm_num)).const_smul (32 : ℝ))).add
    ((hc 3 (by norm_num)).const_smul (27 : ℝ))

private theorem reflectionCLM_of_zero {d : ℕ} (i : Fin d) (a : ℝ) {x : E d}
    (hx : x i = 0) : reflectionCLM i a x = x := by
  rw [reflectionCLM_eq_reflect, reflect_of_zero i a hx]

private theorem reflectedValue_boundary {d : ℕ} (i : Fin d) (F : E d → ℝ)
    {x : E d} (hx : x i = 0) : F x = reflectedValue i F x := by
  simp only [reflectedValue, reflectionCLM_of_zero i 1 hx,
    reflectionCLM_of_zero i 2 hx, reflectionCLM_of_zero i 3 hx]
  ring

private theorem reflectedFirst_boundary {d : ℕ} (i : Fin d)
    (D : E d → E d →L[ℝ] ℝ) {x : E d} (hx : x i = 0) :
    D x = reflectedFirst i D x := by
  simpa only [reflectedFirst, reflectionCLM_of_zero i 1 hx,
    reflectionCLM_of_zero i 2 hx, reflectionCLM_of_zero i 3 hx] using
      (reflection_first_jet_eq i (D x)).symm

private theorem reflectedSecond_boundary {d : ℕ} (i : Fin d)
    (B : E d → E d →L[ℝ] E d →L[ℝ] ℝ) {x : E d} (hx : x i = 0) :
    B x = reflectedSecond i B x := by
  simpa only [reflectedSecond, reflectionCLM_of_zero i 1 hx,
    reflectionCLM_of_zero i 2 hx, reflectionCLM_of_zero i 3 hx] using
      (reflection_second_jet_eq i (B x)).symm

/-- Reflection of a twice differentiable function on the half-space. -/
theorem halfSpace_reflection_C2 {d : ℕ} (i : Fin d) {σ : ℝ}
    (hσ : 0 < σ) (hσ' : σ < 1) (u : E d → ℝ)
    (hu : ContDiffOn ℝ 2 u (halfSpace i))
    (hn : c2HolderNorm σ (halfSpace i) u < ⊤) :
    ∃ v : E d → ℝ, ContDiff ℝ 2 v ∧ Set.EqOn v u (halfSpace i) ∧
      ∀ x, x i < 0 → v x = 6 * u (reflect i 1 x) -
        32 * u (reflect i 2 x) + 27 * u (reflect i 3 x) := by
  classical
  obtain ⟨F, hF, hFu⟩ := halfSpace_contDiffOn_closure i hσ hσ' u hu hn
  obtain ⟨D, B, hB, hDB, hFD⟩ := upper_jets i F hF
  let S : Set (E d) := {x | 0 ≤ x i}
  let T : Set (E d) := {x | x i ≤ 0}
  have hS : IsClosed S := isClosed_le continuous_const (continuous_apply i)
  have hT : IsClosed T := isClosed_le (continuous_apply i) continuous_const
  have hcover : S ∪ T = Set.univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    exact le_total 0 (x i)
  have heq (x : E d) (hx : x ∈ S ∩ T) : x i = 0 := le_antisymm hx.2 hx.1
  have h0 : ∀ x ∈ S ∩ T, F x = reflectedValue i F x :=
    fun x hx => reflectedValue_boundary i F (heq x hx)
  have h1 : ∀ x ∈ S ∩ T, D x = reflectedFirst i D x :=
    fun x hx => reflectedFirst_boundary i D (heq x hx)
  have h2 : ∀ x ∈ S ∩ T, B x = reflectedSecond i B x :=
    fun x hx => reflectedSecond_boundary i B (heq x hx)
  have hfirst : ContDiff ℝ 1 (S.piecewise D (reflectedFirst i D)) :=
    contDiff_one_piecewise_of_closed_cover hcover hS hT h1 h2 hB
      (reflectedSecond_continuousOn i B hB) hDB (reflectedFirst_deriv i D B hDB)
  have hv : ContDiff ℝ 2 (S.piecewise F (reflectedValue i F)) :=
    contDiff_succ_piecewise_of_closed_cover (n := 1) hcover hS hT h0 h1 hfirst
      hFD (reflectedValue_deriv i F D hFD)
  refine ⟨S.piecewise F (reflectedValue i F), hv, ?_, ?_⟩
  · intro x hx
    have hx' : 0 < x i := hx
    have hxS : x ∈ S := le_of_lt hx'
    rw [piecewise_eq_of_mem S F (reflectedValue i F) hxS]
    exact hFu hx
  · intro x hx
    have hxs : x ∉ S := not_le_of_gt hx
    rw [piecewise_eq_of_notMem _ _ _ hxs]
    simp only [reflectedValue, reflectionCLM_eq_reflect]
    rw [hFu (reflect_mem_halfSpace i (by norm_num) hx),
      hFu (reflect_mem_halfSpace i (by norm_num) hx),
      hFu (reflect_mem_halfSpace i (by norm_num) hx)]

end
end LatticeProb.Elliptic.HolderExtension
