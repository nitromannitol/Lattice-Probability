/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.Normalize at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.ArcNonSep
import Mathlib.Tactic.Positivity.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: farthest-pair normalization

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 692–1043.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-! ## Normalization foundation (Maehara farthest-pair setup)

We prepare Maehara's WLOG normalization: the diameter of `J = range r` is realized
by a farthest pair `a, b`, and a similarity homeomorphism `T` moves `a ↦ !₂[-1,0]`,
`b ↦ !₂[1,0]`, scaling every distance by the fixed factor `2 / dist a b`. This
reduces the geometric core (`step_A`, `step_B`) to *normalized* statements in which
the farthest pair sits at `(±1, 0)`. -/

/-- `complexLIE 1 = !₂[1,0]`. -/
lemma complexLIE_one : Arcs.complexLIE (1 : ℂ) = !₂[(1:ℝ), 0] := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (1 : ℂ)
  rw [show Arcs.complexLIE
        = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp only [Complex.one_re, Complex.one_im, one_smul, zero_smul, add_zero,
    EuclideanSpace.basisFun_apply]
  ext i; fin_cases i <;>
    simp

/-- `complexLIE (-1) = !₂[-1,0]`. -/
lemma complexLIE_negOne : Arcs.complexLIE (-1 : ℂ) = !₂[(-1:ℝ), 0] := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (-1 : ℂ)
  rw [show Arcs.complexLIE
        = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero,
    zero_smul, add_zero, EuclideanSpace.basisFun_apply]
  ext i; fin_cases i <;>
    simp

/-- **Task 1 (farthest pair).** The compact curve `range r` contains a pair `a, b`
realizing the diameter of `J`, and `a ≠ b` (as `r` is injective on the sphere, which
has at least two points). -/
theorem exists_farthest_pair {r : sphere (0 : Plane) 1 → Plane}
    (hcont : Continuous r) (hinj : Injective r) :
    ∃ a ∈ range r, ∃ b ∈ range r,
      (∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ dist a b) ∧ a ≠ b := by
  have hcpt : IsCompact (range r) := jordanCurve_isCompact r hcont
  -- two explicit distinct points on the sphere, hence in `range r`
  have hs1 : (!₂[(1:ℝ), 0] : Plane) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  have hs2 : (!₂[(-1:ℝ), 0] : Plane) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  set s1 : sphere (0 : Plane) 1 := ⟨!₂[(1:ℝ), 0], hs1⟩ with hs1def
  set s2 : sphere (0 : Plane) 1 := ⟨!₂[(-1:ℝ), 0], hs2⟩ with hs2def
  have hs12 : s1 ≠ s2 := by
    intro h
    rw [hs1def, hs2def, Subtype.mk_eq_mk] at h
    have hh : (!₂[(1:ℝ), 0] : Plane) 0 = (!₂[(-1:ℝ), 0] : Plane) 0 := by rw [h]
    norm_num [PiLp.toLp_apply] at hh
  have hne : (range r).Nonempty := ⟨r s1, mem_range_self _⟩
  have hprod : IsCompact ((range r) ×ˢ (range r)) := hcpt.prod hcpt
  have hpne : ((range r) ×ˢ (range r)).Nonempty := hne.prod hne
  obtain ⟨⟨a, b⟩, hmem, hmax⟩ :=
    hprod.exists_isMaxOn hpne
      (continuous_dist.continuousOn (s := (range r) ×ˢ (range r)))
  rw [mem_prod] at hmem
  refine ⟨a, hmem.1, b, hmem.2, ?_, ?_⟩
  · intro z hz w hw
    exact isMaxOn_iff.mp hmax (z, w) (mem_prod.mpr ⟨hz, hw⟩)
  · intro hEq
    have hd0 : dist a b = 0 := by rw [hEq, dist_self]
    have hle : dist (r s1) (r s2) ≤ dist a b :=
      isMaxOn_iff.mp hmax (r s1, r s2) (mem_prod.mpr ⟨mem_range_self _, mem_range_self _⟩)
    rw [hd0] at hle
    exact hs12 (hinj (eq_of_dist_eq_zero (le_antisymm hle dist_nonneg)))

/-- **Task 2 (similarity normalization).** Given `a ≠ b` on the plane there is a
similarity homeomorphism `T : Plane ≃ₜ Plane` scaling every distance by the fixed
positive factor `2 / dist a b`, with `T a = !₂[-1,0]` and `T b = !₂[1,0]`. -/
theorem exists_similarity {a b : Plane} (hab : a ≠ b) :
    ∃ T : Plane ≃ₜ Plane,
      (∀ z w, dist (T z) (T w) = (2 / dist a b) * dist z w) ∧
        T a = !₂[(-1:ℝ), 0] ∧ T b = !₂[(1:ℝ), 0] := by
  set L := Arcs.complexLIE with hL
  set A : ℂ := L.symm a with hA
  set B : ℂ := L.symm b with hB
  have hBAne : B ≠ A := by
    intro h; exact hab (L.symm.injective h).symm
  have hABne : B - A ≠ 0 := sub_ne_zero.mpr hBAne
  set α : ℂ := 2 / (B - A) with hα
  have hαne : α ≠ 0 := by rw [hα]; exact div_ne_zero two_ne_zero hABne
  set β : ℂ := -(A + B) / (B - A) with hβ
  set e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ α hαne).trans (Homeomorph.addRight β) with he
  have he_apply : ∀ w : ℂ, e w = α * w + β := by
    intro w
    rw [he]
    simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addRight]
  set T : Plane ≃ₜ Plane := (L.symm.toHomeomorph).trans (e.trans L.toHomeomorph) with hT
  have hT_apply : ∀ w : Plane, T w = L (α * L.symm w + β) := by
    intro w
    rw [hT]
    simp only [Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, he_apply]
  refine ⟨T, ?_, ?_, ?_⟩
  · -- distance scaling
    intro z w
    rw [hT_apply, hT_apply, L.dist_map, dist_eq_norm,
      show (α * L.symm z + β) - (α * L.symm w + β) = α * (L.symm z - L.symm w) by ring,
      norm_mul, ← dist_eq_norm, L.symm.dist_map]
    have hαnorm : ‖α‖ = 2 / dist a b := by
      rw [hα, norm_div]
      rw [show ‖(2:ℂ)‖ = 2 by norm_num]
      congr 1
      rw [hB, hA, ← dist_eq_norm, L.symm.dist_map, dist_comm]
    rw [hαnorm]
  · -- T a = !₂[-1,0]
    have hval : α * A + β = -1 := by rw [hα, hβ]; field_simp; ring
    rw [hT_apply, ← hA, hval, hL]; exact complexLIE_negOne
  · -- T b = !₂[1,0]
    have hval : α * B + β = 1 := by rw [hα, hβ]; field_simp; ring
    rw [hT_apply, ← hB, hval, hL]; exact complexLIE_one

/-- Boundedness is preserved and reflected by a map scaling all distances by a fixed
positive factor. -/
theorem isBounded_image_scaling {T : Plane → Plane} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ z w, dist (T z) (T w) = c * dist z w) (K : Set Plane) :
    IsBounded (T '' K) ↔ IsBounded K := by
  simp only [Metric.isBounded_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / c, fun x hx y hy => ?_⟩
    have h := hC (mem_image_of_mem T hx) (mem_image_of_mem T hy)
    rw [hscale] at h
    rw [le_div_iff₀ hc, mul_comm]; exact h
  · rintro ⟨C, hC⟩
    refine ⟨c * C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hC hx hy) hc.le

/-! ### Setup lemmas for the normalized frame (Steps A, B) -/

/-- Squared Euclidean distance in `Plane` expanded in coordinates. -/
lemma dist_sq_coord (z w : Plane) :
    dist z w ^ 2 = (z 0 - w 0) ^ 2 + (z 1 - w 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- **Setup 1 (the "lens").** In the normalized frame with the farthest pair at
`a = !₂[-1,0]`, `b = !₂[1,0]` and diameter `2` (`hfar`), the whole curve lies in
the rectangle `[-1,1] × [-2,2]`. For `z ∈ range r`, both `dist z a ≤ 2` and
`dist z b ≤ 2`, i.e. `(z 0+1)²+(z 1)² ≤ 4` and `(z 0-1)²+(z 1)² ≤ 4`; these force
`z 0 ∈ [-1,1]` and (adding them) `(z 0)²+(z 1)² ≤ 3`, hence `z 1 ∈ [-2,2]`. -/
theorem normalized_subset_rectangle
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    range r ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} := by
  intro z hz
  have hza : dist z (!₂[(-1:ℝ), 0]) ≤ 2 := hfar z hz _ hm
  have hzb : dist z (!₂[(1:ℝ), 0]) ≤ 2 := hfar z hz _ hp
  have hza2 : dist z (!₂[(-1:ℝ), 0]) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := (!₂[(-1:ℝ), 0] : Plane))]
  have hzb2 : dist z (!₂[(1:ℝ), 0]) ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := (!₂[(1:ℝ), 0] : Plane))]
  rw [dist_sq_coord] at hza2 hzb2
  have ea0 : (!₂[(-1:ℝ), 0] : Plane) 0 = -1 := by simp
  have ea1 : (!₂[(-1:ℝ), 0] : Plane) 1 = 0 := by simp
  have eb0 : (!₂[(1:ℝ), 0] : Plane) 0 = 1 := by simp
  have eb1 : (!₂[(1:ℝ), 0] : Plane) 1 = 0 := by simp
  rw [ea0, ea1] at hza2
  rw [eb0, eb1] at hzb2
  simp only [mem_ofPred_eq, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 1)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]
  · nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - 2), sq_nonneg (z 1 + 2)]

/-- **`arc_path` (reusable reparametrization).** A path in a set `S ⊆ Plane`
joining `a` to `b` can be reparametrized to a map `h : ℝ → Plane` on the interval
`[-1,1]`, with `h (-1) = a`, `h 1 = b`, continuous on `[-1,1]`, and staying in `S`.
This is exactly the shape required by the `crossing` lemma for the horizontal path
(endpoints on the left/right edges of a rectangle). -/
theorem arc_path {S : Set Plane} {a b : Plane} (hj : JoinedIn S a b) :
    ∃ h : ℝ → Plane, ContinuousOn h (Icc (-1:ℝ) 1) ∧ h (-1) = a ∧ h 1 = b ∧
      ∀ t ∈ Icc (-1:ℝ) 1, h t ∈ S := by
  refine ⟨fun t => hj.somePath (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)),
    ?_, ?_, ?_, ?_⟩
  · exact (hj.somePath.continuous.comp
      (continuous_projIcc.comp (by fun_prop))).continuousOn
  · show hj.somePath _ = a
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((-1:ℝ) + 1) / 2) = 0 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.source
  · show hj.somePath _ = b
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) (((1:ℝ) + 1) / 2) = 1 from
      Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hj.somePath.target
  · intro t _; exact hj.somePath_mem _

/-- **Setup 2 (segment meets curve).** The vertical segment from `s = !₂[0,-2]` to
`n = !₂[0,2]` meets the curve. Proof via the `crossing` lemma with horizontal path
`h` a curve-path from `a = !₂[-1,0]` to `b = !₂[1,0]` (the curve is path-connected,
reparametrized by `arc_path`) staying in the rectangle `[-1,1]×[-2,2]`
(`normalized_subset_rectangle`), and vertical path `v t = !₂[0, 2t]` running from the
bottom edge `y=-2` to the top edge `y=2`. Delivers a curve point on the vertical
axis. -/
theorem segment_meets_curve (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (_hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ p ∈ range r, p 0 = 0 ∧ p 1 ∈ Icc (-2:ℝ) 2 := by
  -- the curve is path-connected (continuous image of the path-connected circle)
  have hsp : IsPathConnected (sphere (0:Plane) 1) :=
    isPathConnected_sphere one_lt_rank_plane 0 (by norm_num)
  have : PathConnectedSpace ↥(sphere (0:Plane) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsp
  have h1 : IsPathConnected (univ : Set ↥(sphere (0:Plane) 1)) :=
    pathConnectedSpace_iff_univ.mp ‹_›
  have hpc : IsPathConnected (range r) := by
    have := h1.image hcont; rwa [image_univ] at this
  have hjoin : JoinedIn (range r) (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]) :=
    hpc.joinedIn _ hm _ hp
  obtain ⟨h, hcontOn, hh1, hh2, hhmem⟩ := arc_path hjoin
  have hrect := normalized_subset_rectangle hm hp hfar
  -- vertical path `v t = !₂[0, 2t]`
  set v : ℝ → Plane := fun t => !₂[(0:ℝ), 2 * t] with hvdef
  have hvcont : ContinuousOn v (Icc (-1:ℝ) 1) := by
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have hv0 : ∀ t : ℝ, v t 0 = 0 := by intro t; simp [hvdef]
  have hv1 : ∀ t : ℝ, v t 1 = 2 * t := by intro t; simp [hvdef]
  -- edge/rectangle conditions
  have hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc (-1:ℝ) 1 ∧ h t 1 ∈ Icc (-2:ℝ) 2 :=
    fun t ht => hrect (hhmem t ht)
  have hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2 := by
    intro t ht
    rw [mem_Icc] at ht
    refine ⟨?_, ?_⟩
    · rw [hv0]; simp
    · rw [hv1, mem_Icc]; constructor <;> nlinarith [ht.1, ht.2]
  have hh1' : h (-1) 0 = -1 := by rw [hh1]; simp
  have hh2' : h 1 0 = 1 := by rw [hh2]; simp
  have hv1e : v (-1) 1 = -2 := by rw [hv1]; norm_num
  have hv2e : v 1 1 = 2 := by rw [hv1]; norm_num
  obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1)
    (by norm_num : (-2:ℝ) ≤ 2) h v hcontOn hvcont hhE hvE hh1' hh2' hv1e hv2e
  refine ⟨h s, hhmem s hs, ?_, ?_⟩
  · rw [heq, hv0]
  · rw [heq]; exact (hvE t ht).2

/-- **Setup 3 (top of the axis).** The intersection of the curve with the vertical
axis `Jax = {p ∈ range r | p 0 = 0}` is compact (closed subset of the compact
curve) and nonempty (`segment_meets_curve`), hence attains its `y`-maximum at some
point `l ∈ range r` with `l 0 = 0`. -/
theorem exists_ymax_on_axis (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ l ∈ range r, l 0 = 0 ∧ ∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1 := by
  set Jax : Set Plane := {p ∈ range r | p 0 = 0} with hJax
  have hsub : Jax ⊆ range r := fun p hp => hp.1
  have hJaxcl : IsClosed Jax :=
    (jordanCurve_isClosed r hcont).inter (isClosed_eq (by fun_prop) continuous_const)
  have hJaxcpt : IsCompact Jax :=
    (jordanCurve_isCompact r hcont).of_isClosed_subset hJaxcl hsub
  have hne : Jax.Nonempty := by
    obtain ⟨p, hpr, hp0, _⟩ := segment_meets_curve hbr hcont hinj hm hp hfar
    exact ⟨p, hpr, hp0⟩
  have hcy : Continuous (fun p : Plane => p 1) := by fun_prop
  obtain ⟨l, hlJax, hlmax⟩ :=
    hJaxcpt.exists_isMaxOn hne (f := fun p : Plane => p 1) hcy.continuousOn
  refine ⟨l, hlJax.1, hlJax.2, ?_⟩
  intro p hpr hp0
  exact hlmax (show p ∈ Jax from ⟨hpr, hp0⟩)

/-- **Image of an arc under the subtype coercion is again an arc.** If `A ⊆ ↥K`
(a subset of a subtype of `Plane`) is homeomorphic to `unitInterval`, then its image
`(↑) '' A ⊆ Plane` is homeomorphic to `unitInterval`. The composite coercion
`↥A → Plane` is a continuous injection from a compact space to a Hausdorff space,
hence a (closed) embedding, so `↥A ≃ₜ ↥(range …) = ↥((↑) '' A)`. -/
lemma planar_arc_homeo {K : Set Plane} {A : Set ↥K}
    (e : A ≃ₜ unitInterval) : Nonempty (((↑) '' A : Set Plane) ≃ₜ unitInterval) := by
  have : CompactSpace ↥A := e.symm.compactSpace
  let k : ↥A → Plane := fun a => ((a : ↥K) : Plane)
  have hkc : Continuous k := continuous_subtype_val.comp continuous_subtype_val
  have hki : Injective k := Subtype.coe_injective.comp Subtype.coe_injective
  have hemb : Topology.IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
  have hrange : Set.range k = ((↑) '' A : Set Plane) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨((Homeomorph.setCongr hrange).symm.trans hemb.toHomeomorph.symm).trans e⟩

/-- **Setup 4 (arc split at `a`, `b`).** The curve `range r` splits at the farthest
pair `a = !₂[-1,0]`, `b = !₂[1,0]` into two closed arcs `J_n`, `J_s ⊆ Plane`, each
`≃ₜ unitInterval`, with `J_n ∪ J_s = range r` and `J_n ∩ J_s = {a, b}`, labelled so
that the `y`-topmost axis point `l` lies in `J_n`. -/
theorem jordan_arcs (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ J_n J_s : Set Plane,
      IsClosed J_n ∧ IsClosed J_s ∧
      J_n ∪ J_s = range r ∧
      J_n ∩ J_s = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} ∧
      Nonempty (J_n ≃ₜ unitInterval) ∧ Nonempty (J_s ≃ₜ unitInterval) ∧
      IsPathConnected (J_n \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      IsPathConnected (J_s \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) ∧
      ∃ l ∈ range r, l 0 = 0 ∧ (∀ p ∈ range r, p 0 = 0 → p 1 ≤ l 1) ∧ l ∈ J_n := by
  obtain ⟨l, hlr, hl0, hlmax⟩ := exists_ymax_on_axis hbr hcont hinj hm hp hfar
  set J := jordanCurveHomeo r hcont hinj with hJdef
  have hab : (!₂[(-1:ℝ), 0] : Plane) ≠ !₂[(1:ℝ), 0] := by
    intro h
    have h0 : (!₂[(-1:ℝ), 0] : Plane) 0 = (!₂[(1:ℝ), 0] : Plane) 0 := by rw [h]
    rw [show (!₂[(-1:ℝ), 0] : Plane) 0 = -1 from by simp,
        show (!₂[(1:ℝ), 0] : Plane) 0 = 1 from by simp] at h0
    norm_num at h0
  set x : sphere (0 : Plane) 1 := J.symm ⟨_, hm⟩ with hxdef
  set y : sphere (0 : Plane) 1 := J.symm ⟨_, hp⟩ with hydef
  have hxy : x ≠ y := by
    intro h
    exact hab (Subtype.ext_iff.mp (J.symm.injective h))
  obtain ⟨A₁, A₂, hc1, hc2, hu, hi, ⟨e1⟩, ⟨e2⟩, hpcA1, hpcA2⟩ := Arcs.jordanCurve_split J hxy
  -- transported endpoints: `J x = ⟨a,hm⟩`, `J y = ⟨b,hp⟩`
  have hJx : J x = ⟨_, hm⟩ := J.apply_symm_apply _
  have hJy : J y = ⟨_, hp⟩ := J.apply_symm_apply _
  -- planar images of the two arcs
  set B₁ : Set Plane := (↑) '' A₁ with hB1
  set B₂ : Set Plane := (↑) '' A₂ with hB2
  have hBu : B₁ ∪ B₂ = range r := by
    rw [hB1, hB2, ← Set.image_union, hu, Set.image_univ, Subtype.range_coe]
  have hBi : B₁ ∩ B₂ = {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} := by
    rw [hB1, hB2, ← Set.image_inter Subtype.coe_injective, hi, hJx, hJy,
      Set.image_pair]
  have hn1 : Nonempty (B₁ ≃ₜ unitInterval) := planar_arc_homeo e1
  have hn2 : Nonempty (B₂ ≃ₜ unitInterval) := planar_arc_homeo e2
  have hcl1 : IsClosed B₁ :=
    (isCompact_iff_compactSpace.mpr hn1.some.symm.compactSpace).isClosed
  have hcl2 : IsClosed B₂ :=
    (isCompact_iff_compactSpace.mpr hn2.some.symm.compactSpace).isClosed
  -- transport path-connectedness of the arc interiors down to the plane
  have hpcB1 : IsPathConnected (B₁ \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) := by
    have h := hpcA1.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h
  have hpcB2 : IsPathConnected (B₂ \ {!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]}) := by
    have h := hpcA2.image (continuous_subtype_val (p := fun z => z ∈ range r))
    rwa [Set.image_sdiff Subtype.coe_injective, Set.image_insert_eq, Set.image_singleton,
      hJx, hJy] at h
  -- `l` lies in `range r = B₁ ∪ B₂`; label the containing arc `J_n`
  have hlB : l ∈ B₁ ∪ B₂ := by rw [hBu]; exact hlr
  rcases hlB with hl | hl
  · exact ⟨B₁, B₂, hcl1, hcl2, hBu, hBi, hn1, hn2, hpcB1, hpcB2, l, hlr, hl0, hlmax, hl⟩
  · refine ⟨B₂, B₁, hcl2, hcl1, ?_, ?_, hn2, hn1, hpcB2, hpcB1, l, hlr, hl0, hlmax, hl⟩
    · rw [Set.union_comm]; exact hBu
    · rw [Set.inter_comm]; exact hBi

end MatedCRTHarmonic.Planar.Jordan
