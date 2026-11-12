/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112L1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112A
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine

/-!
# D112 packet L1, part 1: the deterministic geometry of the family `(K_C, W_C)`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.3 (C:1176–1244) in the corrected form
of decision D112 (`decisions/DEC-112.md` §2): the event `fatG` (S3D112A) uses, for every grid
component `C` of the free squares, the finite set of centres `K_C = confCtrs` and the open
`δr/4`-neighbourhood `W_C = confFatW` of the spine.

* `confFatW_subset_innerPart` : `W_C ⊆ U_{δr/4}` (DEC-112 §2: each point of `W_C` is within
  `δr/4` of a point `q` of a segment between centres of adjacent free squares, and the open
  `δr/2`-ball around `q` lies in `int(S_k ∪ S_{k'}) ⊆ U`); this is what Step 1 (condition 3 of
  `E^U_r(z)`, C:1203) needs.
* the affine scaling lemmas (CONF C:1153, `𝒮^z_{δr} = r 𝒮^0_δ + z`): `confCtr_scale`,
  `confSq_scale`, `confFatW_scale`, `confFull_scale`, `confFree_scale`, `confU_scale`,
  `confSqIdx_annulus_scale`; Step 2 (C:1219–1234) works with the unit configuration.
* `closure_innerPart_subset`, `isOpen_innerPart`; the connectedness and finiteness facts are in
  `S3D112L1b`.

Own elementary geometry (DEC-112 §2 sketches the inclusion; CONF leaves it implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-! ## Affine scaling -/

lemma affFwd_re (r : ℝ) (z y : ℂ) : (affFwd r z y).re = r * y.re + z.re := by
  simp [affFwd]

lemma affFwd_im (r : ℝ) (z y : ℂ) : (affFwd r z y).im = r * y.im + z.im := by
  simp [affFwd]

lemma dist_affFwd {r : ℝ} (hr : 0 < r) (z x y : ℂ) :
    dist (affFwd r z x) (affFwd r z y) = r * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, affFwd, affFwd, add_sub_add_right_eq_sub, ← smul_sub,
    norm_smul, Real.norm_of_nonneg hr.le]

lemma eq_image_affFwd_of {r : ℝ} (hr : r ≠ 0) {z : ℂ} {S₁ S : Set ℂ}
    (h : ∀ y, affFwd r z y ∈ S ↔ y ∈ S₁) : S = affFwd r z '' S₁ := by
  ext x
  constructor
  · intro hx
    refine ⟨affMap r z x, ?_, affFwd_affMap hr x⟩
    rw [← h, affFwd_affMap hr]; exact hx
  · rintro ⟨y, hy, rfl⟩; exact (h y).2 hy

theorem confCtr_scale (δ r : ℝ) (z : ℂ) (k : ℤ × ℤ) :
    confCtr (δ * r) z k = affFwd r z (confCtr δ 0 k) := by
  apply Complex.ext
  · rw [affFwd_re]; simp [confCtr]; ring
  · rw [affFwd_im]; simp [confCtr]; ring

theorem confSq_scale {δ r : ℝ} (hr : 0 < r) (z : ℂ) (k : ℤ × ℤ) :
    confSq (δ * r) z k = affFwd r z '' confSq δ 0 k := by
  refine eq_image_affFwd_of hr.ne' fun y => ?_
  simp only [confSq, mem_setOf_eq, affFwd_re, affFwd_im, Complex.zero_re, Complex.zero_im,
    zero_add]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma norm_affFwd_sub {r : ℝ} (hr : 0 < r) (z y : ℂ) : ‖affFwd r z y - z‖ = r * ‖y‖ := by
  rw [affFwd, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hr.le]

theorem confMidAnn_scale {δ r : ℝ} (hr : 0 < r) (z : ℂ) :
    confMidAnn z r (δ * r) = affFwd r z '' confMidAnn 0 1 δ := by
  refine eq_image_affFwd_of hr.ne' fun y => ?_
  simp only [confMidAnn, mem_setOf_eq, norm_affFwd_sub hr, sub_zero]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

theorem annulus_scale {r : ℝ} (hr : 0 < r) (z : ℂ) (a b : ℝ) :
    (annulus z (a * r) (b * r) : Set ℂ) = affFwd r z '' (annulus 0 a b : Set ℂ) := by
  refine eq_image_affFwd_of hr.ne' fun y => ?_
  change a * r < ‖affFwd r z y - z‖ ∧ ‖affFwd r z y - z‖ < b * r ↔ a < ‖y - 0‖ ∧ ‖y - 0‖ < b
  rw [norm_affFwd_sub hr, sub_zero]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

lemma confSqIdx_image {δ r : ℝ} (hr : 0 < r) (z : ℂ) (V : Set ℂ) :
    confSqIdx (δ * r) z (affFwd r z '' V) = confSqIdx δ 0 V := by
  ext k
  simp only [confSqIdx, mem_setOf_eq, confSq_scale hr z k]
  rw [← image_inter (fun a b h => by
    have := congrArg (affMap r z) h; rwa [affMap_affFwd hr.ne', affMap_affFwd hr.ne'] at this),
    image_nonempty]

theorem confFull_scale {δ r : ℝ} (hr : 0 < r) (z : ℂ) :
    confFull (δ * r) z r = confFull δ 0 1 := by
  rw [confFull, confFull, confMidAnn_scale hr z, confSqIdx_image hr]

theorem confFree_scale {δ r : ℝ} (hr : 0 < r) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    confFree (δ * r) z r T = confFree δ 0 1 T := by
  rw [confFree, confFree, confFull_scale hr z]

theorem confSqIdx_annulus_scale {δ r : ℝ} (hr : 0 < r) (z : ℂ) :
    confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)) = confSqIdx δ 0 (annulus 0 3 4) := by
  rw [annulus_scale hr z 3 4, confSqIdx_image hr]

theorem confU_scale {δ r : ℝ} (hr : 0 < r) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    confU r δ z T = affFwd r z '' confU 1 δ 0 T := by
  have hinj : Function.Injective (affFwd r z) := fun a b h => by
    have := congrArg (affMap r z) h; rwa [affMap_affFwd hr.ne', affMap_affFwd hr.ne'] at this
  rw [confU, confU, image_diff hinj, annulus_scale hr z 3 4, image_iUnion₂]
  simp only [mul_one]
  simp_rw [confSq_scale hr z]

/-- the affine map `y ↦ r y + z` as an `ℝ`-affine map -/
def affFwdA (r : ℝ) (z : ℂ) : ℂ →ᵃ[ℝ] ℂ :=
  ⟨affFwd r z, r • LinearMap.id, fun p v => by simp [affFwd, smul_add, add_assoc, add_comm]⟩

theorem confSpine_scale (δ r : ℝ) (z : ℂ) (C : Set (ℤ × ℤ)) :
    confSpine (δ * r) z C = affFwd r z '' confSpine δ 0 C := by
  simp only [confSpine, image_iUnion]
  refine iUnion_congr fun k => iUnion_congr fun _ => iUnion_congr fun k' =>
    iUnion_congr fun _ => iUnion_congr fun _ => ?_
  rw [confCtr_scale, confCtr_scale]
  exact (image_segment ℝ (affFwdA r z) _ _).symm

theorem confFatW_scale {δ r : ℝ} (hr : 0 < r) (z : ℂ) (C : Set (ℤ × ℤ)) :
    confFatW (δ * r) z C = affFwd r z '' confFatW δ 0 C := by
  refine eq_image_affFwd_of hr.ne' fun y => ?_
  simp only [confFatW, mem_thickening_iff, confSpine_scale δ r z C]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hd⟩
    refine ⟨q, hq, ?_⟩
    rw [dist_affFwd hr] at hd
    nlinarith
  · rintro ⟨q, hq, hd⟩
    refine ⟨affFwd r z q, ⟨q, hq, rfl⟩, ?_⟩
    rw [dist_affFwd hr]; nlinarith

theorem confCtrs_scale (δ r : ℝ) (z : ℂ) (C : Set (ℤ × ℤ)) :
    confCtrs (δ * r) z C = affFwd r z '' confCtrs δ 0 C := by
  rw [confCtrs, confCtrs, image_image]
  exact image_congr fun k _ => confCtr_scale δ r z k

/-! ## `innerPart` -/

theorem isOpen_innerPart {U : Set ℂ} (hU : IsOpen U) (ε : ℝ) : IsOpen (innerPart U ε) :=
  hU.inter (isOpen_lt continuous_const (continuous_infDist_pt _))

theorem closure_innerPart_subset {U : Set ℂ} (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    closure (innerPart U ε) ⊆ U := by
  have hsub : innerPart U ε ⊆ closure U ∩ {u | ε ≤ infDist u (frontier U)} :=
    fun u hu => ⟨subset_closure hu.1, hu.2.le⟩
  have hcl : IsClosed (closure U ∩ {u | ε ≤ infDist u (frontier U)}) :=
    isClosed_closure.inter (isClosed_le continuous_const (continuous_infDist_pt _))
  intro u hu
  obtain ⟨h1, h2⟩ := closure_minimal hsub hcl hu
  by_contra hnot
  have hfr : u ∈ frontier U := by
    rw [frontier, hU.interior_eq]; exact ⟨h1, hnot⟩
  have : infDist u (frontier U) = 0 := infDist_zero_of_mem hfr
  simp only [mem_setOf_eq, this] at h2
  linarith

/-! ## `W_C ⊆ U_{δr/4}` -/

/-- a point within `ε` of the centre of a full square lies in `𝔸_{3r,4r}(z)` -/
lemma mem_annulus_of_near_full {ε r : ℝ} (hε : 0 < ε) {z : ℂ} {j : ℤ × ℤ}
    (hj : j ∈ confFull ε z r) {p : ℂ} (hp : dist p (confCtr ε z j) < ε) :
    p ∈ (annulus z (3 * r) (4 * r) : Set ℂ) := by
  obtain ⟨u, ⟨q1, q2, q3, q4⟩, hu⟩ := hj
  have d2 : dist (confCtr ε z j) u ≤ ε := by
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    have h1 : |(confCtr ε z j).re - u.re| ≤ ε / 2 := by
      rw [abs_le]; simp only [confCtr] at *; constructor <;> linarith
    have h2 : |(confCtr ε z j).im - u.im| ≤ ε / 2 := by
      rw [abs_le]; simp only [confCtr] at *; constructor <;> linarith
    linarith
  have d3 : dist p u < 2 * ε := by linarith [dist_triangle p (confCtr ε z j) u]
  have h1 : ‖u - z‖ - ‖p - z‖ ≤ dist p u := by
    rw [dist_comm, dist_eq_norm]; linarith [norm_sub_le_norm_sub_add_norm_sub u p z]
  have h2 : ‖p - z‖ - ‖u - z‖ ≤ dist p u := by
    rw [dist_eq_norm]; linarith [norm_sub_le_norm_sub_add_norm_sub p u z]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- integer window: `jε ≤ x ≤ (j+1)ε` and `mε < x < (m+1)ε` with `m` between `a` and `b`
force `min a b ≤ j ≤ max a b` -/
lemma int_window {ε x m : ℝ} (hε : 0 < ε) {j a b : ℤ} (h1 : (j : ℝ) * ε ≤ x)
    (h2 : x ≤ ((j : ℝ) + 1) * ε) (h3 : m * ε < x) (h4 : x < (m + 1) * ε)
    (hma : min (a : ℝ) b ≤ m) (hmb : m ≤ max (a : ℝ) b) : min a b ≤ j ∧ j ≤ max a b := by
  have e1 : (j : ℝ) < max (a : ℝ) b + 1 := by
    by_contra hc; push_neg at hc; nlinarith
  have e2 : min (a : ℝ) b - 1 < j := by
    by_contra hc; push_neg at hc; nlinarith
  have e1' : (j : ℝ) < ((max a b : ℤ) : ℝ) + 1 := by push_cast; exact e1
  have e2' : ((min a b : ℤ) : ℝ) - 1 < j := by push_cast; exact e2
  constructor
  · have : min a b - 1 < j := by exact_mod_cast e2'
    omega
  · have : j < max a b + 1 := by exact_mod_cast e1'
    omega

lemma sqAdj_cases {k k' : ℤ × ℤ} (h : k = k' ∨ SqAdj k k') :
    (k.1 = k'.1 ∧ (k'.2 - k.2 = 1 ∨ k'.2 - k.2 = -1 ∨ k'.2 = k.2)) ∨
      (k.2 = k'.2 ∧ (k'.1 - k.1 = 1 ∨ k'.1 - k.1 = -1)) := by
  rcases h with rfl | h
  · left; exact ⟨rfl, Or.inr (Or.inr rfl)⟩
  · unfold SqAdj at h
    have ha : k'.1 - k.1 = -1 ∨ k'.1 - k.1 = 0 ∨ k'.1 - k.1 = 1 := by
      have : -1 ≤ k'.1 - k.1 ∧ k'.1 - k.1 ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg (k'.2 - k.2)]
      omega
    have hb : k'.2 - k.2 = -1 ∨ k'.2 - k.2 = 0 ∨ k'.2 - k.2 = 1 := by
      have : -1 ≤ k'.2 - k.2 ∧ k'.2 - k.2 ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg (k'.1 - k.1)]
      omega
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb] at h <;>
      norm_num at h <;> omega

/-- the open `ε/2`-ball around a point of a segment between centres of free adjacent squares
lies in `U` -/
theorem ball_seg_subset_confU {δ r : ℝ} (hε : 0 < δ * r) {z : ℂ} {T : Finset (ℤ × ℤ)}
    {k k' : ℤ × ℤ} (hk : k ∈ confFree (δ * r) z r T) (hk' : k' ∈ confFree (δ * r) z r T)
    (hkk' : k = k' ∨ SqAdj k k') {q : ℂ}
    (hq : q ∈ segment ℝ (confCtr (δ * r) z k) (confCtr (δ * r) z k')) :
    ball q (δ * r / 2) ⊆ confU r δ z T := by
  set ε := δ * r
  intro p hp
  rw [mem_ball] at hp
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
  have hre : (a • confCtr ε z k + b • confCtr ε z k').re - z.re =
      (a * k.1 + b * k'.1 + 1 / 2) * ε := by
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, confCtr]
    have : b = 1 - a := by linarith
    subst this; ring
  have him : (a • confCtr ε z k + b • confCtr ε z k').im - z.im =
      (a * k.2 + b * k'.2 + 1 / 2) * ε := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, confCtr]
    have : b = 1 - a := by linarith
    subst this; ring
  set q := a • confCtr ε z k + b • confCtr ε z k'
  have hpre : |p.re - q.re| < ε / 2 := by
    have := Complex.abs_re_le_norm (p - q)
    rw [Complex.sub_re] at this; rw [dist_eq_norm] at hp; linarith
  have hpim : |p.im - q.im| < ε / 2 := by
    have := Complex.abs_im_le_norm (p - q)
    rw [Complex.sub_im] at this; rw [dist_eq_norm] at hp; linarith
  rw [abs_lt] at hpre hpim
  have mm : ∀ x y : ℝ, min x y ≤ a * x + b * y ∧ a * x + b * y ≤ max x y := by
    intro x y
    have e1 : a * x + b * y = x + b * (y - x) := by
      have : a = 1 - b := by linarith
      subst this; ring
    have e2 : a * x + b * y = y + a * (x - y) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]
      have := mul_nonneg ha (sub_nonneg.2 h); have := mul_nonneg hb (sub_nonneg.2 h)
      constructor <;> linarith
    · rw [min_eq_right h, max_eq_left h]
      have := mul_nonneg ha (sub_nonneg.2 h); have := mul_nonneg hb (sub_nonneg.2 h)
      constructor <;> linarith
  refine ⟨?_, ?_⟩
  · -- `p` lies in the annulus: it is within `ε` of the nearer centre
    rcases le_total a b with hab' | hab'
    · refine mem_annulus_of_near_full hε hk'.1 ?_
      have hd : dist q (confCtr ε z k') ≤ ε / 2 := by
        have e : q - confCtr ε z k' = a • (confCtr ε z k - confCtr ε z k') := by
          simp only [q]
          rw [smul_sub, show b = 1 - a by linarith, sub_smul, one_smul]; abel
        rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg ha, ← dist_eq_norm]
        have := confCtr_dist_le hε.le z hkk'
        nlinarith
      linarith [dist_triangle p q (confCtr ε z k')]
    · refine mem_annulus_of_near_full hε hk.1 ?_
      have hd : dist q (confCtr ε z k) ≤ ε / 2 := by
        have e : q - confCtr ε z k = b • (confCtr ε z k' - confCtr ε z k) := by
          simp only [q]
          rw [smul_sub, show a = 1 - b by linarith, sub_smul, one_smul]; abel
        rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg hb, ← dist_eq_norm, dist_comm]
        have := confCtr_dist_le hε.le z hkk'
        nlinarith
      linarith [dist_triangle p q (confCtr ε z k)]
  · -- `p` lies in no removed square
    simp only [mem_iUnion, not_exists]
    intro j hjT hpj
    obtain ⟨j1, j2, j3, j4⟩ := hpj
    have w1 := int_window hε (x := p.re - z.re) (m := a * k.1 + b * k'.1) (j := j.1) (a := k.1)
      (b := k'.1) (by linarith) (by linarith) (by linarith) (by linarith)
      (mm _ _).1 (mm _ _).2
    have w2 := int_window hε (x := p.im - z.im) (m := a * k.2 + b * k'.2) (j := j.2) (a := k.2)
      (b := k'.2) (by linarith) (by linarith) (by linarith) (by linarith)
      (mm _ _).1 (mm _ _).2
    have hjk : j = k ∨ j = k' := by
      rcases sqAdj_cases hkk' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rcases e2 with e2 | e2 | e2
        · rcases (show j.2 = k.2 ∨ j.2 = k'.2 by omega) with h | h
          · left; exact Prod.ext (by omega) h
          · right; exact Prod.ext (by omega) h
        · rcases (show j.2 = k.2 ∨ j.2 = k'.2 by omega) with h | h
          · left; exact Prod.ext (by omega) h
          · right; exact Prod.ext (by omega) h
        · left; exact Prod.ext (by omega) (by omega)
      · rcases (show j.1 = k.1 ∨ j.1 = k'.1 by omega) with h | h
        · left; exact Prod.ext h (by omega)
        · right; exact Prod.ext h (by omega)
    rcases hjk with rfl | rfl
    · exact hk.2 hjT
    · exact hk'.2 hjT

/-- **`W_C ⊆ U_{δr/4}`** (DEC-112 §2) for every set `C` of free squares -/
theorem confFatW_subset_innerPart {δ r : ℝ} (hε : 0 < δ * r) (z : ℂ) {T : Finset (ℤ × ℤ)}
    {C : Set (ℤ × ℤ)} (hC : C ⊆ confFree (δ * r) z r T) :
    confFatW (δ * r) z C ⊆ innerPart (confU r δ z T) (δ * r / 4) := by
  intro y hy
  obtain ⟨q, hq, hd⟩ := mem_thickening_iff.1 hy
  simp only [confSpine, mem_iUnion] at hq
  obtain ⟨k, hk, k', hk', hkk', hq⟩ := hq
  have hB := ball_seg_subset_confU hε (hC hk) (hC hk') hkk' hq
  have hyU : y ∈ confU r δ z T := hB (by rw [mem_ball]; linarith)
  refine ⟨hyU, ?_⟩
  have hBi : ball q (δ * r / 2) ⊆ interior (confU r δ z T) :=
    interior_maximal hB isOpen_ball
  have hfne : (frontier (confU r δ z T)).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨⟨y, hyU⟩, ?_⟩
    intro hall
    have h0 : (0 : ℂ) + z ∉ confU r δ z T := by
      intro h
      have h1 : 3 * r < ‖0 + z - z‖ ∧ ‖0 + z - z‖ < 4 * r := h.1
      simp only [zero_add, sub_self, norm_zero] at h1; linarith [h1.1, h1.2]
    rw [hall] at h0; exact h0 trivial
  have key : δ * r / 2 - dist y q ≤ infDist y (frontier (confU r δ z T)) := by
    rw [le_infDist hfne]
    intro x hx
    have hxq : δ * r / 2 ≤ dist x q := by
      by_contra hc; push_neg at hc
      exact hx.2 (hBi (mem_ball.2 hc))
    linarith [dist_triangle x y q, dist_comm x y]
  linarith

end LQGMetric.CONF
