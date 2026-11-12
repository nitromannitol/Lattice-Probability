/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112A

/-!
# D112 packet G1b: the full squares are grid-connected (`CONFFullConn`)

Decision D112 (`decisions/DEC-112.md` §2–§4), grid claim used for CONF (3.21) (Gwynne–Miller,
*Confluence of geodesics in LQG*, arXiv:1905.00381, `confluence-final.tex` C:1392–1396).

* `confSqIdx_rtg_of_isPreconnected`: the squares of side `ε` meeting a preconnected set `X ⊆ ℂ`
  are connected in the edge-adjacency grid graph on `confSqIdx ε z X`. Proof: for `w ∈ ℂ` let
  `g w` be its floor-index square; every square containing `w ∈ X` is joined to `g w` through
  squares containing `w` (the corner case goes through a third square at the corner); for `y`
  near `x` the square `g y` contains `x`; so `x, y ↦ g x ~ g y` is an equivalence relation that
  holds locally, hence everywhere on the preconnected `X` (`IsPreconnected.induction₂'`).
* `confMidAnn_isPreconnected`: the closed annulus is the image of `[a, b] × ℝ` under
  `(t, θ) ↦ z + t e^{iθ}`.
* **`confFullConn : CONFFullConn`**.

Own elementary proof (DEC-112 §4, packet G1b; DEVIATIONS DV-D112).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology

namespace LQGMetric.CONF

open Blueprint

/-- the floor-index square of `w` in the grid `𝒮^z_ε` -/
def confFloorIdx (ε : ℝ) (z w : ℂ) : ℤ × ℤ := (⌊(w.re - z.re) / ε⌋, ⌊(w.im - z.im) / ε⌋)

theorem confSq_mem_iff {ε : ℝ} (hε : 0 < ε) (z w : ℂ) (k : ℤ × ℤ) :
    w ∈ confSq ε z k ↔ ((k.1 : ℝ) ≤ (w.re - z.re) / ε ∧ (w.re - z.re) / ε ≤ k.1 + 1) ∧
      ((k.2 : ℝ) ≤ (w.im - z.im) / ε ∧ (w.im - z.im) / ε ≤ k.2 + 1) := by
  simp only [confSq, Set.mem_ofPred_eq, le_div_iff₀ hε, div_le_iff₀ hε]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem confFloorIdx_mem {ε : ℝ} (hε : 0 < ε) (z w : ℂ) : w ∈ confSq ε z (confFloorIdx ε z w) := by
  rw [confSq_mem_iff hε]
  simp only [confFloorIdx]
  exact ⟨⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩, Int.floor_le _, (Int.lt_floor_add_one _).le⟩

/-- two integers whose unit intervals both contain `a` differ by at most one -/
theorem int_close_of_mem {n m : ℤ} {a : ℝ} (hn : (n : ℝ) ≤ a ∧ a ≤ n + 1)
    (hm : (m : ℝ) ≤ a ∧ a ≤ m + 1) : n = m ∨ n = m + 1 ∨ m = n + 1 := by
  have h1 : n ≤ m + 1 := by exact_mod_cast (show (n : ℝ) ≤ m + 1 by linarith)
  have h2 : m ≤ n + 1 := by exact_mod_cast (show (m : ℝ) ≤ n + 1 by linarith)
  omega

theorem confGridRel_symm (F : Set (ℤ × ℤ)) {k k' : ℤ × ℤ} (h : confGridRel F k k') :
    confGridRel F k' k :=
  ⟨sqAdj_symm h.1, h.2.2, h.2.1⟩

/-- two squares containing a common point `w ∈ X` and sharing a row or a column are equal or
adjacent -/
theorem confRtg_step {ε : ℝ} (hε : 0 < ε) (z : ℂ) {X : Set ℂ} {w : ℂ} (hw : w ∈ X)
    {k k' : ℤ × ℤ} (hk : w ∈ confSq ε z k) (hk' : w ∈ confSq ε z k')
    (h : k.1 = k'.1 ∨ k.2 = k'.2) :
    Relation.ReflTransGen (confGridRel (confSqIdx ε z X)) k k' := by
  have hkI : k ∈ confSqIdx ε z X := ⟨w, hk, hw⟩
  have hk'I : k' ∈ confSqIdx ε z X := ⟨w, hk', hw⟩
  rw [confSq_mem_iff hε] at hk hk'
  have c1 := int_close_of_mem hk.1 hk'.1
  have c2 := int_close_of_mem hk.2 hk'.2
  obtain ⟨a, b⟩ := k
  obtain ⟨a', b'⟩ := k'
  simp only at h c1 c2
  have hor : (a = a' ∧ b = b') ∨ SqAdj (a, b) (a', b') := by
    unfold SqAdj; simp only
    rcases h with rfl | rfl
    · rcases c2 with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · right; ring
      · right; ring
    · rcases c1 with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · right; ring
      · right; ring
  rcases hor with ⟨rfl, rfl⟩ | hadj
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hadj, hkI, hk'I⟩

/-- any two squares containing a common point `w ∈ X` are grid-connected in `confSqIdx ε z X`
(through the square `(k'.1, k.2)`, which also contains `w`) -/
theorem confRtg_of_common {ε : ℝ} (hε : 0 < ε) (z : ℂ) {X : Set ℂ} {w : ℂ} (hw : w ∈ X)
    {k k' : ℤ × ℤ} (hk : w ∈ confSq ε z k) (hk' : w ∈ confSq ε z k') :
    Relation.ReflTransGen (confGridRel (confSqIdx ε z X)) k k' := by
  have hj : w ∈ confSq ε z (k'.1, k.2) := by
    have a := (confSq_mem_iff hε z w k).1 hk
    have b := (confSq_mem_iff hε z w k').1 hk'
    exact (confSq_mem_iff hε z w _).2 ⟨b.1, a.2⟩
  exact (confRtg_step hε z hw hk hj (Or.inr rfl)).trans (confRtg_step hε z hw hj hk' (Or.inl rfl))

/-- for `y` close to `x`, the floor-index square of `y` contains `x` -/
theorem confFloorIdx_eventually {ε : ℝ} (hε : 0 < ε) (z x : ℂ) :
    ∀ᶠ y in 𝓝 x, x ∈ confSq ε z (confFloorIdx ε z y) := by
  have cA : Continuous fun y : ℂ => (y.re - z.re) / ε :=
    (Complex.continuous_re.sub continuous_const).div_const _
  have cB : Continuous fun y : ℂ => (y.im - z.im) / ε :=
    (Complex.continuous_im.sub continuous_const).div_const _
  set A := (x.re - z.re) / ε
  set B := (x.im - z.im) / ε
  have e1 := (cA.tendsto x).eventually (gt_mem_nhds (Int.lt_floor_add_one A))
  have e2 := (cA.tendsto x).eventually
    (lt_mem_nhds (show (⌈A⌉ : ℝ) - 1 < A by linarith [Int.ceil_lt_add_one A]))
  have e3 := (cB.tendsto x).eventually (gt_mem_nhds (Int.lt_floor_add_one B))
  have e4 := (cB.tendsto x).eventually
    (lt_mem_nhds (show (⌈B⌉ : ℝ) - 1 < B by linarith [Int.ceil_lt_add_one B]))
  filter_upwards [e1, e2, e3, e4] with y h1 h2 h3 h4
  rw [confSq_mem_iff hε]
  simp only [confFloorIdx]
  have key : ∀ {a b : ℝ}, b < ⌊a⌋ + 1 → (⌈a⌉ : ℝ) - 1 < b →
      ((⌊b⌋ : ℝ) ≤ a ∧ a ≤ ⌊b⌋ + 1) := by
    intro a b hb1 hb2
    have f1 : ⌊b⌋ < ⌊a⌋ + 1 := by
      exact_mod_cast (show (⌊b⌋ : ℝ) < ⌊a⌋ + 1 from lt_of_le_of_lt (Int.floor_le b) hb1)
    have f2 : ⌈a⌉ - 1 ≤ ⌊b⌋ := Int.le_floor.2 (by push_cast; linarith)
    have f1' : (⌊b⌋ : ℝ) ≤ ⌊a⌋ := by exact_mod_cast (show ⌊b⌋ ≤ ⌊a⌋ by omega)
    have f2' : (⌈a⌉ : ℝ) ≤ ⌊b⌋ + 1 := by exact_mod_cast (show ⌈a⌉ ≤ ⌊b⌋ + 1 by omega)
    exact ⟨f1'.trans (Int.floor_le a), (Int.le_ceil a).trans f2'⟩
  exact ⟨key h1 h2, key h3 h4⟩

/-- **the squares meeting a preconnected set are grid-connected** -/
theorem confSqIdx_rtg_of_isPreconnected {ε : ℝ} (hε : 0 < ε) (z : ℂ) {X : Set ℂ}
    (hX : IsPreconnected X) {k k' : ℤ × ℤ} (hk : k ∈ confSqIdx ε z X)
    (hk' : k' ∈ confSqIdx ε z X) :
    Relation.ReflTransGen (confGridRel (confSqIdx ε z X)) k k' := by
  set R := Relation.ReflTransGen (confGridRel (confSqIdx ε z X))
  have hsymm : ∀ {a b}, R a b → R b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single (confGridRel_symm _ hbc)).trans ih
  have key : ∀ x ∈ X, ∀ y ∈ X, R (confFloorIdx ε z x) (confFloorIdx ε z y) := by
    intro x hx y hy
    refine hX.induction₂' (fun x y => R (confFloorIdx ε z x) (confFloorIdx ε z y)) ?_
      (fun _ _ _ _ _ _ h1 h2 => h1.trans h2) hx hy
    intro x hx
    filter_upwards [nhdsWithin_le_nhds (confFloorIdx_eventually hε z x), self_mem_nhdsWithin]
      with y hy hyX
    have h := confRtg_of_common hε z hx (confFloorIdx_mem hε z x) hy
    exact ⟨h, hsymm h⟩
  obtain ⟨x, hxk, hxX⟩ := hk
  obtain ⟨y, hyk, hyX⟩ := hk'
  exact ((confRtg_of_common hε z hxX hxk (confFloorIdx_mem hε z x)).trans (key x hxX y hyX)).trans
    (confRtg_of_common hε z hyX (confFloorIdx_mem hε z y) hyk)

/-- the closed annulus `confMidAnn z r ε` is preconnected (image of `[3r+2ε, 4r−2ε] × ℝ` under
`(t, θ) ↦ z + t e^{iθ}`) -/
theorem confMidAnn_isPreconnected (z : ℂ) {r ε : ℝ} (h0 : 0 ≤ 3 * r + 2 * ε) :
    IsPreconnected (confMidAnn z r ε) := by
  have hf : Continuous fun q : ℝ × ℝ => z + (q.1 : ℂ) * Complex.exp (q.2 * Complex.I) := by
    fun_prop
  have heq : confMidAnn z r ε = (fun q : ℝ × ℝ => z + (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) ''
      (Icc (3 * r + 2 * ε) (4 * r - 2 * ε) ×ˢ univ) := by
    ext u
    constructor
    · intro hu
      refine ⟨(‖u - z‖, Complex.arg (u - z)), ⟨hu, trivial⟩, ?_⟩
      simp only
      rw [Complex.norm_mul_exp_arg_mul_I]; ring
    · rintro ⟨⟨t, θ⟩, ⟨⟨ht1, ht2⟩, -⟩, rfl⟩
      have hn : ‖z + (t : ℂ) * Complex.exp (θ * Complex.I) - z‖ = t := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      show 3 * r + 2 * ε ≤ _ ∧ _ ≤ 4 * r - 2 * ε
      rw [hn]; exact ⟨ht1, ht2⟩
  rw [heq]
  exact (isPreconnected_Icc.prod isPreconnected_univ).image _ hf.continuousOn

/-- **D112 packet G1b: the full squares are grid-connected** -/
theorem confFullConn : CONFFullConn := by
  intro δ r hδ _ hr z k hk k' hk'
  exact confSqIdx_rtg_of_isPreconnected (by positivity) z
    (confMidAnn_isPreconnected z (by positivity)) hk hk'

end LQGMetric.CONF
