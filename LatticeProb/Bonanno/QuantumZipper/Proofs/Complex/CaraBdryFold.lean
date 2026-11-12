/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CaraBdryFold at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdry

/-!
# EXT-CA C5 and C6: the fold lemma and injectivity at non-cut points

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 C5, C6. Standing data: `CarHyp ψ D E R₀`, a
continuous extension `F` of `ψ` to `Hbar` and the limit `wInf` of `ψ` at `∞` (C3,
`CA.Car.continuousOn_extension`).

* **C5** `fold`: if `x < y` and `F x = F y = q`, a preconnected `Z ⊆ E \ {q}` cannot meet both
  `F((x, y))` and `F(ℝ \ [x, y]) ∪ {wInf}`. `fold_infty`: the same with `y = ∞`
  (`F x = wInf = q`), separating `F((-∞, x))` from `F((x, ∞))`.
* **C6** `eq_of_isPreconnected_diff`: if `E \ {q}` is preconnected, `F` takes the value `q` at
  most once on `ℝ ∪ {∞}` (the value at `∞` being `wInf`).

Source: Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Prop. 2.5 and its proof,
printed pp. 23–24 (PDF pp. 31–32): for `F ζ₁ = F ζ₂ = a`, the image `J` of the crosscut `C`
joining them separates the images of the two boundary arcs, so these cannot be joined inside
`∂G \ {a}`; and Thm 2.6, p. 24 (a point that is not a cut point is attained only once).
Pommerenke's crosscut is a circular arc and the separation is the Jordan curve theorem; here the
crosscut is the semicircle over `[x, y]` (or the vertical ray over `x` when `y = ∞`) and the
separation is Janiszewski's theorem (`not_mem_closure_of_isPreconnected`, `CaraBdry.lean`),
DEVIATIONS L-CA-TOPO. That the boundary arcs are not points is C4.
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped Real

namespace QuantumZipper.CA.Car

open QuantumZipper.CA.Topo

theorem ofReal_mem_Hbar (t : ℝ) : ((t : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im by simp

/-- C1 for the extension: boundary values at real points lie in `frontier D`. -/
theorem extension_mem_frontier {ψ F : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) (x : ℝ) : F x ∈ frontier D := by
  have hT := tendsto_nhdsWithin_H_of_extension hEq hF (ofReal_mem_Hbar x)
  set z : ℕ → ℂ := fun n => (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hz
  have hzH : ∀ n, z n ∈ H := fun n => by
    show 0 < (z n).im
    simp only [hz, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, zero_add]
    positivity
  have hzx : Tendsto z atTop (𝓝 (x : ℂ)) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).ofReal.mul_const I).const_add
      (x : ℂ)
    simpa [hz] using this
  have hzw : Tendsto z atTop (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hzx, Eventually.of_forall hzH⟩
  exact frontier_mem_of_tendsto h hzH hzx (hT.comp hzw).mapClusterPt

/-- C1 at `∞`: the limit of `ψ` at `∞` lies in `frontier D`. -/
theorem limit_infty_mem_frontier {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    {wInf : ℂ} (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) :
    wInf ∈ frontier D := by
  set z : ℕ → ℂ := fun n => (((n : ℝ) + 1 : ℝ) : ℂ) * I with hz
  have hzH : ∀ n, z n ∈ H := fun n => by
    show 0 < (z n).im
    simp only [hz, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity
  have hzc : Tendsto z atTop (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    have : (fun n => ‖z n‖) = fun n : ℕ => (n : ℝ) + 1 := funext fun n => by
      simp only [hz, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    rw [this]
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hzl : Tendsto z atTop (Bornology.cobounded ℂ ⊓ 𝓟 H) :=
    tendsto_inf.2 ⟨hzc, tendsto_principal.2 (Eventually.of_forall hzH)⟩
  exact frontier_mem_of_tendsto_cobounded h hzH hzc (hInf.comp hzl).mapClusterPt

private theorem eq_of_mem_sphere_of_im_eq_zero {x y : ℝ} (hxy : x < y) {z : ℂ} (hz0 : z.im = 0)
    (hz : ‖z - (((x + y) / 2 : ℝ) : ℂ)‖ = (y - x) / 2) : z = x ∨ z = y := by
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
  rw [hzr, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hz
  rcases (abs_eq (by linarith : (0 : ℝ) ≤ (y - x) / 2)).1 hz with h | h
  · right; rw [hzr]; congr 1; linarith
  · left; rw [hzr]; congr 1; linarith

/-- **C5 (fold lemma).** If `x < y` and `F x = F y = q`, then a preconnected `Z ⊆ E \ {q}`
misses `F((x, y))`, or it misses `F(ℝ \ [x, y])` and the value `wInf` at `∞`. -/
theorem fold {ψ F : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀) (hEq : EqOn F ψ H)
    (hF : ContinuousOn F Hbar) {wInf : ℂ}
    (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) {x y : ℝ} (hxy : x < y) {q : ℂ}
    (hx : F x = q) (hy : F y = q) {Z : Set ℂ} (hZ : Z ⊆ E \ {q}) (hZc : IsPreconnected Z) :
    (∀ t ∈ Ioo x y, F t ∉ Z) ∨ ((∀ s : ℝ, s ∉ Icc x y → F s ∉ Z) ∧ wInf ∉ Z) := by
  set m : ℂ := (((x + y) / 2 : ℝ) : ℂ) with hm
  set r : ℝ := (y - x) / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  set Λ : Set ℂ := F '' (Hbar ∩ sphere m r) with hΛd
  have hΛ : IsCompact Λ :=
    ((isCompact_sphere m r).inter_left isClosed_Hbar).image_of_continuousOn
      (hF.mono inter_subset_left)
  have hΛD : Λ \ {q} ⊆ D := by
    rintro _ ⟨⟨z, ⟨hzH, hzs⟩, rfl⟩, hne⟩
    rcases (show (0 : ℝ) ≤ z.im from hzH).eq_or_lt with h0 | hpos
    · rw [mem_sphere, dist_eq_norm] at hzs
      rcases eq_of_mem_sphere_of_im_eq_zero hxy h0.symm hzs with rfl | rfl
      · exact absurd hx hne
      · exact absurd hy hne
    · rw [hEq hpos]; exact h.bij.mapsTo hpos
  set U₁ : Set ℂ := H ∩ ball m r with hU₁d
  set U₂ : Set ℂ := H ∩ {z | r < ‖z - m‖} with hU₂d
  have hU₁ : IsOpen U₁ := isOpen_H.inter isOpen_ball
  have hU₂ : IsOpen U₂ := isOpen_H.inter (isOpen_lt continuous_const (by fun_prop))
  have hU : Disjoint U₁ U₂ := by
    refine Set.disjoint_left.2 fun z h1 h2 => ?_
    have h1' := h1.2
    rw [mem_ball, dist_eq_norm] at h1'
    exact lt_asymm h1' h2.2
  have hcov : ∀ z ∈ H, z ∉ U₁ → z ∉ U₂ → ψ z ∈ Λ := by
    intro z hz h1 h2
    have e1 : ¬ ‖z - m‖ < r := fun hb => h1 ⟨hz, by rw [mem_ball, dist_eq_norm]; exact hb⟩
    have e2 : ¬ r < ‖z - m‖ := fun hb => h2 ⟨hz, hb⟩
    exact ⟨z, ⟨H_subset_Hbar hz, by
      rw [mem_sphere, dist_eq_norm]; exact le_antisymm (not_lt.1 e2) (not_lt.1 e1)⟩, hEq hz⟩
  have hZΛ : ∀ p ∈ Z, p ∉ Λ := fun p hp hpΛ =>
    h.sub_compl (hZ hp).1 (hΛD ⟨hpΛ, (hZ hp).2⟩)
  have core := fun {p₁ p₂ : ℂ} (h₁ : p₁ ∈ Z) (h₂ : p₂ ∈ Z) (hp₁ : p₁ ∈ closure (ψ '' U₁)) =>
    not_mem_closure_of_isPreconnected h hΛ hΛD hU₁ hU₂ inter_subset_left inter_subset_left hU
      hcov hZc hZΛ h₁ h₂ hp₁
  by_cases hin : ∃ t ∈ Ioo x y, F t ∈ Z
  · obtain ⟨t, ht, htZ⟩ := hin
    have htb : (t : ℂ) ∈ ball m r := by
      rw [mem_ball, dist_eq_norm, hm, ← ofReal_sub, norm_real, Real.norm_eq_abs,
        abs_sub_lt_iff, hr_def]
      constructor <;> linarith [ht.1, ht.2]
    have hp₁ : F t ∈ closure (ψ '' U₁) := mem_closure_image_of_mem_nhdsWithin hEq hF
      (ofReal_mem_Hbar t) (inter_mem_nhdsWithin H (isOpen_ball.mem_nhds htb))
    right
    refine ⟨fun s hs hsZ => core htZ hsZ hp₁ ?_, fun hwZ => core htZ hwZ hp₁ ?_⟩
    · have hsb : r < ‖(s : ℂ) - m‖ := by
        rw [hm, ← ofReal_sub, norm_real, Real.norm_eq_abs, lt_abs, hr_def]
        rw [mem_Icc, not_and_or, not_le, not_le] at hs
        rcases hs with hs | hs
        · right; linarith
        · left; linarith
      exact mem_closure_image_of_mem_nhdsWithin hEq hF (ofReal_mem_Hbar s)
        (inter_mem_nhdsWithin H ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hsb))
    · refine mem_closure_image_of_mem_cobounded hInf
        (inter_mem (mem_inf_of_right (mem_principal_self H)) (mem_inf_of_left ?_))
      exact mem_of_superset (eventually_cobounded_le_norm (r + ‖m‖ + 1))
        fun z (hz : r + ‖m‖ + 1 ≤ ‖z‖) =>
          show r < ‖z - m‖ by linarith [norm_sub_norm_le z m]
  · left
    exact fun t ht htZ => hin ⟨t, ht, htZ⟩

/-- **C5 at `∞`.** If `F x = wInf = q`, then a preconnected `Z ⊆ E \ {q}` misses `F((-∞, x))`
or misses `F((x, ∞))`. -/
theorem fold_infty {ψ F : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) {wInf : ℂ}
    (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) {x : ℝ} {q : ℂ} (hx : F x = q)
    (hq : wInf = q) {Z : Set ℂ} (hZ : Z ⊆ E \ {q}) (hZc : IsPreconnected Z) :
    (∀ s ∈ Iio x, F s ∉ Z) ∨ (∀ s ∈ Ioi x, F s ∉ Z) := by
  set R : Set ℂ := H ∩ {z | z.re = x} with hRd
  set Λ : Set ℂ := closure (ψ '' R) with hΛd
  have hΛ : IsCompact Λ :=
    (isBounded_ball.subset (image_subset_iff.2 fun z hz => h.bdd (h.bij.mapsTo hz.1))
      : Bornology.IsBounded (ψ '' R)).isCompact_closure
  have hRcl : closure R ⊆ Hbar ∩ {z | z.re = x} :=
    closure_minimal (inter_subset_inter_left _ H_subset_Hbar)
      (isClosed_Hbar.inter (isClosed_eq continuous_re continuous_const))
  have hΛD : Λ \ {q} ⊆ D := by
    rintro p ⟨hp, hne⟩
    rcases closure_image_subset hEq hF hInf inter_subset_left hp with ⟨z, hz, rfl⟩ | hpw
    · obtain ⟨hzH, hzre⟩ := hRcl hz
      rcases (show (0 : ℝ) ≤ z.im from hzH).eq_or_lt with h0 | hpos
      · have : z = (x : ℂ) := Complex.ext (by simpa using hzre) (by simp [h0])
        exact absurd (this ▸ hx) hne
      · rw [hEq hpos]; exact h.bij.mapsTo hpos
    · exact absurd (hpw.trans hq) hne
  set U₁ : Set ℂ := H ∩ {z | z.re < x} with hU₁d
  set U₂ : Set ℂ := H ∩ {z | x < z.re} with hU₂d
  have hU₁ : IsOpen U₁ := isOpen_H.inter (isOpen_lt continuous_re continuous_const)
  have hU₂ : IsOpen U₂ := isOpen_H.inter (isOpen_lt continuous_const continuous_re)
  have hU : Disjoint U₁ U₂ :=
    Set.disjoint_left.2 fun z h1 h2 => lt_asymm (show z.re < x from h1.2) h2.2
  have hcov : ∀ z ∈ H, z ∉ U₁ → z ∉ U₂ → ψ z ∈ Λ := by
    intro z hz h1 h2
    have e1 : ¬ z.re < x := fun hb => h1 ⟨hz, hb⟩
    have e2 : ¬ x < z.re := fun hb => h2 ⟨hz, hb⟩
    exact subset_closure ⟨z, ⟨hz, le_antisymm (not_lt.1 e2) (not_lt.1 e1)⟩, rfl⟩
  have hZΛ : ∀ p ∈ Z, p ∉ Λ := fun p hp hpΛ =>
    h.sub_compl (hZ hp).1 (hΛD ⟨hpΛ, (hZ hp).2⟩)
  by_cases hin : ∃ s ∈ Iio x, F s ∈ Z
  · obtain ⟨s, hs, hsZ⟩ := hin
    have hp₁ : F s ∈ closure (ψ '' U₁) := mem_closure_image_of_mem_nhdsWithin hEq hF
      (ofReal_mem_Hbar s) (inter_mem_nhdsWithin H
        ((isOpen_lt continuous_re continuous_const).mem_nhds (show ((s : ℂ)).re < x by
          simpa using hs)))
    right
    intro s' hs' hs'Z
    refine not_mem_closure_of_isPreconnected h hΛ hΛD hU₁ hU₂ inter_subset_left
      inter_subset_left hU hcov hZc hZΛ hsZ hs'Z hp₁ ?_
    exact mem_closure_image_of_mem_nhdsWithin hEq hF (ofReal_mem_Hbar s')
      (inter_mem_nhdsWithin H ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show x < ((s' : ℂ)).re by simpa using hs')))
  · left
    exact fun s hs hsZ => hin ⟨s, hs, hsZ⟩

/-- **C6 (injectivity where `E \ {q}` is connected).** If `E \ {q}` is preconnected then `F`
takes the value `q` at most once on `ℝ ∪ {∞}`: at most once on `ℝ`, and not at all on `ℝ` if
`wInf = q`. -/
theorem eq_of_isPreconnected_diff {ψ F : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) {wInf : ℂ}
    (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) {q : ℂ}
    (hq : IsPreconnected (E \ {q})) :
    (∀ x y : ℝ, F x = q → F y = q → x = y) ∧ (wInf = q → ∀ x : ℝ, F x ≠ q) := by
  have C4 := fun {a b : ℝ} (hab : a < b) =>
    not_forall_eq_const_Ioo (c := q) h.holo h.bij.injOn hEq hF hab
  -- a boundary value outside `E \ {q}` is `q`
  have hval : ∀ t : ℝ, F t ∉ E \ {q} → F t = q := fun t ht => by
    by_contra hne
    exact ht ⟨h.frontier_sub (extension_mem_frontier h hEq hF t), hne⟩
  have key : ∀ x y : ℝ, x < y → F x = q → F y = q → False := by
    intro x y hxy hx hy
    rcases fold h hEq hF hInf hxy hx hy subset_rfl hq with hin | ⟨hout, -⟩
    · exact C4 hxy fun t ht => hval t (hin t ht)
    · exact C4 (lt_add_one y) fun t ht =>
        hval t (hout t fun htI => (not_le.2 ht.1) htI.2)
  refine ⟨fun x y hx hy => ?_, fun hwq x hx => ?_⟩
  · rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact (key x y hxy hx hy).elim
    · exact hxy
    · exact (key y x hxy hy hx).elim
  · rcases fold_infty h hEq hF hInf hx hwq subset_rfl hq with hl | hr
    · exact C4 (sub_one_lt x) fun t ht => hval t (hl t ht.2)
    · exact C4 (lt_add_one x) fun t ht => hval t (hr t ht.1)

end QuantumZipper.CA.Car
