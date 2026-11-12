/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_4S2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4D

/-!
# CONF Lemma 2.4: one-sided limits are leftmost / rightmost; uniqueness

Source: CONF = Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, proof of Lemma 2.4,
l. 557–558: "By Lemma 2.3, no `D_h`-geodesic from 0 to `y` can cross any of the `P_{q_n^-}`'s.
It follows that each such geodesic lies to the right of `P_y^-`."

* `angle_tendsto`: angle lifts of uniformly convergent paths (normalized at the endpoint)
  converge (own elementary argument: `1 − cos(α_n − β) ≤ ‖P_n − Q‖² / c²` and the intermediate
  value theorem);
* `side_order` (**CONF l. 557–558**): for a one-sided limit `P` (Blueprint `IsSideGeod`) and any
  geodesic `R` to the same point, `R` lies weakly to the right (left) of `P` at every level in
  the lift order of DEC-D: compare `R` with `P_n` through geodesics to rational points
  (`step_order`) and pass to the limit (`angle_tendsto`, `lift_tendsto`);
* `side_weaklyRight`, `isLeftmost_of_side` (Blueprint leftmost ⇒ DEC-D leftmost);
* **`confSideUniq : CONFSideUniq`** (right antisymmetry `DD.right_antisymm`) and
  **`confLem2_4 : DFGPSLem3_8 → CONFLem2_4`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

/-- `1 − cos(x − y) ≤ ‖A − B‖² / c²` for `A = |A| e^{ix}`, `B = |B| e^{iy}`, `|B| ≥ c`,
`‖A − B‖ ≤ c / 2` -/
theorem one_sub_cos_le {A B : ℂ} {x y c : ℝ} (hc : 0 < c)
    (hA : A = (‖A‖ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))
    (hB : B = (‖B‖ : ℂ) * Complex.exp ((y : ℂ) * Complex.I)) (hBc : c ≤ ‖B‖)
    (hAB : ‖A - B‖ ≤ c / 2) : 1 - Real.cos (x - y) ≤ ‖A - B‖ ^ 2 / c ^ 2 := by
  have hAr : A.re = ‖A‖ * Real.cos x := by
    conv_lhs => rw [hA]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hAi : A.im = ‖A‖ * Real.sin x := by
    conv_lhs => rw [hA]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hBr : B.re = ‖B‖ * Real.cos y := by
    conv_lhs => rw [hB]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hBi : B.im = ‖B‖ * Real.sin y := by
    conv_lhs => rw [hB]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hsq : ‖A - B‖ ^ 2 = (A.re - B.re) ^ 2 + (A.im - B.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [Complex.sub_re, Complex.sub_im]; ring
  have hcs := Real.cos_sub x y
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hkey : ‖A - B‖ ^ 2 = (‖A‖ - ‖B‖) ^ 2 + 2 * ‖A‖ * ‖B‖ * (1 - Real.cos (x - y)) := by
    rw [hsq, hAr, hAi, hBr, hBi, hcs]
    linear_combination (‖A‖ ^ 2) * hx + (‖B‖ ^ 2) * hy
  have hAn : c / 2 ≤ ‖A‖ := by
    have := norm_sub_norm_le B A
    rw [norm_sub_rev] at this
    linarith
  have h1c : 0 ≤ 1 - Real.cos (x - y) := by linarith [Real.cos_le_one (x - y)]
  have hprod : c ^ 2 ≤ 2 * ‖A‖ * ‖B‖ := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

/-- angle lifts of uniformly convergent paths, normalized at `b`, converge at `a` -/
theorem angle_tendsto {z : ℂ} {a b : ℝ} (hab : a ≤ b) {Pn : ℕ → ℝ → ℂ} {Q : ℝ → ℂ}
    (hQc : ContinuousOn Q (Icc a b)) (hQz : ∀ r ∈ Icc a b, Q r ≠ z)
    (hunif : ∀ ε > 0, ∀ᶠ n in atTop, ∀ r ∈ Icc a b, ‖Pn n r - Q r‖ < ε)
    {αn : ℕ → ℝ → ℝ} {β : ℝ → ℝ} (hαn : ∀ n, DD.IsAngleLift z (Pn n) a b (αn n))
    (hβ : DD.IsAngleLift z Q a b β) (hb : Tendsto (fun n => αn n b) atTop (𝓝 (β b))) :
    Tendsto (fun n => αn n a) atTop (𝓝 (β a)) := by
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab)
    ((hQc.sub continuousOn_const).norm)
  set c := ‖Q r₀ - z‖ with hcdef
  have hc : 0 < c := norm_pos_iff.2 (sub_ne_zero.2 (hQz r₀ hr₀))
  rw [Metric.tendsto_nhds]
  intro ε hε
  set e := min ε 1 with hedef
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have hpi := Real.pi_gt_three
  have hcos1 : Real.cos e < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) he0
    rwa [Real.cos_zero] at this
  have hcos0 : 0 < Real.cos e := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set d := 1 - Real.cos e with hd
  have hd0 : 0 < d := by linarith
  have hd1 : d ≤ 1 := by linarith
  have hδ : 0 < c * d / 2 := by positivity
  filter_upwards [hunif _ hδ, Metric.tendsto_nhds.1 hb e he0] with n hn hbn
  rw [Real.dist_eq] at hbn ⊢
  set f : ℝ → ℝ := fun r => αn n r - β r with hf
  have hfc : ContinuousOn f (Icc a b) := (hαn n).1.sub hβ.1
  have hcos : ∀ r ∈ Icc a b, Real.cos e < Real.cos (f r) := by
    intro r hr
    have hBc : c ≤ ‖Q r - z‖ := hmin hr
    have hAB : ‖(Pn n r - z) - (Q r - z)‖ < c * d / 2 := by
      rw [sub_sub_sub_cancel_right]; exact hn r hr
    have hle := one_sub_cos_le hc ((hαn n).2 r hr) (hβ.2 r hr) hBc
      (hAB.le.trans (by nlinarith))
    have h2 : ‖(Pn n r - z) - (Q r - z)‖ ^ 2 / c ^ 2 < d := by
      rw [div_lt_iff₀ (by positivity)]
      have h0 := norm_nonneg ((Pn n r - z) - (Q r - z))
      have : ‖(Pn n r - z) - (Q r - z)‖ ^ 2 < (c * d / 2) ^ 2 := by
        exact pow_lt_pow_left₀ hAB h0 two_ne_zero
      nlinarith
    show Real.cos e < Real.cos (αn n r - β r)
    linarith
  have hfa : |f a| < e := by
    by_contra hcon
    push Not at hcon
    have hsub := intermediate_value_Icc' hab hfc.abs
    obtain ⟨r, hr, hre⟩ := hsub ⟨hbn.le, hcon⟩
    have := hcos r hr
    rw [← Real.cos_abs (f r)] at this
    simp only at hre
    rw [hre] at this
    exact lt_irrefl _ this
  exact lt_of_lt_of_le hfa (min_le_left _ _)

section Det
variable {D : ContMetric} {z : ℂ} {s : ℝ}

theorem unif_of_supDistOn {Pn : ℕ → ℝ → ℂ} {P : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hc : Tendsto (fun n => supDistOn (Pn n) P s) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ r ∈ Icc t s, ‖Pn n r - P r‖ < ε := by
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hc) (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 (by linarith))] with n hn r hr
  have h1 : edist (Pn n r) (P r) ≤ ENNReal.ofReal (ε / 2) :=
    (le_iSup₂ (f := fun t (_ : t ∈ Icc 0 s) => edist (Pn n t) (P t)) r
      ⟨ht.trans hr.1, hr.2⟩).trans hn
  rw [edist_le_ofReal (by linarith), dist_eq_norm] at h1
  linarith

/-- **CONF Lemma 2.4, proof l. 557–558**: a one-sided limit `P` (Blueprint `IsSideGeod`) and any
geodesic `R` to the same point: at each level `t ∈ (0, s)`, in the lift order, `R` is weakly
right (`left = true`) resp. left (`left = false`) of `P` -/
theorem side_order
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z (ratPt q))
    {left : Bool} {y : ℂ} {P : ℝ → ℂ} (hP : IsSideGeod left D z s y P) {R : ℝ → ℂ}
    (hR : IsGeodesicL D R s z y) {t : ℝ} (ht : t ∈ Ioo 0 s) {φ₁ : ℝ → ℂ} {θ₁ : ℝ → ℝ}
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) {α β : ℝ → ℝ}
    (hα : DD.IsAngleLift z P t s α) (hβ : DD.IsAngleLift z R t s β) (hαβ : α s = β s)
    {u v : ℝ} (hu1 : φ₁ u = P t) (hu2 : θ₁ u = α t) (hv1 : φ₁ v = R t) (hv2 : θ₁ v = β t) :
    (left = true → v ≤ u) ∧ (left = false → u ≤ v) := by
  obtain ⟨-, hPg, φ, ⟨h1, h2, h3, h4, θ, h5, h6, h7⟩, t₀, ht₀, tn, Pn, htn, hside, hPn,
    hconv⟩ := hP
  have hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ := ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hsI : s ∈ Icc t s := ⟨ht.2.le, le_rfl⟩
  have hPne : ∀ r ∈ Icc t s, P r ≠ z := fun r hr => DD.geodLevel_ne hPg (ht.1.trans_le hr.1) hr.2
  have hyz : y - z ≠ 0 := sub_ne_zero.2 (hPg.2.2.1 ▸ hPne s hsI)
  have hαy := hα.2 s hsI
  rw [hPg.2.2.1] at hαy
  have hθy := h7 t₀
  rw [ht₀] at hθy
  obtain ⟨k, hk⟩ := DD.isAngle_sub hyz hαy hθy
  set w₀ := t₀ + k * (2 * Real.pi) with hw₀
  have hφw₀ : φ w₀ = y := by rw [hw₀, hφ.phi_add_int, ht₀]
  have hθw₀ : θ w₀ = α s := by rw [hw₀, hφ.theta_add_int]; linarith
  have hRw : IsGeodesicL D R s z (φ w₀) := hφw₀ ▸ hR
  have hPn' : ∀ n, IsGeodesicL D (Pn n) s z (φ (tn n + k * (2 * Real.pi))) := fun n => by
    rw [hφ.phi_add_int]; exact hPn n
  choose αn un hαn hαns hun1 hun2 using fun n => exists_normLift hφ hφ₁ ht.1 ht.2 (hPn' n)
  -- the positions of `P_n` converge to that of `P`
  have hb : Tendsto (fun n => αn n s) atTop (𝓝 (α s)) := by
    simp only [hαns, ← hθw₀]
    exact (h5.tendsto w₀).comp (htn.add_const _)
  have hunif := unif_of_supDistOn ht.1.le hconv
  have hat := angle_tendsto ht.2.le ((DD.cl_geodL_continuousOn hPg).mono
    (Icc_subset_Icc_left ht.1.le)) hPne hunif hαn hα hb
  have hlim : Tendsto un atTop (𝓝 u) := by
    refine lift_tendsto hφ₁ ?_ ?_
    · simp only [hun1, hu1]; exact tendsto_of_supDistOn hconv ⟨ht.1.le, ht.2.le⟩
    · simp only [hun2, hu2]; exact hat
  have hβs : β s = θ w₀ := by rw [hθw₀, hαβ]
  constructor
  · intro hl
    subst hl
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have := hside n
    simp only [ite_true] at this
    exact step_order hbc hgeo hq hφ hφ₁ ht.1 ht.2 hRw (hPn' n) hβ (hαn n) hβs (hαns n) hv1 hv2
      (hun1 n) (hun2 n) (by linarith)
  · intro hl
    subst hl
    refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have := hside n
    simp only [Bool.false_eq_true, ite_false] at this
    exact step_order hbc hgeo hq hφ hφ₁ ht.1 ht.2 (hPn' n) hRw (hαn n) hβ (hαns n) hβs
      (hun1 n) (hun2 n) hv1 hv2 (by linarith)

/-- one-sided limits are DEC-D side geodesics -/
theorem side_weaklyRight
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z (ratPt q))
    {left : Bool} {y : ℂ} {P : ℝ → ℂ} (hP : IsSideGeod left D z s y P) {R : ℝ → ℂ}
    (hR : IsGeodesicL D R s z y) :
    if left then DD.WeaklyRightOf D z s R P else DD.WeaklyRightOf D z s P R := by
  cases left
  · intro t ht φ₁ θ₁ hφ₁ α β hα hβ hαβ u v hu1 hu2 hv1 hv2
    exact (side_order hbc hgeo hq hP hR ht hφ₁ hβ hα hαβ.symm hv1 hv2 hu1 hu2).2 rfl
  · intro t ht φ₁ θ₁ hφ₁ α β hα hβ hαβ u v hu1 hu2 hv1 hv2
    exact (side_order hbc hgeo hq hP hR ht hφ₁ hα hβ hαβ hu1 hu2 hv1 hv2).1 rfl

/-- **Blueprint leftmost ⇒ DEC-D leftmost** (CONF Lemma 2.4, l. 557–558; the D76 bridge) -/
theorem isLeftmost_of_side
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z (ratPt q))
    {y : ℂ} {P : ℝ → ℂ} (hP : IsLeftmostGeod D z s y P) : DD.IsLeftmostGeod D z s y P :=
  ⟨hP.1, hP.2.1, fun R hR => by
    have := side_weaklyRight hbc hgeo hq hP hR
    simpa using this⟩

end Det

/-- **CONF Lemma 2.4, uniqueness** (proof l. 557–558) -/
theorem confSideUniq : CONFSideUniq := by
  intro D z₀ hL hbc hgeo hq s hs y hy left Q Q' hQ hQ'
  have hpos : ∀ t ∈ Ioo 0 s, ∃ φ θ, DD.IsPosJordanLift (frontier (filledBall D z₀ t)) z₀ φ θ :=
    fun t ht => DD.posLift_filledBall ht.1 hL (isBounded_ballM_of_bc hbc z₀ t)
      (GM.gm_j1b D z₀ t ht.1 hL (isBounded_ballM_of_bc hbc z₀ t))
  have h1 := side_weaklyRight hbc hgeo hq hQ hQ'.2.1
  have h2 := side_weaklyRight hbc hgeo hq hQ' hQ.2.1
  cases left
  · exact DD.right_antisymm hQ.2.1 hQ'.2.1 hy hpos h2 h1
  · exact DD.right_antisymm hQ.2.1 hQ'.2.1 hy hpos h1 h2

/-- **CONF Lemma 2.4** (`lem-leftmost-geodesic`, l. 533–537), Blueprint reading -/
theorem confLem2_4 (h38 : DFGPSLem3_8) : CONFLem2_4 := confLem2_4_of h38 confSideUniq

end LQGMetric.CONF
