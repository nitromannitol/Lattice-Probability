/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45DetJ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

/-!
# Disjoint arcs of a Jordan curve have distinct hit patterns (task P2-E2R)

GM, arXiv:1905.00383, `uniqueness-final.tex` l. 1674–1675: the point `P(s_k) ∈ Conf_k` "is
determined by which arc of `𝓘_k` contains `P(t_k)`". For `GMConfPtSel` this needs: the distinct
(disjoint, nonempty) arcs `arcOf x`, `x ∈ Conf_k`, of the Jordan curve `∂𝓑^•_{t_k}` meet
different members of a fixed countable base of open sets.

* `gm_real_closure_disjoint`: two disjoint nonempty intervals of `ℝ` cannot each lie in the
  closure of the other;
* `gm_circle_closure_ne`: two disjoint nonempty preconnected subsets of the unit circle have
  different closures (cut the circle at a point outside both, or, if they cover the circle, at a
  point of one of them; `θ ↦ π + arg(-z/p)` identifies the cut circle with `(0, 2π)`);
* `gm_jordan_closure_ne`: the same on a Jordan curve (`JordanMap.IsJordanCurve`; the
  parametrization is a closed embedding of the circle);
* `gm_hitPattern_ne`: such sets are separated by a member of a fixed countable base.

Standard plane topology; own elementary proof (no source needed beyond the definition of a Jordan
curve; DEVIATIONS entry proposed in handoff/P2-E2R.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology Metric Complex

namespace LQGMetric.GM

lemma gm_real_closure_disjoint_aux {I J : Set ℝ} (hI : I.OrdConnected) (hJ : J.OrdConnected)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ J) (haJ : a ∈ closure J) (hbI : b ∈ closure I)
    (hd : Disjoint I J) (hab : a < b) : False := by
  obtain ⟨i, hi, hid⟩ := Metric.mem_closure_iff.1 hbI ((b - a) / 2) (by linarith)
  obtain ⟨j, hj, hjd⟩ := Metric.mem_closure_iff.1 haJ ((b - a) / 2) (by linarith)
  rw [Real.dist_eq] at hid hjd
  have h1 := abs_lt.1 hid
  have h2 := abs_lt.1 hjd
  have hmI : (a + b) / 2 ∈ I := hI.out ha hi ⟨by linarith, by linarith⟩
  have hmJ : (a + b) / 2 ∈ J := hJ.out hj hb ⟨by linarith, by linarith⟩
  exact disjoint_left.1 hd hmI hmJ

/-- two disjoint nonempty intervals of `ℝ` cannot each meet the closure of the other at their
points -/
lemma gm_real_closure_disjoint {I J : Set ℝ} (hI : I.OrdConnected) (hJ : J.OrdConnected)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ J) (haJ : a ∈ closure J) (hbI : b ∈ closure I)
    (hd : Disjoint I J) : False := by
  rcases lt_trichotomy a b with h | h | h
  · exact gm_real_closure_disjoint_aux hI hJ ha hb haJ hbI hd h
  · exact disjoint_left.1 hd ha (h ▸ hb)
  · exact gm_real_closure_disjoint_aux hJ hI hb ha hbI haJ hd.symm h

/-- the angle coordinate of the circle cut at `p` -/
def gmCut (p z : ℂ) : ℝ := Real.pi + arg (-(z / p))

lemma gm_cut_aux {p z : ℂ} (hp : ‖p‖ = 1) (hz : ‖z‖ = 1) (hzp : z ≠ p) :
    arg (-(z / p)) ≠ Real.pi ∧ -(z / p) ≠ 0 := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hn : ‖-(z / p)‖ = 1 := by rw [norm_neg, norm_div, hp, hz, div_one]
  refine ⟨fun h => hzp ?_, fun h => by rw [h, norm_zero] at hn; exact zero_ne_one hn⟩
  rw [arg_eq_pi_iff] at h
  have hw : -(z / p) = -1 := by
    apply Complex.ext
    · have := Complex.sq_norm (-(z / p))
      rw [hn, normSq_apply, ← sq, ← sq, h.2] at this
      simp only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero] at this
      have : (-(z / p)).re = -1 := by nlinarith [h.1]
      simpa using this
    · simpa using h.2
  have : z / p = 1 := by simpa using hw
  rwa [div_eq_one_iff_eq hp0] at this

lemma gm_cut_mem {p z : ℂ} (hp : ‖p‖ = 1) (hz : ‖z‖ = 1) (hzp : z ≠ p) :
    gmCut p z ∈ Ioo 0 (2 * Real.pi) := by
  have h := (gm_cut_aux hp hz hzp).1
  have h1 := neg_pi_lt_arg (-(z / p))
  have h2 := lt_of_le_of_ne (arg_le_pi (-(z / p))) h
  exact ⟨by unfold gmCut; linarith, by unfold gmCut; linarith⟩

lemma gm_cut_continuousOn {p : ℂ} (hp : ‖p‖ = 1) :
    ContinuousOn (gmCut p) (sphere 0 1 \ {p}) := by
  intro z hz
  have hz1 : ‖z‖ = 1 := by simpa using hz.1
  have hzp : z ≠ p := hz.2
  have hslit : -(z / p) ∈ slitPlane := mem_slitPlane_iff_arg.2 (gm_cut_aux hp hz1 hzp)
  have : ContinuousAt (fun w : ℂ => arg (-(w / p))) z :=
    (continuousAt_arg hslit).comp (f := fun w : ℂ => -(w / p)) (by fun_prop)
  exact (continuousAt_const.add this).continuousWithinAt

lemma gm_cut_injOn {p : ℂ} (hp : ‖p‖ = 1) : InjOn (gmCut p) (sphere 0 1 \ {p}) := by
  intro z hz w hw he
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hz1 : ‖z‖ = 1 := by simpa using hz.1
  have hw1 : ‖w‖ = 1 := by simpa using hw.1
  have ha : arg (-(z / p)) = arg (-(w / p)) := by unfold gmCut at he; linarith
  have hn : ‖-(z / p)‖ = ‖-(w / p)‖ := by simp [hz1, hw1]
  have := ext_norm_arg hn ha
  have : z / p = w / p := neg_injective this
  exact (div_left_inj' hp0).1 this

/-- the point of the cut circle with angle coordinate `m` -/
def gmUncut (p : ℂ) (m : ℝ) : ℂ := -p * (cos ((m - Real.pi : ℝ)) + sin ((m - Real.pi : ℝ)) * I)

lemma gm_cut_uncut {p : ℂ} (hp : ‖p‖ = 1) {m : ℝ} (hm : m ∈ Ioo 0 (2 * Real.pi)) :
    gmCut p (gmUncut p m) = m ∧ gmUncut p m ∈ sphere 0 1 \ {p} := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have e : -(gmUncut p m / p) = cos ((m - Real.pi : ℝ)) + sin ((m - Real.pi : ℝ)) * I := by
    unfold gmUncut
    field_simp
  have hc : gmCut p (gmUncut p m) = m := by
    unfold gmCut
    rw [e, arg_cos_add_sin_mul_I ⟨by linarith [hm.1], by linarith [hm.2]⟩]
    ring
  refine ⟨hc, ?_, fun h => ?_⟩
  · rw [mem_sphere_zero_iff_norm, gmUncut, norm_mul, norm_neg, hp, one_mul]
    exact norm_cos_add_sin_mul_I _
  · have h' : gmUncut p m = p := h
    have hpp : gmCut p p = 2 * Real.pi := by
      unfold gmCut
      rw [div_self hp0, show -(1 : ℂ) = (-1 : ℂ) from rfl, arg_neg_one]
      ring
    have := hc
    rw [h', hpp] at this
    linarith [hm.2]

/-- **two disjoint nonempty preconnected subsets of the unit circle have different closures** -/
theorem gm_circle_closure_ne {A B : Set ℂ} (hAs : A ⊆ sphere 0 1) (hBs : B ⊆ sphere 0 1)
    (hA : IsPreconnected A) (hB : IsPreconnected B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hd : Disjoint A B) (hcl : closure A = closure B) : False := by
  obtain ⟨a, ha⟩ := hAn
  obtain ⟨b, hb⟩ := hBn
  by_cases hq : ∃ q ∈ sphere (0 : ℂ) 1, q ∉ A ∧ q ∉ B
  · obtain ⟨q, hq, hqA, hqB⟩ := hq
    have hq1 : ‖q‖ = 1 := by simpa using hq
    have hAq : A ⊆ sphere 0 1 \ {q} := fun z hz => ⟨hAs hz, fun h => hqA (h ▸ hz)⟩
    have hBq : B ⊆ sphere 0 1 \ {q} := fun z hz => ⟨hBs hz, fun h => hqB (h ▸ hz)⟩
    have hfc := gm_cut_continuousOn hq1
    have hI := isPreconnected_iff_ordConnected.1 (hA.image _ (hfc.mono hAq))
    have hJ := isPreconnected_iff_ordConnected.1 (hB.image _ (hfc.mono hBq))
    have haB : a ∈ closure B := hcl ▸ subset_closure ha
    have hbA : b ∈ closure A := hcl.symm ▸ subset_closure hb
    refine gm_real_closure_disjoint hI hJ (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
      (((hfc a (hAq ha)).mono hBq).mem_closure_image haB)
      (((hfc b (hBq hb)).mono hAq).mem_closure_image hbA) ?_
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
    exact disjoint_left.1 hd hz (gm_cut_injOn hq1 (hBq hw) (hAq hz) he ▸ hw)
  · push_neg at hq
    have hb1 : ‖b‖ = 1 := by simpa using hBs hb
    have hAb : A ⊆ sphere 0 1 \ {b} := fun z hz =>
      ⟨hAs hz, fun h => disjoint_left.1 hd hz (h ▸ hb)⟩
    have hcov : sphere 0 1 \ {b} ⊆ closure A := by
      intro z hz
      by_cases hzA : z ∈ A
      · exact subset_closure hzA
      · exact hcl ▸ subset_closure (hq z hz.1 hzA)
    have hfc := gm_cut_continuousOn hb1
    have hI := isPreconnected_iff_ordConnected.1 (hA.image _ (hfc.mono hAb))
    have hfull : Ioo 0 (2 * Real.pi) ⊆ gmCut b '' A := by
      intro x hx
      have hdense : ∀ u v, 0 ≤ u → u < v → v ≤ 2 * Real.pi →
          (gmCut b '' A ∩ Ioo u v).Nonempty := by
        intro u v hu huv hv
        have hm : (u + v) / 2 ∈ Ioo 0 (2 * Real.pi) := ⟨by linarith, by linarith⟩
        obtain ⟨hc, hmem⟩ := gm_cut_uncut hb1 hm
        have hcl' := ((hfc _ hmem).mono hAb).mem_closure_image (hcov hmem)
        rw [hc] at hcl'
        obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hcl' (Ioo u v)
          (Ioo_mem_nhds (by linarith) (by linarith))
        exact ⟨y, hy2, hy1⟩
      obtain ⟨y, hyI, hy⟩ := hdense 0 x le_rfl hx.1 hx.2.le
      obtain ⟨z, hzI, hz⟩ := hdense x (2 * Real.pi) hx.1.le hx.2 le_rfl
      exact hI.out hyI hzI ⟨hy.2.le, hz.1.le⟩
    have hBb : B ⊆ {b} := by
      intro z hz
      by_contra hzb
      have hzS : z ∈ sphere (0 : ℂ) 1 \ {b} := ⟨hBs hz, hzb⟩
      obtain ⟨w, hw, he⟩ := hfull (gm_cut_mem hb1 (by simpa using hBs hz) hzb)
      exact disjoint_left.1 hd (gm_cut_injOn hb1 (hAb hw) hzS he ▸ hw) hz
    have : a ∈ ({b} : Set ℂ) := by
      have := hcl ▸ subset_closure ha
      rwa [(closure_mono hBb).antisymm (by simpa using subset_closure hb) |>.trans
        closure_singleton] at this
    exact disjoint_left.1 hd ha (this ▸ hb)

/-- **disjoint nonempty preconnected subsets of a Jordan curve have different closures** -/
theorem gm_jordan_closure_ne {Γ A B : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (hAΓ : A ⊆ Γ)
    (hBΓ : B ⊆ Γ) (hA : IsPreconnected A) (hB : IsPreconnected B) (hAn : A.Nonempty)
    (hBn : B.Nonempty) (hd : Disjoint A B) : closure A ≠ closure B := by
  intro hcl
  obtain ⟨γ, hc, hinj, himg⟩ := hΓ
  haveI : CompactSpace (sphere (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  let φ : sphere (0 : ℂ) 1 → ℂ := fun x => γ x
  have hφc : Continuous φ := hc.restrict
  have hφi : Function.Injective φ := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hφ := hφc.isClosedEmbedding hφi
  have hval : IsClosedEmbedding (Subtype.val : sphere (0 : ℂ) 1 → ℂ) :=
    isClosed_sphere.isClosedEmbedding_subtypeVal
  have himA : ∀ C ⊆ Γ, φ '' (φ ⁻¹' C) = C := by
    intro C hC
    refine image_preimage_eq_of_subset ?_
    intro z hz
    rw [← himg] at hC
    obtain ⟨x, hx, rfl⟩ := hC hz
    exact ⟨⟨x, hx⟩, rfl⟩
  have hA' : IsPreconnected (φ ⁻¹' A) :=
    hφ.isInducing.isPreconnected_image.1 (by rw [himA A hAΓ]; exact hA)
  have hB' : IsPreconnected (φ ⁻¹' B) :=
    hφ.isInducing.isPreconnected_image.1 (by rw [himA B hBΓ]; exact hB)
  have hcl' : closure (φ ⁻¹' A) = closure (φ ⁻¹' B) := by
    apply hφi.image_injective
    rw [← hφ.closure_image_eq, ← hφ.closure_image_eq, himA A hAΓ, himA B hBΓ, hcl]
  have hne : ∀ C ⊆ Γ, C.Nonempty → (Subtype.val '' (φ ⁻¹' C)).Nonempty := by
    intro C hC hCn
    obtain ⟨z, hz⟩ := hCn
    rw [← himA C hC] at hz
    obtain ⟨x, hx, -⟩ := hz
    exact ⟨x, x, hx, rfl⟩
  refine gm_circle_closure_ne (A := Subtype.val '' (φ ⁻¹' A)) (B := Subtype.val '' (φ ⁻¹' B))
    (by rintro _ ⟨x, -, rfl⟩; exact x.2) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    (hA'.image _ continuous_subtype_val.continuousOn)
    (hB'.image _ continuous_subtype_val.continuousOn) (hne A hAΓ hAn) (hne B hBΓ hBn)
    ((disjoint_image_iff Subtype.val_injective).2 (hd.preimage φ)) ?_
  rw [hval.closure_image_eq, hval.closure_image_eq, hcl']

/-- a fixed countable base of the topology of `ℂ`, enumerated by `ℕ` -/
theorem gm_exists_countable_base : ∃ V : ℕ → Set ℂ, (∀ n, IsOpen (V n)) ∧
    ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis ℂ
  have hne : b.Nonempty := by
    obtain ⟨v, hv, -⟩ := hb.exists_subset_of_mem_open (mem_univ (0 : ℂ)) isOpen_univ
    exact ⟨v, hv⟩
  obtain ⟨V, hV⟩ := hbc.exists_eq_range hne
  refine ⟨V, fun n => hb.isOpen (hV ▸ mem_range_self n), fun x O hO hx => ?_⟩
  obtain ⟨v, hvb, hxv, hvO⟩ := hb.exists_subset_of_mem_open hx hO
  rw [hV] at hvb
  obtain ⟨n, rfl⟩ := hvb
  exact ⟨n, hxv, hvO⟩

lemma gm_closure_subset_of_hits {V : ℕ → Set ℂ}
    (hV : ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O)
    (hVo : ∀ n, IsOpen (V n)) {A B : Set ℂ}
    (h : ∀ n, (A ∩ V n).Nonempty → (B ∩ V n).Nonempty) : closure A ⊆ closure B := by
  intro x hx
  by_contra hxB
  obtain ⟨n, hxn, hnO⟩ := hV x _ isClosed_closure.isOpen_compl hxB
  obtain ⟨y, hyA, hyn⟩ := (_root_.mem_closure_iff.1 hx (V n) (hVo n) hxn)
  obtain ⟨z, hzB, hzn⟩ := h n ⟨y, hyn, hyA⟩
  exact hnO hzn (subset_closure hzB)

/-- **disjoint nonempty arcs of a Jordan curve have distinct hit patterns** on a countable base -/
theorem gm_hitPattern_ne {V : ℕ → Set ℂ}
    (hV : ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O)
    (hVo : ∀ n, IsOpen (V n)) {Γ A B : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (hAΓ : A ⊆ Γ)
    (hBΓ : B ⊆ Γ) (hA : IsPreconnected A) (hB : IsPreconnected B) (hAn : A.Nonempty)
    (hBn : B.Nonempty) (hd : Disjoint A B) :
    (fun n => (A ∩ V n).Nonempty) ≠ (fun n => (B ∩ V n).Nonempty) := by
  intro he
  apply gm_jordan_closure_ne hΓ hAΓ hBΓ hA hB hAn hBn hd
  exact (gm_closure_subset_of_hits hV hVo fun n h => (congrFun he n) ▸ h).antisymm
    (gm_closure_subset_of_hits hV hVo fun n h => (congrFun he n) ▸ h)

end LQGMetric.GM
