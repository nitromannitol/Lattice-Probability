/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eArcs
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Jordan-curve facts for the canonical arc subdivision (DEC-120 §4, packet J3)

Inputs of the arc choice `T39JArcChoice` (CONF C:1740–1744, DV-D120-1) for a Jordan curve
`Γ = γ(∂𝔻)` (`JordanMap.IsJordanCurve`, e.g. `∂𝓑^•_τ`, `GM.gm_filledBall_frontier_isJordanCurve'`):

* `t39j_jordan_split`: for `x ≠ y ∈ Γ`, compact preconnected arcs `A, B ∋ x, y` with
  `A ∪ B = Γ` such that **two points `a ∈ A ∖ {x,y}`, `b ∈ B ∖ {x,y}` separate `x` from `y`**
  (no preconnected `C ⊆ Γ ∖ {a,b}` contains both) — from `GM.p412e_split` applied twice;
* `t39j_jordan_finite_pieces`: `Γ ∖ P` (`P` finite) is a finite union of preconnected subsets
  of `Γ ∖ P` (images of order-connected parameter sets; induction on `P`);
* `t39j_jordan_comp_nhds`: components of `Γ ∖ P` are relatively open (ULC,
  `JordanMap.jm_ulc_of_isJordanCurve`).

Own elementary arguments (standard plane topology), reusing `GM.p412e_split`, `GM.p412eC*`.
-/

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.CONF

/-- a preconnected set contained in the union of two complements of closed sets covering `Γ` -/
theorem t39j_pre_sub_or {C Γ A B : Set ℂ} (hC : IsPreconnected C) (hCΓ : C ⊆ Γ)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Γ ⊆ A ∪ B) (hCAB : C ∩ (A ∩ B) = ∅) :
    C ⊆ Bᶜ ∨ C ⊆ Aᶜ := by
  refine isPreconnected_iff_subset_of_disjoint.1 hC _ _ hB.isOpen_compl hA.isOpen_compl
    (fun z hz => ?_) ?_
  · by_cases hzB : z ∈ B
    · right; intro hzA; exact (Set.eq_empty_iff_forall_notMem.1 hCAB) z ⟨hz, hzA, hzB⟩
    · left; exact hzB
  · ext z; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hz hzB hzA
    rcases hAB (hCΓ hz) with h | h
    · exact hzA h
    · exact hzB h

/-- **splitting a Jordan curve at `x ≠ y`**, with the interleaving property -/
theorem t39j_jordan_split {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) {x y : ℂ} (hx : x ∈ Γ)
    (hy : y ∈ Γ) (hxy : x ≠ y) :
    ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ IsPreconnected A ∧ IsPreconnected B ∧
      A ∪ B = Γ ∧ A ∩ B = {x, y} ∧ (A \ {x, y}).Nonempty ∧ (B \ {x, y}).Nonempty ∧
      ∀ a ∈ A \ {x, y}, ∀ b ∈ B \ {x, y}, ∀ C : Set ℂ, IsPreconnected C →
        C ⊆ Γ \ {a, b} → x ∈ C → y ∉ C := by
  obtain ⟨γ, hγc, hγi, rfl⟩ := hΓ
  obtain ⟨A, B, A₀, B₀, hAc, hBc, hAB, hAiB, hA₀A, hB₀B, hAe, hBe, hxA₀, hyA₀, hxB₀, hyB₀, hA₀p,
    hB₀p, hxcA, hycA, hxcB, hycB⟩ := GM.p412e_split hγc hγi hx hy hxy
  have hpA : IsPreconnected A := hA₀p.subset_closure hA₀A (by
    rw [hAe]; exact union_subset subset_closure (by
      rintro z (rfl | rfl); exacts [hxcA, hycA]))
  have hpB : IsPreconnected B := hB₀p.subset_closure hB₀B (by
    rw [hBe]; exact union_subset subset_closure (by
      rintro z (rfl | rfl); exacts [hxcB, hycB]))
  have hA₀eq : A \ {x, y} = A₀ := by
    rw [hAe]; ext z; simp only [mem_diff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h | h | h, hn⟩
      · exact h
      · exact absurd (Or.inl h) hn
      · exact absurd (Or.inr h) hn
    · intro h; exact ⟨Or.inl h, by rintro (rfl | rfl); exacts [hxA₀ h, hyA₀ h]⟩
  have hB₀eq : B \ {x, y} = B₀ := by
    rw [hBe]; ext z; simp only [mem_diff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h | h | h, hn⟩
      · exact h
      · exact absurd (Or.inl h) hn
      · exact absurd (Or.inr h) hn
    · intro h; exact ⟨Or.inl h, by rintro (rfl | rfl); exacts [hxB₀ h, hyB₀ h]⟩
  have hne : ∀ {S : Set ℂ}, IsPreconnected S → x ∈ closure S → x ∉ S → S.Nonempty := by
    intro S _ hxS hxn
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hxS; exact hxS
  refine ⟨A, B, hAc, hBc, hpA, hpB, hAB, hAiB, ?_, ?_, ?_⟩
  · rw [hA₀eq]; exact hne hA₀p hxcA hxA₀
  · rw [hB₀eq]; exact hne hB₀p hxcB hxB₀
  intro a ha b hb C hC hCs hxC hyC
  have haΓ : a ∈ γ '' Metric.sphere 0 1 := hAB ▸ Or.inl ha.1
  have hbΓ : b ∈ γ '' Metric.sphere 0 1 := hAB ▸ Or.inr hb.1
  have hab : a ≠ b := by
    rintro rfl
    have : a ∈ A ∩ B := ⟨ha.1, hb.1⟩
    rw [hAiB] at this; exact ha.2 this
  obtain ⟨A', B', -, -, hA'c, hB'c, hpA', hpB', hA'B', hA'iB', -, -, -⟩ :=
    (show ∃ A' B' : Set ℂ, True ∧ True ∧ IsCompact A' ∧ IsCompact B' ∧ IsPreconnected A' ∧
        IsPreconnected B' ∧ A' ∪ B' = γ '' Metric.sphere 0 1 ∧ A' ∩ B' = {a, b} ∧ True ∧ True ∧
        True from by
      obtain ⟨A', B', A'₀, B'₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        h16, h17, h18⟩ := GM.p412e_split hγc hγi haΓ hbΓ hab
      refine ⟨A', B', trivial, trivial, h1, h2, h13.subset_closure h5 ?_,
        h14.subset_closure h6 ?_, h3, h4, trivial, trivial, trivial⟩
      · rw [h7]; exact union_subset subset_closure (by rintro z (rfl | rfl); exacts [h15, h16])
      · rw [h8]; exact union_subset subset_closure (by rintro z (rfl | rfl); exacts [h17, h18]))
  have hCΓ : C ⊆ γ '' Metric.sphere 0 1 := fun z hz => (hCs hz).1
  have hCab : C ∩ (A' ∩ B') = ∅ := by
    rw [hA'iB']; ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hz hz'; exact (hCs hz).2 hz'
  -- the arc of the `{a,b}`-splitting not meeting `C` connects `a ∈ A` to `b ∈ B` avoiding `x, y`
  have key : ∀ E : Set ℂ, IsPreconnected E → E ⊆ γ '' Metric.sphere 0 1 → a ∈ E → b ∈ E →
      x ∉ E → y ∉ E → False := by
    intro E hE hEΓ haE hbE hxE hyE
    have hEab : E ∩ (A ∩ B) = ∅ := by
      rw [hAiB]; ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and, mem_insert_iff,
        mem_singleton_iff]
      rintro hz (rfl | rfl); exacts [hxE hz, hyE hz]
    rcases t39j_pre_sub_or hE hEΓ hAc.isClosed hBc.isClosed hAB.ge hEab with h | h
    · exact h hbE hb.1
    · exact h haE ha.1
  rcases t39j_pre_sub_or hC hCΓ hA'c.isClosed hB'c.isClosed hA'B'.ge hCab with h | h
  · refine key B' hpB' (hA'B' ▸ subset_union_right) ?_ ?_ (fun hx' => h hxC hx')
      (fun hy' => h hyC hy')
    · have : a ∈ A' ∩ B' := by rw [hA'iB']; exact Or.inl rfl
      exact this.2
    · have : b ∈ A' ∩ B' := by rw [hA'iB']; exact Or.inr rfl
      exact this.2
  · refine key A' hpA' (hA'B' ▸ subset_union_left) ?_ ?_ (fun hx' => h hxC hx')
      (fun hy' => h hyC hy')
    · have : a ∈ A' ∩ B' := by rw [hA'iB']; exact Or.inl rfl
      exact this.1
    · have : b ∈ A' ∩ B' := by rw [hA'iB']; exact Or.inr rfl
      exact this.1

/-- removing finitely many values from the image of an order-connected set on which `f` is
injective leaves a finite union of images of order-connected sets -/
theorem t39j_pieces_aux {f : ℝ → ℂ} {I : Set ℝ} (hI : I.OrdConnected) (hf : InjOn f I)
    (P : Finset ℂ) : ∃ 𝒥 : Set (Set ℝ), 𝒥.Finite ∧ (∀ J ∈ 𝒥, J.OrdConnected ∧ J ⊆ I) ∧
      f '' I \ ↑P = ⋃ J ∈ 𝒥, f '' J := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨{I}, finite_singleton _, by simpa using hI, by simp⟩
  | insert q P _ ih =>
    obtain ⟨𝒥, h𝒥f, h𝒥, heq⟩ := ih
    let L : Set ℝ → Set ℝ := fun J => J ∩ {t | ∀ s ∈ J, f s = q → t < s}
    let R : Set ℝ → Set ℝ := fun J => J ∩ {t | ∀ s ∈ J, f s = q → s < t}
    have hoc : ∀ J ∈ 𝒥, (L J).OrdConnected ∧ (R J).OrdConnected := by
      intro J hJ
      constructor
      · refine (h𝒥 J hJ).1.inter ⟨fun a ha b hb t ht s hs hfs => ?_⟩
        exact lt_of_le_of_lt ht.2 (hb s hs hfs)
      · refine (h𝒥 J hJ).1.inter ⟨fun a ha b hb t ht s hs hfs => ?_⟩
        exact lt_of_lt_of_le (ha s hs hfs) ht.1
    refine ⟨L '' 𝒥 ∪ R '' 𝒥, (h𝒥f.image _).union (h𝒥f.image _), ?_, ?_⟩
    · rintro K (⟨J, hJ, rfl⟩ | ⟨J, hJ, rfl⟩)
      · exact ⟨(hoc J hJ).1, inter_subset_left.trans (h𝒥 J hJ).2⟩
      · exact ⟨(hoc J hJ).2, inter_subset_left.trans (h𝒥 J hJ).2⟩
    · rw [Finset.coe_insert, insert_eq, union_comm ({q} : Set ℂ) (↑P), ← diff_diff, heq]
      ext z
      simp only [mem_diff, mem_iUnion, mem_image, mem_union, mem_singleton_iff, exists_prop]
      constructor
      · rintro ⟨⟨J, hJ, t, htJ, rfl⟩, hq⟩
        have htI := (h𝒥 J hJ).2 htJ
        by_cases hex : ∃ s ∈ J, f s = q
        · obtain ⟨s, hsJ, hsq⟩ := hex
          have hst : t ≠ s := by rintro rfl; exact hq hsq
          have huniq : ∀ s' ∈ J, f s' = q → s' = s := fun s' hs' h' =>
            hf ((h𝒥 J hJ).2 hs') ((h𝒥 J hJ).2 hsJ) (h'.trans hsq.symm)
          rcases lt_or_gt_of_ne hst with h | h
          · exact ⟨L J, Or.inl ⟨J, hJ, rfl⟩, t, ⟨htJ, fun s' hs' h' => huniq s' hs' h' ▸ h⟩,
              rfl⟩
          · exact ⟨R J, Or.inr ⟨J, hJ, rfl⟩, t, ⟨htJ, fun s' hs' h' => huniq s' hs' h' ▸ h⟩,
              rfl⟩
        · push_neg at hex
          exact ⟨L J, Or.inl ⟨J, hJ, rfl⟩, t, ⟨htJ, fun s' hs' h' => absurd h' (hex s' hs')⟩,
            rfl⟩
      · rintro ⟨K, (⟨J, hJ, rfl⟩ | ⟨J, hJ, rfl⟩), t, ht, rfl⟩
        · exact ⟨⟨J, hJ, t, ht.1, rfl⟩, fun h => lt_irrefl t (ht.2 t ht.1 h)⟩
        · exact ⟨⟨J, hJ, t, ht.1, rfl⟩, fun h => lt_irrefl t (ht.2 t ht.1 h)⟩

/-- **`Γ ∖ P` is a finite union of preconnected subsets of `Γ ∖ P`** (Jordan `Γ`, finite `P`) -/
theorem t39j_jordan_finite_pieces {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (P : Finset ℂ) :
    ∃ 𝒢 : Set (Set ℂ), 𝒢.Finite ∧ (∀ G ∈ 𝒢, IsPreconnected G ∧ G ⊆ Γ \ ↑P) ∧
      Γ \ ↑P ⊆ ⋃₀ 𝒢 := by
  obtain ⟨γ, hγc, hγi, rfl⟩ := hΓ
  set f : ℝ → ℂ := γ ∘ GM.p412eC with hf
  have hfc : Continuous f := continuousOn_univ.1
    (hγc.comp GM.p412eC_continuous.continuousOn (fun t _ => GM.p412eC_mem t))
  have himg : f '' Ico 0 1 = γ '' Metric.sphere 0 1 := by
    rw [hf, image_comp]; congr 1
    rw [← (by simpa using GM.p412eC_image_Icc 0 : GM.p412eC '' Icc 0 1 = Metric.sphere 0 1)]
    refine Subset.antisymm (image_mono Ico_subset_Icc_self) ?_
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.2 with h | h
    · refine ⟨0, ⟨le_rfl, one_pos⟩, ?_⟩
      rw [h]; have := GM.p412eC_add_int 0 1; push_cast at this; simpa using this.symm
    · exact ⟨t, ⟨ht.1, h⟩, rfl⟩
  have hinj : InjOn f (Ico 0 1) := by
    intro s hs t ht hst
    have h' : GM.p412eC s = GM.p412eC t := hγi (GM.p412eC_mem s) (GM.p412eC_mem t) hst
    obtain ⟨n, hn⟩ := GM.p412eC_eq_iff.1 h'
    have h1 : (n : ℝ) < 1 := by linarith [hs.2, ht.1]
    have h2 : (-1 : ℝ) < n := by linarith [hs.1, ht.2]
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    have : n = 0 := by omega
    subst this; simpa using hn
  obtain ⟨𝒥, h𝒥f, h𝒥, heq⟩ := t39j_pieces_aux ordConnected_Ico hinj P
  refine ⟨(fun J => f '' J) '' 𝒥, h𝒥f.image _, ?_, ?_⟩
  · rintro _ ⟨J, hJ, rfl⟩
    refine ⟨(h𝒥 J hJ).1.isPreconnected.image f hfc.continuousOn, ?_⟩
    rw [← himg, heq]; exact subset_biUnion_of_mem (u := fun J => f '' J) hJ
  · rw [← himg, heq]
    intro z hz
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨J, hJ, hzJ⟩ := hz
    exact ⟨f '' J, ⟨J, hJ, rfl⟩, hzJ⟩

/-- **components of `Γ ∖ P` are relatively open** (ULC of Jordan curves) -/
theorem t39j_jordan_comp_nhds {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (P : Finset ℂ)
    {y : ℂ} (hy : y ∈ Γ \ ↑P) :
    ∃ δ > 0, ∀ z ∈ Γ, dist y z < δ → z ∈ connectedComponentIn (Γ \ ↑P) y := by
  have hPc : IsClosed (↑P : Set ℂ) := P.finite_toSet.isClosed
  obtain ⟨r, hr, hrP⟩ := Metric.isOpen_iff.1 hPc.isOpen_compl y hy.2
  have hΓc : IsCompact Γ := by
    obtain ⟨γ, hγc, -, rfl⟩ := hΓ; exact (isCompact_sphere 0 1).image_of_continuousOn hγc
  obtain ⟨δ, hδ, hU⟩ := JordanMap.jm_ulc_of_isJordanCurve hΓ (r / 2) (by positivity)
  refine ⟨δ, hδ, fun z hz hyz => ?_⟩
  obtain ⟨β, hβΓ, hβc, hyβ, hzβ, hβd⟩ := hU y hy.1 z hz hyz
  have hβP : β ⊆ Γ \ ↑P := fun w hw => ⟨hβΓ hw, hrP (by
    rw [mem_ball, dist_comm]
    exact lt_of_le_of_lt ((Metric.dist_le_diam_of_mem (hΓc.isBounded.subset hβΓ) hyβ hw).trans
      hβd) (by linarith))⟩
  exact hβc.subset_connectedComponentIn hyβ hβP hzβ

end LQGMetric.CONF
