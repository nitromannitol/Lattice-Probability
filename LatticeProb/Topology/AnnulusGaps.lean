/-
# Gaps between crossing continua of a round annulus

Let `K ⊆ ℂ` be closed, `x ∈ ℂ` and `0 ≤ s < t`. Let `P`, `P'` be continua of the closed annulus
`closedBall x t \ ball x s` avoiding `K`, meeting the inner circle `sphere x s`, and meeting the outer circle
`sphere x t` only at `circleMap x t θ` and `circleMap x t θ'` respectively, where `θ < θ' < θ + 2π`. Suppose the
arcs of angular radius `ε` about these two points miss `K`, and that no connected subset of
`closedBall x t \ K` contains both points. Then a component of `K ∩ {z | s ≤ dist z x ≤ t}` crosses the annulus
(it meets both boundary circles) and contains a point `circleMap x t α` with `θ + ε ≤ α ≤ θ' - ε`.

The proof applies the Hex lemma `exists_isPreconnected_meets_top_and_inner_or_bot` to the arcs
`Top = circleMap x t '' [θ + ε, θ' - ε]` and `Bot = circleMap x t '' [θ' + ε, θ + 2π - ε]`, joined below by
`P ∪ [a, x] ∪ [x, a'] ∪ P'`; the alternation lemma `false_of_alternating_annulus_crossings` shows that the
resulting component cannot meet `Bot`.
-/
import LatticeProb.Topology.DiskHex
import LatticeProb.Topology.DiskAlternationComplex
import LatticeProb.Topology.PlaneTopology
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

open Set Metric Complex

namespace LatticeProb.Topology

/-- A point of the circle `sphere x t` is `circleMap x t γ` for an angle `γ` in any half-open window
`[a, a + 2π)`. -/
theorem exists_mem_Ico_circleMap_eq {x z : ℂ} {t : ℝ} (hz : dist z x = t) (a : ℝ) :
    ∃ γ ∈ Ico a (a + 2 * Real.pi), circleMap x t γ = z := by
  have h0 : circleMap x t (arg (z - x)) = z := by
    simp only [circleMap]
    rw [← hz, dist_eq_norm, norm_mul_exp_arg_mul_I]
    ring
  refine ⟨toIcoMod Real.two_pi_pos a (arg (z - x)), toIcoMod_mem_Ico _ _ _, ?_⟩
  rw [← self_sub_toIcoDiv_zsmul, (periodic_circleMap x t).sub_zsmul_eq, h0]

/-- The images under `circleMap x t` (with `t ≠ 0`) of two angle intervals `[a₁, b₁]` and `[a₂, b₂]` with
`b₁ < a₂` and `b₂ < a₁ + 2π` are disjoint. -/
theorem disjoint_circleMap_image_Icc {x : ℂ} {t : ℝ} (ht : t ≠ 0) {a₁ b₁ a₂ b₂ : ℝ}
    (h₁₂ : b₁ < a₂) (h₂₁ : b₂ < a₁ + 2 * Real.pi) :
    Disjoint (circleMap x t '' Icc a₁ b₁) (circleMap x t '' Icc a₂ b₂) := by
  rw [disjoint_left]
  rintro _ ⟨α, hα, rfl⟩ ⟨β, hβ, hαβ⟩
  have h : β = α := eq_of_circleMap_eq ht
    (by rw [abs_lt]; constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]) hαβ
  linarith [hα.2, hβ.1]

/-- The part of `K` in the closed annulus, written with the `1`-Lipschitz function `dist · x`. -/
theorem inter_preimage_dist_Icc (K : Set ℂ) (x : ℂ) (s t : ℝ) :
    K ∩ (fun z => dist z x) ⁻¹' Icc s t = K ∩ (closedBall x t \ ball x s) := by
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_Icc, mem_sdiff, mem_closedBall, mem_ball, not_lt]
  tauto

/-- **A crossing component in each gap.** Let `K ⊆ ℂ` be closed and `0 ≤ s < t`. Let `P`, `P'` be continua of
the closed annulus `closedBall x t \ ball x s` disjoint from `K`, meeting `sphere x s` at `a`, `a'`, and meeting
`sphere x t` only at `circleMap x t θ`, `circleMap x t θ'`, where `θ + 2ε ≤ θ' < θ + 2π`. If the arcs of angular
radius `ε` about `θ` and `θ'` miss `K` and no preconnected subset of `closedBall x t \ K` contains both endpoints,
then some component of `K ∩ (dist · x) ⁻¹' [s, t]` meets both `{dist · x = s}` and `{dist · x = t}` and contains
`circleMap x t α` for some `α ∈ [θ + ε, θ' - ε]`. -/
theorem exists_crossing_component_meets_gap {x : ℂ} {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {K : Set ℂ} (hK : IsClosed K) {P P' : Set ℂ} {a a' : ℂ} {θ θ' ε : ℝ}
    (hP : IsCompact P) (hPc : IsConnected P) (hP' : IsCompact P') (hP'c : IsConnected P')
    (hPA : P ⊆ closedBall x t \ ball x s) (hP'A : P' ⊆ closedBall x t \ ball x s)
    (haP : a ∈ P) (ha : dist a x = s) (ha'P : a' ∈ P') (ha' : dist a' x = s)
    (hbP : circleMap x t θ ∈ P) (hb'P : circleMap x t θ' ∈ P')
    (hPt : ∀ z ∈ P, dist z x = t → z = circleMap x t θ)
    (hP't : ∀ z ∈ P', dist z x = t → z = circleMap x t θ')
    (hPK : Disjoint P K) (hP'K : Disjoint P' K) (hε : 0 < ε) (hθε : θ + 2 * ε ≤ θ')
    (hθ' : θ' < θ + 2 * Real.pi)
    (hεK : ∀ γ ∈ Ioo (θ - ε) (θ + ε), circleMap x t γ ∉ K)
    (hεK' : ∀ γ ∈ Ioo (θ' - ε) (θ' + ε), circleMap x t γ ∉ K)
    (hjoin : ∀ Z ⊆ closedBall x t \ K, IsPreconnected Z → circleMap x t θ ∈ Z →
      circleMap x t θ' ∉ Z) :
    ∃ C ∈ connectedComponentsIn (K ∩ (fun z => dist z x) ⁻¹' Icc s t),
      ((∃ p ∈ C, dist p x = s) ∧ ∃ p ∈ C, dist p x = t) ∧
      ∃ α ∈ Icc (θ + ε) (θ' - ε), circleMap x t α ∈ C := by
  have ht : 0 < t := hs.trans_lt hst
  have htne : t ≠ 0 := ht.ne'
  have hpi := Real.pi_pos
  have hec : Continuous (circleMap x t) := continuous_circleMap x t
  have himS : ∀ u v : ℝ, circleMap x t '' Icc u v ⊆ sphere x t := fun u v =>
    image_subset_iff.2 fun γ _ => circleMap_mem_sphere x ht.le γ
  have himC : ∀ u v : ℝ, IsCompact (circleMap x t '' Icc u v) := fun u v =>
    isCompact_Icc.image hec
  have himP : ∀ u v : ℝ, IsPreconnected (circleMap x t '' Icc u v) := fun u v =>
    isPreconnected_Icc.image _ hec.continuousOn
  set Top := circleMap x t '' Icc (θ + ε) (θ' - ε) with hTop
  set Bot := circleMap x t '' Icc (θ' + ε) (θ + 2 * Real.pi - ε) with hBot
  have hTB : Disjoint Top Bot := disjoint_circleMap_image_Icc htne (by linarith) (by linarith)
  have hArcBot : Disjoint (circleMap x t '' Icc θ θ') Bot :=
    disjoint_circleMap_image_Icc htne (by linarith) (by linarith)
  have hbTop : circleMap x t θ ∉ Top :=
    disjoint_left.1 (disjoint_circleMap_image_Icc htne (a₁ := θ) (b₁ := θ) (a₂ := θ + ε)
      (b₂ := θ' - ε) (by linarith) (by linarith)) (mem_image_of_mem _ (left_mem_Icc.2 le_rfl))
  have hb'Top : circleMap x t θ' ∉ Top :=
    disjoint_right.1 (disjoint_circleMap_image_Icc htne (a₁ := θ + ε) (b₁ := θ' - ε) (a₂ := θ')
      (b₂ := θ') (by linarith) (by linarith)) (mem_image_of_mem _ (left_mem_Icc.2 le_rfl))
  -- the circle points of `K` lie on `Top ∪ Bot`
  have hKS : K ∩ sphere x t ⊆ Top ∪ Bot := by
    rintro z ⟨hzK, hzS⟩
    obtain ⟨γ, ⟨hγ1, hγ2⟩, rfl⟩ := exists_mem_Ico_circleMap_eq (mem_sphere.1 hzS) θ
    by_cases h1 : γ < θ + ε
    · exact absurd hzK (hεK γ ⟨by linarith, h1⟩)
    by_cases h2 : γ ≤ θ' - ε
    · exact Or.inl (mem_image_of_mem _ ⟨not_lt.1 h1, h2⟩)
    by_cases h3 : γ < θ' + ε
    · exact absurd hzK (hεK' γ ⟨by linarith [not_le.1 h2], h3⟩)
    by_cases h4 : γ ≤ θ + 2 * Real.pi - ε
    · exact Or.inr (mem_image_of_mem _ ⟨not_lt.1 h3, h4⟩)
    · refine absurd ?_ (hεK (γ - 2 * Real.pi) ⟨by linarith [not_le.1 h4], by linarith⟩)
      rwa [(periodic_circleMap x t).sub_eq]
  -- the lower connection `Γ = P ∪ [a, x] ∪ [a', x] ∪ P'`
  have hsegc : ∀ b : ℂ, IsConnected (segment ℝ b x) := fun b => by
    rw [segment_eq_image']
    have hc : Continuous fun μ : ℝ => b + μ • (x - b) := by fun_prop
    exact (isConnected_Icc zero_le_one).image _ hc.continuousOn
  have hseg : ∀ {b : ℂ}, dist b x = s → segment ℝ b x ⊆ closedBall x s := fun {b} hb =>
    (convex_closedBall x s).segment_subset (mem_closedBall.2 hb.le) (mem_closedBall_self hs)
  have hsegK : ∀ {b : ℂ} {Q : Set ℂ}, b ∈ Q → Disjoint Q K → dist b x = s →
      Disjoint (segment ℝ b x) (K ∩ (closedBall x t \ ball x s)) := fun {b} {Q} hbQ hQK hb => by
    rw [disjoint_left]
    rintro z hz ⟨hzK, -, hzs⟩
    have hzb := eq_of_mem_segment_center_of_not_mem_ball (mem_sphere.2 hb) hz hzs
    exact disjoint_left.1 hQK (hzb ▸ hbQ) hzK
  have hsegTop : ∀ {b : ℂ}, dist b x = s → Disjoint (segment ℝ b x) Top := fun {b} hb => by
    rw [disjoint_left]
    intro z hz hzT
    have h1 := mem_closedBall.1 (hseg hb hz)
    have h2 := mem_sphere.1 (himS _ _ hzT)
    linarith
  set Γ := P ∪ segment ℝ a x ∪ segment ℝ a' x ∪ P' with hΓdef
  have hΓc : IsConnected Γ := by
    have h1 : IsConnected (P ∪ segment ℝ a x) :=
      hPc.union ⟨a, haP, left_mem_segment ℝ a x⟩ (hsegc a)
    have h2 : IsConnected (P ∪ segment ℝ a x ∪ segment ℝ a' x) :=
      h1.union ⟨x, Or.inr (right_mem_segment ℝ a x), right_mem_segment ℝ a' x⟩ (hsegc a')
    exact h2.union ⟨a', Or.inr (left_mem_segment ℝ a' x), ha'P⟩ hP'c
  have hΓD : Γ ⊆ closedBall x t :=
    union_subset (union_subset (union_subset (fun z hz => (hPA hz).1)
      ((hseg ha).trans (closedBall_subset_closedBall hst.le)))
      ((hseg ha').trans (closedBall_subset_closedBall hst.le))) fun z hz => (hP'A hz).1
  have hΓS : Disjoint Γ (K ∩ (closedBall x t \ ball x s)) :=
    disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨disjoint_union_left.2
      ⟨hPK.mono_right inter_subset_left, hsegK haP hPK ha⟩, hsegK ha'P hP'K ha'⟩,
      hP'K.mono_right inter_subset_left⟩
  have hPTop : ∀ {Q : Set ℂ} {b : ℂ}, (∀ z ∈ Q, dist z x = t → z = b) → b ∉ Top →
      Disjoint Q Top := fun {Q} {b} hQ hbT => by
    rw [disjoint_left]
    intro z hzQ hzT
    exact hbT (hQ z hzQ (mem_sphere.1 (himS _ _ hzT)) ▸ hzT)
  have hΓTop : Disjoint Γ Top :=
    disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨disjoint_union_left.2
      ⟨hPTop hPt hbTop, hsegTop ha⟩, hsegTop ha'⟩, hPTop hP't hb'Top⟩
  -- the Hex lemma
  obtain ⟨H, hHS, hHc, ⟨h, hhH, hhTop⟩, ⟨w, hwH, hw⟩⟩ :=
    exists_isPreconnected_meets_top_and_inner_or_bot ht hst hK (himC _ _) (himC _ _) (himS _ _)
      hTB (himP _ _) hKS (himS θ θ') (himP θ θ') hArcBot
      (mem_image_of_mem _ (left_mem_Icc.2 (by linarith))) (mem_image_of_mem _ (right_mem_Icc.2 (by linarith)))
      hΓc.isPreconnected (Or.inl (Or.inl (Or.inl hbP))) (Or.inr hb'P) hΓD hΓS hΓTop hjoin
  obtain ⟨α, hα, rfl⟩ := hhTop
  -- the component of `K ∩ (dist · x) ⁻¹' [s, t]` containing `H`
  set S := K ∩ (fun z => dist z x) ⁻¹' Icc s t with hSdef
  have hSeq : S = K ∩ (closedBall x t \ ball x s) := inter_preimage_dist_Icc K x s t
  have hHS' : H ⊆ S := hSeq ▸ hHS
  have hScl : IsClosed S := hK.inter (isClosed_Icc.preimage (continuous_id.dist continuous_const))
  set C := connectedComponentIn S (circleMap x t α) with hCdef
  have hhS : circleMap x t α ∈ S := hHS' hhH
  have hHC : H ⊆ C := hHc.subset_connectedComponentIn hhH hHS'
  have hCcl : IsClosed C := closure_subset_iff_isClosed.1
    (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hhS)) (closure_minimal (connectedComponentIn_subset _ _) hScl))
  have hCA : C ⊆ closedBall x t \ ball x s :=
    (connectedComponentIn_subset _ _).trans (hSeq ▸ inter_subset_right)
  have hCK : C ⊆ K := (connectedComponentIn_subset _ _).trans inter_subset_left
  have hCcpt : IsCompact C :=
    (isCompact_closedBall x t).of_isClosed_subset hCcl (hCA.trans sdiff_subset)
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.2 hhS
  have hb2 : circleMap x t (θ + 2 * Real.pi) ∈ P := by
    rw [periodic_circleMap x t θ]
    exact hbP
  -- `C` does not meet `Bot`, by alternation with `P'` and `P`
  have hCBot : ∀ z ∈ C, z ∉ Bot := by
    rintro z hzC ⟨β, hβ, rfl⟩
    exact false_of_alternating_annulus_crossings hs hst (θ₁ := α) (θ₂ := θ') (θ₃ := β)
      (θ₄ := θ + 2 * Real.pi) (by linarith [hα.2]) (by linarith [hβ.1]) (by linarith [hβ.2])
      (by linarith [hα.1]) hP' hP'c hP hPc hP'A hPA ha'P (mem_sphere.2 ha') haP (mem_sphere.2 ha)
      hCcpt hCconn hCA (disjoint_union_right.2 ⟨hP'K.symm.mono_left hCK, hPK.symm.mono_left hCK⟩)
      (hHC hhH) hzC hb'P hb2
  rcases hw with hws | hwB
  · exact ⟨C, mem_image_of_mem _ hhS, ⟨⟨w, hHC hwH, mem_sphere.1 hws⟩,
      ⟨circleMap x t α, hHC hhH, mem_sphere.1 (himS _ _ (mem_image_of_mem _ hα))⟩⟩, α, hα, hHC hhH⟩
  · exact absurd hwB (hCBot w (hHC hwH))

end LatticeProb.Topology
