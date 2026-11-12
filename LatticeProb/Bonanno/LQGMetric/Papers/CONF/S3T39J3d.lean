/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J3d at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J3c

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The canonical arcs of a Jordan curve: `t39j_arcChoice` (DEC-120 §4, packet J3)

For a Jordan curve `Γ` the arcs `t39jArcs m i Γ` (S3T39J3c) are preconnected
(`t39j_arcL_conn`: singletons and components of `Γ ∖ P_L`, `t39j_class_eq`), pairwise disjoint
(`t39j_arcs_disj`), cover `Γ` once `t39jQ (t39jLev m Γ) m Γ` holds (`t39j_arcL_cover`), and
eventually separate any finite `F ⊆ Γ` (`t39j_arcs_sep`): the level `t39jLev m Γ → ∞`
(`t39j_lev_eventually`, from finitely many components each containing a label,
`t39j_jordan_finite_pieces`, `t39j_jordan_comp_nhds`, `t39j_pt_dense`), and two points `x ≠ y`
are separated once cut points in both arcs of `t39j_jordan_split` have index `< L`.

**`t39jArcChoice : T39JArcChoice`**, **`t39j_arcChoice : Nonempty T39JArcChoice`**.

CONF C:1740–1744 (DV-D120-1). Own construction (no published source builds a measurable arc
choice; CONF uses harmonic measure).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology Function

namespace LQGMetric.CONF

theorem t39j_cl_eq {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) : closure Γ = Γ :=
  (t39j_jordan_isCompact hΓ).isClosed.closure_eq

theorem t39j_pt_mem_jordan {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) {j : ℕ}
    (hv : t39jValid j Γ) : t39jPt j Γ ∈ Γ := by
  have := (t39jPt_mem hv).1; rwa [t39j_cl_eq hΓ] at this

theorem t39j_comp_symm {F : Set ℂ} {x y : ℂ} (hx : x ∈ F) (h : y ∈ connectedComponentIn F x) :
    x ∈ connectedComponentIn F y := by
  rw [← connectedComponentIn_eq h]; exact mem_connectedComponentIn hx

theorem t39j_free_mem {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) {L j : ℕ}
    (h : t39jFree L j Γ) : t39jPt j Γ ∈ Γ \ t39jCut L Γ :=
  ⟨t39j_pt_mem_jordan hΓ h.1, h.2⟩

theorem t39j_comp_nhds' {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) {y : ℂ}
    (hy : y ∈ Γ \ t39jCut L Γ) :
    ∃ δ > 0, ∀ z ∈ Γ, dist y z < δ → z ∈ connectedComponentIn (Γ \ t39jCut L Γ) y := by
  have hfin := t39j_cut_finite L Γ
  have h := t39j_jordan_comp_nhds hΓ hfin.toFinset (by rw [hfin.coe_toFinset]; exact hy)
  rwa [hfin.coe_toFinset] at h

/-- every component of `Γ ∖ P_L` contains a free label -/
theorem t39j_label_in_comp {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) {x : ℂ}
    (hx : x ∈ Γ \ t39jCut L Γ) :
    ∃ j, t39jFree L j Γ ∧ t39jPt j Γ ∈ connectedComponentIn (Γ \ t39jCut L Γ) x := by
  obtain ⟨δ, hδ, hU⟩ := t39j_comp_nhds' hΓ L hx
  obtain ⟨j, hv, hj, -⟩ := t39j_pt_dense (subset_closure hx.1) hδ
  have hjΓ : t39jPt j Γ ∈ Γ := t39j_pt_mem_jordan hΓ hv
  have hjC := hU _ hjΓ (by rw [dist_comm]; exact hj)
  exact ⟨j, ⟨hv, (connectedComponentIn_subset _ _ hjC).2⟩, hjC⟩

/-- for each level `L`, `t39jQ L m Γ` holds for all large `m` -/
theorem t39j_Q_eventually {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) :
    ∃ M, ∀ m, M ≤ m → t39jQ L m Γ := by
  set F := Γ \ t39jCut L Γ with hF
  have hfin := t39j_cut_finite L Γ
  obtain ⟨𝒢, h𝒢f, h𝒢, hcov⟩ := t39j_jordan_finite_pieces hΓ hfin.toFinset
  rw [hfin.coe_toFinset] at h𝒢 hcov
  have hex : ∀ G : 𝒢, ∃ j, (G : Set ℂ).Nonempty →
      t39jFree L j Γ ∧ ∀ z ∈ (G : Set ℂ), t39jPt j Γ ∈ connectedComponentIn F z := by
    rintro ⟨G, hG⟩
    rcases G.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · exact ⟨0, fun h' => absurd h h'.ne_empty⟩
    · obtain ⟨j, hj, hjC⟩ := t39j_label_in_comp hΓ L ((h𝒢 G hG).2 hx)
      refine ⟨j, fun _ => ⟨hj, fun z hz => ?_⟩⟩
      have hzx : z ∈ connectedComponentIn F x :=
        (h𝒢 G hG).1.subset_connectedComponentIn hx (h𝒢 G hG).2 hz
      rwa [← connectedComponentIn_eq hzx]
  choose J hJ using hex
  have := h𝒢f.to_subtype
  obtain ⟨M, hM⟩ := (Set.finite_range J).bddAbove
  refine ⟨M + 1, fun m hm j hjf => ?_⟩
  have hjF := t39j_free_mem hΓ hjf
  obtain ⟨G, hG, hjG⟩ := hcov hjF
  obtain ⟨hJf, hJC⟩ := hJ ⟨G, hG⟩ ⟨_, hjG⟩
  have hJle : J ⟨G, hG⟩ ≤ M := hM ⟨⟨G, hG⟩, rfl⟩
  refine ⟨J ⟨G, hG⟩, by omega, hJf, ?_⟩
  exact t39j_rc_of_comp hΓ L (t39j_free_mem hΓ hJf) (t39j_comp_symm hjF (hJC _ hjG))

open Classical in
/-- **the level tends to `∞`**, and eventually `t39jQ` holds at the chosen level -/
theorem t39j_lev_eventually {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) :
    ∀ᶠ m in atTop, L ≤ t39jLev m Γ ∧ t39jQ (t39jLev m Γ) m Γ := by
  obtain ⟨M, hM⟩ := t39j_Q_eventually hΓ L
  filter_upwards [eventually_ge_atTop (max M L)] with m hm
  have hQ := hM m (le_trans (le_max_left _ _) hm)
  have hLm : L ≤ m := le_trans (le_max_right _ _) hm
  unfold t39jLev
  exact ⟨Nat.le_findGreatest hLm hQ, Nat.findGreatest_spec (P := fun L => t39jQ L m Γ) hLm hQ⟩

theorem t39j_arcL_mem {L i : ℕ} {Γ : Set ℂ} {z : ℂ} (h : z ∈ t39jArcL L i Γ) :
    (i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ ∧ z = t39jPt i Γ) ∨
      (¬ (i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ) ∧ t39jNew L i Γ ∧
        z ∈ t39jClass L Γ (t39jPt i Γ)) := by
  unfold t39jArcL at h
  split_ifs at h with h1 h2
  · exact Or.inl ⟨h1.1, h1.2.1, h1.2.2, h⟩
  · exact Or.inr ⟨h1, h2, h⟩
  · exact absurd h (notMem_empty z)

theorem t39j_arcL_conn {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L i : ℕ) :
    IsPreconnected (t39jArcL L i Γ) := by
  unfold t39jArcL
  split_ifs with h1 h2
  · exact isPreconnected_singleton
  · rw [t39j_class_eq hΓ L (t39j_free_mem hΓ h2.1)]; exact isPreconnected_connectedComponentIn
  · exact isPreconnected_empty

theorem t39j_arcL_disj {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) {i i' : ℕ}
    (hii : i < i') : Disjoint (t39jArcL L i Γ) (t39jArcL L i' Γ) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rcases t39j_arcL_mem hz with ⟨hi, hv, -, he⟩ | ⟨-, hn, hzc⟩ <;>
    rcases t39j_arcL_mem hz' with ⟨hi', hv', hf', he'⟩ | ⟨-, hn', hzc'⟩
  · exact hf' i hii hv (he.symm.trans he')
  · exact hzc'.2.1 ⟨i, hi, hv, he⟩
  · exact hzc.2.1 ⟨i', hi', hv', he'⟩
  · rw [t39j_class_eq hΓ L (t39j_free_mem hΓ hn.1)] at hzc
    rw [t39j_class_eq hΓ L (t39j_free_mem hΓ hn'.1)] at hzc'
    refine hn'.2 i hii ⟨hn.1, t39j_rc_of_comp hΓ L (t39j_free_mem hΓ hn.1) ?_⟩
    rw [connectedComponentIn_eq hzc]
    exact t39j_comp_symm (t39j_free_mem hΓ hn'.1) hzc'

theorem t39j_arcs_disj {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (m : ℕ) :
    Pairwise (Disjoint on fun i : Fin m => t39jArcs m i Γ) := by
  intro i i' hne
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · exact t39j_arcL_disj hΓ _ h
  · exact (t39j_arcL_disj hΓ _ h).symm

/-- **covering** at a level `L ≤ m` with `t39jQ L m Γ` -/
theorem t39j_arcL_cover {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) {L m : ℕ} (hLm : L ≤ m)
    (hQ : t39jQ L m Γ) {x : ℂ} (hx : x ∈ Γ) : ∃ i < m, x ∈ t39jArcL L i Γ := by
  classical
  by_cases hxP : x ∈ t39jCut L Γ
  · have hex : ∃ j, j < L ∧ t39jValid j Γ ∧ t39jPt j Γ = x := by
      obtain ⟨j, hj, hv, rfl⟩ := hxP; exact ⟨j, hj, hv, rfl⟩
    obtain ⟨hj₀L, hj₀v, hj₀x⟩ := Nat.find_spec hex
    have hfirst : t39jFirst (Nat.find hex) Γ := fun i' hi' hv' he =>
      Nat.find_min hex hi' ⟨lt_trans hi' hj₀L, hv', he.trans hj₀x⟩
    refine ⟨Nat.find hex, lt_of_lt_of_le hj₀L hLm, ?_⟩
    unfold t39jArcL; rw [if_pos ⟨hj₀L, hj₀v, hfirst⟩]; exact hj₀x.symm
  · have hxF : x ∈ Γ \ t39jCut L Γ := ⟨hx, hxP⟩
    obtain ⟨j, hjf, hjC⟩ := t39j_label_in_comp hΓ L hxF
    obtain ⟨i, him, hif, hrc⟩ := hQ j hjf
    have hpi : t39jFree L i Γ ∧
        x ∈ connectedComponentIn (Γ \ t39jCut L Γ) (t39jPt i Γ) := by
      refine ⟨hif, ?_⟩
      rw [connectedComponentIn_eq (t39j_comp_of_rc hΓ L (t39j_free_mem hΓ hif)
        (t39j_free_mem hΓ hjf) hrc)]
      exact t39j_comp_symm hxF hjC
    have hex : ∃ i, t39jFree L i Γ ∧
        x ∈ connectedComponentIn (Γ \ t39jCut L Γ) (t39jPt i Γ) := ⟨i, hpi⟩
    obtain ⟨hi₀f, hi₀C⟩ := Nat.find_spec hex
    have hi₀m : Nat.find hex < m := lt_of_le_of_lt (Nat.find_min' hex hpi) him
    have hnS1 : ¬ (Nat.find hex < L ∧ t39jValid (Nat.find hex) Γ ∧ t39jFirst (Nat.find hex) Γ) :=
      fun h => hi₀f.2 ⟨_, h.1, h.2.1, rfl⟩
    have hnew : t39jNew L (Nat.find hex) Γ := by
      refine ⟨hi₀f, fun i' hi' ⟨hf', hrc'⟩ => Nat.find_min hex hi' ⟨hf', ?_⟩⟩
      rw [connectedComponentIn_eq (t39j_comp_of_rc hΓ L (t39j_free_mem hΓ hf')
        (t39j_free_mem hΓ hi₀f) hrc')]
      exact hi₀C
    refine ⟨Nat.find hex, hi₀m, ?_⟩
    unfold t39jArcL
    rw [if_neg hnS1, if_pos hnew, t39j_class_eq hΓ L (t39j_free_mem hΓ hi₀f)]
    exact hi₀C

/-- a valid label outside a closed set missing a point of `Γ` -/
theorem t39j_label_off_closed {Γ T : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (hT : IsClosed T)
    {a : ℂ} (ha : a ∈ Γ) (haT : a ∉ T) :
    ∃ j, t39jValid j Γ ∧ t39jPt j Γ ∈ Γ ∧ t39jPt j Γ ∉ T := by
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 hT.isOpen_compl a haT
  obtain ⟨j, hv, hj, -⟩ := t39j_pt_dense (subset_closure ha) hε
  exact ⟨j, hv, t39j_pt_mem_jordan hΓ hv, hεT hj⟩

/-- **two points are eventually in different arcs** -/
theorem t39j_pair_sep {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) {x y : ℂ} (hx : x ∈ Γ)
    (hy : y ∈ Γ) (hxy : x ≠ y) :
    ∃ L₁, ∀ L, L₁ ≤ L → ∀ i, x ∈ t39jArcL L i Γ → y ∈ t39jArcL L i Γ → False := by
  obtain ⟨A, B, hAc, hBc, -, -, hAB, hAiB, ⟨a, haA, hax⟩, ⟨b, hbB, hbx⟩, hsep⟩ :=
    t39j_jordan_split hΓ hx hy hxy
  have hxyA : ({x, y} : Set ℂ) ⊆ A := hAiB ▸ inter_subset_left
  have hxyB : ({x, y} : Set ℂ) ⊆ B := hAiB ▸ inter_subset_right
  have haB : a ∉ B := fun h => hax (hAiB ▸ ⟨haA, h⟩)
  have hbA : b ∉ A := fun h => hbx (hAiB ▸ ⟨h, hbB⟩)
  obtain ⟨ja, hva, hjaΓ, hjaB⟩ :=
    t39j_label_off_closed hΓ hBc.isClosed (hAB ▸ Or.inl haA) haB
  obtain ⟨jb, hvb, hjbΓ, hjbA⟩ :=
    t39j_label_off_closed hΓ hAc.isClosed (hAB ▸ Or.inr hbB) hbA
  have hjaA : t39jPt ja Γ ∈ A \ {x, y} :=
    ⟨((hAB ▸ hjaΓ : t39jPt ja Γ ∈ A ∪ B)).resolve_right hjaB, fun h => hjaB (hxyB h)⟩
  have hjbB : t39jPt jb Γ ∈ B \ {x, y} :=
    ⟨((hAB ▸ hjbΓ : t39jPt jb Γ ∈ A ∪ B)).resolve_left hjbA, fun h => hjbA (hxyA h)⟩
  refine ⟨max ja jb + 1, fun L hL i hxi hyi => ?_⟩
  have hca : t39jPt ja Γ ∈ t39jCut L Γ := ⟨ja, by omega, hva, rfl⟩
  have hcb : t39jPt jb Γ ∈ t39jCut L Γ := ⟨jb, by omega, hvb, rfl⟩
  rcases t39j_arcL_mem hxi with ⟨h1, h2, h3, hx'⟩ | ⟨hn1, hn, hxc⟩ <;>
    rcases t39j_arcL_mem hyi with ⟨h1', h2', h3', hy'⟩ | ⟨hn1', hn', hyc⟩
  · exact hxy (hx'.trans hy'.symm)
  · exact hn1' ⟨h1, h2, h3⟩
  · exact hn1 ⟨h1', h2', h3'⟩
  · rw [t39j_class_eq hΓ L (t39j_free_mem hΓ hn.1)] at hxc hyc
    refine hsep _ hjaA _ hjbB _ isPreconnected_connectedComponentIn (fun z hz => ?_) hxc hyc
    have hzF := connectedComponentIn_subset _ _ hz
    refine ⟨hzF.1, ?_⟩
    rintro (rfl | rfl); exacts [hzF.2 hca, hzF.2 hcb]

/-- **eventual covering and separation** -/
theorem t39j_arcs_sep {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (F : Finset ℂ)
    (hF : (F : Set ℂ) ⊆ Γ) :
    ∀ᶠ m in atTop, (∀ x ∈ F, ∃ i, x ∈ t39jArcs m i Γ) ∧
      ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ t39jArcs m i Γ → y ∈ t39jArcs m i Γ → x = y := by
  have hpair : ∀ x ∈ F, ∀ y ∈ F, ∀ᶠ m in atTop, ∀ i : Fin m,
      x ∈ t39jArcs m i Γ → y ∈ t39jArcs m i Γ → x = y := by
    intro x hx y hy
    by_cases hxy : x = y
    · exact Eventually.of_forall fun _ _ _ _ => hxy
    obtain ⟨L₁, hL₁⟩ := t39j_pair_sep hΓ (hF hx) (hF hy) hxy
    filter_upwards [t39j_lev_eventually hΓ L₁] with m hm i hxi hyi
    exact (hL₁ _ hm.1 i hxi hyi).elim
  have hpair' : ∀ᶠ m in atTop, ∀ x ∈ F, ∀ y ∈ F, ∀ i : Fin m,
      x ∈ t39jArcs m i Γ → y ∈ t39jArcs m i Γ → x = y :=
    (eventually_all_finset F).2 fun x hx => (eventually_all_finset F).2 (hpair x hx)
  filter_upwards [hpair', t39j_lev_eventually hΓ 0] with m hm hm0
  refine ⟨fun x hx => ?_, fun i x hx y hy => hm x hx y hy i⟩
  obtain ⟨i, him, hi⟩ := t39j_arcL_cover hΓ (t39j_lev_le m Γ) hm0.2 (hF hx)
  exact ⟨⟨i, him⟩, hi⟩

/-- **the canonical measurable arc choice** -/
def t39jArcChoice : T39JArcChoice where
  arcs := t39jArcs
  subset := t39j_arcs_subset
  meas := fun m i _ hU => t39j_arcs_meas m i hU
  conn := fun _ _ _ hΓ _ => t39j_arcL_conn hΓ _ _
  disj := fun m _ hΓ => t39j_arcs_disj hΓ m
  sep := fun _ hΓ F hF => t39j_arcs_sep hΓ F hF

end LQGMetric.CONF
