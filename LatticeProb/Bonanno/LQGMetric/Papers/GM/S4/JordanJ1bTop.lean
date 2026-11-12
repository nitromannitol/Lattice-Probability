/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.JordanJ1bTop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1b

/-!
# Node J1b, topological half: MS l. 572–582 reduced to a sector lemma for crossing continua

Miller–Sheffield arXiv:1506.03806, proof of Prop 2.1 (`mapmaking_final.tex` l. 572–582):
"Suppose for contradiction that `Γ` is not locally connected … the closure of every component of
`Γ ∩ B(z, s)` has non-empty intersection with `∂B(z, s)` … the number of such components which
intersect `B(z, ε)` must be infinite … there must be an annulus `A` … such that `A ∩ Γ` contains
infinitely many connected components crossing it … It is not hard to see from this that both
`A ∩ U` and `A ∩ Ũ` contain infinitely many distinct components crossing `A`."

* `j1b_bumping`: boundary bumping for an arbitrary closed set `F` (generalizes
  `jl_boundary_bumping`, same proof).
* `j1b_exists_crossing`: a continuum meeting `B(x, r₁)` and `ℂ ∖ B̄(x, r₂)` contains a continuum
  in the closed annulus meeting both boundary circles (two applications of bumping).
* `gm_j1bTop_of_sector`: MS's chain l. 572–582 — infinitely many components of `Γ ∩ B̄(x, R')`
  approach `x` (else local connectedness), each contains a continuum crossing the annulus
  `{R'/8 ≤ |y − x| ≤ R'/2}`, these are pairwise disjoint, and every point of them is in the closure
  of `V`; if only finitely many components of `A ∖ Γ` met `V` in the middle, one of them would
  touch three disjoint crossing continua, contradicting the **sector lemma** `GMSector` (three
  pairwise disjoint continua crossing a closed annulus cut the open annulus so that no connected
  subset of the complement touches all three). `GMSector` is the planar-topology content of MS's
  "it is not hard to see" (l. 582); it is the open node left by this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.GM

/-- **Boundary bumping** for a closed set `F` (MS l. 572; same proof as `jl_boundary_bumping`). -/
theorem j1b_bumping {Γ F : Set ℂ} (hΓc : IsCompact Γ) (hΓ : IsPreconnected Γ) (hF : IsClosed F)
    {x : ℂ} (hx : x ∈ Γ ∩ F) (hout : ¬ Γ ⊆ interior F) :
    (connectedComponentIn (Γ ∩ F) x ∩ frontier F).Nonempty := by
  set G := Γ ∩ F with hG
  have hGc : IsCompact G := hΓc.inter_right hF
  have hGcl : IsClosed G := hGc.isClosed
  haveI : CompactSpace G := isCompact_iff_compactSpace.1 hGc
  set x' : G := ⟨x, hx⟩
  rw [connectedComponentIn_eq_image hx]
  by_contra hne
  set S : Set G := {p | (p : ℂ) ∈ frontier F} with hS
  have hSc : IsCompact S := (isClosed_frontier.preimage continuous_subtype_val).isCompact
  have hSC : S ∩ ⋂ s : {s : Set G // IsClopen s ∧ x' ∈ s}, s.1 = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    refine eq_empty_iff_forall_notMem.2 fun p ⟨hpS, hpC⟩ => hne ⟨p, ⟨p, hpC, rfl⟩, hpS⟩
  obtain ⟨t, ht⟩ : ∃ t : Finset {s : Set G // IsClopen s ∧ x' ∈ s},
      ¬ (S ∩ ⋂ i ∈ t, i.1).Nonempty := by
    by_contra h
    push Not at h
    have := hSc.inter_iInter_nonempty (fun s : {s : Set G // IsClopen s ∧ x' ∈ s} => s.1)
      (fun s => s.2.1.1) h
    rw [hSC] at this
    exact this.ne_empty rfl
  set W : Set G := ⋂ i ∈ t, i.1 with hW
  have hWcl : IsClopen W := isClopen_biInter_finset fun s _ => s.2.1
  have hxW : x' ∈ W := mem_iInter₂.2 fun s _ => s.2.2
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.1 hWcl.2
  set W' : Set ℂ := (↑) '' W with hW'
  have hW'c : IsClosed W' := hGcl.isClosedEmbedding_subtypeVal.isClosedMap W hWcl.1
  have hW'int : W' ⊆ interior F := by
    rintro _ ⟨p, hp, rfl⟩
    have hpS : p ∉ S := fun h => ht ⟨p, h, hp⟩
    by_contra h
    exact hpS (show (p : ℂ) ∈ frontier F from ⟨subset_closure p.2.2, h⟩)
  obtain ⟨q, hqΓ, hqb⟩ := not_subset.1 hout
  have hcov : Γ ⊆ (O ∩ interior F) ∪ W'ᶜ := by
    intro p hp
    by_cases hpW : p ∈ W'
    · obtain ⟨p', hp', rfl⟩ := hpW
      exact Or.inl ⟨(hOW ▸ hp' : p' ∈ (↑) ⁻¹' O), hW'int ⟨p', hp', rfl⟩⟩
    · exact Or.inr hpW
  have hxO : x ∈ O := (hOW ▸ hxW : x' ∈ (↑) ⁻¹' O)
  have hxint : x ∈ interior F := hW'int ⟨x', hxW, rfl⟩
  obtain ⟨p, hpΓ, ⟨hpO, hpb⟩, hpW⟩ := hΓ (O ∩ interior F) W'ᶜ (hO.inter isOpen_interior)
    hW'c.isOpen_compl hcov ⟨x, hx.1, hxO, hxint⟩ ⟨q, hqΓ, fun h => hqb (hW'int h)⟩
  have hpG : p ∈ G := ⟨hpΓ, interior_subset hpb⟩
  exact hpW ⟨⟨p, hpG⟩, hOW ▸ (show (⟨p, hpG⟩ : G) ∈ (↑) ⁻¹' O from hpO), rfl⟩

/-- Components of a closed set are closed. -/
theorem j1b_isClosed_cc {F : Set ℂ} (hF : IsClosed F) (p : ℂ) :
    IsClosed (connectedComponentIn F p) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  by_cases hp : p ∈ F
  · exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hp))
      (closure_minimal (connectedComponentIn_subset _ _) hF) hy
  · rw [connectedComponentIn_eq_empty hp] at hy ⊢
    simpa using hy

/-- `K` is a continuum in the closed annulus `{r₁ ≤ |y − x| ≤ r₂}` meeting both circles. -/
def j1bCrossing (x : ℂ) (r₁ r₂ : ℝ) (K : Set ℂ) : Prop :=
  IsCompact K ∧ IsPreconnected K ∧ (∀ y ∈ K, r₁ ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ r₂) ∧
    (∃ y ∈ K, ‖y - x‖ = r₁) ∧ (∃ y ∈ K, ‖y - x‖ = r₂)

theorem j1b_continuous_norm_sub (x : ℂ) : Continuous fun y : ℂ => ‖y - x‖ :=
  (continuous_id.sub continuous_const).norm

/-- A continuum meeting `B(x, r₁)` and `ℂ ∖ B̄(x, r₂)` contains a crossing continuum of the
closed annulus (MS l. 582, "components crossing `A`"). -/
theorem j1b_exists_crossing {Y : Set ℂ} (hYc : IsCompact Y) (hY : IsPreconnected Y) {x p q : ℂ}
    {r₁ r₂ : ℝ} (h12 : r₁ < r₂) (hp : p ∈ Y) (hp1 : ‖p - x‖ < r₁) (hq : q ∈ Y)
    (hq2 : r₂ < ‖q - x‖) : ∃ K ⊆ Y, j1bCrossing x r₁ r₂ K := by
  have hn := j1b_continuous_norm_sub x
  set F₁ : Set ℂ := {y | r₁ ≤ ‖y - x‖} with hF₁d
  have hF₁ : IsClosed F₁ := isClosed_le continuous_const hn
  have hint₁ : {y : ℂ | r₁ < ‖y - x‖} ⊆ interior F₁ :=
    interior_maximal (fun y (hy : r₁ < ‖y - x‖) => show r₁ ≤ ‖y - x‖ from hy.le)
      (isOpen_lt continuous_const hn)
  have hfr₁ : ∀ y ∈ frontier F₁, ‖y - x‖ = r₁ := fun y hy =>
    le_antisymm (not_lt.1 fun h => hy.2 (hint₁ h)) (hF₁.frontier_subset hy)
  have hq₁ : q ∈ Y ∩ F₁ := ⟨hq, show r₁ ≤ ‖q - x‖ by linarith⟩
  obtain ⟨p', hp'C, hp'fr⟩ := j1b_bumping hYc hY hF₁ hq₁
    (fun h => (not_le.2 hp1) (show p ∈ F₁ from interior_subset (h hp)))
  set C := connectedComponentIn (Y ∩ F₁) q with hC
  have hCc : IsCompact C := (hYc.inter_right hF₁).of_isClosed_subset
    (j1b_isClosed_cc (hYc.isClosed.inter hF₁) q) (connectedComponentIn_subset _ _)
  have hCp : IsPreconnected C := isPreconnected_connectedComponentIn
  have hfr₂ : ∀ y ∈ frontier (closedBall x r₂), ‖y - x‖ = r₂ := fun y hy => by
    have h1 : y ∈ closedBall x r₂ := isClosed_closedBall.frontier_subset hy
    have h2 : y ∉ ball x r₂ := fun h =>
      hy.2 (interior_maximal ball_subset_closedBall isOpen_ball h)
    rw [mem_closedBall, dist_eq_norm] at h1
    rw [mem_ball, dist_eq_norm] at h2
    linarith [not_lt.1 h2]
  have hqC : q ∈ C := mem_connectedComponentIn hq₁
  have hp'F₂ : p' ∈ C ∩ closedBall x r₂ :=
    ⟨hp'C, by rw [mem_closedBall, dist_eq_norm, hfr₁ p' hp'fr]; exact h12.le⟩
  obtain ⟨q', hq'K, hq'fr⟩ := j1b_bumping hCc hCp isClosed_closedBall hp'F₂ (fun h => by
    have := interior_subset (h hqC)
    rw [mem_closedBall, dist_eq_norm] at this
    linarith)
  refine ⟨connectedComponentIn (C ∩ closedBall x r₂) p',
    (connectedComponentIn_subset _ _).trans
      (inter_subset_left.trans ((connectedComponentIn_subset _ _).trans inter_subset_left)),
    (hCc.inter_right isClosed_closedBall).of_isClosed_subset
      (j1b_isClosed_cc (hCc.isClosed.inter isClosed_closedBall) p')
      (connectedComponentIn_subset _ _),
    isPreconnected_connectedComponentIn, fun y hy => ?_,
    ⟨p', mem_connectedComponentIn hp'F₂, hfr₁ p' hp'fr⟩, ⟨q', hq'K, hfr₂ q' hq'fr⟩⟩
  have hy' := connectedComponentIn_subset _ _ hy
  have hyF₁ : y ∈ F₁ := (connectedComponentIn_subset _ _ hy'.1).2
  have hy2 := hy'.2
  rw [mem_closedBall, dist_eq_norm] at hy2
  exact ⟨hyF₁, hy2⟩

/-- **Sector lemma** (open node; the planar-topology content of MS l. 582): three pairwise
disjoint continua crossing the closed annulus `{r₁ ≤ |y − x| ≤ r₂}` are not all touched by the
closure of one connected subset of the open annulus avoiding them. -/
def GMSector : Prop :=
  ∀ (x : ℂ) (r₁ r₂ : ℝ) (K₁ K₂ K₃ W : Set ℂ), 0 < r₁ → r₁ < r₂ →
    j1bCrossing x r₁ r₂ K₁ → j1bCrossing x r₁ r₂ K₂ → j1bCrossing x r₁ r₂ K₃ →
    Disjoint K₁ K₂ → Disjoint K₁ K₃ → Disjoint K₂ K₃ → IsPreconnected W →
    W ⊆ j1bAnn x r₁ r₂ → Disjoint W (K₁ ∪ K₂ ∪ K₃) →
    ¬ ((closure W ∩ K₁).Nonempty ∧ (closure W ∩ K₂).Nonempty ∧ (closure W ∩ K₃).Nonempty)

/-- **MS l. 572–582**: the sector lemma implies the topological half `GMJ1bTop` of J1b. -/
theorem gm_j1bTop_of_sector (hsec : GMSector) : GMJ1bTop := by
  intro Γ V x ε R hΓc hΓp hVΓ hΓV hx hε hR hbad
  have hn := j1b_continuous_norm_sub x
  set R' := min (ε / 3) R with hR'
  have hR'pos : 0 < R' := lt_min (by linarith) hR
  have hR'ε : 2 * R' < ε := by have := min_le_left (ε / 3) R; linarith
  have hR'R : R' ≤ R := min_le_right _ _
  set F := Γ ∩ closedBall x R' with hF
  have hFc : IsCompact F := hΓc.inter_right isClosed_closedBall
  have hxF : x ∈ F := ⟨hx, mem_closedBall_self hR'pos.le⟩
  have hbadC : ∀ a ∈ Γ, (¬ ∃ β ⊆ Γ, IsPreconnected β ∧ x ∈ β ∧ a ∈ β ∧ diam β ≤ ε) →
      a ∉ connectedComponentIn F x := fun a _ hb haC =>
    hb ⟨_, (connectedComponentIn_subset _ _).trans inter_subset_left,
      isPreconnected_connectedComponentIn, mem_connectedComponentIn hxF, haC,
      (diam_le_of_subset_closedBall hR'pos.le
        ((connectedComponentIn_subset _ _).trans inter_subset_right)).trans hR'ε.le⟩
  have hout : ¬ Γ ⊆ interior (closedBall x R') := fun h => by
    obtain ⟨a, ha, -, hb⟩ := hbad 1 one_pos
    exact hb ⟨Γ, subset_rfl, hΓp, hx, ha,
      (diam_le_of_subset_closedBall hR'pos.le (h.trans interior_subset)).trans hR'ε.le⟩
  have haF : ∀ a ∈ Γ, ‖a - x‖ < R' / 8 → a ∈ F := fun a ha har =>
    ⟨ha, by rw [mem_closedBall, dist_eq_norm]; linarith⟩
  refine ⟨R' / 8, R' / 5, R' / 3, R' / 2, by positivity, by linarith, by linarith, by linarith,
    by linarith, fun hfin => ?_⟩
  set 𝒲 := {W | ∃ w ∈ V, R' / 5 ≤ ‖w - x‖ ∧ ‖w - x‖ ≤ R' / 3 ∧
    W = connectedComponentIn (j1bAnn x (R' / 8) (R' / 2) \ Γ) w} with h𝒲
  set 𝒞 : Set (Set ℂ) := {C | ∃ a ∈ Γ, ‖a - x‖ < R' / 8 ∧
    (¬ ∃ β ⊆ Γ, IsPreconnected β ∧ x ∈ β ∧ a ∈ β ∧ diam β ≤ ε) ∧
    C = connectedComponentIn F a} with h𝒞
  have hCF : ∀ C ∈ 𝒞, C ⊆ F := by
    rintro C ⟨a, -, -, -, rfl⟩
    exact connectedComponentIn_subset _ _
  -- infinitely many components of `Γ ∩ B̄(x, R')` approach `x` (MS l. 572)
  have h𝒞inf : 𝒞.Infinite := by
    intro h𝒞fin
    have hcl : IsClosed (⋃ C ∈ 𝒞, C) := h𝒞fin.isClosed_biUnion fun C hC => by
      obtain ⟨a, -, -, -, rfl⟩ := hC
      exact j1b_isClosed_cc hFc.isClosed a
    have hxn : x ∉ ⋃ C ∈ 𝒞, C := by
      rw [mem_iUnion₂]
      rintro ⟨C, ⟨a, ha, har, hb, rfl⟩, hxC⟩
      refine hbadC a ha hb ?_
      rw [← connectedComponentIn_eq hxC]
      exact mem_connectedComponentIn (haF a ha har)
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl x hxn
    obtain ⟨a, ha, hax, hb⟩ := hbad (min ρ (R' / 8)) (lt_min hρ (by positivity))
    have har : ‖a - x‖ < R' / 8 := by rw [← dist_eq_norm]; exact hax.trans_le (min_le_right _ _)
    exact hρsub (mem_ball.2 (hax.trans_le (min_le_left _ _)))
      (mem_iUnion₂.2 ⟨_, ⟨a, ha, har, hb, rfl⟩, mem_connectedComponentIn (haF a ha har)⟩)
  -- each contains a continuum crossing the annulus (MS l. 582)
  have hcross : ∀ C ∈ 𝒞, ∃ K ⊆ C, j1bCrossing x (R' / 8) (R' / 2) K := by
    rintro C ⟨a, ha, har, -, rfl⟩
    have haF' := haF a ha har
    obtain ⟨q, hqC, hqfr⟩ := j1b_bumping hΓc hΓp isClosed_closedBall haF' hout
    have hq : R' ≤ ‖q - x‖ := by
      by_contra h
      refine hqfr.2 (interior_maximal ball_subset_closedBall isOpen_ball ?_)
      rw [mem_ball, dist_eq_norm]
      exact not_le.1 h
    exact j1b_exists_crossing
      (hFc.of_isClosed_subset (j1b_isClosed_cc hFc.isClosed a) (connectedComponentIn_subset _ _))
      isPreconnected_connectedComponentIn (by linarith) (mem_connectedComponentIn haF') har hqC
      (by linarith)
  choose! K hKC hK using hcross
  have hmid : ∀ C ∈ 𝒞, ∃ y ∈ K C, ‖y - x‖ = R' / 4 := by
    intro C hC
    obtain ⟨-, hKp, -, ⟨y₁, hy₁, h₁⟩, ⟨y₂, hy₂, h₂⟩⟩ := hK C hC
    obtain ⟨y, hy, hyv⟩ := hKp.intermediate_value hy₁ hy₂ hn.continuousOn
      (show R' / 4 ∈ Icc ‖y₁ - x‖ ‖y₂ - x‖ by rw [h₁, h₂]; constructor <;> linarith)
    exact ⟨y, hy, hyv⟩
  choose! y hyK hy using hmid
  -- each `y C` is in the closure of one of the finitely many components `W ∈ 𝒲`
  have h𝒲cov : ∀ C ∈ 𝒞, ∃ W ∈ 𝒲, y C ∈ closure W := by
    intro C hC
    have hyΓ : y C ∈ Γ := (hCF C hC (hKC C hC (hyK C hC))).1
    set O : Set ℂ := {w | R' / 5 < ‖w - x‖ ∧ ‖w - x‖ < R' / 3} with hO
    have hOo : IsOpen O := (isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const)
    have hyO : y C ∈ O := by
      show R' / 5 < ‖y C - x‖ ∧ ‖y C - x‖ < R' / 3
      rw [hy C hC]; constructor <;> linarith
    have hcl : y C ∈ closure (O ∩ V) := hOo.inter_closure ⟨hyO, hΓV hyΓ⟩
    have hsub : O ∩ V ⊆ ⋃ W ∈ 𝒲, W := fun w ⟨⟨hw1, hw2⟩, hwV⟩ => mem_iUnion₂.2
      ⟨_, ⟨w, hwV, hw1.le, hw2.le, rfl⟩,
        mem_connectedComponentIn ⟨⟨by linarith, by linarith⟩, disjoint_left.1 hVΓ hwV⟩⟩
    have h1 := closure_mono hsub hcl
    rw [Set.Finite.closure_biUnion hfin] at h1
    obtain ⟨W, hW, hyW⟩ := mem_iUnion₂.1 h1
    exact ⟨W, hW, hyW⟩
  choose! g hg𝒲 hgy using h𝒲cov
  obtain ⟨W, hW𝒲, hWinf⟩ : ∃ W ∈ 𝒲, {C | C ∈ 𝒞 ∧ g C = W}.Infinite := by
    by_contra h
    push Not at h
    refine h𝒞inf ((hfin.biUnion fun W hW => h W hW)
      |>.subset fun C hC => mem_iUnion₂.2 ⟨g C, hg𝒲 C hC, hC, rfl⟩)
  obtain ⟨C₁, hC₁, hg₁⟩ := hWinf.nonempty
  obtain ⟨C₂, ⟨hC₂, hg₂⟩, hC₂n⟩ := hWinf.exists_notMem_finset {C₁}
  obtain ⟨C₃, ⟨hC₃, hg₃⟩, hC₃n⟩ := hWinf.exists_notMem_finset {C₁, C₂}
  have h21 : C₂ ≠ C₁ := fun h => hC₂n (by simp [h])
  have h31 : C₃ ≠ C₁ := fun h => hC₃n (by simp [h])
  have h32 : C₃ ≠ C₂ := fun h => hC₃n (by simp [h])
  have hdisj : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → Disjoint (K C) (K C') := by
    intro C hC C' hC' hne
    refine disjoint_left.2 fun p hp hp' => hne ?_
    have hpC := hKC C hC hp
    have hpC' := hKC C' hC' hp'
    obtain ⟨a, -, -, -, rfl⟩ := hC
    obtain ⟨a', -, -, -, rfl⟩ := hC'
    rw [connectedComponentIn_eq hpC, connectedComponentIn_eq hpC']
  obtain ⟨w, hwV, hw1, hw2, rfl⟩ := hW𝒲
  have hWsub : connectedComponentIn (j1bAnn x (R' / 8) (R' / 2) \ Γ) w ⊆
      j1bAnn x (R' / 8) (R' / 2) \ Γ := connectedComponentIn_subset _ _
  have hKΓ : ∀ C ∈ 𝒞, K C ⊆ Γ := fun C hC p hp => (hCF C hC (hKC C hC hp)).1
  refine hsec x (R' / 8) (R' / 2) (K C₁) (K C₂) (K C₃) _ (by positivity) (by linarith)
    (hK C₁ hC₁) (hK C₂ hC₂) (hK C₃ hC₃) (hdisj C₁ hC₁ C₂ hC₂ h21.symm)
    (hdisj C₁ hC₁ C₃ hC₃ h31.symm) (hdisj C₂ hC₂ C₃ hC₃ h32.symm)
    isPreconnected_connectedComponentIn (hWsub.trans diff_subset) ?_
    ⟨⟨y C₁, hg₁ ▸ hgy C₁ hC₁, hyK C₁ hC₁⟩, ⟨y C₂, hg₂ ▸ hgy C₂ hC₂, hyK C₂ hC₂⟩,
      ⟨y C₃, hg₃ ▸ hgy C₃ hC₃, hyK C₃ hC₃⟩⟩
  refine disjoint_left.2 fun p hp hpK => (hWsub hp).2 ?_
  rcases hpK with (h | h) | h
  · exact hKΓ C₁ hC₁ h
  · exact hKΓ C₂ hC₂ h
  · exact hKΓ C₃ hC₃ h

/-- **J1b from the sector lemma** (MS Prop 2.1 proof, l. 570–601). -/
theorem gm_j1b_of_sector (hsec : GMSector) : GMJ1b := fun _ _ _ hs hL hbd =>
  gm_filledBallBdyLC_of_top (gm_j1bTop_of_sector hsec) hs hL hbd

/-- GM.S-Jordan (GPS Lemma 2.4 for filled balls) modulo the sector lemma only. -/
theorem gm_filledBall_frontier_isJordanCurve_of_sector (hsec : GMSector) {D : ContMetric}
    {z : ℂ} {s : ℝ} (hs : 0 < s) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (Blueprint.ballM D z s)) :
    JordanMap.IsJordanCurve (frontier (Blueprint.filledBall D z s)) :=
  gm_filledBall_frontier_isJordanCurve hs hL hbd (gm_j1b_of_sector hsec D z s hs hL hbd)

/-- J2 for filled balls (`gm_filledBall_conformal`) modulo the sector lemma only. -/
theorem gm_filledBall_conformal_of_sector (hsec : GMSector) {D : ContMetric} {z : ℂ} {s : ℝ}
    (hs : 0 < s) (hL : D.IsLength) (hbd : Bornology.IsBounded (Blueprint.ballM D z s)) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (closedBall 0 1 \ {0}) ∧ InjOn Ψ (closedBall 0 1 \ {0}) ∧
      DifferentiableOn ℂ Ψ (ball 0 1 \ {0}) ∧
      Ψ '' (ball 0 1 \ {0}) = (Blueprint.filledBall D z s)ᶜ ∧
      Ψ '' sphere 0 1 = frontier (Blueprint.filledBall D z s) ∧
      Tendsto Ψ (𝓝[≠] 0) (Bornology.cobounded ℂ) :=
  gm_filledBall_conformal hs hL hbd (gm_j1b_of_sector hsec D z s hs hL hbd)

end LQGMetric.GM
