import LatticeProb.Topology.CrosscutSeparation
import LatticeProb.Topology.ComplementComponents

/-!
# The two sides of a crosscut

Let `C ⊆ ℂ` be a connected open set and `γ = f([0,1])` a path whose open part `γ° = f((0,1))` lies in `C` and whose
endpoints lie off `C` (a crosscut of `C`). Suppose that `γ` is locally two-sided in `C`: every point `y ∈ γ°` has a
ball `B ⊆ C` such that `B \ γ` is the union of two preconnected sets whose closures both contain `γ ∩ B` (Whyburn,
*Analytic Topology*, Chapter VI; Kuratowski, *Topology* II, §61).

* `subset_or_subset_of_mem_closure_of_mem_connectedComponentsIn`: a component `U` of a set `O` whose closure contains
  `e` contains one of two preconnected subsets of `O` covering `O` near `e`.
* `mem_closure_of_mem_connectedComponentsIn_diff_arc`: every component of `C \ γ` has all of `γ°` in its closure.
* `finite_connectedComponentsIn_diff_arc`: `C \ γ` has finitely many (at most two) components.
-/

open Set Metric
open scoped Topology

namespace LatticeProb.Topology

section General

variable {α : Type*} [TopologicalSpace α] {O U : Set α}

/-- The closure of a component of a set `O` meets `O` only inside that component. -/
theorem closure_inter_subset_of_mem_connectedComponentsIn (hU : U ∈ connectedComponentsIn O) :
    closure U ∩ O ⊆ U := by
  obtain ⟨x, -, rfl⟩ := hU
  exact closure_connectedComponentIn_inter_subset O x

/-- A preconnected subset of `O` that meets a component of `O` lies in that component. -/
theorem subset_of_mem_connectedComponentsIn_of_nonempty_inter {P : Set α} (hU : U ∈ connectedComponentsIn O)
    (hP : IsPreconnected P) (hPO : P ⊆ O) (hPU : (P ∩ U).Nonempty) : P ⊆ U := by
  obtain ⟨x, -, rfl⟩ := hU
  obtain ⟨w, hwP, hwU⟩ := hPU
  rw [connectedComponentIn_eq hwU]
  exact hP.subset_connectedComponentIn hwP hPO

/-- **Local sides.** Let `U` be a component of `O` with `e ∈ closure U`, and let `B` be a neighbourhood of `e` such
that `B ∩ O` is covered by two preconnected subsets `P₁, P₂` of `O`. Then `U` contains `P₁` or `P₂`. -/
theorem subset_or_subset_of_mem_closure_of_mem_connectedComponentsIn {P₁ P₂ B : Set α} {e : α}
    (hU : U ∈ connectedComponentsIn O) (heU : e ∈ closure U) (hB : B ∈ 𝓝 e) (hP₁ : IsPreconnected P₁)
    (hP₂ : IsPreconnected P₂) (hPO : P₁ ∪ P₂ ⊆ O) (hBO : B ∩ O ⊆ P₁ ∪ P₂) : P₁ ⊆ U ∨ P₂ ⊆ U := by
  obtain ⟨w, hwB, hwU⟩ := mem_closure_iff_nhds.1 heU B hB
  rcases hBO ⟨hwB, subset_of_mem_connectedComponentsIn hU hwU⟩ with hw | hw
  · exact Or.inl (subset_of_mem_connectedComponentsIn_of_nonempty_inter hU hP₁
      (subset_union_left.trans hPO) ⟨w, hw, hwU⟩)
  · exact Or.inr (subset_of_mem_connectedComponentsIn_of_nonempty_inter hU hP₂
      (subset_union_right.trans hPO) ⟨w, hw, hwU⟩)

/-- Under the hypotheses of `subset_or_subset_of_mem_closure_of_mem_connectedComponentsIn`, with `p ∈ P₁` and
`q ∈ P₂`, the component `U` is the component of `p` or the component of `q`. -/
theorem eq_or_eq_of_mem_closure_of_mem_connectedComponentsIn {P₁ P₂ B : Set α} {e p q : α}
    (hU : U ∈ connectedComponentsIn O) (heU : e ∈ closure U) (hB : B ∈ 𝓝 e) (hP₁ : IsPreconnected P₁)
    (hP₂ : IsPreconnected P₂) (hPO : P₁ ∪ P₂ ⊆ O) (hBO : B ∩ O ⊆ P₁ ∪ P₂) (hp : p ∈ P₁) (hq : q ∈ P₂) :
    U = connectedComponentIn O p ∨ U = connectedComponentIn O q := by
  rcases subset_or_subset_of_mem_closure_of_mem_connectedComponentsIn hU heU hB hP₁ hP₂ hPO hBO with h | h
  · obtain ⟨x, -, rfl⟩ := hU
    exact Or.inl (connectedComponentIn_eq (h hp))
  · obtain ⟨x, -, rfl⟩ := hU
    exact Or.inr (connectedComponentIn_eq (h hq))

end General

section Arc

variable {C : Set ℂ} {f : ℝ → ℂ}

/-- **Every side of a crosscut abuts on the whole crosscut.** Let `C ⊆ ℂ` be open and connected, and `f` continuous
on `[0,1]` with `f((0,1)) ⊆ C` and `f 0, f 1 ∉ C`. Suppose every point `y ∈ f((0,1))` has a ball `B ⊆ C` with
`B \ f([0,1]) = P₁ ∪ P₂`, `P₁, P₂` preconnected and `f([0,1]) ∩ B ⊆ closure P₁ ∩ closure P₂`. Then the closure of
every component of `C \ f([0,1])` contains `f((0,1))`. -/
theorem mem_closure_of_mem_connectedComponentsIn_diff_arc (hC : IsOpen C) (hCc : IsPreconnected C)
    (hf : ContinuousOn f (Icc 0 1)) (hγC : f '' Ioo 0 1 ⊆ C) (h0 : f 0 ∉ C) (h1 : f 1 ∉ C)
    (hloc : ∀ y ∈ f '' Ioo 0 1, ∃ r > 0, ball y r ⊆ C ∧ ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧
      IsPreconnected P₂ ∧ ball y r \ f '' Icc 0 1 = P₁ ∪ P₂ ∧
      f '' Icc 0 1 ∩ ball y r ⊆ closure P₁ ∩ closure P₂)
    {U : Set ℂ} (hU : U ∈ connectedComponentsIn (C \ f '' Icc 0 1)) : f '' Ioo 0 1 ⊆ closure U := by
  set γ := f '' Icc 0 1 with hγ
  have hγo : f '' Ioo 0 1 ⊆ γ := fun _ ⟨t, ht, hty⟩ => ⟨t, Ioo_subset_Icc_self ht, hty⟩
  have hγc : IsClosed γ := (isCompact_Icc.image_of_continuousOn hf).isClosed
  have hO : IsOpen (C \ γ) := hC.sdiff hγc
  have hUO : U ⊆ C \ γ := subset_of_mem_connectedComponentsIn hU
  have hUo : IsOpen U := by
    obtain ⟨x, -, rfl⟩ := hU
    exact hO.connectedComponentIn
  -- near a point of `γ°` in `closure U`, all of `γ` lies in `closure U`
  have hstep : ∀ y ∈ f '' Ioo 0 1, y ∈ closure U → ∃ ε > 0, γ ∩ ball y ε ⊆ closure U := by
    intro y hy hyU
    obtain ⟨r, hr, hrC, P₁, P₂, hP₁, hP₂, hsplit, hcl⟩ := hloc y hy
    have hPO : P₁ ∪ P₂ ⊆ C \ γ := by rw [← hsplit]; exact sdiff_subset_sdiff_left hrC
    have hBO : ball y r ∩ (C \ γ) ⊆ P₁ ∪ P₂ := by rw [← hsplit]; exact fun z hz => ⟨hz.1, hz.2.2⟩
    refine ⟨r, hr, fun z hz => ?_⟩
    rcases subset_or_subset_of_mem_closure_of_mem_connectedComponentsIn hU hyU (ball_mem_nhds y hr) hP₁ hP₂
      hPO hBO with h | h
    · exact closure_mono h (hcl hz).1
    · exact closure_mono h (hcl hz).2
  -- the points near which `γ` lies in `closure U` form an open set
  let u : Set ℂ := {z | ∃ ε > 0, γ ∩ ball z ε ⊆ closure U}
  have hu : IsOpen u := by
    rw [Metric.isOpen_iff]
    rintro z ⟨ε, hε, hz⟩
    refine ⟨ε / 2, half_pos hε, fun z' hz' => ?_⟩
    refine ⟨ε / 2, half_pos hε, fun w hw => hz ⟨hw.1, ball_subset_ball' ?_ hw.2⟩⟩
    rw [mem_ball] at hz'
    linarith
  have hγp : IsPreconnected (f '' Ioo 0 1) := isPreconnected_Ioo.image f (hf.mono Ioo_subset_Icc_self)
  have hcover : f '' Ioo 0 1 ⊆ u ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hyU : y ∈ closure U
    · exact Or.inl (hstep y hy hyU)
    · exact Or.inr hyU
  have hdisj : f '' Ioo 0 1 ∩ (u ∩ (closure U)ᶜ) = ∅ := by
    refine eq_empty_of_subset_empty ?_
    rintro y ⟨hy, ⟨ε, hε, hsub⟩, hyU⟩
    exact hyU (hsub ⟨hγo hy, mem_ball_self hε⟩)
  rcases isPreconnected_iff_subset_of_disjoint.1 hγp u (closure U)ᶜ hu isClosed_closure.isOpen_compl hcover
    hdisj with h | h
  · intro y hy
    obtain ⟨ε, hε, hsub⟩ := h hy
    exact hsub ⟨hγo hy, mem_ball_self hε⟩
  · -- otherwise `U` would be relatively clopen in `C`
    exfalso
    have hcl : closure U ∩ C ⊆ U := by
      rintro x ⟨hxU, hxC⟩
      refine closure_inter_subset_of_mem_connectedComponentsIn hU ⟨hxU, hxC, ?_⟩
      rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      rcases eq_or_lt_of_le ht0 with rfl | ht0
      · exact h0 hxC
      rcases eq_or_lt_of_le ht1 with rfl | ht1
      · exact h1 hxC
      exact h ⟨t, ⟨ht0, ht1⟩, rfl⟩ hxU
    obtain ⟨x₀, hx₀, hUx⟩ := hU
    have hUne : (C ∩ U).Nonempty := ⟨x₀, hx₀.1, hUx ▸ mem_connectedComponentIn hx₀⟩
    have hCU := hCc.subset_of_closure_inter_subset hUo hUne hcl
    have hmid : f (1 / 2) ∈ f '' Ioo 0 1 := ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    exact (hUO (hCU (hγC hmid))).2 (hγo hmid)

/-- **A crosscut has at most two sides.** Under the hypotheses of
`mem_closure_of_mem_connectedComponentsIn_diff_arc`, `C \ f([0,1])` has finitely many components: each is the
component of a point of one of the two local sides at `f (1/2)`. -/
theorem finite_connectedComponentsIn_diff_arc (hC : IsOpen C) (hCc : IsPreconnected C)
    (hf : ContinuousOn f (Icc 0 1)) (hγC : f '' Ioo 0 1 ⊆ C) (h0 : f 0 ∉ C) (h1 : f 1 ∉ C)
    (hloc : ∀ y ∈ f '' Ioo 0 1, ∃ r > 0, ball y r ⊆ C ∧ ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧
      IsPreconnected P₂ ∧ ball y r \ f '' Icc 0 1 = P₁ ∪ P₂ ∧
      f '' Icc 0 1 ∩ ball y r ⊆ closure P₁ ∩ closure P₂) :
    (connectedComponentsIn (C \ f '' Icc 0 1)).Finite := by
  have hmid : f (1 / 2) ∈ f '' Ioo 0 1 := ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  obtain ⟨r, hr, hrC, P₁, P₂, hP₁, hP₂, hsplit, hcl⟩ := hloc _ hmid
  have he : f (1 / 2) ∈ f '' Icc 0 1 ∩ ball (f (1 / 2)) r :=
    ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩, mem_ball_self hr⟩
  obtain ⟨p, hp⟩ := closure_nonempty_iff.1 ⟨_, (hcl he).1⟩
  obtain ⟨q, hq⟩ := closure_nonempty_iff.1 ⟨_, (hcl he).2⟩
  have hPO : P₁ ∪ P₂ ⊆ C \ f '' Icc 0 1 := by rw [← hsplit]; exact sdiff_subset_sdiff_left hrC
  have hBO : ball (f (1 / 2)) r ∩ (C \ f '' Icc 0 1) ⊆ P₁ ∪ P₂ := by
    rw [← hsplit]; exact fun z hz => ⟨hz.1, hz.2.2⟩
  refine ((finite_singleton (connectedComponentIn (C \ f '' Icc 0 1) q)).insert
    (connectedComponentIn (C \ f '' Icc 0 1) p)).subset ?_
  intro U hU
  exact eq_or_eq_of_mem_closure_of_mem_connectedComponentsIn hU
    (mem_closure_of_mem_connectedComponentsIn_diff_arc hC hCc hf hγC h0 h1 hloc hU hmid)
    (ball_mem_nhds _ hr) hP₁ hP₂ hPO hBO hp hq

end Arc

end LatticeProb.Topology
