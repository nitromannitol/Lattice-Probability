/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.ArcDisconnectMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.ArcDisconnect

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 3.7, topological step: proof

See `LQGMetric.Topo.ArcDisconnect` for the statement's source (arXiv:1905.00381,
`confluence-final.tex` lines 1467–1468) and the outline of this own argument.
-/

namespace LQGMetric

open Set Metric

/-- Rerouting: if a convex bounded open `U ∋ c` has closure disjoint from `K` and contains `Y`,
and `y` lies outside `closure U`, then an admissible path from `y` to `x ∈ K` can be replaced by
one avoiding `Y` (along the level set `{G = 1}` of the gauge of `U`). -/
theorem exists_path_avoiding {K Y U : Set ℂ} {c : ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUb : Bornology.IsBounded U) (hcU : c ∈ U) (hYU : Y ⊆ U) (hUK : Disjoint (closure U) K)
    {y x : ℂ} (γ : Path y x) (hy : y ∉ closure U) (hxK : x ∈ K)
    (hK : range γ ∩ K ⊆ {x}) (hγY : (range γ ∩ Y).Nonempty) :
    ∃ γ' : Path y x, range γ' ∩ K ⊆ {x} ∧ range γ' ∩ Y = ∅ := by
  set G := ConvexLevel.G U c with hGdef
  have hGc : Continuous G := ConvexLevel.continuous_G hUo hUc hcU
  have hG1 : ∀ z, G z ≤ 1 → z ∈ closure U := fun z hz =>
    ConvexLevel.mem_closure_of_G_le_one hUo hUc hcU hz
  have hGY : ∀ z ∈ Y, G z < 1 := fun z hz =>
    (ConvexLevel.G_lt_one_iff hUo hUc hcU z).2 (hYU hz)
  have hGK : ∀ z ∈ K, 1 < G z := fun z hz =>
    lt_of_not_ge fun h => Set.disjoint_left.1 hUK (hG1 z h) hz
  have hGy : 1 < G y := lt_of_not_ge fun h => hy (hG1 y h)
  have hGx : 1 < G x := hGK x hxK
  obtain ⟨z₀, ⟨τ₀, hτ₀⟩, hz₀Y⟩ := hγY
  set f : ℝ → ℝ := fun t => G (γ.extend t) with hf
  have hfc : Continuous f := hGc.comp γ.continuous_extend
  have hf0 : 1 < f 0 := by simpa [hf] using hGy
  have hf1 : 1 < f 1 := by simpa [hf] using hGx
  set T := Icc (0 : ℝ) 1 ∩ f ⁻¹' Iic 1 with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_Iic.preimage hfc)
  have hτ₀T : (τ₀ : ℝ) ∈ T := by
    refine ⟨τ₀.2, ?_⟩
    show G (γ.extend τ₀) ≤ 1
    rw [γ.extend_extends' τ₀, hτ₀]; exact (hGY _ hz₀Y).le
  have hTne : T.Nonempty := ⟨_, hτ₀T⟩
  have hTb : BddBelow T := ⟨0, fun u hu => hu.1.1⟩
  have hTa : BddAbove T := ⟨1, fun u hu => hu.1.2⟩
  set τ₁ := sInf T
  set τ₂ := sSup T
  have hτ₁ : τ₁ ∈ T := hTc.csInf_mem hTne hTb
  have hτ₂ : τ₂ ∈ T := hTc.csSup_mem hTne hTa
  have h12 : τ₁ ≤ τ₂ := csInf_le hTb hτ₂
  have hbefore : ∀ t ∈ Icc (0 : ℝ) τ₁, 1 ≤ f t := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have : τ₁ ≤ t := csInf_le hTb ⟨⟨ht.1, ht.2.trans hτ₁.1.2⟩, hlt.le⟩
    have htτ : t = τ₁ := le_antisymm ht.2 this
    -- `f τ₁ < 1`: an earlier time with `f = 1`
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc' hτ₁.1.1 hfc.continuousOn
      ⟨(htτ ▸ hlt).le, hf0.le⟩
    have : τ₁ ≤ v := csInf_le hTb ⟨⟨hv.1, hv.2.trans hτ₁.1.2⟩, hfv.le⟩
    have hvτ : v = τ₁ := le_antisymm hv.2 this
    rw [hvτ, ← htτ] at hfv; linarith
  have hafter : ∀ t ∈ Icc τ₂ 1, 1 ≤ f t := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have : t ≤ τ₂ := le_csSup hTa ⟨⟨hτ₂.1.1.trans ht.1, ht.2⟩, hlt.le⟩
    have htτ : t = τ₂ := le_antisymm this ht.1
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hτ₂.1.2 hfc.continuousOn
      ⟨(htτ ▸ hlt).le, hf1.le⟩
    have : v ≤ τ₂ := le_csSup hTa ⟨⟨hτ₂.1.1.trans hv.1, hv.2⟩, hfv.le⟩
    have hvτ : v = τ₂ := le_antisymm this hv.1
    rw [hvτ, ← htτ] at hfv; linarith
  have hfτ₁ : f τ₁ = 1 := le_antisymm hτ₁.2 (hbefore τ₁ ⟨hτ₁.1.1, le_rfl⟩)
  have hfτ₂ : f τ₂ = 1 := le_antisymm hτ₂.2 (hafter τ₂ ⟨le_rfl, hτ₂.1.2⟩)
  have hJ : JoinedIn {z | G z = 1} (γ.extend τ₁) (γ.extend τ₂) :=
    (ConvexLevel.isPathConnected_level hUo hUc hUb hcU).joinedIn _ hfτ₁ _ hfτ₂
  let p₁ := pathOfIcc γ.extend hτ₁.1.1 γ.continuous_extend.continuousOn
  let p₃ := pathOfIcc γ.extend hτ₂.1.2 γ.continuous_extend.continuousOn
  let γ' : Path y x :=
    ((p₁.trans hJ.somePath).trans p₃).cast γ.extend_zero.symm γ.extend_one.symm
  have hrange : range γ' = (range p₁ ∪ range hJ.somePath) ∪ range p₃ := by
    simp only [γ', Path.cast_coe, Path.trans_range]
  have hrγ : ∀ {a b : ℝ} (hab : a ≤ b),
      range (pathOfIcc γ.extend hab γ.continuous_extend.continuousOn) ⊆ range γ := by
    intro a b hab z hz
    obtain ⟨u, -, rfl⟩ := range_pathOfIcc_subset _ hab _ hz
    rw [← γ.extend_range]; exact mem_range_self u
  refine ⟨γ', ?_, ?_⟩
  · rintro z ⟨hz, hzK⟩
    rw [hrange] at hz
    rcases hz with (hz | hz) | hz
    · exact hK ⟨hrγ _ hz, hzK⟩
    · obtain ⟨t, rfl⟩ := hz
      have : G (hJ.somePath t) = 1 := hJ.somePath_mem t
      linarith [hGK _ hzK]
    · exact hK ⟨hrγ _ hz, hzK⟩
  · rw [eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzY⟩
    have hGz := hGY z hzY
    rw [hrange] at hz
    rcases hz with (hz | hz) | hz
    · obtain ⟨u, hu, rfl⟩ := range_pathOfIcc_subset _ _ _ hz
      linarith [hbefore u hu]
    · obtain ⟨t, rfl⟩ := hz
      have : G (hJ.somePath t) = 1 := hJ.somePath_mem t
      linarith
    · obtain ⟨u, hu, rfl⟩ := range_pathOfIcc_subset _ _ _ hz
      linarith [hafter u hu]

/-- **CONF Lemma 3.7, topological step** (arXiv:1905.00381, tex 1467–1468): if a bounded set
`Y` with `diam Y ≤ d` disconnects `I ⊆ ∂K` from `∞` in `ℂ \ K` (`K` closed), then so does
`closedBall x d` for some `x ∈ ∂K`. -/
theorem exists_frontier_closedBall_disconnects {K Y I : Set ℂ} (hK : IsClosed K)
    (hI : I ⊆ frontier K) (hIne : I.Nonempty) (hYb : Bornology.IsBounded Y) {d : ℝ}
    (hd : diam Y ≤ d) (hY : DisconnectsFromInfty K Y I) :
    ∃ x ∈ frontier K, DisconnectsFromInfty K (closedBall x d) I := by
  obtain ⟨x₀, hx₀⟩ := hIne
  have vac : (∃ R' : ℝ, ∀ (y x : ℂ) (γ : Path y x), R' < ‖y‖ → x ∈ I →
      range γ ∩ K ⊆ {x} → False) → ∃ x ∈ frontier K, DisconnectsFromInfty K (closedBall x d) I :=
    fun ⟨R', h⟩ => ⟨x₀, hI hx₀, R', fun y x γ hy hx hK => (h y x γ hy hx hK).elim⟩
  rcases Y.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · obtain ⟨R, hR⟩ := hY
    exact vac ⟨R, fun y x γ hy hx hK => by simpa using hR y x γ hy hx hK⟩
  set W : Set ℂ := ⋂ y ∈ Y, closedBall y d with hW
  have hYW : Y ⊆ W := fun z hz => mem_iInter₂.2 fun y hy =>
    mem_closedBall.2 ((dist_le_diam_of_mem hYb hz hy).trans hd)
  by_cases hA : ∃ x ∈ frontier K, x ∈ W
  · obtain ⟨x, hxF, hxW⟩ := hA
    refine ⟨x, hxF, hY.mono fun y hy => ?_⟩
    have := mem_iInter₂.1 hxW y hy
    rw [mem_closedBall, dist_comm] at this
    exact this
  push Not at hA
  have hWconv : Convex ℝ W := convex_iInter₂ fun y _ => convex_closedBall y d
  have hWcl : IsClosed W := isClosed_biInter fun y _ => isClosed_closedBall
  have hWb : Bornology.IsBounded W := isBounded_closedBall.subset (biInter_subset_of_mem hy₀)
  have hWc : IsCompact W := isCompact_of_isClosed_isBounded hWcl hWb
  by_cases hB : (W ∩ K).Nonempty
  · have hsub : W ⊆ interior K ∪ (closure K)ᶜ := by
      intro z hz
      by_cases h : z ∈ closure K
      · left; by_contra h'; exact hA z ⟨h, h'⟩ hz
      · exact Or.inr h
    rcases hWconv.isPreconnected.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset_closure) hsub with h | h
    · obtain ⟨R, hR⟩ := hY
      refine vac ⟨R, fun y x γ hy hx hK => ?_⟩
      obtain ⟨z, hzγ, hzY⟩ := hR y x γ hy hx hK
      have hzint := h (hYW hzY)
      have hzx : z = x := hK ⟨hzγ, interior_subset hzint⟩
      exact (hI hx).2 (hzx ▸ hzint)
    · obtain ⟨z, hzW, hzK⟩ := hB
      exact (h hzW (subset_closure hzK)).elim
  · rw [not_nonempty_iff_eq_empty] at hB
    have hWK : W ⊆ Kᶜ := fun z hz hzK => (eq_empty_iff_forall_notMem.1 hB) z ⟨hz, hzK⟩
    obtain ⟨δ, hδ, hδK⟩ := hWc.exists_cthickening_subset_open hK.isOpen_compl hWK
    set U := thickening δ W with hU
    have hUK : Disjoint (closure U) K := by
      rw [Set.disjoint_left]
      intro z hz hzK
      exact hδK (closure_thickening_subset_cthickening δ W hz) hzK
    have hWU : W ⊆ U := self_subset_thickening hδ W
    obtain ⟨ρ, hρ⟩ := isBounded_iff_forall_norm_le.1 (hWb.thickening (δ := δ)).closure
    obtain ⟨R, hR⟩ := hY
    refine vac ⟨max R ρ, fun y x γ hy hx hKγ => ?_⟩
    have hyU : y ∉ closure U := fun h => by
      have := hρ y h
      linarith [le_max_right R ρ]
    have hxK : x ∈ K := hK.closure_eq ▸ (hI hx).1
    have hγY := hR y x γ (lt_of_le_of_lt (le_max_left _ _) hy) hx hKγ
    obtain ⟨γ', hγ'K, hγ'Y⟩ := exists_path_avoiding isOpen_thickening (hWconv.thickening δ)
      hWb.thickening (hWU (hYW hy₀)) (hYW.trans hWU) hUK γ hyU hxK hKγ hγY
    have := hR y x γ' (lt_of_le_of_lt (le_max_left _ _) hy) hx hγ'K
    rw [hγ'Y] at this
    exact this.ne_empty rfl

end LQGMetric
