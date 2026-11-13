/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.PolarSets at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.AroundLoop

 








set_option autoImplicit false

noncomputable section

open Set Metric Complex

namespace SupercriticalLQGUniqueness.B2.Strong

theorem continuous_expChart (c : ℂ) : Continuous (expChart c) := by
  unfold expChart; fun_prop

theorem expChart_injOn (c : ℂ) {S : Set ℂ}
    (hS : ∀ w ∈ S, ∀ w' ∈ S, |w.im - w'.im| < 2 * Real.pi) : InjOn (expChart c) S := by
  intro w hw w' hw' h
  have h' : Complex.exp w = Complex.exp w' := add_left_cancel h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h'
  have him : w.im - w'.im = 2 * Real.pi * n := by
    rw [hn]; simp; ring
  have hlt := hS w hw w' hw'
  rw [him, abs_mul, abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi)] at hlt
  have hn1 : |(n : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith [Real.pi_pos]
  have : n = 0 := by
    rw [← Int.cast_abs] at hn1
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast hn1)
  rw [hn, this]; simp

theorem isOpen_openSet (B : Box) : IsOpen B.openSet := by
  have h : B.openSet = re ⁻¹' Ioo B.x₀ B.x₁ ∩ im ⁻¹' Ioo B.y₀ B.y₁ := by
    ext w; simp [Box.openSet, and_assoc]
  rw [h]
  exact (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)

theorem convex_openSet (B : Box) : Convex ℝ B.openSet := by
  have h : B.openSet = reLm ⁻¹' Ioo B.x₀ B.x₁ ∩ imLm ⁻¹' Ioo B.y₀ B.y₁ := by
    ext w; simp [Box.openSet, and_assoc]
  rw [h]
  exact ((convex_Ioo _ _).linear_preimage reLm).inter ((convex_Ioo _ _).linear_preimage imLm)

theorem isOpen_polarOpen (c : ℂ) (B : Box) : IsOpen (polarOpen c B) := by
  have : polarOpen c B = (fun z => c + z) '' (Complex.exp '' B.openSet) := by
    rw [polarOpen, image_image]; rfl
  rw [this]
  exact (Homeomorph.addLeft c).isOpenMap _ (isOpenMap_exp _ (isOpen_openSet B))

theorem isConnected_polarOpen (c : ℂ) (B : Box) (hx : B.x₀ < B.x₁) (hy : B.y₀ < B.y₁) :
    IsConnected (polarOpen c B) := by
  have hne : B.openSet.Nonempty :=
    ⟨⟨(B.x₀ + B.x₁) / 2, (B.y₀ + B.y₁) / 2⟩,
      ⟨show B.x₀ < (B.x₀ + B.x₁) / 2 by linarith, show (B.x₀ + B.x₁) / 2 < B.x₁ by linarith,
        show B.y₀ < (B.y₀ + B.y₁) / 2 by linarith, show (B.y₀ + B.y₁) / 2 < B.y₁ by linarith⟩⟩
  exact ((convex_openSet B).isConnected hne).image _ (continuous_expChart c).continuousOn

theorem isCompact_polarClosed (c : ℂ) (B : Box) : IsCompact (polarClosed c B) :=
  LQGMetric.Sector.isCompact_rect.image (continuous_expChart c)

theorem isConnected_polarClosed (c : ℂ) (B : Box) (hx : B.x₀ ≤ B.x₁) (hy : B.y₀ ≤ B.y₁) :
    IsConnected (polarClosed c B) := by
  have hne : B.closedSet.Nonempty := ⟨⟨B.x₀, B.y₀⟩, ⟨⟨le_rfl, hx⟩, ⟨le_rfl, hy⟩⟩⟩
  exact (LQGMetric.Sector.convex_rect.isConnected hne).image _
    (continuous_expChart c).continuousOn

theorem polarClosed_subset (c : ℂ) {K U : Box} (h : K.closedSet ⊆ U.openSet) :
    polarClosed c K ⊆ polarOpen c U :=
  image_mono h

 
theorem injOn_openSet (c : ℂ) (U : Box) (h : U.y₁ - U.y₀ < 2 * Real.pi) :
    InjOn (expChart c) U.openSet := by
  refine expChart_injOn c fun w hw w' hw' => abs_sub_lt_iff.2 ⟨?_, ?_⟩
  · linarith [hw.2.2.2, hw'.2.2.1]
  · linarith [hw.2.2.1, hw'.2.2.2]

theorem cfgU_height (L Δ : ℝ) (k : Fin 4) :
    (cfgU L Δ k).y₁ - (cfgU L Δ k).y₀ < 2 * Real.pi := by
  have := Real.pi_pos
  fin_cases k <;> simp [cfgU, boxR, boxA, wd] <;> linarith

theorem cfgU_nondeg (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    (cfgU L Δ k).x₀ < (cfgU L Δ k).x₁ ∧ (cfgU L Δ k).y₀ < (cfgU L Δ k).y₁ := by
  have := Real.pi_pos
  fin_cases k <;> refine ⟨?_, ?_⟩ <;> simp [cfgU, boxR, boxA, wd] <;> linarith

theorem cfgK₁_le (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    (cfgK₁ L Δ k).x₀ ≤ (cfgK₁ L Δ k).x₁ ∧ (cfgK₁ L Δ k).y₀ ≤ (cfgK₁ L Δ k).y₁ := by
  have := Real.pi_pos
  fin_cases k <;> refine ⟨?_, ?_⟩ <;> simp [cfgK₁, segR, segA, wd] <;> linarith

theorem cfgK₂_le (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    (cfgK₂ L Δ k).x₀ ≤ (cfgK₂ L Δ k).x₁ ∧ (cfgK₂ L Δ k).y₀ ≤ (cfgK₂ L Δ k).y₁ := by
  have := Real.pi_pos
  fin_cases k <;> refine ⟨?_, ?_⟩ <;> simp [cfgK₂, segR, segA, wd] <;> linarith

 
theorem nontrivial_polarClosed (c : ℂ) {K U : Box} (hKU : K.closedSet ⊆ U.openSet)
    (hU : U.y₁ - U.y₀ < 2 * Real.pi) (hK : K.x₀ ≤ K.x₁ ∧ K.y₀ ≤ K.y₁)
    (hne : K.x₀ < K.x₁ ∨ K.y₀ < K.y₁) : (polarClosed c K).Nontrivial := by
  have p₀ : (⟨K.x₀, K.y₀⟩ : ℂ) ∈ K.closedSet := ⟨⟨le_rfl, hK.1⟩, ⟨le_rfl, hK.2⟩⟩
  have p₁ : (⟨K.x₁, K.y₁⟩ : ℂ) ∈ K.closedSet := ⟨⟨hK.1, le_rfl⟩, ⟨hK.2, le_rfl⟩⟩
  refine ⟨_, mem_image_of_mem _ p₀, _, mem_image_of_mem _ p₁, fun h => ?_⟩
  have := injOn_openSet c U hU (hKU p₀) (hKU p₁) h
  rcases hne with h' | h'
  · have := congrArg Complex.re this; simp at this; linarith
  · have := congrArg Complex.im this; simp at this; linarith

theorem cfgK_nondeg (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    ((cfgK₁ L Δ k).x₀ < (cfgK₁ L Δ k).x₁ ∨ (cfgK₁ L Δ k).y₀ < (cfgK₁ L Δ k).y₁) ∧
      ((cfgK₂ L Δ k).x₀ < (cfgK₂ L Δ k).x₁ ∨ (cfgK₂ L Δ k).y₀ < (cfgK₂ L Δ k).y₁) := by
  have := wd_pos
  fin_cases k <;> simp [cfgK₁, cfgK₂, segR, segA, hΔ, this] <;> linarith

theorem cfgK_disjoint (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    Disjoint (cfgK₁ L Δ k).closedSet (cfgK₂ L Δ k).closedSet := by
  have := wd_pos
  have h8 : 8 * wd = Real.pi := by unfold wd; ring
  rw [Set.disjoint_left]
  rintro w ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨e, f⟩, ⟨g, h⟩⟩
  fin_cases k <;> simp [cfgK₁, cfgK₂, segR, segA] at a b c d e f g h <;> linarith

 
theorem axiomV_data (c : ℂ) (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    IsOpen (polarOpen c (cfgU L Δ k)) ∧ IsConnected (polarOpen c (cfgU L Δ k)) ∧
      IsCompact (polarClosed c (cfgK₁ L Δ k)) ∧ IsCompact (polarClosed c (cfgK₂ L Δ k)) ∧
      IsConnected (polarClosed c (cfgK₁ L Δ k)) ∧ IsConnected (polarClosed c (cfgK₂ L Δ k)) ∧
      (polarClosed c (cfgK₁ L Δ k)).Nontrivial ∧ (polarClosed c (cfgK₂ L Δ k)).Nontrivial ∧
      polarClosed c (cfgK₁ L Δ k) ⊆ polarOpen c (cfgU L Δ k) ∧
      polarClosed c (cfgK₂ L Δ k) ⊆ polarOpen c (cfgU L Δ k) ∧
      Disjoint (polarClosed c (cfgK₁ L Δ k)) (polarClosed c (cfgK₂ L Δ k)) := by
  have h1 := cfgK₁_subset L Δ hΔ k
  have h2 := cfgK₂_subset L Δ hΔ k
  have hinj := injOn_openSet c _ (cfgU_height L Δ k)
  refine ⟨isOpen_polarOpen c _, isConnected_polarOpen c _ (cfgU_nondeg L Δ hΔ k).1
      (cfgU_nondeg L Δ hΔ k).2, isCompact_polarClosed c _, isCompact_polarClosed c _,
    isConnected_polarClosed c _ (cfgK₁_le L Δ hΔ k).1 (cfgK₁_le L Δ hΔ k).2,
    isConnected_polarClosed c _ (cfgK₂_le L Δ hΔ k).1 (cfgK₂_le L Δ hΔ k).2,
    nontrivial_polarClosed c h1 (cfgU_height L Δ k) (cfgK₁_le L Δ hΔ k)
      (cfgK_nondeg L Δ hΔ k).1,
    nontrivial_polarClosed c h2 (cfgU_height L Δ k) (cfgK₂_le L Δ hΔ k)
      (cfgK_nondeg L Δ hΔ k).2,
    polarClosed_subset c h1, polarClosed_subset c h2, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨w, hw, rfl⟩ ⟨w', hw', hzz⟩
  have := hinj (h2 hw') (h1 hw) hzz
  subst this
  exact Set.disjoint_left.1 (cfgK_disjoint L Δ hΔ k) hw hw'
