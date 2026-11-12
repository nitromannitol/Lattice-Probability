/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J3b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J2b
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Rational chain classes are the components of `Γ ∖ P_L` (DEC-120 §4, packet J3)

For a Jordan curve `Γ` and the cut set `P_L = t39jCut L Γ` (S3T39J2b):

* `t39j_rc_of_preconnected`: two points of a compact preconnected `K ⊆ Γ` avoiding `P_L` are
  related by `t39jRC` (ε-chains in `K`, `IsPreconnected.induction₂'`);
* **`t39j_rc_of_comp`**: `y ∈ connectedComponentIn (Γ ∖ P_L) x → t39jRC L Γ x y`
  (the arc of `t39j_jordan_split` without cut points);
* **`t39j_comp_of_rc`**: the converse (the component is relatively clopen in the compact set
  `{z ∈ Γ | dist(z, P_L) ≥ η/2}`, a chain cannot jump the positive gap);
* `t39j_rc_iff`, `t39j_class_eq`: `t39jClass L Γ x = connectedComponentIn (Γ ∖ P_L) x`.

CONF C:1740–1744 (DV-D120-1). Own elementary arguments (ε-chain description of the components of
`Γ ∖ P` for a Jordan curve), reusing `t39j_jordan_split`, `t39j_jordan_comp_nhds` (S3T39J3).
-/

noncomputable section

open Set Metric Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric.CONF

theorem t39j_jordan_isCompact {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) : IsCompact Γ := by
  obtain ⟨γ, hγc, -, rfl⟩ := hΓ; exact (isCompact_sphere 0 1).image_of_continuousOn hγc

theorem t39j_cut_finite (L : ℕ) (Γ : Set ℂ) : (t39jCut L Γ).Finite :=
  ((Set.finite_Iio L).image fun j => t39jPt j Γ).subset (by
    rintro p ⟨j, hj, -, rfl⟩; exact ⟨j, hj, rfl⟩)

theorem t39j_coe_lt_edist {r : ℝ≥0} {a b : ℂ} (h : (r : ℝ≥0∞) < edist a b) :
    (r : ℝ) < dist a b := by
  rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at h; exact h

/-- a rational point within `δ` of `z` -/
theorem t39j_rq_near (z : ℂ) {δ : ℝ} (hδ : 0 < δ) : ∃ w ∈ range t39jRq, dist z w < δ := by
  obtain ⟨j, -, hj⟩ := t39j_ball_basis z hδ
  have hc : t39jBc j ∈ ball z δ := hj (mem_closedBall_self (t39jBr_pos j).le)
  exact ⟨t39jBc j, ⟨((t39jPar j).1, (t39jPar j).2.1), rfl⟩, by rw [dist_comm]; exact hc⟩

/-- concatenation of rational chains -/
theorem t39jReach_append {L : ℕ} {η ε δ : ℝ} {Γ : Set ℂ} {w w' u : ℂ} {n : ℕ}
    (h1 : t39jReach L η ε δ Γ n w w') (hw' : t39jGood L η δ Γ w') (hu : t39jGood L η δ Γ u)
    (hd : dist w' u + 2 * δ < ε) :
    ∀ k u', t39jReach L η ε δ Γ k u u' → t39jReach L η ε δ Γ (n + 1 + k) w u'
  | 0, u', h => by
    have h' : u = u' := h
    subst h'; exact ⟨w', h1, hw', hu, hd⟩
  | k + 1, u', ⟨v, hv, hgv, hgu', hdv⟩ =>
    ⟨v, t39jReach_append h1 hw' hu hd k v hv, hgv, hgu', hdv⟩

/-- **points of a compact preconnected `K ⊆ Γ` avoiding the cut are chain-related** -/
theorem t39j_rc_of_preconnected {L : ℕ} {Γ K : Set ℂ} (hK : IsPreconnected K)
    (hKc : IsCompact K) (hKΓ : K ⊆ Γ) (hKP : Disjoint K (t39jCut L Γ)) {x y : ℂ} (hx : x ∈ K)
    (hy : y ∈ K) : t39jRC L Γ x y := by
  obtain ⟨r, hr, hrK⟩ := exists_pos_forall_lt_edist hKc (t39j_cut_finite L Γ).isClosed hKP
  have hr' : (0 : ℝ) < r := hr
  have hrK' : ∀ a ∈ K, ∀ p ∈ t39jCut L Γ, (r : ℝ) < dist a p := fun a ha p hp =>
    t39j_coe_lt_edist (hrK a ha p hp)
  obtain ⟨η, hη0, hηr⟩ := exists_rat_btwn (show (0 : ℝ) < r / 2 by positivity)
  refine ⟨η, by exact_mod_cast hη0, fun ε hε => ?_⟩
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (show (0 : ℝ) < min ((ε : ℝ) / 5) (((r : ℝ) - η) / 2) by
    refine lt_min (by positivity) ?_; linarith)
  have hδε : (δ : ℝ) < ε / 5 := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδr : (δ : ℝ) < ((r : ℝ) - η) / 2 := lt_of_lt_of_le hδ (min_le_right _ _)
  have hδ0' : (0 : ℝ) < δ := hδ0
  -- good rational points near points of `K`
  have hgood : ∀ a ∈ K, ∃ w, t39jGood L η δ Γ w ∧ dist a w < δ := by
    intro a ha
    obtain ⟨w, hwq, hw⟩ := t39j_rq_near a hδ0'
    refine ⟨w, ⟨hwq, ⟨a, hKΓ ha, mem_ball.2 hw⟩, fun p hp => ?_⟩, hw⟩
    have := hrK' a ha p hp
    linarith [dist_triangle a w p]
  let Pr : ℂ → ℂ → Prop := fun a b => ∃ w w' : ℂ, ∃ n : ℕ, t39jGood L η δ Γ w ∧
    t39jGood L η δ Γ w' ∧ dist a w < δ ∧ dist w' b < δ ∧ t39jReach L η ε δ Γ n w w'
  have hloc : ∀ a ∈ K, ∀ b ∈ K, dist a b < δ → Pr a b := by
    intro a ha b hb hab
    obtain ⟨w, hw, hwa⟩ := hgood a ha
    obtain ⟨w', hw', hwb⟩ := hgood b hb
    refine ⟨w, w', 1, hw, hw', hwa, by rw [dist_comm]; exact hwb, w, rfl, hw, hw', ?_⟩
    linarith [dist_triangle w a w', dist_triangle a b w', dist_comm a w]
  have hPr : Pr x y := by
    refine hK.induction₂' Pr (fun a ha => ?_) (fun a b c _ _ _ hab hbc => ?_) hx hy
    · filter_upwards [inter_mem_nhdsWithin K (ball_mem_nhds a hδ0'),
        self_mem_nhdsWithin] with b hb hbK
      have hab : dist b a < δ := hb.2
      exact ⟨hloc a ha b hbK (by rw [dist_comm]; exact hab), hloc b hbK a ha hab⟩
    · obtain ⟨w₁, w₁', n₁, hg₁, hg₁', h₁, h₁', hr₁⟩ := hab
      obtain ⟨w₂, w₂', n₂, hg₂, hg₂', h₂, h₂', hr₂⟩ := hbc
      exact ⟨w₁, w₂', n₁ + 1 + n₂, hg₁, hg₂', h₁, h₂', t39jReach_append hr₁ hg₁' hg₂
        (by linarith [dist_triangle w₁' b w₂]) n₂ w₂' hr₂⟩
  obtain ⟨w, w', n, hg, hg', h1, h2, hr⟩ := hPr
  exact ⟨δ, by exact_mod_cast hδ0, w, w', n, hg, hg', by linarith, by linarith, hr⟩

/-- **components are chain classes** -/
theorem t39j_rc_of_comp {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) {x y : ℂ}
    (hx : x ∈ Γ \ t39jCut L Γ) (hy : y ∈ connectedComponentIn (Γ \ t39jCut L Γ) x) :
    t39jRC L Γ x y := by
  have hyF := connectedComponentIn_subset _ _ hy
  by_cases hxy : x = y
  · subst hxy
    exact t39j_rc_of_preconnected isPreconnected_singleton isCompact_singleton
      (singleton_subset_iff.2 hx.1) (disjoint_singleton_left.2 hx.2) rfl rfl
  obtain ⟨A, B, hAc, hBc, hAp, hBp, hAB, hAiB, -, -, hsep⟩ :=
    t39j_jordan_split hΓ hx.1 hyF.1 hxy
  have hxA : x ∈ A ∩ B := by rw [hAiB]; exact Or.inl rfl
  have hyA : y ∈ A ∩ B := by rw [hAiB]; exact Or.inr rfl
  have hor : Disjoint A (t39jCut L Γ) ∨ Disjoint B (t39jCut L Γ) := by
    by_contra hc
    simp only [not_or, not_disjoint_iff] at hc
    obtain ⟨⟨a, haA, haP⟩, ⟨b, hbB, hbP⟩⟩ := hc
    have hnot : ∀ {p}, p ∈ t39jCut L Γ → p ∉ ({x, y} : Set ℂ) := by
      rintro p hp (rfl | rfl); exacts [hx.2 hp, hyF.2 hp]
    refine hsep a ⟨haA, hnot haP⟩ b ⟨hbB, hnot hbP⟩ _ isPreconnected_connectedComponentIn
      (fun z hz => ?_) (mem_connectedComponentIn hx) hy
    have hzF := connectedComponentIn_subset _ _ hz
    refine ⟨hzF.1, ?_⟩
    rintro (rfl | rfl); exacts [hzF.2 haP, hzF.2 hbP]
  rcases hor with h | h
  · exact t39j_rc_of_preconnected hAp hAc (hAB ▸ subset_union_left) h hxA.1 hyA.1
  · exact t39j_rc_of_preconnected hBp hBc (hAB ▸ subset_union_right) h hxA.2 hyA.2

/-- **chain classes are components** -/
theorem t39j_comp_of_rc {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) {x y : ℂ}
    (hx : x ∈ Γ \ t39jCut L Γ) (hy : y ∈ Γ \ t39jCut L Γ) (h : t39jRC L Γ x y) :
    y ∈ connectedComponentIn (Γ \ t39jCut L Γ) x := by
  set P := t39jCut L Γ with hP
  set C := connectedComponentIn (Γ \ P) x with hC
  have hΓc := t39j_jordan_isCompact hΓ
  obtain ⟨η, hη, H⟩ := h
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  set K' : Set ℂ := Γ ∩ ⋂ p ∈ P, {z | (η : ℝ) / 2 ≤ dist z p} with hK'
  have hK'c : IsClosed K' := hΓc.isClosed.inter (isClosed_biInter fun p _ =>
    isClosed_le continuous_const (continuous_id.dist continuous_const))
  have memK' : ∀ {z}, z ∈ Γ → (∀ p ∈ P, (η : ℝ) / 2 ≤ dist z p) → z ∈ K' := fun hz hp =>
    ⟨hz, mem_iInter₂.2 hp⟩
  have K'F : K' ⊆ Γ \ P := fun z hz => ⟨hz.1, fun hzP => by
    have := mem_iInter₂.1 hz.2 z hzP; rw [mem_ofPred_eq, dist_self] at this; linarith⟩
  have hCF : C ⊆ Γ \ P := connectedComponentIn_subset _ _
  -- `C ∩ K'` closed
  have hC1c : IsClosed (C ∩ K') := by
    refine isClosed_of_closure_subset fun z hz => ?_
    have hzK : z ∈ K' := closure_minimal inter_subset_right hK'c hz
    refine ⟨?_, hzK⟩
    have hzC : z ∈ closure C := closure_mono inter_subset_left hz
    have hpre : IsPreconnected (insert z C) := isPreconnected_connectedComponentIn.subset_closure
      (subset_insert _ _) (insert_subset hzC subset_closure)
    exact hpre.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hx))
      (insert_subset (K'F hzK) hCF) (mem_insert _ _)
  -- `K' ∖ C` closed (components are relatively open)
  have hC2c : IsClosed (K' \ C) := by
    refine isClosed_of_closure_subset fun z hz => ?_
    have hzK : z ∈ K' := closure_minimal sdiff_subset hK'c hz
    refine ⟨hzK, fun hzC => ?_⟩
    have hfin := t39j_cut_finite L Γ
    have hzF : z ∈ Γ \ ↑hfin.toFinset := by rw [hfin.coe_toFinset]; exact K'F hzK
    obtain ⟨δ, hδ, hδC⟩ := t39j_jordan_comp_nhds hΓ hfin.toFinset hzF
    rw [hfin.coe_toFinset, ← connectedComponentIn_eq hzC] at hδC
    obtain ⟨z', hz', hzz'⟩ := Metric.mem_closure_iff.1 hz δ hδ
    exact hz'.2 (hδC z' hz'.1.1 hzz')
  obtain ⟨r₀, hr₀, hr₀C⟩ := exists_pos_forall_lt_edist ((hΓc.of_isClosed_subset hC1c
    (inter_subset_right.trans inter_subset_left))) hC2c (by
      rw [Set.disjoint_left]; rintro z ⟨hzC, -⟩ ⟨-, hzC'⟩; exact hzC' hzC)
  have hr₀' : (0 : ℝ) < r₀ := hr₀
  have hsepC : ∀ a ∈ C ∩ K', ∀ b ∈ K', dist a b < r₀ → b ∈ C := by
    intro a ha b hb hab
    by_contra hbC
    have := t39j_coe_lt_edist (hr₀C a ha b ⟨hb, hbC⟩); linarith
  obtain ⟨ε, hε0, hε⟩ := exists_rat_btwn (show (0 : ℝ) < min (r₀ : ℝ) ((η : ℝ) / 2) by
    refine lt_min hr₀' (by positivity))
  have hεr : (ε : ℝ) < r₀ := lt_of_lt_of_le hε (min_le_left _ _)
  have hεη : (ε : ℝ) < η / 2 := lt_of_lt_of_le hε (min_le_right _ _)
  obtain ⟨δ, hδ0, w, w', n, hg, hg', h1, h2, hr⟩ := H ε (by exact_mod_cast hε0)
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  -- points near good points lie in `K'`
  have hnearK : ∀ {v z}, t39jGood L η δ Γ v → z ∈ Γ → dist z v < δ → z ∈ K' := by
    intro v z hv hz hzv
    refine memK' hz fun p hp => ?_
    have := hv.2.2 p hp
    linarith [dist_triangle v z p, dist_comm z v]
  have hxK : x ∈ K' := memK' hx.1 fun p hp => by
    have := hg.2.2 p hp; linarith [dist_triangle w x p, dist_comm x w]
  have hyK : y ∈ K' := memK' hy.1 fun p hp => by
    have := hg'.2.2 p hp; linarith [dist_triangle w' y p]
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have claim : ∀ k v, t39jReach L η ε δ Γ k w v → t39jGood L η δ Γ v →
      ∀ z ∈ Γ, dist z v < δ → z ∈ C := by
    intro k
    induction k with
    | zero =>
      intro v hv hgv z hz hzv
      have hv' : w = v := hv
      subst hv'
      exact hsepC x ⟨hxC, hxK⟩ z (hnearK hgv hz hzv)
        (by linarith [dist_triangle x w z, dist_comm z w])
    | succ k ih =>
      rintro v ⟨u, hu, hgu, -, hduv⟩ hgv z hz hzv
      obtain ⟨zu, hzuΓ, hzu⟩ := hgu.2.1
      have hzu' : dist zu u < δ := hzu
      have hzuC := ih u hu hgu zu hzuΓ hzu'
      exact hsepC zu ⟨hzuC, hnearK hgu hzuΓ hzu'⟩ z (hnearK hgv hz hzv)
        (by linarith [dist_triangle zu u z, dist_triangle u v z, dist_comm z v])
  obtain ⟨z', hz'Γ, hz'⟩ := hg'.2.1
  have hz'' : dist z' w' < δ := hz'
  have hz'C := claim n w' hr hg' z' hz'Γ hz''
  exact hsepC z' ⟨hz'C, hnearK hg' hz'Γ hz''⟩ y hyK (by linarith [dist_triangle z' w' y])

/-- **the chain class of `x` is its component in `Γ ∖ P_L`** -/
theorem t39j_class_eq {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) (L : ℕ) {x : ℂ}
    (hx : x ∈ Γ \ t39jCut L Γ) :
    t39jClass L Γ x = connectedComponentIn (Γ \ t39jCut L Γ) x := by
  have hcl : closure Γ = Γ := (t39j_jordan_isCompact hΓ).isClosed.closure_eq
  ext y
  constructor
  · rintro ⟨hyΓ, hyP, hrc⟩
    rw [hcl] at hyΓ
    exact t39j_comp_of_rc hΓ L hx ⟨hyΓ, hyP⟩ hrc
  · intro hy
    have hyF := connectedComponentIn_subset _ _ hy
    exact ⟨subset_closure hyF.1, hyF.2, t39j_rc_of_comp hΓ L hx hy⟩

end LQGMetric.CONF
