/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.SectorMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.SectorPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The sector lemma `GMSector` (last open node of J1b)

Miller–Sheffield arXiv:1506.03806, proof of Prop. 2.1 (`mapmaking_final.tex` l. 582, "it is not
hard to see"): three pairwise disjoint continua `K₁, K₂, K₃` crossing the closed annulus
`{r₁ ≤ |y − x| ≤ r₂}` are not all touched by the closure of one connected subset `W` of the open
annulus avoiding them.

Proof (own write-up of the classical argument, DEVIATIONS proposed). Suppose `kᵢ ∈ cl W ∩ Kᵢ`.
Work in log coordinates `E w = x + e^w`. Each `Kᵢ` carries a continuous logarithm `ℓᵢ` of
`y − x` (`hasLog_crossing`). Spurs `[ωᵢ, κᵢ]` join points `E ωᵢ ∈ W` to lifts `κᵢ` of `kᵢ`
avoiding the other two continua (`exists_spur`); paths in the component `U ⊇ W` of the open
annulus minus `K₁ ∪ K₂ ∪ K₃` from `E ω₁` to `E ω₂`, `E ω₃` are lifted from `ω₁`
(`exists_lift_path`), ending at `ω₂ + c₂`, `ω₃ + c₃`. With the lifts `Lᵢ = ℓᵢ(Kᵢ) + dᵢ` through
`κ₁`, `κ₂ + c₂`, `κ₃ + c₃` — three pairwise disjoint crossers of a rectangle
`[log r₁, log r₂] × [−R, R]` — the lifted spurs and paths give connected sets `Nᵢ` avoiding `Lᵢ`
and containing the other two lifts, contradicting `three_crossers_rect`.
-/

namespace LQGMetric

namespace Sector

open Set Metric RectCross

theorem chain5 {S₁ S₂ S₃ S₄ S₅ : Set ℂ} (h₁ : IsPreconnected S₁) (h₂ : IsPreconnected S₂)
    (h₃ : IsPreconnected S₃) (h₄ : IsPreconnected S₄) (h₅ : IsPreconnected S₅)
    {p₁ p₂ p₃ p₄ : ℂ} (hp₁ : p₁ ∈ S₁) (hp₁' : p₁ ∈ S₂) (hp₂ : p₂ ∈ S₂) (hp₂' : p₂ ∈ S₃)
    (hp₃ : p₃ ∈ S₃) (hp₃' : p₃ ∈ S₄) (hp₄ : p₄ ∈ S₄) (hp₄' : p₄ ∈ S₅) :
    IsPreconnected (S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅) :=
  (((h₁.union' ⟨p₁, hp₁, hp₁'⟩ h₂).union' ⟨p₂, Or.inr hp₂, hp₂'⟩ h₃).union'
    ⟨p₃, Or.inr hp₃, hp₃'⟩ h₄).union' ⟨p₄, Or.inr hp₄, hp₄'⟩ h₅

theorem exp_d_eq_one {x k κ c l : ℂ} (hκ : x + Complex.exp κ = k) (hc : Complex.exp c = 1)
    (hl : Complex.exp l = k - x) (hk : k - x ≠ 0) : Complex.exp (κ + c - l) = 1 := by
  have : Complex.exp κ = k - x := by rw [← hκ]; ring
  rw [Complex.exp_sub, Complex.exp_add, hc, mul_one, hl, this, div_self hk]

theorem re_mem_of_ann {x w : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : x + Complex.exp w ∈ GM.j1bAnn x r₁ r₂) : w.re ∈ Icc (Real.log r₁) (Real.log r₂) := by
  have hw : w.re = Real.log ‖x + Complex.exp w - x‖ := re_of_exp_eq (by ring)
  obtain ⟨h1, h2⟩ := h
  rw [hw]
  exact ⟨Real.log_le_log hr₁ h1.le, Real.log_le_log (hr₁.trans h1) h2.le⟩

theorem lift_disjoint {x : ℂ} {K K' : Set ℂ} {ℓ ℓ' : ℂ → ℂ} {d d' : ℂ}
    (hℓ : ∀ z ∈ K, Complex.exp (ℓ z) = z - x) (hℓ' : ∀ z ∈ K', Complex.exp (ℓ' z) = z - x)
    (hd : Complex.exp d = 1) (hd' : Complex.exp d' = 1) (hK : Disjoint K K') :
    Disjoint ((fun z => ℓ z + d) '' K) ((fun z => ℓ' z + d') '' K') :=
  disjoint_left.2 fun _ h h' => hK.le_bot ⟨exp_mem_of_mem_lift hℓ hd h, exp_mem_of_mem_lift hℓ' hd' h'⟩

theorem piece_subset {x : ℂ} {a b R : ℝ} {X All K : Set ℂ} {ℓ : ℂ → ℂ} {d : ℂ}
    (hR : All ⊆ ball 0 R) (hX : X ⊆ All) (hre : ∀ z ∈ X, z.re ∈ Icc a b)
    (hE : ∀ z ∈ X, x + Complex.exp z ∉ K) (hℓ : ∀ z ∈ K, Complex.exp (ℓ z) = z - x)
    (hd : Complex.exp d = 1) : X ⊆ rect a b (-R) R \ ((fun z => ℓ z + d) '' K) := by
  intro z hz
  have h := mem_ball_zero_iff.1 (hR (hX hz))
  have him := abs_le.1 ((Complex.abs_im_le_norm z).trans h.le)
  exact ⟨⟨hre z hz, him⟩, fun hL => hE z hz (exp_mem_of_mem_lift hℓ hd hL)⟩

end Sector

open Sector Set Metric in
/-- **The sector lemma** (MS l. 582): proved. -/
theorem GM.gmSector : GM.GMSector := by
  intro x r₁ r₂ K₁ K₂ K₃ W hr₁ h12 hK₁ hK₂ hK₃ d₁₂ d₁₃ d₂₃ hWp hWA hWd hcl
  obtain ⟨⟨k₁, hk₁W, hk₁K⟩, ⟨k₂, hk₂W, hk₂K⟩, ⟨k₃, hk₃W, hk₃K⟩⟩ := hcl
  have hc₁ := hK₁.1.isClosed
  have hc₂ := hK₂.1.isClosed
  have hc₃ := hK₃.1.isClosed
  obtain ⟨ℓ₁, hℓ₁c, hℓ₁⟩ := hasLog_crossing hr₁ h12 hK₁ hK₂ d₁₂
  obtain ⟨ℓ₂, hℓ₂c, hℓ₂⟩ := hasLog_crossing hr₁ h12 hK₂ hK₁ d₁₂.symm
  obtain ⟨ℓ₃, hℓ₃c, hℓ₃⟩ := hasLog_crossing hr₁ h12 hK₃ hK₁ d₁₃.symm
  obtain ⟨ω₁, κ₁, hκ₁, hω₁W, hS₁⟩ := exists_spur hr₁ hWA (hc₂.union hc₃).isOpen_compl hk₁W
    (fun h => h.elim (fun h => d₁₂.le_bot ⟨hk₁K, h⟩) (fun h => d₁₃.le_bot ⟨hk₁K, h⟩))
    (hK₁.2.2.1 k₁ hk₁K)
  obtain ⟨ω₂, κ₂, hκ₂, hω₂W, hS₂⟩ := exists_spur hr₁ hWA (hc₁.union hc₃).isOpen_compl hk₂W
    (fun h => h.elim (fun h => d₁₂.le_bot ⟨h, hk₂K⟩) (fun h => d₂₃.le_bot ⟨hk₂K, h⟩))
    (hK₂.2.2.1 k₂ hk₂K)
  obtain ⟨ω₃, κ₃, hκ₃, hω₃W, hS₃⟩ := exists_spur hr₁ hWA (hc₁.union hc₂).isOpen_compl hk₃W
    (fun h => h.elim (fun h => d₁₃.le_bot ⟨h, hk₃K⟩) (fun h => d₂₃.le_bot ⟨h, hk₃K⟩))
    (hK₃.2.2.1 k₃ hk₃K)
  -- the component `U ⊇ W` of the open annulus minus the continua
  have hAo : IsOpen (GM.j1bAnn x r₁ r₂ \ (K₁ ∪ K₂ ∪ K₃)) := by
    have : GM.j1bAnn x r₁ r₂ = {y | r₁ < ‖y - x‖} ∩ {y | ‖y - x‖ < r₂} := rfl
    rw [this]
    exact ((isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) continuous_const)).sdiff ((hc₁.union hc₂).union hc₃)
  set U := connectedComponentIn (GM.j1bAnn x r₁ r₂ \ (K₁ ∪ K₂ ∪ K₃)) (x + Complex.exp ω₁)
    with hU
  have hWsub : W ⊆ GM.j1bAnn x r₁ r₂ \ (K₁ ∪ K₂ ∪ K₃) := fun z hz =>
    ⟨hWA hz, fun h => hWd.le_bot ⟨hz, h⟩⟩
  have hWU : W ⊆ U := hWp.subset_connectedComponentIn hω₁W hWsub
  have hUsub : U ⊆ GM.j1bAnn x r₁ r₂ \ (K₁ ∪ K₂ ∪ K₃) := connectedComponentIn_subset _ _
  have hxU : x ∉ U := fun h => by
    have := (hUsub h).1.1
    rw [sub_self, norm_zero] at this
    linarith
  obtain ⟨P₃, hP₃c, hP₃p, hω₁P₃, hP₃U, c₃, hc₃e, hP₃e⟩ := exists_lift_path
    hAo.connectedComponentIn isPreconnected_connectedComponentIn hxU (hWU hω₁W) (hWU hω₃W)
  obtain ⟨P₂, hP₂c, hP₂p, hω₁P₂, hP₂U, c₂, hc₂e, hP₂e⟩ := exists_lift_path
    hAo.connectedComponentIn isPreconnected_connectedComponentIn hxU (hWU hω₁W) (hWU hω₂W)
  -- lifted crossers
  have hkx : ∀ {K : Set ℂ} {k : ℂ}, GM.j1bCrossing x r₁ r₂ K → k ∈ K → k - x ≠ 0 :=
    fun hK hk h => by have := (hK.2.2.1 _ hk).1; rw [h, norm_zero] at this; linarith
  set d₁ := κ₁ + 0 - ℓ₁ k₁ with hd₁
  set d₂ := κ₂ + c₂ - ℓ₂ k₂ with hd₂
  set d₃ := κ₃ + c₃ - ℓ₃ k₃ with hd₃
  have hd₁e : Complex.exp d₁ = 1 :=
    exp_d_eq_one hκ₁ Complex.exp_zero (hℓ₁ k₁ hk₁K) (hkx hK₁ hk₁K)
  have hd₂e : Complex.exp d₂ = 1 := exp_d_eq_one hκ₂ hc₂e (hℓ₂ k₂ hk₂K) (hkx hK₂ hk₂K)
  have hd₃e : Complex.exp d₃ = 1 := exp_d_eq_one hκ₃ hc₃e (hℓ₃ k₃ hk₃K) (hkx hK₃ hk₃K)
  set L₁ := (fun z => ℓ₁ z + d₁) '' K₁ with hL₁
  set L₂ := (fun z => ℓ₂ z + d₂) '' K₂ with hL₂
  set L₃ := (fun z => ℓ₃ z + d₃) '' K₃ with hL₃
  have hκL₁ : κ₁ ∈ L₁ := ⟨k₁, hk₁K, by rw [hd₁]; ring⟩
  have hκL₂ : κ₂ + c₂ ∈ L₂ := ⟨k₂, hk₂K, by rw [hd₂]; ring⟩
  have hκL₃ : κ₃ + c₃ ∈ L₃ := ⟨k₃, hk₃K, by rw [hd₃]; ring⟩
  -- lifted spurs
  set Q₁ := (fun s => spur ω₁ κ₁ s + 0) '' Icc (0 : ℝ) 1 with hQ₁
  set Q₂ := (fun s => spur ω₂ κ₂ s + c₂) '' Icc (0 : ℝ) 1 with hQ₂
  set Q₃ := (fun s => spur ω₃ κ₃ s + c₃) '' Icc (0 : ℝ) 1 with hQ₃
  have hQc : ∀ ω κ c : ℂ, IsCompact ((fun s => spur ω κ s + c) '' Icc (0 : ℝ) 1) := fun ω κ c =>
    isCompact_Icc.image ((continuous_spur ω κ).add continuous_const)
  have hQp : ∀ ω κ c : ℂ, IsPreconnected ((fun s => spur ω κ s + c) '' Icc (0 : ℝ) 1) :=
    fun ω κ c => isPreconnected_Icc.image _
      ((continuous_spur ω κ).add continuous_const).continuousOn
  have hQ0 : ∀ ω κ c : ℂ, ω + c ∈ (fun s => spur ω κ s + c) '' Icc (0 : ℝ) 1 := fun ω κ c =>
    ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [spur]⟩
  have hQ1 : ∀ ω κ c : ℂ, κ + c ∈ (fun s => spur ω κ s + c) '' Icc (0 : ℝ) 1 := fun ω κ c =>
    ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [spur]⟩
  have hQprop : ∀ {ω κ c : ℂ} {O : Set ℂ}, Complex.exp c = 1 →
      (∀ s ∈ Icc (0 : ℝ) 1, x + Complex.exp (spur ω κ s) ∈ O ∧
        (spur ω κ s).re ∈ Icc (Real.log r₁) (Real.log r₂)) →
      ∀ z ∈ (fun s => spur ω κ s + c) '' Icc (0 : ℝ) 1,
        x + Complex.exp z ∈ O ∧ z.re ∈ Icc (Real.log r₁) (Real.log r₂) := by
    rintro ω κ c O hc hS _ ⟨s, hs, rfl⟩
    have hc0 : c.re = 0 := by obtain ⟨n, rfl⟩ := Complex.exp_eq_one_iff.1 hc; simp
    refine ⟨?_, ?_⟩
    · rw [Complex.exp_add, hc, mul_one]; exact (hS s hs).1
    · rw [Complex.add_re, hc0, add_zero]; exact (hS s hs).2
  have hQ₁' := hQprop Complex.exp_zero hS₁
  have hQ₂' := hQprop hc₂e hS₂
  have hQ₃' := hQprop hc₃e hS₃
  -- a bounding rectangle
  set All := L₁ ∪ L₂ ∪ L₃ ∪ P₂ ∪ P₃ ∪ Q₁ ∪ Q₂ ∪ Q₃ with hAll
  have hAllc : IsCompact All :=
    (((((((hK₁.1.image_of_continuousOn (hℓ₁c.add continuousOn_const)).union
      (hK₂.1.image_of_continuousOn (hℓ₂c.add continuousOn_const))).union
      (hK₃.1.image_of_continuousOn (hℓ₃c.add continuousOn_const))).union hP₂c).union hP₃c).union
      (hQc _ _ _)).union (hQc _ _ _)).union (hQc _ _ _)
  obtain ⟨R, hR⟩ := hAllc.isBounded.subset_ball 0
  have hRpos : 0 < R := by
    have := mem_ball_zero_iff.1 (hR (show κ₁ ∈ All from Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hκL₁))))))))
    exact (norm_nonneg _).trans_lt this
  have hyb : ∀ {K : Set ℂ} {ℓ : ℂ → ℂ} {d : ℂ}, (fun z => ℓ z + d) '' K ⊆ All →
      ∀ z ∈ K, -R < (ℓ z + d).im ∧ (ℓ z + d).im < R := fun hsub z hz => by
    have h := mem_ball_zero_iff.1 (hR (hsub ⟨z, hz, rfl⟩))
    exact abs_lt.1 ((Complex.abs_im_le_norm _).trans_lt h)
  have sL₁ : L₁ ⊆ All := fun z hz => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hz)))))))
  have sL₂ : L₂ ⊆ All := fun z hz => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz))))))
  have sL₃ : L₃ ⊆ All := fun z hz => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz)))))
  have sP₂ : P₂ ⊆ All := fun z hz => Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz))))
  have sP₃ : P₃ ⊆ All := fun z hz => Or.inl (Or.inl (Or.inl (Or.inr hz)))
  have sQ₁ : Q₁ ⊆ All := fun z hz => Or.inl (Or.inl (Or.inr hz))
  have sQ₂ : Q₂ ⊆ All := fun z hz => Or.inl (Or.inr hz)
  have sQ₃ : Q₃ ⊆ All := fun z hz => Or.inr hz
  have hC₁ := isCrosser_lift (y₀ := -R) (y₁ := R) hr₁ hK₁ hℓ₁c hℓ₁ hd₁e (hyb sL₁)
  have hC₂ := isCrosser_lift (y₀ := -R) (y₁ := R) hr₁ hK₂ hℓ₂c hℓ₂ hd₂e (hyb sL₂)
  have hC₃ := isCrosser_lift (y₀ := -R) (y₁ := R) hr₁ hK₃ hℓ₃c hℓ₃ hd₃e (hyb sL₃)
  -- facts about the pieces
  have reL : ∀ {L : Set ℂ}, IsCrosser (Real.log r₁) (Real.log r₂) (-R) R L →
      ∀ z ∈ L, z.re ∈ Icc (Real.log r₁) (Real.log r₂) := fun hC z hz => (hC.2.2.1 hz).1
  have reP : ∀ {P : Set ℂ}, (∀ z ∈ P, x + Complex.exp z ∈ U) →
      ∀ z ∈ P, z.re ∈ Icc (Real.log r₁) (Real.log r₂) := fun hP z hz =>
    re_mem_of_ann hr₁ (hUsub (hP z hz)).1
  have EP : ∀ {P : Set ℂ}, (∀ z ∈ P, x + Complex.exp z ∈ U) → ∀ {K : Set ℂ},
      K ⊆ K₁ ∪ K₂ ∪ K₃ → ∀ z ∈ P, x + Complex.exp z ∉ K := fun hP K hK z hz h =>
    (hUsub (hP z hz)).2 (hK h)
  have EL : ∀ {K K' : Set ℂ} {ℓ : ℂ → ℂ} {d : ℂ}, (∀ z ∈ K, Complex.exp (ℓ z) = z - x) →
      Complex.exp d = 1 → Disjoint K K' →
      ∀ z ∈ (fun z => ℓ z + d) '' K, x + Complex.exp z ∉ K' := fun hℓ hd hKK' z hz h =>
    hKK'.le_bot ⟨exp_mem_of_mem_lift hℓ hd hz, h⟩
  have EQ : ∀ {Q K : Set ℂ} {O : Set ℂ}, (∀ z ∈ Q, x + Complex.exp z ∈ O ∧
      z.re ∈ Icc (Real.log r₁) (Real.log r₂)) → K ⊆ Oᶜ → ∀ z ∈ Q, x + Complex.exp z ∉ K :=
    fun hQ hK z hz h => hK h (hQ z hz).1
  have hy : -R < R := by linarith
  have hx : Real.log r₁ ≤ Real.log r₂ := Real.log_le_log hr₁ h12.le
  refine three_crossers_rect hx hy hC₁ hC₂ hC₃
    (lift_disjoint hℓ₁ hℓ₂ hd₁e hd₂e d₁₂) (lift_disjoint hℓ₁ hℓ₃ hd₁e hd₃e d₁₃)
    (lift_disjoint hℓ₂ hℓ₃ hd₂e hd₃e d₂₃)
    (N₁ := L₂ ∪ Q₂ ∪ (P₂ ∪ P₃) ∪ Q₃ ∪ L₃) (N₂ := L₁ ∪ Q₁ ∪ P₃ ∪ Q₃ ∪ L₃)
    (N₃ := L₁ ∪ Q₁ ∪ P₂ ∪ Q₂ ∪ L₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact chain5 hC₂.2.1 (hQp _ _ _) (hP₂p.union ω₁ hω₁P₂ hω₁P₃ hP₃p) (hQp _ _ _) hC₃.2.1
      hκL₂ (hQ1 _ _ _) (hQ0 _ _ _) (Or.inl hP₂e) (Or.inr hP₃e) (hQ0 _ _ _) (hQ1 _ _ _) hκL₃
  · refine union_subset (union_subset (union_subset (union_subset ?_ ?_) ?_) ?_) ?_
    · exact piece_subset hR sL₂ (reL hC₂) (EL hℓ₂ hd₂e d₁₂.symm) hℓ₁ hd₁e
    · exact piece_subset hR sQ₂ (fun z hz => (hQ₂' z hz).2)
        (EQ hQ₂' (by intro z hz h; exact h (Or.inl hz))) hℓ₁ hd₁e
    · exact piece_subset hR (union_subset sP₂ sP₃)
        (fun z hz => hz.elim (reP hP₂U z) (reP hP₃U z))
        (fun z hz => hz.elim (EP hP₂U (fun y hy => Or.inl (Or.inl hy)) z)
          (EP hP₃U (fun y hy => Or.inl (Or.inl hy)) z)) hℓ₁ hd₁e
    · exact piece_subset hR sQ₃ (fun z hz => (hQ₃' z hz).2)
        (EQ hQ₃' (by intro z hz h; exact h (Or.inl hz))) hℓ₁ hd₁e
    · exact piece_subset hR sL₃ (reL hC₃) (EL hℓ₃ hd₃e d₁₃.symm) hℓ₁ hd₁e
  · intro z hz
    rcases hz with hz | hz
    · exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
    · exact Or.inr hz
  · exact chain5 hC₁.2.1 (hQp _ _ _) hP₃p (hQp _ _ _) hC₃.2.1
      (⟨k₁, hk₁K, by rw [hd₁]; ring⟩ : κ₁ + 0 ∈ L₁) (hQ1 ω₁ κ₁ 0) (hQ0 ω₁ κ₁ 0)
      (by rw [add_zero]; exact hω₁P₃) hP₃e (hQ0 _ _ _)
      (hQ1 _ _ _) hκL₃
  · refine union_subset (union_subset (union_subset (union_subset ?_ ?_) ?_) ?_) ?_
    · exact piece_subset hR sL₁ (reL hC₁) (EL hℓ₁ hd₁e d₁₂) hℓ₂ hd₂e
    · exact piece_subset hR sQ₁ (fun z hz => (hQ₁' z hz).2)
        (EQ hQ₁' (by intro z hz h; exact h (Or.inl hz))) hℓ₂ hd₂e
    · exact piece_subset hR sP₃ (reP hP₃U)
        (EP hP₃U (fun y hy => Or.inl (Or.inr hy))) hℓ₂ hd₂e
    · exact piece_subset hR sQ₃ (fun z hz => (hQ₃' z hz).2)
        (EQ hQ₃' (by intro z hz h; exact h (Or.inr hz))) hℓ₂ hd₂e
    · exact piece_subset hR sL₃ (reL hC₃) (EL hℓ₃ hd₃e d₂₃.symm) hℓ₂ hd₂e
  · intro z hz
    rcases hz with hz | hz
    · exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
    · exact Or.inr hz
  · exact chain5 hC₁.2.1 (hQp _ _ _) hP₂p (hQp _ _ _) hC₂.2.1
      (⟨k₁, hk₁K, by rw [hd₁]; ring⟩ : κ₁ + 0 ∈ L₁) (hQ1 ω₁ κ₁ 0) (hQ0 ω₁ κ₁ 0)
      (by rw [add_zero]; exact hω₁P₂) hP₂e (hQ0 _ _ _)
      (hQ1 _ _ _) hκL₂
  · refine union_subset (union_subset (union_subset (union_subset ?_ ?_) ?_) ?_) ?_
    · exact piece_subset hR sL₁ (reL hC₁) (EL hℓ₁ hd₁e d₁₃) hℓ₃ hd₃e
    · exact piece_subset hR sQ₁ (fun z hz => (hQ₁' z hz).2)
        (EQ hQ₁' (by intro z hz h; exact h (Or.inr hz))) hℓ₃ hd₃e
    · exact piece_subset hR sP₂ (reP hP₂U)
        (EP hP₂U (fun y hy => Or.inr hy)) hℓ₃ hd₃e
    · exact piece_subset hR sQ₂ (fun z hz => (hQ₂' z hz).2)
        (EQ hQ₂' (by intro z hz h; exact h (Or.inr hz))) hℓ₃ hd₃e
    · exact piece_subset hR sL₂ (reL hC₂) (EL hℓ₂ hd₂e d₂₃) hℓ₃ hd₃e
  · intro z hz
    rcases hz with hz | hz
    · exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
    · exact Or.inr hz

end LQGMetric
