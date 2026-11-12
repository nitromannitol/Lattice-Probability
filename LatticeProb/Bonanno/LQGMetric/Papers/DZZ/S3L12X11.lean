/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X10

/-!
# DZZ Lemma 3.12: the coarse ring from four cut side crossings (D93 §2, packet P-6a)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1461–1477)
and Remark 3.15 (l. 1360–1363), ring form of DEC-93 §2: four side parts `Lᵢ ++ Fᵢ ++ Hᵢ`
(walk order, from the home corner `c₀` around to `c₀`), glued at meeting points, with the zone
data of S3L12X9, give a `CoarseRing` (spur walks `side_walk`, blocks `walk_noGap`, closing
`cyc_of_closed`).

* `isChain_and_mem`; **`coarseRing_of_sides`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma isChain_and_mem {α : Type*} {R : α → α → Prop} {p : α → Prop} :
    ∀ {l : List α}, l.IsChain R → (∀ x ∈ l, p x) → l.IsChain (fun a b => R a b ∧ p a ∧ p b)
  | [], _, _ => .nil
  | [_], _, _ => .singleton _
  | a :: b :: t, h, hp => by
    rw [List.isChain_cons_cons] at h ⊢
    exact ⟨⟨h.1, hp a (by simp), hp b (by simp)⟩,
      isChain_and_mem h.2 fun x hx => hp x (List.mem_cons_of_mem _ hx)⟩

/-- **The coarse ring from four cut side crossings.** -/
theorem coarseRing_of_sides {C : DyBox} {k h d : ℕ} (hK : 2 ^ k = 2 * h)
    {L₁ F₁ H₁ L₂ F₂ H₂ L₃ F₃ H₃ L₄ F₄ H₄ : List (ℤ × ℤ)} {c₀ c₁ c₂ c₃ m₀ m₁ m₂ m₃ : ℤ × ℤ}
    (hc₁ : (L₁ ++ F₁ ++ H₁).IsChain PercAdj4) (hc₂ : (L₂ ++ F₂ ++ H₂).IsChain PercAdj4)
    (hc₃ : (L₃ ++ F₃ ++ H₃).IsChain PercAdj4) (hc₄ : (L₄ ++ F₄ ++ H₄).IsChain PercAdj4)
    (hu₁ : m₀ ∈ L₁ ∨ (L₁ = [] ∧ m₀ ∈ F₁)) (hv₁ : m₁ ∈ H₁ ∨ (H₁ = [] ∧ m₁ ∈ F₁))
    (hu₂ : m₁ ∈ L₂ ∨ (L₂ = [] ∧ m₁ ∈ F₂)) (hv₂ : m₂ ∈ H₂ ∨ (H₂ = [] ∧ m₂ ∈ F₂))
    (hu₃ : m₂ ∈ L₃ ∨ (L₃ = [] ∧ m₂ ∈ F₃)) (hv₃ : m₃ ∈ H₃ ∨ (H₃ = [] ∧ m₃ ∈ F₃))
    (hu₄ : m₃ ∈ L₄ ∨ (L₄ = [] ∧ m₃ ∈ F₄)) (hv₄ : m₀ ∈ H₄ ∨ (H₄ = [] ∧ m₀ ∈ F₄))
    (hsite : ∀ z, z ∈ L₁ ++ F₁ ++ H₁ ∨ z ∈ L₂ ++ F₂ ++ H₂ ∨ z ∈ L₃ ++ F₃ ++ H₃ ∨
      z ∈ L₄ ++ F₄ ++ H₄ → InGrid (C.n + k) (l37c C h) z ∧ annBox (2 * (h : ℤ) - 2) z ∧
        ∃ e, (h : ℤ) + 2 ≤ annDir e z)
    (hF : ∀ z, z ∈ F₁ ∨ z ∈ F₂ ∨ z ∈ F₃ ∨ z ∈ F₄ →
      (∀ bt ∈ boxCollBdry (siteBox (C.n + k) (l37c C h) z) d, m bt < δ ^ 2) ∧
        ∀ P, IsParent m δ C P → ¬ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox)
    (hZ : ∀ z c, (z ∈ L₁ ∧ c = c₀) ∨ (z ∈ H₁ ∧ c = c₁) ∨ (z ∈ L₂ ∧ c = c₁) ∨
      (z ∈ H₂ ∧ c = c₂) ∨ (z ∈ L₃ ∧ c = c₂) ∨ (z ∈ H₃ ∧ c = c₃) ∨ (z ∈ L₄ ∧ c = c₃) ∨
      (z ∈ H₄ ∧ c = c₀) →
      (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox) ∧
        ∀ P, IsParent m δ C P → ((siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
          (siteBox (C.n + k) (l37c C h) c).closedBox ⊆ P.closedBox))
    (hhome : ∀ P, IsParent m δ C P →
      ¬ (siteBox (C.n + k) (l37c C h) c₀).closedBox ⊆ P.closedBox)
    (hF₂ : (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) c₁).closedBox ⊆ P.closedBox) →
      (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) c₂).closedBox ⊆ P.closedBox) →
      F₂ = [])
    (hF₃ : (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) c₂).closedBox ⊆ P.closedBox) →
      (∃ P, IsParent m δ C P ∧ (siteBox (C.n + k) (l37c C h) c₃).closedBox ⊆ P.closedBox) →
      F₃ = [])
    (h13 : ∀ P, IsParent m δ C P →
      (siteBox (C.n + k) (l37c C h) c₁).closedBox ⊆ P.closedBox →
      (siteBox (C.n + k) (l37c C h) c₃).closedBox ⊆ P.closedBox → False)
    (hsep : ∀ M : Set DyBox, (∀ z, z ∈ L₁ ++ F₁ ++ H₁ ∨ z ∈ L₂ ++ F₂ ++ H₂ ∨
      z ∈ L₃ ++ F₃ ++ H₃ ∨ z ∈ L₄ ++ F₄ ++ H₄ → siteBox (C.n + k) (l37c C h) z ∈ M) →
      EnclosesBox C M)
    (hnt : ∃ z ∈ L₁ ++ F₁ ++ H₁, ∃ z' ∈ L₁ ++ F₁ ++ H₁,
      siteBox (C.n + k) (l37c C h) z ≠ siteBox (C.n + k) (l37c C h) z') :
    ∃ l, CoarseRing m δ C k d l := by
  set sb := siteBox (C.n + k) (l37c C h)
  have hs4 : ∀ x y, PercAdj4 x y → PercAdj4 y x := fun x y hxy => percAdj4_symm hxy
  obtain ⟨A₁, B₁, D₁, w₁, h₁, l₁, s₁, a₁, b₁, d₁⟩ := side_walk hs4 hc₁ hu₁ hv₁
  obtain ⟨A₂, B₂, D₂, w₂, h₂, l₂, s₂, a₂, b₂, d₂⟩ := side_walk hs4 hc₂ hu₂ hv₂
  obtain ⟨A₃, B₃, D₃, w₃, h₃, l₃, s₃, a₃, b₃, d₃⟩ := side_walk hs4 hc₃ hu₃ hv₃
  obtain ⟨A₄, B₄, D₄, w₄, h₄, l₄, s₄, a₄, b₄, d₄⟩ := side_walk hs4 hc₄ hu₄ hv₄
  set W := A₁ ++ B₁ ++ D₁ ++ (A₂ ++ B₂ ++ D₂) ++ (A₃ ++ B₃ ++ D₃) ++ (A₄ ++ B₄ ++ D₄) with hW
  -- membership
  have hmemW : ∀ z, z ∈ W ↔ z ∈ L₁ ++ F₁ ++ H₁ ∨ z ∈ L₂ ++ F₂ ++ H₂ ∨ z ∈ L₃ ++ F₃ ++ H₃ ∨
      z ∈ L₄ ++ F₄ ++ H₄ := by
    intro z
    rw [← s₁ z, ← s₂ z, ← s₃ z, ← s₄ z, hW]
    simp only [List.mem_append, or_assoc]
  -- the walk is closed and a chain
  have junction : ∀ (X Y : List (ℤ × ℤ)) (x : ℤ × ℤ), X.getLast? = some x → Y.head? = some x →
      ∀ a ∈ X.getLast?, ∀ b ∈ Y.head?, EqOr PercAdj4 a b := by
    intro X Y x hX hY a ha b hb
    rw [hX] at ha; rw [hY] at hb; cases ha; cases hb; exact Or.inl rfl
  have ne : ∀ (X : List (ℤ × ℤ)) (x : ℤ × ℤ), X.head? = some x → X ≠ [] := by
    intro X x hX hX'; rw [hX'] at hX; simp at hX
  have hWc : W.IsChain (EqOr PercAdj4) := by
    have c12 := List.isChain_append.2 ⟨w₁, w₂, junction _ _ m₁ l₁ h₂⟩
    have c123 := List.isChain_append.2 ⟨c12, w₃, by
      rw [List.getLast?_append_of_ne_nil _ (ne _ _ h₂)]; exact junction _ _ m₂ l₂ h₃⟩
    have c1234 := List.isChain_append.2 ⟨c123, w₄, by
      rw [List.getLast?_append_of_ne_nil _ (ne _ _ h₃)]; exact junction _ _ m₃ l₃ h₄⟩
    exact c1234
  have hWh : W.head? = some m₀ := by
    rw [hW, List.append_assoc, List.append_assoc, List.head?_append_of_ne_nil _ (ne _ _ h₁), h₁]
  have hWl : W.getLast? = some m₀ := by
    rw [hW, List.getLast?_append_of_ne_nil _ (ne _ _ h₄), l₄]
  -- the box walk
  have hgrid : ∀ z ∈ W, InGrid (C.n + k) (l37c C h) z := fun z hz => (hsite z ((hmemW z).1 hz)).1
  set Wb := W.map sb with hWb
  have hWbc : Wb.IsChain (EqOr Neighbour) := by
    rw [hWb, List.isChain_map]
    refine (isChain_and_mem hWc hgrid).imp fun a b hab => ?_
    rcases hab.1 with e | e
    · exact Or.inl (congrArg sb e)
    · exact Or.inr (neighbour_siteBox hab.2.1 hab.2.2 e)
  have hWbne : Wb ≠ [] := by simpa [hWb] using ne _ _ hWh
  have hWbcl : Wb.head? = Wb.getLast? := by
    rw [hWb, List.head?_map, List.getLast?_map, hWh, hWl]
  obtain ⟨z, hz, z', hz', hzz⟩ := hnt
  obtain ⟨Z, hZne, hZc, hZs, hZm⟩ := cyc_of_closed hWbc hWbne hWbcl
    ⟨sb z, List.mem_map_of_mem ((hmemW z).2 (Or.inl hz)), sb z',
      List.mem_map_of_mem ((hmemW z').2 (Or.inl hz')), hzz⟩
  have hmemZ : ∀ b, b ∈ Z ↔ ∃ z ∈ W, sb z = b := fun b => by rw [hZm, hWb, List.mem_map]
  refine ⟨Z, hZne, hZc, ?_, ?_, ?_⟩
  · -- the boxes
    intro b hb
    obtain ⟨z, hzW, rfl⟩ := (hmemZ b).1 hb
    obtain ⟨hzg, hzN, e, he⟩ := hsite z ((hmemW z).1 hzW)
    refine ⟨siteBox_mem_boxColl C hK hzg hzN, disjoint_siteBox C hK hzg he, ?_⟩
    have hz6 : z ∈ A₁ ∨ z ∈ B₁ ∨ z ∈ D₁ ∨ z ∈ A₂ ∨ z ∈ B₂ ∨ z ∈ D₂ ∨ z ∈ A₃ ∨ z ∈ B₃ ∨
        z ∈ D₃ ∨ z ∈ A₄ ∨ z ∈ B₄ ∨ z ∈ D₄ := by
      rw [hW] at hzW; simp only [List.mem_append, or_assoc] at hzW; exact hzW
    rcases hz6 with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inr (hZ z c₀ (Or.inl ⟨a₁ z h, rfl⟩)).1
    · exact Or.inl (hF z (Or.inl (b₁ z h))).1
    · exact Or.inr (hZ z c₁ (Or.inr (Or.inl ⟨d₁ z h, rfl⟩))).1
    · exact Or.inr (hZ z c₁ (Or.inr (Or.inr (Or.inl ⟨a₂ z h, rfl⟩)))).1
    · exact Or.inl (hF z (Or.inr (Or.inl (b₂ z h)))).1
    · exact Or.inr (hZ z c₂ (Or.inr (Or.inr (Or.inr (Or.inl ⟨d₂ z h, rfl⟩))))).1
    · exact Or.inr (hZ z c₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a₃ z h, rfl⟩)))))).1
    · exact Or.inl (hF z (Or.inr (Or.inr (Or.inl (b₃ z h))))).1
    · exact Or.inr (hZ z c₃ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨d₃ z h, rfl⟩))))))).1
    · exact Or.inr (hZ z c₃ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨a₄ z h, rfl⟩)))))))).1
    · exact Or.inl (hF z (Or.inr (Or.inr (Or.inr (b₄ z h))))).1
    · exact Or.inr (hZ z c₀ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨d₄ z h, rfl⟩)))))))).1
  · -- separation
    exact hsep _ fun z hz => (hmemZ _).2 ⟨z, (hmemW z).2 hz, rfl⟩
  · -- blocks
    intro P hP
    set Q : ℤ × ℤ → Prop := fun z => (sb z).closedBox ⊆ P.closedBox
    have zq : ∀ z c, (z ∈ L₁ ∧ c = c₀) ∨ (z ∈ H₁ ∧ c = c₁) ∨ (z ∈ L₂ ∧ c = c₁) ∨
        (z ∈ H₂ ∧ c = c₂) ∨ (z ∈ L₃ ∧ c = c₂) ∨ (z ∈ H₃ ∧ c = c₃) ∨ (z ∈ L₄ ∧ c = c₃) ∨
        (z ∈ H₄ ∧ c = c₀) → (Q z ↔ (sb c).closedBox ⊆ P.closedBox) :=
      fun z c hzc => (hZ z c hzc).2 P hP
    have fq : ∀ z, z ∈ F₁ ∨ z ∈ F₂ ∨ z ∈ F₃ ∨ z ∈ F₄ → ¬ Q z := fun z hz => (hF z hz).2 P hP
    have hgap : NoGap Q W := by
      refine walk_noGap (κ₁ := (sb c₁).closedBox ⊆ P.closedBox)
        (κ₂ := (sb c₂).closedBox ⊆ P.closedBox) (κ₃ := (sb c₃).closedBox ⊆ P.closedBox)
        (fun x hx hq => hhome P hP ((zq x c₀ (Or.inl ⟨a₁ x hx, rfl⟩)).1 hq))
        (fun x hx hq => hhome P hP ((zq x c₀ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d₄ x hx, rfl⟩)))))))).1 hq))
        (fun x hx => fq x (Or.inl (b₁ x hx))) (fun x hx => fq x (Or.inr (Or.inl (b₂ x hx))))
        (fun x hx => fq x (Or.inr (Or.inr (Or.inl (b₃ x hx)))))
        (fun x hx => fq x (Or.inr (Or.inr (Or.inr (b₄ x hx)))))
        (fun x hx => zq x c₁ (Or.inr (Or.inl ⟨d₁ x hx, rfl⟩)))
        (fun x hx => zq x c₁ (Or.inr (Or.inr (Or.inl ⟨a₂ x hx, rfl⟩))))
        (fun x hx => zq x c₂ (Or.inr (Or.inr (Or.inr (Or.inl ⟨d₂ x hx, rfl⟩)))))
        (fun x hx => zq x c₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a₃ x hx, rfl⟩))))))
        (fun x hx => zq x c₃ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d₃ x hx, rfl⟩)))))))
        (fun x hx => zq x c₃ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a₄ x hx, rfl⟩))))))))
        (fun k1 k2 => ?_) (fun k2 k3 => ?_) (fun k1 k3 => absurd (h13 P hP k1 k3) id)
      · have e := hF₂ ⟨P, hP, k1⟩ ⟨P, hP, k2⟩
        exact List.eq_nil_iff_forall_not_mem.2 fun x hx => by
          have := b₂ x hx; rw [e] at this; simp at this
      · have e := hF₃ ⟨P, hP, k2⟩ ⟨P, hP, k3⟩
        exact List.eq_nil_iff_forall_not_mem.2 fun x hx => by
          have := b₃ x hx; rw [e] at this; simp at this
    obtain ⟨W₁, W₂, W₃, eW, hW2, hW13⟩ := block_of_noGap W hgap
    have hgapb : NoGap (fun b : DyBox => b.closedBox ⊆ P.closedBox) Wb := by
      rw [hWb, eW, List.map_append, List.map_append]
      refine noGap_of_block (fun b hb => ?_) (fun b hb => ?_)
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb; exact hW2 z hz
      · rw [← List.map_append] at hb
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb; exact hW13 z hz
    exact block_of_noGap Z (noGap_sublist hZs hgapb)

end DZZ
end LQGMetric
