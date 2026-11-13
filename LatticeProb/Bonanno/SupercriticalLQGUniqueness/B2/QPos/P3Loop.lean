/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Loop at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Winding

 












set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 

 
def rightInd (c v : ℤ × ℤ) : ℤ := if c.1 + 1 ≤ v.1 then 1 else 0

theorem sum_crossVal_above (w : ℕ → ℤ × ℤ) (hw : ∀ k, latticeAdjacent (w k) (w (k + 1)))
    (c : ℤ × ℤ) (s d : ℕ) (habove : ∀ i < d, c.2 < (w (s + i)).2) :
    ∑ i ∈ range d, crossVal c (w (s + i)) (w (s + i + 1)) = rightInd c (w (s + d)) - rightInd c (w s) := by
  have : ∀ i ∈ range d, crossVal c (w (s + i)) (w (s + i + 1)) =
      rightInd c (w (s + (i + 1))) - rightInd c (w (s + i)) := by
    intro i hi
    rw [crossVal_eq_of_above c _ _ (hw (s + i)) (habove i (mem_range.mp hi))]
    rfl
  rw [sum_congr rfl this, sum_range_sub (fun i => rightInd c (w (s + i)))]
  simp

theorem sum_crossVal_below (w : ℕ → ℤ × ℤ) (c : ℤ × ℤ) (s d : ℕ)
    (hbelow : ∀ i < d, (w (s + i)).2 ≤ c.2) :
    ∑ i ∈ range d, crossVal c (w (s + i)) (w (s + i + 1)) = 0 :=
  sum_eq_zero (fun i hi => crossVal_eq_zero_of_below c _ _ (hbelow i (mem_range.mp hi)))

theorem sum_crossVal_vertical (w : ℕ → ℤ × ℤ) (c : ℤ × ℤ) (s d : ℕ)
    (hv : ∀ i < d, (w (s + i)).2 ≠ (w (s + i + 1)).2) :
    ∑ i ∈ range d, crossVal c (w (s + i)) (w (s + i + 1)) = 0 :=
  sum_eq_zero (fun i hi => crossVal_eq_zero_of_vertical c _ _ (hv i (mem_range.mp hi)))

 

theorem exists_dup_split {α : Type*} [DecidableEq α] :
    ∀ {L : List α}, ¬ L.Nodup → ∃ A a B C, L = A ++ a :: (B ++ a :: C)
  | [], h => absurd List.nodup_nil h
  | x :: L, h => by
    rw [List.nodup_cons] at h
    by_cases hx : x ∈ L
    · obtain ⟨B, C, rfl⟩ := List.append_of_mem hx
      exact ⟨[], x, B, C, by simp⟩
    · have : ¬ L.Nodup := fun hL => h ⟨hx, hL⟩
      obtain ⟨A, a, B, C, rfl⟩ := exists_dup_split this
      exact ⟨x :: A, a, B, C, by simp⟩

theorem wind_singleton (c v : ℤ × ℤ) : wind c [v] = 0 := rfl

 
theorem exists_simple_loop (c : ℤ × ℤ) :
    ∀ (n : ℕ) (l : List (ℤ × ℤ)), l.length ≤ n → l.IsChain latticeAdjacent → IsClosed l →
      wind c l ≠ 0 → ∃ l' : List (ℤ × ℤ), l'.IsChain latticeAdjacent ∧ IsClosed l' ∧
        l'.dropLast.Nodup ∧ (∀ v ∈ l', v ∈ l) ∧ wind c l' ≠ 0
  | 0, l, hlen, _, hcl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact absurd this hcl.1
  | n + 1, l, hlen, hch, hcl, hw => by
    classical
    by_cases hnd : l.dropLast.Nodup
    · exact ⟨l, hch, hcl, hnd, fun v hv => hv, hw⟩
    obtain ⟨A, a, B, C, hdec⟩ := exists_dup_split hnd
    obtain ⟨v, hv⟩ : ∃ v, l.getLast hcl.1 = v := ⟨_, rfl⟩
    have hl : l = A ++ a :: (B ++ a :: (C ++ [v])) := by
      have h := List.dropLast_append_getLast hcl.1
      rw [hdec, hv] at h
      rw [← h]; simp
    
    set l₁ : List (ℤ × ℤ) := a :: (B ++ [a]) with hl₁
    set l₂ : List (ℤ × ℤ) := A ++ a :: (C ++ [v]) with hl₂
    have hsum : wind c l = wind c l₁ + wind c l₂ := by
      unfold wind
      have e1 : stepSum (crossVal c) l = stepSum (crossVal c) (A ++ [a]) +
          stepSum (crossVal c) (a :: (B ++ a :: (C ++ [v]))) := by
        rw [hl]; exact stepSum_append_cons _ _ _ _
      have e2 : stepSum (crossVal c) (a :: (B ++ a :: (C ++ [v]))) =
          stepSum (crossVal c) (a :: (B ++ [a])) + stepSum (crossVal c) (a :: (C ++ [v])) := by
        have := stepSum_append_cons (crossVal c) (a :: B) a (C ++ [v]); simpa using this
      have e3 : stepSum (crossVal c) l₂ = stepSum (crossVal c) (A ++ [a]) +
          stepSum (crossVal c) (a :: (C ++ [v])) := stepSum_append_cons _ _ _ _
      rw [e1, e2, e3, hl₁]; ring
    
    have hch' := hch
    rw [hl, List.isChain_append] at hch'
    obtain ⟨hchA, hchR, hjA⟩ := hch'
    have hchR' := hchR
    rw [show a :: (B ++ a :: (C ++ [v])) = (a :: B) ++ a :: (C ++ [v]) by simp,
      List.isChain_append] at hchR'
    obtain ⟨hchaB, hchaC, hjB⟩ := hchR'
    have hch₁ : l₁.IsChain latticeAdjacent := by
      rw [hl₁, show a :: (B ++ [a]) = (a :: B) ++ [a] by simp, List.isChain_append]
      refine ⟨hchaB, List.isChain_singleton a, ?_⟩
      intro x hx y hy
      simp at hy; subst hy
      exact hjB x hx a (by simp)
    have hch₂ : l₂.IsChain latticeAdjacent := by
      rw [hl₂, List.isChain_append]
      exact ⟨hchA, hchaC, fun x hx y hy => hjA x hx y (by simpa using hy)⟩
    
    have hcl₁ : IsClosed l₁ := ⟨by simp [hl₁], by
      rw [hl₁, ← List.cons_append, List.getLast?_append]; simp⟩
    have hcl₂ : IsClosed l₂ := by
      refine ⟨by simp [hl₂], ?_⟩
      have hhead : l₂.head? = l.head? := by
        rw [hl₂, hl, List.head?_append, List.head?_append]; simp
      have h1 : l₂.getLast? = some v := by
        rw [hl₂, show A ++ a :: (C ++ [v]) = (A ++ a :: C) ++ [v] by simp, List.getLast?_append]
        simp
      have h2 : l.getLast? = some v := by
        rw [hl, show A ++ a :: (B ++ a :: (C ++ [v])) = (A ++ a :: (B ++ a :: C)) ++ [v] by simp,
          List.getLast?_append]
        simp
      rw [hhead, hcl.2, h1, h2]
    
    have hmem₁ : ∀ x ∈ l₁, x ∈ l := by
      intro x hx; rw [hl]; simp [hl₁] at hx ⊢; tauto
    have hmem₂ : ∀ x ∈ l₂, x ∈ l := by
      intro x hx; rw [hl]; simp [hl₂] at hx ⊢; tauto
    have hlen₁ : l₁.length ≤ n := by
      have : l.length = A.length + B.length + C.length + 3 := by rw [hl]; simp; ring
      simp [hl₁]; omega
    have hlen₂ : l₂.length ≤ n := by
      have : l.length = A.length + B.length + C.length + 3 := by rw [hl]; simp; ring
      simp [hl₂]; omega
    by_cases hw₁ : wind c l₁ = 0
    · have hw₂ : wind c l₂ ≠ 0 := by rw [hsum, hw₁, zero_add] at hw; exact hw
      obtain ⟨l', h1, h2, h3, h4, h5⟩ := exists_simple_loop c n l₂ hlen₂ hch₂ hcl₂ hw₂
      exact ⟨l', h1, h2, h3, fun x hx => hmem₂ x (h4 x hx), h5⟩
    · obtain ⟨l', h1, h2, h3, h4, h5⟩ := exists_simple_loop c n l₁ hlen₁ hch₁ hcl₁ hw₁
      exact ⟨l', h1, h2, h3, fun x hx => hmem₁ x (h4 x hx), h5⟩

 
theorem simple_loop_cyclic {l : List (ℤ × ℤ)} (hch : l.IsChain latticeAdjacent)
    (hcl : IsClosed l) (c : ℤ × ℤ) (hw : wind c l ≠ 0) :
    l.dropLast ≠ [] ∧ l.dropLast.IsChain latticeAdjacent ∧
      ∃ z w, l.dropLast.head? = some z ∧ l.dropLast.getLast? = some w ∧ latticeAdjacent w z := by
  have hne := hcl.1
  have hdl : l.dropLast ++ [l.getLast hne] = l := List.dropLast_append_getLast hne
  have hpne : l.dropLast ≠ [] := by
    intro h
    rw [h] at hdl
    rw [← hdl] at hw
    exact hw (wind_singleton c _)
  refine ⟨hpne, ?_, ?_⟩
  · exact hch.infix (List.IsPrefix.isInfix (List.dropLast_prefix l))
  · have hch' := hch
    rw [← hdl, List.isChain_append] at hch'
    obtain ⟨z, hz⟩ : ∃ z, l.dropLast.head? = some z := ⟨_, List.head?_eq_head hpne⟩
    obtain ⟨w, hw'⟩ : ∃ w, l.dropLast.getLast? = some w := ⟨_, List.getLast?_eq_getLast hpne⟩
    refine ⟨z, w, hz, hw', ?_⟩
    have hadj := hch'.2.2 w hw' (l.getLast hne) (by simp)
    have hzl : l.getLast hne = z := by
      have h1 := hcl.2
      rw [List.getLast?_eq_getLast hne] at h1
      have h2 : l.head? = some z := by
        conv_lhs => rw [← hdl]
        rw [List.head?_append, hz]; rfl
      rw [h2] at h1
      exact (Option.some_injective _ h1).symm
    rw [hzl] at hadj
    exact hadj

 

theorem seg_succ_cons (w : ℕ → ℤ × ℤ) (s d : ℕ) : seg w s (d + 1) = w s :: seg w (s + 1) d := by
  unfold seg
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  congr 1; omega

theorem seg_getLast (w : ℕ → ℤ × ℤ) (s d : ℕ) :
    (seg w s d).getLast (seg_ne_nil w s d) = w (s + d) := by
  have := seg_getLast? w s d
  rw [List.getLast?_eq_getLast (seg_ne_nil w s d)] at this
  exact Option.some_injective _ this

theorem getLast_append_seg (L : List (ℤ × ℤ)) (w : ℕ → ℤ × ℤ) (s d : ℕ)
    (h : L ++ seg w s d ≠ []) : (L ++ seg w s d).getLast h = w (s + d) := by
  rw [List.getLast_append_of_ne_nil h (seg_ne_nil w s d), seg_getLast]

 
theorem stepSum_glue_seg (f : ℤ × ℤ → ℤ × ℤ → ℤ) (L : List (ℤ × ℤ)) (hL : L ≠ [])
    (w : ℕ → ℤ × ℤ) (d : ℕ) (hlast : L.getLast hL = w 0) :
    stepSum f (L ++ seg w 1 d) = stepSum f L + ∑ i ∈ range (d + 1), f (w (0 + i)) (w (0 + i + 1)) := by
  rw [← stepSum_seg]
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L = L₀ ++ [w 0] := ⟨L.dropLast, by
    conv_lhs => rw [← List.dropLast_append_getLast hL]
    rw [hlast]⟩
  subst hL₀
  rw [List.append_assoc, List.singleton_append, stepSum_append_cons, seg_succ_cons]

theorem isChain_glue_seg (L : List (ℤ × ℤ)) (hL : L ≠ []) (w : ℕ → ℤ × ℤ) (d : ℕ)
    (hw : ∀ k, latticeAdjacent (w k) (w (k + 1))) (hLc : L.IsChain latticeAdjacent)
    (hlast : L.getLast hL = w 0) :
    (L ++ seg w 1 d).IsChain latticeAdjacent := by
  rw [List.isChain_append]
  refine ⟨hLc, seg_isChain w hw 1 d, ?_⟩
  intro x hx y hy
  rw [List.getLast?_eq_getLast hL] at hx
  rw [seg_head?] at hy
  simp at hx hy
  rw [← hx, ← hy, hlast]
  exact hw 0

 
theorem strip_crossing (w : ℕ → ℤ × ℤ) (hw : ∀ k, latticeAdjacent (w k) (w (k + 1)))
    (k1 d1 k2 d2 : ℕ) (h1 x0 h2 H : ℤ)
    (hγ1 : ∀ i ≤ d1, |(w (k1 + i)).2| ≤ h1)
    (hγ1s : x0 + h2 < (w k1).1) (hγ1e : (w (k1 + d1)).1 < x0 - h2)
    (hγ2 : ∀ i ≤ d2, |(w (k2 + i)).1 - x0| ≤ h2 ∧ (w (k2 + i)).2 < H)
    (hγ2s : (w k2).2 < -h1) (hγ2e : h1 < (w (k2 + d2)).2) (hH : h1 < H) :
    ∃ i ≤ d1, ∃ i' ≤ d2, w (k1 + i) = w (k2 + i') := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hh2 : 0 ≤ h2 := le_trans (abs_nonneg _) (hγ2 0 (Nat.zero_le _)).1
  obtain ⟨a, ha⟩ : ∃ a, (w (k1 + d1)).1 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (w (k1 + d1)).2 = b := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', (w k1).1 = a' := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', (w k1).2 = b' := ⟨_, rfl⟩
  have hbH : b < H := by have := abs_le.mp (hγ1 d1 le_rfl); omega
  have hb'H : b' < H := by have := abs_le.mp (hγ1 0 (Nat.zero_le _)); simp at this; omega
  have haa' : a < a' := by omega
  obtain ⟨dU, hdU⟩ : ∃ dU : ℕ, (dU : ℤ) = H - b - 1 := ⟨(H - b - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨dH, hdH⟩ : ∃ dH : ℕ, (dH : ℤ) = a' - a - 1 := ⟨(a' - a - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨dD, hdD⟩ : ∃ dD : ℕ, (dD : ℤ) = H - b' - 1 := ⟨(H - b' - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  let U : ℕ → ℤ × ℤ := fun i => (a, b + i)
  let Hf : ℕ → ℤ × ℤ := fun i => (a + i, H)
  let Dn : ℕ → ℤ × ℤ := fun i => (a', H - i)
  have hU : ∀ k, latticeAdjacent (U k) (U (k + 1)) := fun k => by
    simp only [U, latticeAdjacent]; right; right; left; constructor <;> push_cast <;> ring
  have hHf : ∀ k, latticeAdjacent (Hf k) (Hf (k + 1)) := fun k => by
    simp only [Hf, latticeAdjacent]; left; constructor <;> push_cast <;> ring
  have hDn : ∀ k, latticeAdjacent (Dn k) (Dn (k + 1)) := fun k => by
    simp only [Dn, latticeAdjacent]; right; right; right; constructor <;> push_cast <;> ring
  have hU0 : U 0 = w (k1 + d1) := by simp only [U]; ext <;> simp [ha, hb]
  have hUe : U (1 + dU) = Hf 0 := by simp only [U, Hf]; ext <;> push_cast <;> omega
  have hHe : Hf (1 + dH) = Dn 0 := by simp only [Hf, Dn]; ext <;> push_cast <;> omega
  have hDe : Dn (1 + dD) = w k1 := by simp only [Dn]; ext <;> push_cast <;> omega
  
  have hne1 : seg w k1 d1 ≠ [] := seg_ne_nil w k1 d1
  have hne2 : seg w k1 d1 ++ seg U 1 dU ≠ [] := by simp [seg_ne_nil]
  have hne3 : seg w k1 d1 ++ seg U 1 dU ++ seg Hf 1 dH ≠ [] := by simp [seg_ne_nil]
  have hl1 : (seg w k1 d1).getLast hne1 = U 0 := by rw [seg_getLast, hU0]
  have hl2 : (seg w k1 d1 ++ seg U 1 dU).getLast hne2 = Hf 0 := by
    rw [getLast_append_seg, hUe]
  have hl3 : (seg w k1 d1 ++ seg U 1 dU ++ seg Hf 1 dH).getLast hne3 = Dn 0 := by
    rw [getLast_append_seg, hHe]
  set Γ := seg w k1 d1 ++ seg U 1 dU ++ seg Hf 1 dH ++ seg Dn 1 dD with hΓ
  have hchain : Γ.IsChain latticeAdjacent :=
    isChain_glue_seg _ hne3 Dn dD hDn
      (isChain_glue_seg _ hne2 Hf dH hHf
        (isChain_glue_seg _ hne1 U dU hU (seg_isChain w hw k1 d1) hl1) hl2) hl3
  have hcl : IsClosed Γ := by
    refine ⟨by simp [hΓ, seg_ne_nil], ?_⟩
    rw [hΓ, List.head?_append, List.head?_append, List.head?_append, seg_head?,
      List.getLast?_eq_getLast (by simp [seg_ne_nil]), getLast_append_seg, hDe]
    rfl
  
  have hdec : ∀ c : ℤ × ℤ, wind c Γ =
      (∑ i ∈ range d1, crossVal c (w (k1 + i)) (w (k1 + i + 1))) +
      (∑ i ∈ range (dU + 1), crossVal c (U (0 + i)) (U (0 + i + 1))) +
      (∑ i ∈ range (dH + 1), crossVal c (Hf (0 + i)) (Hf (0 + i + 1))) +
      (∑ i ∈ range (dD + 1), crossVal c (Dn (0 + i)) (Dn (0 + i + 1))) := by
    intro c
    unfold wind
    rw [hΓ, stepSum_glue_seg _ _ hne3 Dn dD hl3, stepSum_glue_seg _ _ hne2 Hf dH hl2,
      stepSum_glue_seg _ _ hne1 U dU hl1, stepSum_seg]
  have hUv : ∀ c : ℤ × ℤ, ∑ i ∈ range (dU + 1), crossVal c (U (0 + i)) (U (0 + i + 1)) = 0 :=
    fun c => sum_crossVal_vertical U c 0 _ (fun i _ => by simp [U])
  have hDv : ∀ c : ℤ × ℤ, ∑ i ∈ range (dD + 1), crossVal c (Dn (0 + i)) (Dn (0 + i + 1)) = 0 :=
    fun c => sum_crossVal_vertical Dn c 0 _ (fun i _ => by simp [Dn])
  have hHv : ∀ c : ℤ × ℤ, c.2 < H → c.1 + 1 ≤ a' → a < c.1 + 1 →
      ∑ i ∈ range (dH + 1), crossVal c (Hf (0 + i)) (Hf (0 + i + 1)) = 1 := by
    intro c hc h1' h2'
    rw [sum_crossVal_above Hf hHf c 0 _ (fun i _ => by simpa [Hf] using hc)]
    simp only [rightInd, Hf]
    push_cast
    rw [if_pos (by omega), if_neg (by omega)]
    norm_num
  
  have hout : ∀ i ≤ d2, w (k2 + i) ∉ Γ := by
    intro i hi hmem
    obtain ⟨hx2, hy2⟩ := hγ2 i hi
    have hx2' := abs_le.mp hx2
    rw [hΓ] at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with ((hm | hm) | hm) | hm
    · obtain ⟨i', hi', he⟩ := mem_seg.mp hm
      exact hcon i' hi' i hi he
    · obtain ⟨i', _, he⟩ := mem_seg.mp hm
      have := congrArg Prod.fst he; simp [U] at this; omega
    · obtain ⟨i', _, he⟩ := mem_seg.mp hm
      have := congrArg Prod.snd he; simp [Hf] at this; omega
    · obtain ⟨i', _, he⟩ := mem_seg.mp hm
      have := congrArg Prod.fst he; simp [Dn] at this; omega
  have hcst := wind_eq_along_fun hchain hcl w hw k2 d2 hout
  
  have hstart : wind (w k2) Γ = 0 := by
    rw [hdec, hUv, hDv]
    have hx := abs_le.mp (hγ2 0 (Nat.zero_le _)).1
    simp only [add_zero] at hx
    rw [hHv (w k2) (by simpa using (hγ2 0 (Nat.zero_le _)).2) (by omega) (by omega)]
    rw [sum_crossVal_above w hw (w k2) k1 d1 (fun i hi => by
      have := abs_le.mp (hγ1 i hi.le); omega)]
    simp only [rightInd]
    rw [if_neg (by omega), if_pos (by simp; omega)]
    norm_num
  have hend : wind (w (k2 + d2)) Γ = 1 := by
    rw [hdec, hUv, hDv]
    have hx := abs_le.mp (hγ2 d2 le_rfl).1
    rw [hHv (w (k2 + d2)) (hγ2 d2 le_rfl).2 (by omega) (by omega)]
    rw [sum_crossVal_below w (w (k2 + d2)) k1 d1 (fun i hi => by
      have := abs_le.mp (hγ1 i hi.le); omega)]
    norm_num
  rw [hstart, hend] at hcst
  exact absurd hcst (by norm_num)

end SupercriticalLQGUniqueness.B2.QPos.P3
