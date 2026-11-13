/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Winding at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBox

 













set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 
def stepSum (f : ℤ × ℤ → ℤ × ℤ → ℤ) : List (ℤ × ℤ) → ℤ
  | a :: b :: l => f a b + stepSum f (b :: l)
  | _ => 0

@[simp] theorem stepSum_nil (f : ℤ × ℤ → ℤ × ℤ → ℤ) : stepSum f [] = 0 := rfl
@[simp] theorem stepSum_singleton (f : ℤ × ℤ → ℤ × ℤ → ℤ) (a : ℤ × ℤ) : stepSum f [a] = 0 := rfl
@[simp] theorem stepSum_cons_cons (f : ℤ × ℤ → ℤ × ℤ → ℤ) (a b : ℤ × ℤ) (l : List (ℤ × ℤ)) :
    stepSum f (a :: b :: l) = f a b + stepSum f (b :: l) := rfl

theorem stepSum_append_cons (f : ℤ × ℤ → ℤ × ℤ → ℤ) (L : List (ℤ × ℤ)) (a : ℤ × ℤ)
    (R : List (ℤ × ℤ)) :
    stepSum f (L ++ a :: R) = stepSum f (L ++ [a]) + stepSum f (a :: R) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    cases L with
    | nil => simp
    | cons c L =>
      simp only [List.cons_append, stepSum_cons_cons] at ih ⊢
      rw [ih]; ring

 
theorem stepSum_sub (f g : ℤ × ℤ → ℤ × ℤ → ℤ) (l : List (ℤ × ℤ)) :
    stepSum (fun a b => f a b - g a b) l = stepSum f l - stepSum g l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [stepSum_cons_cons] at ih ⊢
      rw [ih]; ring

theorem stepSum_congr_chain {R : ℤ × ℤ → ℤ × ℤ → Prop} {f g : ℤ × ℤ → ℤ × ℤ → ℤ}
    (hfg : ∀ a b, R a b → f a b = g a b) :
    ∀ {l : List (ℤ × ℤ)}, l.IsChain R → stepSum f l = stepSum g l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [List.isChain_cons_cons] at h
    simp only [stepSum_cons_cons]
    rw [hfg a b h.1, stepSum_congr_chain hfg h.2]

theorem stepSum_eq_zero_of_mem {f : ℤ × ℤ → ℤ × ℤ → ℤ} :
    ∀ {l : List (ℤ × ℤ)}, (∀ a ∈ l, ∀ b ∈ l, f a b = 0) → stepSum f l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [stepSum_cons_cons]
    rw [h a (by simp) b (by simp), stepSum_eq_zero_of_mem (l := b :: l)
      (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]
    simp

theorem stepSum_telescope (G : ℤ × ℤ → ℤ) :
    ∀ (a : ℤ × ℤ) (l : List (ℤ × ℤ)),
      stepSum (fun x y => G y - G x) (a :: l) = G ((a :: l).getLast (by simp)) - G a
  | a, [] => by simp
  | a, b :: l => by
    simp only [stepSum_cons_cons]
    rw [stepSum_telescope G b l]
    simp only [List.getLast_cons_cons]
    ring

 
def IsClosed (l : List (ℤ × ℤ)) : Prop := l ≠ [] ∧ l.head? = l.getLast?

theorem stepSum_telescope_closed (G : ℤ × ℤ → ℤ) {l : List (ℤ × ℤ)} (hl : IsClosed l) :
    stepSum (fun x y => G y - G x) l = 0 := by
  obtain ⟨hne, hcl⟩ := hl
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [stepSum_telescope]
  have : (a :: l').getLast (by simp) = a := by
    have h := hcl
    rw [List.head?_cons, List.getLast?_eq_getLast (by simp)] at h
    exact (Option.some_injective _ h).symm
  rw [this]; ring

 

 
def seg (w : ℕ → ℤ × ℤ) (s d : ℕ) : List (ℤ × ℤ) := (List.range (d + 1)).map (fun i => w (s + i))

theorem seg_succ (w : ℕ → ℤ × ℤ) (s d : ℕ) :
    seg w s (d + 1) = seg w s d ++ [w (s + (d + 1))] := by
  unfold seg
  rw [List.range_succ, List.map_append]
  simp

theorem seg_ne_nil (w : ℕ → ℤ × ℤ) (s d : ℕ) : seg w s d ≠ [] := by
  simp [seg]

theorem mem_seg {w : ℕ → ℤ × ℤ} {s d : ℕ} {v : ℤ × ℤ} :
    v ∈ seg w s d ↔ ∃ i ≤ d, w (s + i) = v := by
  simp only [seg, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩

theorem seg_head? (w : ℕ → ℤ × ℤ) (s d : ℕ) : (seg w s d).head? = some (w s) := by
  simp [seg, List.range_succ_eq_map]

theorem seg_getLast? (w : ℕ → ℤ × ℤ) (s d : ℕ) : (seg w s d).getLast? = some (w (s + d)) := by
  cases d with
  | zero => simp [seg]
  | succ d => rw [seg_succ, List.getLast?_append]; simp

theorem seg_zero (w : ℕ → ℤ × ℤ) (s : ℕ) : seg w s 0 = [w s] := by simp [seg]

theorem stepSum_append_singleton (f : ℤ × ℤ → ℤ × ℤ → ℤ) (X : List (ℤ × ℤ)) (hX : X ≠ [])
    (b : ℤ × ℤ) : stepSum f (X ++ [b]) = stepSum f X + f (X.getLast hX) b := by
  obtain ⟨L, x, rfl⟩ : ∃ L x, X = L ++ [x] := by
    rcases List.eq_nil_or_concat X with h | h
    · exact absurd h hX
    · obtain ⟨L, x, h⟩ := h; exact ⟨L, x, by rw [h, List.concat_eq_append]⟩
  rw [List.append_assoc, List.singleton_append, stepSum_append_cons]
  simp

theorem stepSum_seg (f : ℤ × ℤ → ℤ × ℤ → ℤ) (w : ℕ → ℤ × ℤ) (s d : ℕ) :
    stepSum f (seg w s d) = ∑ i ∈ range d, f (w (s + i)) (w (s + i + 1)) := by
  induction d with
  | zero => simp [seg_zero]
  | succ d ih =>
    rw [sum_range_succ, ← ih, seg_succ, stepSum_append_singleton f _ (seg_ne_nil w s d)]
    have hl : (seg w s d).getLast (seg_ne_nil w s d) = w (s + d) := by
      have := seg_getLast? w s d
      rw [List.getLast?_eq_getLast (seg_ne_nil w s d)] at this
      exact Option.some_injective _ this
    rw [hl]
    congr 3

theorem seg_isChain {R : ℤ × ℤ → ℤ × ℤ → Prop} (w : ℕ → ℤ × ℤ) (hw : ∀ k, R (w k) (w (k + 1)))
    (s d : ℕ) : (seg w s d).IsChain R := by
  unfold seg
  rw [List.isChain_map, List.isChain_range]
  intro m _
  exact hw (s + m)

 

 

def crossVal (c a b : ℤ × ℤ) : ℤ :=
  if a.2 = b.2 ∧ c.2 < a.2 ∧ a.1 = c.1 ∧ b.1 = c.1 + 1 then 1
  else if a.2 = b.2 ∧ c.2 < a.2 ∧ a.1 = c.1 + 1 ∧ b.1 = c.1 then -1 else 0

 
def wind (c : ℤ × ℤ) (l : List (ℤ × ℤ)) : ℤ := stepSum (crossVal c) l

 
def edgeV (c a b : ℤ × ℤ) : ℤ :=
  if a = (c.1, c.2 + 1) ∧ b = (c.1 + 1, c.2 + 1) then 1
  else if a = (c.1 + 1, c.2 + 1) ∧ b = (c.1, c.2 + 1) then -1 else 0

theorem crossVal_sub_up (c a b : ℤ × ℤ) :
    crossVal c a b - crossVal (c.1, c.2 + 1) a b = edgeV c a b := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [crossVal, edgeV, Prod.mk.injEq]
  split_ifs <;> omega

 

def colInd (c v : ℤ × ℤ) : ℤ := if v.1 = c.1 + 1 ∧ c.2 < v.2 then 1 else 0

def edgeH (c a b : ℤ × ℤ) : ℤ :=
  if a = (c.1 + 1, c.2) ∧ b = (c.1 + 1, c.2 + 1) then 1
  else if a = (c.1 + 1, c.2 + 1) ∧ b = (c.1 + 1, c.2) then -1 else 0

theorem crossVal_sub_right (c a b : ℤ × ℤ) (hab : latticeAdjacent a b) :
    crossVal c a b - crossVal (c.1 + 1, c.2) a b = (colInd c b - colInd c a) - edgeH c a b := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [latticeAdjacent] at hab
  simp only [crossVal, colInd, edgeH, Prod.mk.injEq]
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    subst h1 h2 <;> split_ifs <;> omega

theorem wind_eq_up {l : List (ℤ × ℤ)} (c : ℤ × ℤ) (hz : (c.1, c.2 + 1) ∉ l) :
    wind c l = wind (c.1, c.2 + 1) l := by
  have h := stepSum_sub (crossVal c) (crossVal (c.1, c.2 + 1)) l
  have h0 : stepSum (fun a b => crossVal c a b - crossVal (c.1, c.2 + 1) a b) l = 0 := by
    apply stepSum_eq_zero_of_mem
    intro a ha b hb
    rw [crossVal_sub_up]
    unfold edgeV
    split_ifs with h1 h2
    · exact absurd (h1.1 ▸ ha) hz
    · exact absurd (h2.2 ▸ hb) hz
    · rfl
  unfold wind; linarith

theorem wind_eq_right {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent) (hcl : IsClosed l)
    (c : ℤ × ℤ) (hz : (c.1 + 1, c.2) ∉ l) :
    wind c l = wind (c.1 + 1, c.2) l := by
  have h := stepSum_sub (crossVal c) (crossVal (c.1 + 1, c.2)) l
  have h1 : stepSum (fun a b => crossVal c a b - crossVal (c.1 + 1, c.2) a b) l =
      stepSum (fun a b => (colInd c b - colInd c a) - edgeH c a b) l :=
    stepSum_congr_chain (fun a b hab => crossVal_sub_right c a b hab) hchain
  have h2 := stepSum_sub (fun a b => colInd c b - colInd c a) (edgeH c) l
  have h3 := stepSum_telescope_closed (colInd c) hcl
  have h4 : stepSum (edgeH c) l = 0 := by
    apply stepSum_eq_zero_of_mem
    intro a ha b hb
    unfold edgeH
    split_ifs with e1 e2
    · exact absurd (e1.1 ▸ ha) hz
    · exact absurd (e2.2 ▸ hb) hz
    · rfl
  unfold wind; linarith

 
theorem wind_eq_of_adj {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent) (hcl : IsClosed l)
    {z z' : ℤ × ℤ} (hzz' : latticeAdjacent z z') (hz : z ∉ l) (hz' : z' ∉ l) :
    wind z l = wind z' l := by
  simp only [latticeAdjacent] at hzz'
  rcases hzz' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e : z' = (z.1 + 1, z.2) := Prod.ext h1 h2
    subst e
    exact wind_eq_right hchain hcl z hz'
  · have e : z' = (z.1 - 1, z.2) := Prod.ext h1 h2
    subst e
    have := wind_eq_right hchain hcl (z.1 - 1, z.2) (by simpa using hz)
    simpa using this.symm
  · have e : z' = (z.1, z.2 + 1) := Prod.ext h1 h2
    subst e
    exact wind_eq_up z hz'
  · have e : z' = (z.1, z.2 - 1) := Prod.ext h1 h2
    subst e
    have := wind_eq_up (l := l) (z.1, z.2 - 1) (by simpa using hz)
    simpa using this.symm

 
theorem wind_eq_along {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent) (hcl : IsClosed l) :
    ∀ (q : List (ℤ × ℤ)) (a : ℤ × ℤ), (a :: q).IsChain latticeAdjacent →
      (∀ v ∈ a :: q, v ∉ l) → wind a l = wind ((a :: q).getLast (by simp)) l
  | [], a, _, _ => by simp
  | b :: q, a, hq, hav => by
    rw [List.isChain_cons_cons] at hq
    rw [wind_eq_of_adj hchain hcl hq.1 (hav a (by simp)) (hav b (by simp)),
      wind_eq_along hchain hcl q b hq.2 (fun v hv => hav v (List.mem_cons_of_mem _ hv))]
    simp

theorem wind_eq_along_fun {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent) (hcl : IsClosed l)
    (w : ℕ → ℤ × ℤ) (hw : ∀ k, latticeAdjacent (w k) (w (k + 1))) (s d : ℕ)
    (hout : ∀ i ≤ d, w (s + i) ∉ l) : wind (w s) l = wind (w (s + d)) l := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [ih (fun i hi => hout i (by omega))]
    exact wind_eq_of_adj hchain hcl (hw (s + d)) (hout d (by omega)) (hout (d + 1) le_rfl)

 

theorem crossVal_eq_zero_of_right (c a b : ℤ × ℤ) (ha : c.1 + 1 ≤ a.1) (hb : c.1 + 1 ≤ b.1) :
    crossVal c a b = 0 := by
  unfold crossVal; split_ifs <;> omega

theorem crossVal_eq_zero_of_left (c a b : ℤ × ℤ) (ha : a.1 ≤ c.1) (hb : b.1 ≤ c.1) :
    crossVal c a b = 0 := by
  unfold crossVal; split_ifs <;> omega

theorem crossVal_eq_zero_of_below (c a b : ℤ × ℤ) (ha : a.2 ≤ c.2) :
    crossVal c a b = 0 := by
  unfold crossVal; split_ifs <;> omega

theorem crossVal_eq_zero_of_vertical (c a b : ℤ × ℤ) (h : a.2 ≠ b.2) : crossVal c a b = 0 := by
  unfold crossVal; split_ifs <;> simp_all

 
theorem crossVal_eq_of_above (c a b : ℤ × ℤ) (hab : latticeAdjacent a b) (ha : c.2 < a.2) :
    crossVal c a b = (if c.1 + 1 ≤ b.1 then 1 else 0) - (if c.1 + 1 ≤ a.1 then 1 else 0) := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [latticeAdjacent] at hab
  simp only at ha
  simp only [crossVal]
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    subst h1 h2 <;> split_ifs <;> omega

theorem wind_eq_zero_of_right {c : ℤ × ℤ} {l : List (ℤ × ℤ)} (h : ∀ a ∈ l, c.1 + 1 ≤ a.1) :
    wind c l = 0 :=
  stepSum_eq_zero_of_mem (fun a ha b hb => crossVal_eq_zero_of_right c a b (h a ha) (h b hb))

theorem wind_eq_zero_of_left {c : ℤ × ℤ} {l : List (ℤ × ℤ)} (h : ∀ a ∈ l, a.1 ≤ c.1) :
    wind c l = 0 :=
  stepSum_eq_zero_of_mem (fun a ha b hb => crossVal_eq_zero_of_left c a b (h a ha) (h b hb))

theorem wind_eq_zero_of_below {c : ℤ × ℤ} {l : List (ℤ × ℤ)} (h : ∀ a ∈ l, a.2 ≤ c.2) :
    wind c l = 0 :=
  stepSum_eq_zero_of_mem (fun a ha _ _ => crossVal_eq_zero_of_below c a _ (h a ha))

 

theorem wind_eq_shift_x {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent) (hcl : IsClosed l)
    (x y : ℤ) (d : ℕ) (hout : ∀ i ≤ d, (x + i, y) ∉ l) : wind (x, y) l = wind (x + d, y) l := by
  have := wind_eq_along_fun hchain hcl (fun i => (x + i, y))
    (fun k => by simp [latticeAdjacent]; omega) 0 d (by simpa using hout)
  simpa using this

theorem wind_eq_shift_y {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent) (hcl : IsClosed l)
    (x y : ℤ) (d : ℕ) (hout : ∀ i ≤ d, (x, y + i) ∉ l) : wind (x, y) l = wind (x, y + d) l := by
  have := wind_eq_along_fun hchain hcl (fun i => (x, y + i))
    (fun k => by simp [latticeAdjacent]; omega) 0 d (by simpa using hout)
  simpa using this

 

 
theorem wind_eq_origin_of_near {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent)
    (hcl : IsClosed l) {r₁ : ℤ} (hinner : ∀ v : ℤ × ℤ, |v.1| ≤ r₁ → |v.2| ≤ r₁ → v ∉ l)
    (a1 a2 : ℤ) (ha1 : |a1| ≤ r₁) (ha2 : |a2| ≤ r₁) : wind (a1, a2) l = wind (0, 0) l := by
  have ha1' := abs_le.mp ha1
  have ha2' := abs_le.mp ha2
  have hx : wind (a1, a2) l = wind (0, a2) l := by
    rcases le_total a1 0 with h | h
    · have := wind_eq_shift_x hchain hcl a1 a2 (-a1).toNat (fun i hi =>
        hinner _ (by show |a1 + (i : ℤ)| ≤ r₁; rw [abs_le]; constructor <;> omega) ha2)
      rw [this]; congr 2; omega
    · have := wind_eq_shift_x hchain hcl 0 a2 a1.toNat (fun i hi =>
        hinner _ (by show |0 + (i : ℤ)| ≤ r₁; rw [abs_le]; constructor <;> omega) ha2)
      rw [this]; congr 2; omega
  have hy : wind (0, a2) l = wind (0, 0) l := by
    rcases le_total a2 0 with h | h
    · have := wind_eq_shift_y hchain hcl 0 a2 (-a2).toNat (fun i hi =>
        hinner _ (by show |(0 : ℤ)| ≤ r₁; simp; omega)
          (by show |a2 + (i : ℤ)| ≤ r₁; rw [abs_le]; constructor <;> omega))
      rw [this]; congr 2; omega
    · have := wind_eq_shift_y hchain hcl 0 0 a2.toNat (fun i hi =>
        hinner _ (by show |(0 : ℤ)| ≤ r₁; simp; omega)
          (by show |0 + (i : ℤ)| ≤ r₁; rw [abs_le]; constructor <;> omega))
      rw [this]; congr 2; omega
  rw [hx, hy]

 
theorem wind_eq_zero_of_far {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent)
    (hcl : IsClosed l) {ρ₂ r₂ : ℤ} (hout : ∀ a ∈ l, |a.1| ≤ ρ₂ ∧ |a.2| ≤ ρ₂)
    (hr₂ : ρ₂ < r₂) (b1 b2 : ℤ) (hb : r₂ ≤ |b1| ∨ r₂ ≤ |b2|) : wind (b1, b2) l = 0 := by
  have hX : ∀ v ∈ l, -ρ₂ ≤ v.1 ∧ v.1 ≤ ρ₂ := fun v hv => abs_le.mp (hout v hv).1
  have hY : ∀ v ∈ l, -ρ₂ ≤ v.2 ∧ v.2 ≤ ρ₂ := fun v hv => abs_le.mp (hout v hv).2
  rcases hb with hb | hb
  · rcases le_or_gt 0 b1 with h | h
    · rw [abs_of_nonneg h] at hb
      exact wind_eq_zero_of_left (fun v hv => by have := hX v hv; show v.1 ≤ b1; omega)
    · rw [abs_of_neg h] at hb
      exact wind_eq_zero_of_right (fun v hv => by have := hX v hv; show b1 + 1 ≤ v.1; omega)
  · rcases le_or_gt 0 b2 with h | h
    · rw [abs_of_nonneg h] at hb
      exact wind_eq_zero_of_below (fun v hv => by have := hY v hv; show v.2 ≤ b2; omega)
    · rw [abs_of_neg h] at hb
      rcases le_total ρ₂ b1 with h1 | h1
      · exact wind_eq_zero_of_left (fun v hv => by have := hX v hv; show v.1 ≤ b1; omega)
      · have hmove := wind_eq_shift_x hchain hcl b1 b2 (ρ₂ - b1).toNat (by
          intro i _ hv
          have := hY _ hv
          simp only at this
          omega)
        rw [hmove]
        exact wind_eq_zero_of_left (fun v hv => by
          have := hX v hv; show v.1 ≤ b1 + ((ρ₂ - b1).toNat : ℤ); omega)

 

theorem blocking {l : List (ℤ × ℤ)} (hchain : l.IsChain latticeAdjacent) (hcl : IsClosed l)
    {ρ₁ ρ₂ r₁ r₂ : ℤ} (hout : ∀ a ∈ l, |a.1| ≤ ρ₂ ∧ |a.2| ≤ ρ₂)
    (hin : ∀ a ∈ l, ρ₁ ≤ |a.1| ∨ ρ₁ ≤ |a.2|) (hw : wind (0, 0) l ≠ 0)
    (hr₁ : r₁ < ρ₁) (hr₂ : ρ₂ < r₂)
    (a : ℤ × ℤ) (q : List (ℤ × ℤ)) (hq : (a :: q).IsChain latticeAdjacent)
    (ha : |a.1| ≤ r₁ ∧ |a.2| ≤ r₁)
    (hb : r₂ ≤ |((a :: q).getLast (by simp)).1| ∨ r₂ ≤ |((a :: q).getLast (by simp)).2|) :
    ∃ v ∈ a :: q, v ∈ l := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hinner : ∀ v : ℤ × ℤ, |v.1| ≤ r₁ → |v.2| ≤ r₁ → v ∉ l := by
    intro v h1 h2 hv
    rcases hin v hv with h | h <;> omega
  have hcst := wind_eq_along hchain hcl q a hq (fun v hv hvl => hcon v hv hvl)
  have hA := wind_eq_origin_of_near hchain hcl hinner a.1 a.2 ha.1 ha.2
  have hB := wind_eq_zero_of_far hchain hcl hout hr₂ _ _ hb
  simp only [Prod.mk.eta] at hA hB
  rw [hA, hB] at hcst
  exact hw hcst

end SupercriticalLQGUniqueness.B2.QPos.P3
