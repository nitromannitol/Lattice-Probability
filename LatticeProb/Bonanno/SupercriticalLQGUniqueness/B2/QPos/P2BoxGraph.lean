/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2BoxGraph at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2EdgeGraph
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFModel

 








set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem WiredConductances.ext' {V : Type*} [Fintype V] {G₁ G₂ : WiredConductances V}
    (he : G₁.edge = G₂.edge) (hb : G₁.boundary = G₂.boundary) : G₁ = G₂ := by
  cases G₁; cases G₂
  simp only at he hb
  subst he hb
  rfl

 
def dirVec : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

theorem mem_interiorSites (n : ℕ) (z : ℤ × ℤ) :
    z ∈ interiorSites n ↔ (-interiorRadius n ≤ z.1 ∧ z.1 ≤ interiorRadius n) ∧
      (-interiorRadius n ≤ z.2 ∧ z.2 ≤ interiorRadius n) := by
  unfold interiorSites
  exact Finset.mem_product.trans (by rw [Finset.mem_Icc, Finset.mem_Icc])

 
def boxNbr (n : ℕ) (z : DGFFSite n) (d : Fin 4) : Option (DGFFSite n) :=
  if h : z.1 + dirVec d ∈ interiorSites n then some ⟨_, h⟩ else none

 
def boxHalfCond (n : ℕ) (h : DGFFSite n × Fin 4) : ℝ :=
  if boxNbr n h.1 h.2 = none then dgffConductance else dgffConductance / 2

theorem dirVec_ne_zero (d : Fin 4) : dirVec d ≠ 0 := by
  fin_cases d <;> simp [dirVec]

 
def boxEdgeGraph (n : ℕ) : EdgeGraph (DGFFSite n) (DGFFSite n × Fin 4) where
  tail h := some h.1
  head h := boxNbr n h.1 h.2
  cond := boxHalfCond n
  cond_pos h := by
    unfold boxHalfCond
    split_ifs
    · exact dgffConductance_pos
    · exact half_pos dgffConductance_pos
  tail_ne_head h := by
    unfold boxNbr
    split_ifs with hm
    · intro heq
      have := congrArg (fun x : Option (DGFFSite n) => x.map Subtype.val) heq
      simp only [Option.map_some, Option.some.injEq] at this
      exact dirVec_ne_zero h.2 (by
        have h' := this
        have : h.1.1 + dirVec h.2 - h.1.1 = 0 := by rw [← h']; simp
        simpa using this)
    · simp

theorem boxNbr_eq_some_iff (n : ℕ) (z w : DGFFSite n) (d : Fin 4) :
    boxNbr n z d = some w ↔ w.1 = z.1 + dirVec d := by
  unfold boxNbr
  split_ifs with hm
  · simp only [Option.some.injEq]
    constructor
    · intro h; rw [← h]
    · intro h; exact Subtype.ext h.symm
  · simp only [reduceCtorEq, false_iff]
    intro h
    exact hm (h ▸ w.2)

theorem boxNbr_eq_none_iff (n : ℕ) (z : DGFFSite n) (d : Fin 4) :
    boxNbr n z d = none ↔ z.1 + dirVec d ∉ interiorSites n := by
  unfold boxNbr
  split_ifs with hm <;> simp [hm]

open Classical in
 
theorem sum_dir_ind (z w : ℤ × ℤ) :
    ∑ d : Fin 4, (if w = z + dirVec d then (1 : ℝ) else 0) =
      if latticeAdjacent z w then 1 else 0 := by
  rw [Fin.sum_univ_four]
  have d0 : dirVec 0 = (1, 0) := rfl
  have d1 : dirVec 1 = (-1, 0) := rfl
  have d2 : dirVec 2 = (0, 1) := rfl
  have d3 : dirVec 3 = (0, -1) := rfl
  rw [d0, d1, d2, d3]
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, add_zero]
  unfold latticeAdjacent
  split_ifs <;> first | (exfalso; omega) | norm_num

open Classical in
theorem boxEdgeGraph_edgeCond (n : ℕ) (z w : DGFFSite n) :
    (boxEdgeGraph n).edgeCond z w = if latticeAdjacent z.1 w.1 then dgffConductance else 0 := by
  have hdir : ∀ a b : DGFFSite n, ∑ d : Fin 4, boxHalfCond n (a, d) * EdgeGraph.ind (boxNbr n a d) b =
      if latticeAdjacent a.1 b.1 then dgffConductance / 2 else 0 := by
    intro a b
    have hd : ∀ d, boxHalfCond n (a, d) * EdgeGraph.ind (boxNbr n a d) b =
        (dgffConductance / 2) * (if b.1 = a.1 + dirVec d then 1 else 0) := by
      intro d
      unfold EdgeGraph.ind
      by_cases h : boxNbr n a d = some b
      · rw [if_pos h, if_pos ((boxNbr_eq_some_iff n a b d).mp h)]
        unfold boxHalfCond
        simp [h]
      · rw [if_neg h, if_neg (fun h' => h ((boxNbr_eq_some_iff n a b d).mpr h'))]
        ring
    rw [Finset.sum_congr rfl (fun d _ => hd d), ← Finset.mul_sum, sum_dir_ind]
    split_ifs <;> ring
  unfold EdgeGraph.edgeCond
  rw [Fintype.sum_prod_type]
  have hx : ∀ x : DGFFSite n, ∑ d : Fin 4, (boxEdgeGraph n).cond (x, d) *
      (EdgeGraph.ind ((boxEdgeGraph n).tail (x, d)) z * EdgeGraph.ind ((boxEdgeGraph n).head (x, d)) w +
        EdgeGraph.ind ((boxEdgeGraph n).tail (x, d)) w * EdgeGraph.ind ((boxEdgeGraph n).head (x, d)) z) =
      (if x = z then ∑ d : Fin 4, boxHalfCond n (z, d) * EdgeGraph.ind (boxNbr n z d) w else 0) +
        (if x = w then ∑ d : Fin 4, boxHalfCond n (w, d) * EdgeGraph.ind (boxNbr n w d) z else 0) := by
    intro x
    have ht : ∀ (d : Fin 4) (y : DGFFSite n),
        EdgeGraph.ind ((boxEdgeGraph n).tail (x, d)) y = if x = y then 1 else 0 := by
      intro d y
      show EdgeGraph.ind (some x) y = _
      unfold EdgeGraph.ind
      simp
    simp only [ht]
    by_cases hxz : x = z <;> by_cases hxw : x = w
    · subst hxz; subst hxw
      simp only [if_true, one_mul, mul_add, Finset.sum_add_distrib]
      rfl
    · subst hxz
      simp only [if_true, if_neg hxw, one_mul, zero_mul, add_zero]
      rfl
    · subst hxw
      simp only [if_true, if_neg hxz, one_mul, zero_mul, zero_add]
      rfl
    · simp only [if_neg hxz, if_neg hxw, zero_mul, add_zero, mul_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), hdir, hdir]
  have hsymm : latticeAdjacent w.1 z.1 ↔ latticeAdjacent z.1 w.1 :=
    ⟨latticeAdjacent_symm, latticeAdjacent_symm⟩
  by_cases hadj : latticeAdjacent z.1 w.1
  · rw [if_pos hadj, if_pos (hsymm.mpr hadj), if_pos hadj]; ring
  · rw [if_neg hadj, if_neg (fun h => hadj (hsymm.mp h)), if_neg hadj]; ring

theorem boxEdgeGraph_bdryCond (n : ℕ) (z : DGFFSite n) :
    (boxEdgeGraph n).bdryCond z = boxBoundaryConductance n z := by
  unfold EdgeGraph.bdryCond
  rw [Fintype.sum_prod_type]
  have hx : ∀ x : DGFFSite n, ∑ d : Fin 4, (boxEdgeGraph n).cond (x, d) *
      (EdgeGraph.ind ((boxEdgeGraph n).tail (x, d)) z *
          (if (boxEdgeGraph n).head (x, d) = none then 1 else 0) +
        (if (boxEdgeGraph n).tail (x, d) = none then 1 else 0) *
          EdgeGraph.ind ((boxEdgeGraph n).head (x, d)) z) =
      if x = z then ∑ d : Fin 4, boxHalfCond n (z, d) *
        (if boxNbr n z d = none then 1 else 0) else 0 := by
    intro x
    have htail : ∀ d : Fin 4, (boxEdgeGraph n).tail (x, d) = some x := fun d => rfl
    have hnone : ∀ d : Fin 4, ¬ ((boxEdgeGraph n).tail (x, d) = none) := fun d => by
      rw [htail]; exact Option.some_ne_none x
    by_cases hxz : x = z
    · subst hxz
      rw [if_pos rfl]
      apply Finset.sum_congr rfl
      intro d _
      rw [if_neg (hnone d), zero_mul, add_zero]
      have hind : EdgeGraph.ind ((boxEdgeGraph n).tail (x, d)) x = 1 := by
        unfold EdgeGraph.ind; rw [htail]; simp
      rw [hind, one_mul]
      have hh : (boxEdgeGraph n).head (x, d) = boxNbr n x d := rfl
      by_cases hb : boxNbr n x d = none
      · rw [if_pos (hh.trans hb), if_pos hb]; rfl
      · rw [if_neg (fun h => hb (hh.symm.trans h)), if_neg hb]; rfl
    · rw [if_neg hxz]
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg (hnone d), zero_mul, add_zero]
      have hind : EdgeGraph.ind ((boxEdgeGraph n).tail (x, d)) z = 0 := by
        unfold EdgeGraph.ind; rw [htail]; simp [hxz]
      rw [hind, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hz := z.2
  rw [mem_interiorSites] at hz
  have hd : ∀ d : Fin 4, boxHalfCond n (z, d) * (if boxNbr n z d = none then 1 else 0) =
      if z.1 + dirVec d ∉ interiorSites n then dgffConductance else 0 := by
    intro d
    unfold boxHalfCond
    simp only
    by_cases h : boxNbr n z d = none
    · rw [if_pos h, if_pos h, if_pos ((boxNbr_eq_none_iff n z d).mp h), mul_one]
    · rw [if_neg h, if_neg h, if_neg (fun h' => h ((boxNbr_eq_none_iff n z d).mpr h')), mul_zero]
  rw [Finset.sum_congr rfl (fun d _ => hd d), Fin.sum_univ_four]
  unfold boxBoundaryConductance
  have d0 : dirVec 0 = (1, 0) := rfl
  have d1 : dirVec 1 = (-1, 0) := rfl
  have d2 : dirVec 2 = (0, 1) := rfl
  have d3 : dirVec 3 = (0, -1) := rfl
  rw [d0, d1, d2, d3]
  simp only [mem_interiorSites, Prod.fst_add, Prod.snd_add]
  have e0 : (¬ ((-interiorRadius n ≤ z.1.1 + 1 ∧ z.1.1 + 1 ≤ interiorRadius n) ∧
      (-interiorRadius n ≤ z.1.2 + 0 ∧ z.1.2 + 0 ≤ interiorRadius n))) ↔
      z.1.1 = interiorRadius n := by constructor <;> intro h <;> omega
  have e1 : (¬ ((-interiorRadius n ≤ z.1.1 + -1 ∧ z.1.1 + -1 ≤ interiorRadius n) ∧
      (-interiorRadius n ≤ z.1.2 + 0 ∧ z.1.2 + 0 ≤ interiorRadius n))) ↔
      z.1.1 = -interiorRadius n := by constructor <;> intro h <;> omega
  have e2 : (¬ ((-interiorRadius n ≤ z.1.1 + 0 ∧ z.1.1 + 0 ≤ interiorRadius n) ∧
      (-interiorRadius n ≤ z.1.2 + 1 ∧ z.1.2 + 1 ≤ interiorRadius n))) ↔
      z.1.2 = interiorRadius n := by constructor <;> intro h <;> omega
  have e3 : (¬ ((-interiorRadius n ≤ z.1.1 + 0 ∧ z.1.1 + 0 ≤ interiorRadius n) ∧
      (-interiorRadius n ≤ z.1.2 + -1 ∧ z.1.2 + -1 ≤ interiorRadius n))) ↔
      z.1.2 = -interiorRadius n := by constructor <;> intro h <;> omega
  rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl, if_congr e3 rfl rfl]
  split_ifs <;> ring

 
theorem boxEdgeGraph_toWired (n : ℕ) : (boxEdgeGraph n).toWired = boxConductances n := by
  apply WiredConductances.ext'
  · funext z w
    change (boxEdgeGraph n).edgeCond z w = _
    rw [boxEdgeGraph_edgeCond]
    rfl
  · funext z
    change (boxEdgeGraph n).bdryCond z = _
    rw [boxEdgeGraph_bdryCond]
    rfl

end SupercriticalLQGUniqueness.B2.QPos
