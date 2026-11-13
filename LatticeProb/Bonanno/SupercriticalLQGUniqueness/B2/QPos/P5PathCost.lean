/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5PathCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5Geometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5DisjointCosts

 











set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

 
def fwdPath {α : Type*} (γ : List α) (d : α) (a : ℕ) (i : ℕ) : α := γ.getD (a + i) d

 
def bwdPath {α : Type*} (γ : List α) (d : α) (a : ℕ) (i : ℕ) : α := γ.getD (a - i) d

theorem getD_eq_getElem' {α : Type*} (γ : List α) (d : α) {j : ℕ} (hj : j < γ.length) :
    γ.getD j d = γ[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem list_sum_eq_range {α : Type*} (γ : List α) (d : α) (f : α → ℝ) :
    (γ.map f).sum = ∑ j ∈ range γ.length, f (γ.getD j d) := by
  induction γ with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

 




theorem segments_cost {n : ℕ} (z : ℤ × ℤ) (γ : List (DGFFSite n)) (d : DGFFSite n)
    (w : DGFFSite n → ℝ) (hw : ∀ c, 0 ≤ w c) (φ : ℕ → ℕ) (N : ℕ)
    (hφ : ∀ i ≤ N, φ i < γ.length) (hinj : ∀ i ≤ N, ∀ j ≤ N, φ i = φ j → i = j)
    (VG : Finset ℕ) (hVG : ∀ k ∈ VG, k ≤ n) (R' : ℝ)
    (seg : ∀ k ∈ VG, ∃ s t : ℕ, s ≤ t ∧ t ≤ N ∧
      (∀ i, s ≤ i → i ≤ t → AnnAt n z k (γ.getD (φ i) d)) ∧
      R' ≤ ∑ i ∈ Icc s t, w (γ.getD (φ i) d)) :
    (VG.card : ℝ) * R' ≤ (γ.map w).sum := by
  classical
  choose! s t hst htN hann hR using seg
  set S : ℕ → Finset ℕ := fun k => (Icc (s k) (t k)).image φ
  rw [list_sum_eq_range γ d w]
  apply disjoint_segment_cost_lower VG S (range γ.length) (fun j => w (γ.getD j d)) R'
  · intro k hk l hl hkl
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [S, Finset.mem_image, Finset.mem_Icc] at hj1 hj2
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hj1
    obtain ⟨i', ⟨hi1', hi2'⟩, hii'⟩ := hj2
    have hk' := hann k hk i hi1 hi2
    have hl' := hann l hl i' hi1' hi2'
    rw [hii'] at hl'
    exact annAt_disjoint hkl (hVG k hk) (hVG l hl) hk' hl'
  · intro k hk j hj
    simp only [S, Finset.mem_image, Finset.mem_Icc] at hj
    obtain ⟨i, ⟨_, hi2⟩, rfl⟩ := hj
    exact Finset.mem_range.mpr (hφ i (le_trans hi2 (htN k hk)))
  · intro j _; exact hw _
  · intro k hk
    simp only [S]
    rw [Finset.sum_image]
    · exact hR k hk
    · intro i hi j hj hij
      simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
      exact hinj i (le_trans hi.2 (htN k hk)) j (le_trans hj.2 (htN k hk)) hij

 
theorem fwdPath_adj {n : ℕ} {γ : List (DGFFSite n)} (hγ : γ.IsChain fun x y => latticeAdjacent x.1 y.1)
    (d : DGFFSite n) (a : ℕ) {i : ℕ} (hi : a + i + 1 < γ.length) :
    latticeAdjacent (fwdPath γ d a i).1 (fwdPath γ d a (i + 1)).1 := by
  unfold fwdPath
  rw [getD_eq_getElem' γ d (by omega), getD_eq_getElem' γ d (by omega)]
  have := (List.isChain_iff_getElem.mp hγ) (a + i) hi
  simpa [Nat.add_assoc] using this

 
theorem bwdPath_adj {n : ℕ} {γ : List (DGFFSite n)} (hγ : γ.IsChain fun x y => latticeAdjacent x.1 y.1)
    (d : DGFFSite n) {a : ℕ} (ha : a < γ.length) {i : ℕ} (hi : i < a) :
    latticeAdjacent (bwdPath γ d a i).1 (bwdPath γ d a (i + 1)).1 := by
  unfold bwdPath
  rw [getD_eq_getElem' γ d (by omega), getD_eq_getElem' γ d (by omega)]
  have := (List.isChain_iff_getElem.mp hγ) (a - (i + 1)) (by omega)
  have e : a - (i + 1) + 1 = a - i := by omega
  simp only [e] at this
  exact latticeAdjacent_symm this

 





theorem multi_scale_cost {n : ℕ} (z : ℤ × ℤ) (γ : List (DGFFSite n))
    (hγ : γ.IsChain fun x y => latticeAdjacent x.1 y.1)
    (w : DGFFSite n → ℝ) (hw : ∀ c, 0 ≤ w c) (a : ℕ) (ha : a < γ.length)
    (VG : Finset ℕ) (hVG : ∀ k ∈ VG, k + 4 ≤ n) (R' : ℝ)
    (hnear : ∀ k ∈ VG, latticeRadius (γ[a].1 - z) ≤ dgffInnerRadius (n - k))
    (hfar : (∀ k ∈ VG, dgffOuterRadius (n - k) ≤ latticeRadius ((γ[γ.length - 1]'(by omega)).1 - z)) ∨
      (∀ k ∈ VG, dgffOuterRadius (n - k) ≤ latticeRadius ((γ[0]'(by omega)).1 - z)))
    (hseg : ∀ k ∈ VG, ∀ (q : ℕ → DGFFSite n) (s t : ℕ), s ≤ t →
      (∀ i, s ≤ i → i ≤ t → AnnAt n z k (q i)) →
      IsDGFFAnnulusPath (n - k)
        (List.ofFn fun i : Fin (t - s + 1) => unshiftOr n z k (q (s + i))) →
      R' ≤ ∑ i ∈ Icc s t, w (q i)) :
    (VG.card : ℝ) * R' ≤ (γ.map w).sum := by
  set d := γ[a]
  rcases hfar with hfar | hfar
  · 
    set N := γ.length - 1 - a
    apply segments_cost z γ d w hw (fun i => a + i) N (fun i hi => by omega)
      (fun i _ j _ h => by omega) VG (fun k hk => by have := hVG k hk; omega) R'
    intro k hk
    obtain ⟨s, t, hst, htN, hann, hcross⟩ := scale_crossing (hVG k hk) (fwdPath γ d a) N
      (by unfold fwdPath; rw [add_zero, getD_eq_getElem' γ d ha]; exact hnear k hk)
      (by unfold fwdPath; rw [show a + N = γ.length - 1 by omega, getD_eq_getElem' γ d (by omega)]
          exact hfar k hk)
      (fun i hi => fwdPath_adj hγ d a (by omega))
    exact ⟨s, t, hst, htN, hann, hseg k hk (fwdPath γ d a) s t hst hann hcross⟩
  · 
    apply segments_cost z γ d w hw (fun i => a - i) a (fun i hi => by omega)
      (fun i hi j hj h => by omega) VG (fun k hk => by have := hVG k hk; omega) R'
    intro k hk
    obtain ⟨s, t, hst, htN, hann, hcross⟩ := scale_crossing (hVG k hk) (bwdPath γ d a) a
      (by unfold bwdPath; rw [Nat.sub_zero, getD_eq_getElem' γ d ha]; exact hnear k hk)
      (by unfold bwdPath; rw [Nat.sub_self, getD_eq_getElem' γ d (by omega)]; exact hfar k hk)
      (fun i hi => bwdPath_adj hγ d ha hi)
    exact ⟨s, t, hst, htN, hann, hseg k hk (bwdPath γ d a) s t hst hann hcross⟩

 


theorem crossing_meets_around {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    (γ : List (DGFFSite n)) (hγ : γ.IsChain fun x y => latticeAdjacent x.1 y.1)
    {a b : ℕ} (ha : a < γ.length) (hb : b < γ.length)
    (hnear : latticeRadius (γ[a].1 - z) ≤ dgffInnerRadius (n - k))
    (hfar : dgffOuterRadius (n - k) ≤ latticeRadius (γ[b].1 - z))
    {P : List (DGFFSite (n - k))} (hP : IsDGFFAroundPath (n - k) P) :
    ∃ c ∈ γ, AnnAt n z k c ∧ unshiftOr n z k c ∈ P := by
  set d := γ[a]
  have hk4 := hk.1
  
  obtain ⟨q, N, hq0, hqN, hqadj, hqmem⟩ : ∃ (q : ℕ → DGFFSite n) (N : ℕ),
      latticeRadius ((q 0).1 - z) ≤ dgffInnerRadius (n - k) ∧
      dgffOuterRadius (n - k) ≤ latticeRadius ((q N).1 - z) ∧
      (∀ i < N, latticeAdjacent (q i).1 (q (i + 1)).1) ∧ (∀ i ≤ N, q i ∈ γ) := by
    rcases le_total a b with hab | hab
    · refine ⟨fwdPath γ d a, b - a, ?_, ?_, fun i hi => fwdPath_adj hγ d a (by omega), ?_⟩
      · unfold fwdPath; rw [add_zero, getD_eq_getElem' γ d ha]; exact hnear
      · unfold fwdPath; rw [show a + (b - a) = b by omega, getD_eq_getElem' γ d hb]; exact hfar
      · intro i hi; unfold fwdPath; rw [getD_eq_getElem' γ d (by omega)]
        exact List.getElem_mem _
    · refine ⟨bwdPath γ d a, a - b, ?_, ?_, fun i hi => bwdPath_adj hγ d ha (by omega), ?_⟩
      · unfold bwdPath; rw [Nat.sub_zero, getD_eq_getElem' γ d ha]; exact hnear
      · unfold bwdPath; rw [show a - (a - b) = b by omega, getD_eq_getElem' γ d hb]; exact hfar
      · intro i hi; unfold bwdPath; rw [getD_eq_getElem' γ d (by omega)]
        exact List.getElem_mem _
  obtain ⟨s, t, hst, htN, hann, hcross⟩ := scale_crossing hk4 q N hq0 hqN hqadj
  obtain ⟨c', hc'P, hc'σ⟩ := hP.2.2.2.2 _ hcross
  rw [List.mem_ofFn] at hc'σ
  obtain ⟨i, rfl⟩ := hc'σ
  exact ⟨q (s + i), hqmem _ (by omega), hann _ (by omega) (by omega), hc'P⟩

end SupercriticalLQGUniqueness.B2.QPos.P5
