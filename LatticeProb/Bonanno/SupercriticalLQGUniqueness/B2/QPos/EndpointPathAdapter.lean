/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.EndpointPathAdapter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointExtraction
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFDistance

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem latticeSupRadius_eq_latticeRadius (z : ℤ × ℤ) :
    latticeSupRadius z = (latticeRadius z : ℤ) := by
  simp [latticeSupRadius, latticeRadius]

 


theorem dgff_annulus_subpath_of_full_path
    (n N : ℕ) (p : ℕ → DGFFSite n)
    (hgap : dgffInnerRadius n + 1 < dgffOuterRadius n)
    (hstart : latticeRadius (p 0).1 ≤ dgffInnerRadius n)
    (hend : dgffOuterRadius n ≤ latticeRadius (p N).1)
    (hpath : ∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1)
    (ξ : ℝ) (h : EuclideanSpace ℝ (DGFFSite n)) :
    ∃ q : List (DGFFSite n), IsDGFFAnnulusPath n q ∧
      dgffPathCost n ξ h q ≤
        dgffPathCost n ξ h (List.ofFn fun i : Fin (N + 1) => p i) := by
  have hstart' : latticeSupRadius (p 0).1 ≤ (dgffInnerRadius n : ℤ) := by
    rw [latticeSupRadius_eq_latticeRadius]
    exact_mod_cast hstart
  have hend' : (dgffOuterRadius n : ℤ) ≤ latticeSupRadius (p N).1 := by
    rw [latticeSupRadius_eq_latticeRadius]
    exact_mod_cast hend
  have hgap' : (dgffInnerRadius n : ℤ) + 1 < (dgffOuterRadius n : ℤ) := by
    exact_mod_cast hgap
  obtain ⟨s, t, hs0, hst, htN, hs, ht, hband⟩ :=
    lattice_annular_indices (fun i => (p i).1) N
      (dgffInnerRadius n) (dgffOuterRadius n) hgap' hstart' hend' hpath
  let l : List (DGFFSite n) := List.ofFn fun i : Fin (N + 1) => p i
  let q : List (DGFFSite n) := (l.drop s).take (t - s + 1)
  have hl : l.length = N + 1 := by simp [l]
  have hqLen : q.length = t - s + 1 := by
    simp [q, hl]
    omega
  have hqGet (i : ℕ) (hi : i < q.length) :
      q[i] = p (s + i) := by
    dsimp [q]
    simp only [List.getElem_take, List.getElem_drop]
    simp only [l, List.getElem_ofFn]
  have hchain : q.IsChain (fun z w => latticeAdjacent z.1 w.1) := by
    have hlchain : l.IsChain (fun z w => latticeAdjacent z.1 w.1) := by
      rw [List.isChain_ofFn]
      intro i hi
      simpa using hpath i (by omega)
    exact (hlchain.drop s).take (t - s + 1)
  have hqmem : ∀ z ∈ q, inDGFFAnnulus n z := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    rw [hqGet i hi]
    have hh := hband (s + i) (by omega) (by omega : s + i ≤ t)
    rw [latticeSupRadius_eq_latticeRadius] at hh
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have hqhead : q.head? = some (p s) := by
    have hlen : 0 < q.length := by omega
    have hne : q ≠ [] := by intro he; simp [he] at hlen
    rw [List.head?_eq_some_head hne]
    simp only [List.head_eq_getElem]
    rw [hqGet 0 hlen]
    simp
  have hqlast : q.getLast? = some (p t) := by
    have hlen : 0 < q.length := by omega
    have hne : q ≠ [] := by intro he; simp [he] at hlen
    rw [List.getLast?_eq_some_getLast hne]
    have hidx : q.length - 1 < q.length := by omega
    rw [List.getLast_eq_getElem]
    simpa [hqLen, Nat.add_sub_of_le hst] using hqGet (q.length - 1) hidx
  have hqpath : IsDGFFAnnulusPath n q := by
    refine ⟨hchain, hqmem, p s, p t, hqhead, hqlast, ?_, ?_⟩
    · have hs' := hs
      rw [latticeSupRadius_eq_latticeRadius] at hs'
      exact_mod_cast hs'
    · have ht' := ht
      rw [latticeSupRadius_eq_latticeRadius] at ht'
      exact_mod_cast ht'
  refine ⟨q, hqpath, ?_⟩
  have hdecomp : l = l.take s ++ q ++ (l.drop s).drop (t - s + 1) := by
    calc
      l = l.take s ++ l.drop s := (List.take_append_drop s l).symm
      _ = l.take s ++ ((l.drop s).take (t - s + 1) ++
          (l.drop s).drop (t - s + 1)) := by
            congr 1
            exact (List.take_append_drop (t - s + 1) (l.drop s)).symm
      _ = l.take s ++ q ++ (l.drop s).drop (t - s + 1) := by
            simp [q, List.append_assoc]
  have hcost := dgff_inclusive_subpath_le ξ (fun z : DGFFSite n => h z)
    (l.take s) q ((l.drop s).drop (t - s + 1))
  rw [← hdecomp] at hcost
  simpa [dgffPathCost, l] using hcost

 

theorem dgffAnnulusDistance_le_fullPathCost
    (n N : ℕ) (p : ℕ → DGFFSite n)
    (hgap : dgffInnerRadius n + 1 < dgffOuterRadius n)
    (hstart : latticeRadius (p 0).1 ≤ dgffInnerRadius n)
    (hend : dgffOuterRadius n ≤ latticeRadius (p N).1)
    (hpath : ∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1)
    (ξ : ℝ) (h : EuclideanSpace ℝ (DGFFSite n)) :
    dgffAnnulusDistance n ξ h ≤
      dgffPathCost n ξ h (List.ofFn fun i : Fin (N + 1) => p i) := by
  obtain ⟨q, hq, hcost⟩ :=
    dgff_annulus_subpath_of_full_path n N p hgap hstart hend hpath ξ h
  have hbelow : BddBelow (Set.range
      (fun q : {q : List (DGFFSite n) // IsDGFFAnnulusPath n q} =>
        dgffPathCost n ξ h q.1)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨q, rfl⟩
    exact inclusivePathCost_nonneg _ (fun z => (Real.exp_pos _).le) q.1
  exact (ciInf_le hbelow ⟨q, hq⟩).trans hcost

end SupercriticalLQGUniqueness.B2.QPos
