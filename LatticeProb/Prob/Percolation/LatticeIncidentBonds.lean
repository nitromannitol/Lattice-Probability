import LatticeProb.Graph.Zd
import LatticeProb.ParticleHole

/-!
# All bonds incident to an integer box

The literal neighbor union includes every crossing bond of `[-R,R]^d`.
Its canonical enumeration uses a positive coordinate direction and the lower endpoint.
-/

namespace LatticeProb.Percolation.LatticeIncident

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- All unordered nearest-neighbor bonds with an endpoint in `[-R,R]^d`. -/
def incidentBonds (d R : ℕ) : Finset (Sym2 (Site d)) :=
  (boxFinset (0 : Site d) R).biUnion fun x => (nbrFinset x).image fun y => s(x, y)

/-- The exact coordinate bounds for membership in the centered integer box. -/
theorem mem_centered_box {R : ℕ} {x : Site d} :
    x ∈ boxFinset (0 : Site d) R ↔ ∀ j, -(R : ℤ) ≤ x j ∧ x j ≤ R := by
  simp only [boxFinset, Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply,
    zero_sub, zero_add]

/-- Literal membership is incidence to a box vertex along a lattice edge. -/
theorem mem_incidentBonds {R : ℕ} {e : Sym2 (Site d)} :
    e ∈ incidentBonds d R ↔ ∃ x ∈ boxFinset (0 : Site d) R,
      ∃ y, (lattice d).Adj x y ∧ s(x, y) = e := by
  simp only [incidentBonds, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, y, hy, he⟩
    exact ⟨x, hx, y, Graph.Zd.adj_iff.mpr (Graph.Zd.mem_nbrFinset.mp hy), he⟩
  · rintro ⟨x, hx, y, hy, he⟩
    exact ⟨x, hx, y, Graph.Zd.mem_nbrFinset.mpr (Graph.Zd.adj_iff.mp hy), he⟩

/-- A bond belongs exactly when it is a lattice edge with at least one endpoint in the box. -/
theorem mk_mem_incidentBonds {R : ℕ} {x y : Site d} :
    s(x, y) ∈ incidentBonds d R ↔ (lattice d).Adj x y ∧
      (x ∈ boxFinset (0 : Site d) R ∨ y ∈ boxFinset (0 : Site d) R) := by
  rw [mem_incidentBonds]
  constructor
  · rintro ⟨a, ha, b, hab, he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hab, Or.inl ha⟩
    · exact ⟨hab.symm, Or.inr ha⟩
  · rintro ⟨hxy, hx | hy⟩
    · exact ⟨x, hx, y, hxy, rfl⟩
    · exact ⟨y, hy, x, hxy.symm, Sym2.eq_swap⟩

/-- Lower endpoints for positive `i`-bonds incident to the box. -/
def lowerSites (R : ℕ) (i : Fin d) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc (if j = i then -(R : ℤ) - 1 else -(R : ℤ)) R

/-- Complete coordinate characterization of the lower-endpoint finset. -/
theorem mem_lowerSites {R : ℕ} {i : Fin d} {v : Site d} :
    v ∈ lowerSites R i ↔ ∀ j,
      (if j = i then -(R : ℤ) - 1 else -(R : ℤ)) ≤ v j ∧ v j ≤ R := by
  simp only [lowerSites, Fintype.mem_piFinset, Finset.mem_Icc]

/-- A lower endpoint is allowed exactly when one endpoint of its positive bond is in the box. -/
theorem mem_lowerSites_iff_endpoint {R : ℕ} {i : Fin d} {v : Site d} :
    v ∈ lowerSites R i ↔ v ∈ boxFinset (0 : Site d) R ∨
      v + unit i ∈ boxFinset (0 : Site d) R := by
  classical
  rw [mem_lowerSites, mem_centered_box, mem_centered_box]
  constructor
  · intro hv
    by_cases hi : -(R : ℤ) ≤ v i
    · left
      intro j
      have hj := hv j
      split_ifs at hj with h
      · subst j; exact ⟨hi, hj.2⟩
      · exact hj
    · right
      intro j
      have hj := hv j
      by_cases h : j = i
      · subst j
        simp only [ite_true] at hj
        simp only [Pi.add_apply, unit, Pi.single_eq_same]
        omega
      · simpa only [if_neg h, Pi.add_apply, unit, Pi.single_eq_of_ne h,
          add_zero] using hj
  · rintro (hv | hv) j
    · have hj := hv j
      split_ifs <;> omega
    · have hj := hv j
      by_cases h : j = i
      · subst j
        simp only [Pi.add_apply, unit, Pi.single_eq_same] at hj
        simp only [ite_true]
        omega
      · simpa only [if_neg h, Pi.add_apply, unit, Pi.single_eq_of_ne h,
          add_zero] using hj

/-- The bond encoded by an axis and its lower endpoint. -/
def positiveBond (i : Fin d) (v : Site d) : Sym2 (Site d) := s(v, v + unit i)

/-- Positive bonds have a unique axis and lower endpoint, even as unordered pairs. -/
theorem positiveBond_injective {i j : Fin d} {v w : Site d}
    (h : positiveBond i v = positiveBond j w) : i = j ∧ v = w := by
  classical
  rcases Sym2.eq_iff.mp h with ⟨hvw, htop⟩ | ⟨hvw, htop⟩
  · subst w
    have hu : unit i = unit j := add_left_cancel htop
    have hij : i = j := by
      by_contra hij
      have hc := congrFun hu i
      simp only [unit, Pi.single_eq_same, Pi.single_eq_of_ne hij] at hc
      omega
    exact ⟨hij, rfl⟩
  · have hc := congrFun htop i
    have hb := congrFun hvw i
    simp only [Pi.add_apply, unit, Pi.single_eq_same] at hc hb
    by_cases hij : i = j
    · subst j
      simp only [Pi.single_eq_same] at hb
      omega
    · simp only [Pi.single_eq_of_ne hij] at hb
      omega

/-- The canonical positive-bond enumeration equals the literal incident-neighbor union. -/
theorem incidentBonds_eq_biUnion (R : ℕ) :
    incidentBonds d R = Finset.univ.biUnion
      (fun i : Fin d => (lowerSites R i).image (positiveBond i)) := by
  classical
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro he
    obtain ⟨x, hx, y, hxy, rfl⟩ := mem_incidentBonds.mp he
    obtain ⟨i, rfl | rfl⟩ := Graph.Zd.adj_iff.mp hxy
    · exact ⟨i, x, mem_lowerSites_iff_endpoint.mpr (Or.inl hx), rfl⟩
    · refine ⟨i, x - unit i, mem_lowerSites_iff_endpoint.mpr (Or.inr ?_), ?_⟩
      · simpa only [sub_add_cancel] using hx
      · simp only [positiveBond, sub_add_cancel, Sym2.eq_swap]
  · rintro ⟨i, v, hv, rfl⟩
    apply mk_mem_incidentBonds.mpr
    exact ⟨Graph.Zd.adj_iff.mpr ⟨i, Or.inl rfl⟩,
      mem_lowerSites_iff_endpoint.mp hv⟩

end

end LatticeProb.Percolation.LatticeIncident
