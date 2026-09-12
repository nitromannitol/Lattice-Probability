/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Dual
import LatticeProb.Lattice.Planar.KingPaths

open Finset

namespace LatticeProb.Lattice.Planar

/-- Counterclockwise rotation of a lattice vector. -/
def rotL' (d : Site) : Site := (-d.2, d.1)

theorem rotL'_rotL' (d : Site) : rotL' (rotL' d) = -d := by
  ext <;> simp [rotL']

/-- The edge boundary of `K`: directed edges from `K` to its complement. -/
def bdry (K : Finset Site) : Finset (Site × Site) :=
  K.biUnion (fun h => ((squareGraph.neighborFinset h).filter (fun x => x ∉ K)).image (fun x => (h, x)))

theorem mem_bdry {K : Finset Site} {e : Site × Site} :
    e ∈ bdry K ↔ e.1 ∈ K ∧ e.2 ∉ K ∧ squareGraph.Adj e.1 e.2 := by
  simp only [bdry, mem_biUnion, mem_image, mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨h, hh, x, ⟨hadj, hx⟩, rfl⟩
    exact ⟨hh, hx, hadj⟩
  · rintro ⟨hh, hx, hadj⟩
    exact ⟨e.1, hh, e.2, ⟨hadj, hx⟩, rfl⟩

/-- The next boundary edge, keeping `K` on the left. -/
def bsucc (K : Finset Site) (e : Site × Site) : Site × Site :=
  let d := e.2 - e.1
  let y := e.1 + rotL' d
  let w := e.2 + rotL' d
  if w ∈ K then (w, e.2) else if y ∈ K then (y, w) else (e.1, y)

/-- Unit steps: `x - h` for adjacent `h, x` is one of the four directions. -/
theorem adj_sub_mem {h x : Site} (hadj : squareGraph.Adj h x) :
    x - h = (1, 0) ∨ x - h = (-1, 0) ∨ x - h = (0, 1) ∨ x - h = (0, -1) := by
  rw [squareGraph_adj] at hadj
  obtain ⟨a, b⟩ := h; obtain ⟨c, d⟩ := x
  simp only [Prod.mk_sub_mk, Prod.mk.injEq]
  simp only at hadj
  rcases abs_cases (a - c) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases abs_cases (b - d) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> omega

theorem adj_of_unit {h x : Site} (hu : x - h = (1, 0) ∨ x - h = (-1, 0) ∨ x - h = (0, 1) ∨ x - h = (0, -1)) :
    squareGraph.Adj h x := by
  rw [squareGraph_adj]
  obtain ⟨a, b⟩ := h; obtain ⟨c, d⟩ := x
  simp only [Prod.mk_sub_mk, Prod.mk.injEq] at hu
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [show a - c = -(c - a) by ring, show b - d = -(d - b) by ring, h1, h2] <;> simp

theorem rotL'_unit {d : Site} (hd : d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) :
    rotL' d = (1, 0) ∨ rotL' d = (-1, 0) ∨ rotL' d = (0, 1) ∨ rotL' d = (0, -1) := by
  rcases hd with rfl | rfl | rfl | rfl <;> simp [rotL']

theorem bsucc_mem {K : Finset Site} {e : Site × Site} (he : e ∈ bdry K) : bsucc K e ∈ bdry K := by
  obtain ⟨hh, hx, hadj⟩ := mem_bdry.1 he
  have hu := adj_sub_mem hadj
  have hru := rotL'_unit hu
  unfold bsucc
  simp only
  split_ifs with hw hy
  · refine mem_bdry.2 ⟨hw, hx, adj_of_unit ?_⟩
    have : e.2 - (e.2 + rotL' (e.2 - e.1)) = - rotL' (e.2 - e.1) := by abel
    rw [this]
    rcases hru with h | h | h | h <;> rw [h] <;> simp
  · refine mem_bdry.2 ⟨hy, hw, adj_of_unit ?_⟩
    have : e.2 + rotL' (e.2 - e.1) - (e.1 + rotL' (e.2 - e.1)) = e.2 - e.1 := by abel
    rw [this]; exact hu
  · refine mem_bdry.2 ⟨hh, hy, adj_of_unit ?_⟩
    have : e.1 + rotL' (e.2 - e.1) - e.1 = rotL' (e.2 - e.1) := by abel
    rw [this]; exact hru

/-- The outer endpoints of consecutive boundary edges are equal or king-adjacent. -/
theorem bsucc_outer {K : Finset Site} (e : Site × Site) (he : e ∈ bdry K) :
    (bsucc K e).2 = e.2 ∨ KingStep e.2 (bsucc K e).2 := by
  obtain ⟨-, -, hadj⟩ := mem_bdry.1 he
  have hu := adj_sub_mem hadj
  unfold bsucc
  simp only
  split_ifs with hw hy
  · exact Or.inl rfl
  · right
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg (fun p : Site => p - e.2) h
      simp only [sub_self, add_sub_cancel_left] at this
      rcases hu with h' | h' | h' | h' <;> rw [h'] at this <;> simp [rotL', Prod.ext_iff] at this
    · rcases hu with h' | h' | h' | h' <;> rw [h'] <;> simp [linf, rotL']
  · right
    refine ⟨?_, ?_⟩
    · intro h
      have : e.2 - e.1 = rotL' (e.2 - e.1) := by
        have := congrArg (fun p : Site => p - e.1) h
        simpa using this
      rcases hu with h' | h' | h' | h' <;> rw [h'] at this <;> simp [rotL', Prod.ext_iff] at this
    · have : e.1 + rotL' (e.2 - e.1) - e.2 = rotL' (e.2 - e.1) - (e.2 - e.1) := by abel
      rw [this]
      rcases hu with h' | h' | h' | h' <;> rw [h'] <;> simp [linf, rotL']

/-- The successor map is injective on the boundary. -/
theorem bsucc_injOn (K : Finset Site) : Set.InjOn (bsucc K) ↑(bdry K) := by
  intro e₁ he₁ e₂ he₂ h
  obtain ⟨hh₁, hx₁, hadj₁⟩ := mem_bdry.1 (Finset.mem_coe.1 he₁)
  obtain ⟨hh₂, hx₂, hadj₂⟩ := mem_bdry.1 (Finset.mem_coe.1 he₂)
  have hu₁ := adj_sub_mem hadj₁
  have hu₂ := adj_sub_mem hadj₂
  obtain ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ := e₁
  obtain ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ := e₂
  simp only [Prod.mk_sub_mk, Prod.mk.injEq] at hu₁ hu₂
  simp only [bsucc, rotL', Prod.mk_sub_mk, Prod.mk_add_mk] at h hh₁ hx₁ hh₂ hx₂
  simp only [Prod.mk.injEq]
  by_cases hw₁ : (c₁ + -(d₁ - b₁), d₁ + (c₁ - a₁)) ∈ K <;>
  by_cases hy₁ : (a₁ + -(d₁ - b₁), b₁ + (c₁ - a₁)) ∈ K <;>
  by_cases hw₂ : (c₂ + -(d₂ - b₂), d₂ + (c₂ - a₂)) ∈ K <;>
  by_cases hy₂ : (a₂ + -(d₂ - b₂), b₂ + (c₂ - a₂)) ∈ K <;>
  simp only [hw₁, hy₁, hw₂, hy₂, if_true, if_false, Prod.mk.injEq] at h <;>
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h <;>
  first
  | (refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega)
  | (exfalso; apply hx₂; convert hh₁ using 2 <;> omega)
  | (exfalso; apply hx₁; convert hh₂ using 2 <;> omega)
  | (exfalso; apply hw₂; convert hh₁ using 2 <;> omega)
  | (exfalso; apply hy₂; convert hh₁ using 2 <;> omega)
  | (exfalso; apply hw₁; convert hh₂ using 2 <;> omega)

/-- The faces at the two ends of the dual edge of a boundary edge. -/
def f0 (e : Site × Site) : Site := rightFace e.1 (dirOf (e.2 - e.1))

def f1 (e : Site × Site) : Site := leftFace e.1 (dirOf (e.2 - e.1))

/-- Clockwise rotation. -/
def rotR' (d : Site) : Site := (d.2, -d.1)

theorem rotR'_rotL' (d : Site) : rotR' (rotL' d) = d := by
  ext <;> simp [rotR', rotL']

theorem f1_sub_f0 {e : Site × Site} (hadj : squareGraph.Adj e.1 e.2) :
    f1 e - f0 e = rotL' (e.2 - e.1) := by
  have hu := adj_sub_mem hadj
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  simp only [Prod.mk_sub_mk] at hu ⊢
  simp only [f0, f1, Prod.mk_sub_mk]
  rcases hu with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h
  · have hc : c = a + 1 := by omega
    have hd : d = b := by omega
    subst hc hd
    simp [leftFace, rightFace, dirOf, dirVec, rotL']
  · have hc : c = a - 1 := by omega
    have hd : d = b := by omega
    subst hc hd
    simp [leftFace, rightFace, dirOf, dirVec, rotL']
  · have hc : c = a := by omega
    have hd : d = b + 1 := by omega
    subst hc hd
    simp [leftFace, rightFace, dirOf, dirVec, rotL']
  · have hc : c = a := by omega
    have hd : d = b - 1 := by omega
    subst hc hd
    simp [leftFace, rightFace, dirOf, dirVec, rotL']

theorem sub_eq_rotR' {e : Site × Site} (hadj : squareGraph.Adj e.1 e.2) :
    e.2 - e.1 = rotR' (f1 e - f0 e) := by
  rw [f1_sub_f0 hadj, rotR'_rotL']

/-- The next boundary edge starts at the face where the current one ends. -/
theorem f0_bsucc {K : Finset Site} {e : Site × Site} (he : e ∈ bdry K) :
    f0 (bsucc K e) = f1 e := by
  obtain ⟨-, -, hadj⟩ := mem_bdry.1 he
  have hu := adj_sub_mem hadj
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  simp only [Prod.mk_sub_mk] at hu
  rcases hu with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h
  · have hc : c = a + 1 := by omega
    have hd : d = b := by omega
    subst hc hd
    unfold bsucc; simp only [rotL', Prod.mk_sub_mk, Prod.mk_add_mk]
    split_ifs <;> simp [f0, f1, leftFace, rightFace, dirOf, dirVec]
  · have hc : c = a - 1 := by omega
    have hd : d = b := by omega
    subst hc hd
    unfold bsucc; simp only [rotL', Prod.mk_sub_mk, Prod.mk_add_mk]
    (split_ifs <;> simp [f0, f1, leftFace, rightFace, dirOf, dirVec]); omega
  · have hc : c = a := by omega
    have hd : d = b + 1 := by omega
    subst hc hd
    unfold bsucc; simp only [rotL', Prod.mk_sub_mk, Prod.mk_add_mk]
    split_ifs <;> simp [f0, f1, leftFace, rightFace, dirOf, dirVec] <;> omega
  · have hc : c = a := by omega
    have hd : d = b - 1 := by omega
    subst hc hd
    unfold bsucc; simp only [rotL', Prod.mk_sub_mk, Prod.mk_add_mk]
    (split_ifs <;> simp [f0, f1, leftFace, rightFace, dirOf, dirVec]); omega

/-- The outer normals over an invariant set of boundary edges sum to zero. -/
theorem sum_bdry_eq_zero (K : Finset Site) (S : Finset (Site × Site)) (hS : S ⊆ bdry K)
    (hinv : ∀ e ∈ S, bsucc K e ∈ S) : ∑ e ∈ S, (e.2 - e.1) = 0 := by
  have hadj : ∀ e ∈ S, squareGraph.Adj e.1 e.2 := fun e he => (mem_bdry.1 (hS he)).2.2
  have himg : S.image (bsucc K) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
      exact hinv e he
    · rw [Finset.card_image_of_injOn ((bsucc_injOn K).mono (Finset.coe_subset.2 hS))]
  have hsum : ∑ e ∈ S, f1 e = ∑ e ∈ S, f0 e := by
    calc ∑ e ∈ S, f1 e = ∑ e ∈ S, f0 (bsucc K e) := Finset.sum_congr rfl (fun e he => (f0_bsucc (hS he)).symm)
      _ = ∑ e ∈ S.image (bsucc K), f0 e :=
          (Finset.sum_image ((bsucc_injOn K).mono (Finset.coe_subset.2 hS))).symm
      _ = ∑ e ∈ S, f0 e := by rw [himg]
  have hrot : ∀ (T : Finset (Site × Site)) (g : Site × Site → Site),
      ∑ e ∈ T, rotR' (g e) = rotR' (∑ e ∈ T, g e) := by
    intro T g
    simp only [rotR', Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, Finset.sum_neg_distrib]
    simp
  calc ∑ e ∈ S, (e.2 - e.1) = ∑ e ∈ S, rotR' (f1 e - f0 e) :=
        Finset.sum_congr rfl (fun e he => sub_eq_rotR' (hadj e he))
    _ = rotR' (∑ e ∈ S, (f1 e - f0 e)) := hrot S _
    _ = rotR' 0 := by rw [Finset.sum_sub_distrib, hsum, sub_self]
    _ = 0 := rfl

end LatticeProb.Lattice.Planar
