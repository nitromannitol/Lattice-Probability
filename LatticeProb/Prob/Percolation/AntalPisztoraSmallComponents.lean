import LatticeProb.Prob.Percolation.AntalPisztoraCentres
import LatticeProb.Prob.Percolation.AntalPisztoraExit
import LatticeProb.Walk.Energy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

/-- The actual lattice cube is the integer rectangle used by first-exit walks. -/
theorem latticeCube_mem_integer_rectangle {d : ℕ} (c : Fin d → ℝ)
    (r : Set.Ioi (0 : ℝ)) (v : Vertex d) :
    v ∈ latticeCube c r ↔
      ∀ i, ⌈c i - r.val⌉ ≤ v i ∧ v i ≤ ⌊c i + r.val⌋ := by
  exact (Set.Finite.mem_toFinset (finite_latticeCubeSet c r)).trans
    (mem_latticeCubeSet_iff c r v)

/-- The integer endpoint interval is wide enough for a radius-h clamp. -/
theorem latticeCube_integer_width {d : ℕ} (c : Fin d → ℝ)
    (r : Set.Ioi (0 : ℝ)) (h : ℤ) (hr : (h : ℝ) + 1 ≤ r.val) :
    ∀ i, ⌈c i - r.val⌉ + 2 * h ≤ ⌊c i + r.val⌋ := by
  intro i
  have hc := Int.ceil_lt_add_one (c i - r.val)
  have hf := Int.lt_floor_add_one (c i + r.val)
  have hi : ((⌈c i - r.val⌉ : ℤ) : ℝ) + 2 * (h : ℝ) ≤
      ((⌊c i + r.val⌋ : ℤ) : ℝ) := by linarith
  exact_mod_cast hi

/-- A finite set contained in a coordinate radius-2h box has the required volume bound. -/
theorem finite_sites_card_le_ap_box {d : ℕ} (N : {n : ℕ // 0 < n})
    (hdiv : N.val % 8 = 0) (a : Vertex d) (T : Finset (Vertex d))
    (hT : ∀ z ∈ T, ∀ i, |z i - a i| ≤ 2 * ((5 * (N.val : ℤ)) / 4)) :
    T.card ≤ (8 * N.val) ^ d := by
  classical
  let h : ℤ := 5 * (N.val : ℤ) / 4
  let q : ℕ := (4 * h).toNat
  let b : Vertex d := fun i => a i - 2 * h
  have hh : 0 < h := (ap_outer_integer_radius N hdiv).1
  have hq : (q : ℤ) = 4 * h := by
    dsimp [q]
    exact Int.toNat_of_nonneg (by omega)
  have hsub : T ⊆ LatticeProb.qbox b q := by
    intro z hz
    rw [LatticeProb.qbox, Finset.mem_image]
    refine ⟨z - b, ?_, by simp⟩
    rw [Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_Icc, Pi.sub_apply]
    have hi := abs_le.mp (hT z hz i)
    change 0 ≤ z i - (a i - 2 * h) ∧ z i - (a i - 2 * h) ≤ q
    rw [hq]
    constructor <;> omega
  have hN : (0 : ℤ) < N.val := by exact_mod_cast N.property
  have h8 : (N.val : ℤ) % 8 = 0 := by exact_mod_cast hdiv
  have hbound : (q : ℤ) + 1 ≤ 8 * (N.val : ℤ) := by
    rw [hq]
    dsimp [h]
    omega
  have hnat : q + 1 ≤ 8 * N.val := by exact_mod_cast hbound
  calc
    T.card ≤ (LatticeProb.qbox b q).card := Finset.card_le_card hsub
    _ = (q + 1) ^ d := LatticeProb.card_qbox b q
    _ ≤ (8 * N.val) ^ d := Nat.pow_le_pow_left hnat _

/-- A connected family of good boxes has one ambient component; every other
component is coordinatewise small and has finite support of controlled size. -/
theorem apCentres_other_components_small {d : ℕ} [NeZero d] (ω : Configuration d)
    (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) (N : {n : ℕ // 0 < n})
    (hdiv : N.val % 8 = 0)
    (hr : (((5 * (N.val : ℤ)) / 4 : ℤ) : ℝ) + 1 ≤ r.val)
    (hp : ∀ k ∈ apCentres c r N (by linarith),
      apProjectedProperty k N ((openGraph ω).induce (apOuter k N : Set (Vertex d)))) :
    ∃ H : ((openGraph ω).induce (latticeCube c r : Set (Vertex d))).ConnectedComponent,
      ∀ K : ((openGraph ω).induce (latticeCube c r : Set (Vertex d))).ConnectedComponent,
        K ≠ H →
        (∀ v ∈ K.supp, ∀ w ∈ K.supp, ∀ i,
          |v.val i - w.val i| ≤ 2 * ((5 * (N.val : ℤ)) / 4)) ∧
        K.supp.Finite ∧ K.supp.ncard ≤ (8 * N.val) ^ d := by
  classical
  have hr' : (((5 * (N.val : ℤ)) / 4 : ℤ) : ℝ) < r.val := by linarith
  let Q := latticeCube c r
  let l : Vertex d := fun i => ⌈c i - r.val⌉
  let u : Vertex d := fun i => ⌊c i + r.val⌋
  let h : ℤ := 5 * (N.val : ℤ) / 4
  let R : Set (Vertex d) := {z | ∀ i, l i ≤ z i ∧ z i ≤ u i}
  let G := (openGraph ω).induce (Q : Set (Vertex d))
  let GR := (openGraph ω).induce R
  have hQR : (Q : Set (Vertex d)) ⊆ R := by
    intro z hz
    exact (latticeCube_mem_integer_rectangle c r z).mp hz
  let F : G →g GR := ((openGraph ω).induceHomOfLE hQR).toHom
  have hw : ∀ i, l i + 2 * h ≤ u i := latticeCube_integer_width c r h hr
  have hh : 0 < h := (ap_outer_integer_radius N hdiv).1
  have he : (h : ℝ) = 5 * (N.val : ℝ) / 4 := (ap_outer_integer_radius N hdiv).2
  obtain ⟨H, hH⟩ := apCentres_backbone ω c r N hdiv hr hr' hp
  refine ⟨H, ?_⟩
  intro K hKH
  have hdiam : ∀ v ∈ K.supp, ∀ w ∈ K.supp, ∀ i,
      |v.val i - w.val i| ≤ 2 * h := by
    intro v hv w hwK i
    by_contra hbad
    have hgap : 2 * h < |v.val i - w.val i| := lt_of_not_ge hbad
    have hvR : ∀ j, l j ≤ v.val j ∧ v.val j ≤ u j := hQR v.property
    have hwR : ∀ j, l j ≤ w.val j ∧ w.val j ≤ u j := hQR w.property
    let k := boxCenterClamp l u v.val h
    have hcov := apCentres_clamped_cover c r N hdiv hr hr' v.val v.property
    change k ∈ apCentres c r N hr' ∧ v.val ∈ apOuter k N ∧ _ at hcov
    have hx : |v.val i - k i| ≤ h := by
      have hxR := ((mem_apOuter_iff k v.val N).mp hcov.2.1) i
      rw [← he] at hxR
      exact_mod_cast hxR
    have hout : w.val ∉ apOuter k N := by
      intro hwB
      have hyR := ((mem_apOuter_iff k w.val N).mp hwB) i
      rw [← he] at hyR
      have hy : |w.val i - k i| ≤ h := by exact_mod_cast hyR
      have hx' := abs_le.mp hx
      have hy' := abs_le.mp hy
      rcases lt_abs.mp hgap with hg | hg <;> omega
    obtain ⟨p⟩ := K.reachable_of_mem_supp hv hwK
    have pR : GR.Walk ⟨v.val, hvR⟩ ⟨w.val, hwR⟩ := p.map F
    obtain ⟨C, hcross, hvB, hvC, y, q, hpref, hsub, hinside, j, hface, hwide⟩ :=
      ap_first_exit_attaches ω l u v.val N hdiv hw hvR ⟨w.val, hwR⟩ pR hout (hp k hcov.1)
    obtain ⟨C0, hC0, hAll⟩ := hH k hcov.1
    obtain ⟨hvQ, hvH⟩ := hAll C hcross ⟨v.val, hvB⟩ hvC
    have hvH' : v ∈ H.supp := by simpa using hvH
    exact hKH (SimpleGraph.ConnectedComponent.eq_of_common_vertex hv hvH')
  refine ⟨hdiam, ?_⟩
  have hfinite : K.supp.Finite := Set.toFinite K.supp
  refine ⟨hfinite, ?_⟩
  obtain ⟨a, ha⟩ := K.nonempty_supp
  let T : Finset (Vertex d) := hfinite.toFinset.image Subtype.val
  have hT : ∀ z ∈ T, ∀ i, |z i - a.val i| ≤ 2 * h := by
    intro z hz i
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxK : x ∈ K.supp := hfinite.mem_toFinset.mp hx
    exact hdiam x hxK a ha i
  have hcard := finite_sites_card_le_ap_box N hdiv a.val T hT
  have hEq : T.card = hfinite.toFinset.card := by
    exact Finset.card_image_of_injective _ Subtype.val_injective
  rw [hEq] at hcard
  rw [Set.ncard_eq_toFinset_card K.supp hfinite]
  exact hcard

end LatticeProb.Percolation
