import LatticeProb.Prob.Percolation.AntalPisztoraBackbone

/-! # Admissible centres of lattice cubes -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ}

/-- At a scale divisible by eight, the integer radius is exactly the AP outer radius. -/
theorem ap_outer_integer_radius (N : {n : ℕ // 0 < n}) (hdiv : N.val % 8 = 0) :
    0 < (5 * (N.val : ℤ)) / 4 ∧
      (((5 * (N.val : ℤ)) / 4 : ℤ) : ℝ) = 5 * (N.val : ℝ) / 4 := by
  have h8 : (N.val : ℤ) % 8 = 0 := by exact_mod_cast hdiv
  have hn : (0 : ℤ) < N.val := by exact_mod_cast N.property
  have hp : 0 < 5 * (N.val : ℤ) / 4 := by omega
  have he : 4 * (5 * (N.val : ℤ) / 4) = 5 * (N.val : ℤ) := by omega
  have her : (4 : ℝ) * ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) = 5 * (N.val : ℝ) := by
    exact_mod_cast he
  exact ⟨hp, by linarith⟩

/-- The integer centres whose outer cubes fit inside the given cube. -/
def apCentres (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) (N : {n : ℕ // 0 < n})
    (hr : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) < r.val) : Finset (Vertex d) :=
  latticeCube c ⟨r.val - ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ), by
    simp only [Set.mem_Ioi]; linarith⟩

/-- The smaller cube is exactly the family of all centres whose AP box is contained
in the original cube. -/
theorem mem_apCentres_iff (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (N : {n : ℕ // 0 < n}) (hdiv : N.val % 8 = 0)
    (hr : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) < r.val) (k : Vertex d) :
    k ∈ apCentres c r N hr ↔ apOuter k N ⊆ latticeCube c r := by
  classical
  let h : ℤ := 5 * (N.val : ℤ) / 4
  have hh : 0 < h := (ap_outer_integer_radius N hdiv).1
  have he : (h : ℝ) = 5 * (N.val : ℝ) / 4 := (ap_outer_integer_radius N hdiv).2
  constructor
  · intro hk z hz
    have hk' := (mem_latticeCube_iff _ _ k).mp hk
    have hz' := (mem_apOuter_iff _ _ _).mp hz
    apply (mem_latticeCube_iff _ _ z).mpr
    intro i
    have hkI := hk' i
    change |(k i : ℝ) - c i| ≤ r.val - (h : ℝ) at hkI
    have hzI := hz' i
    rw [← he] at hzI
    rw [abs_le] at hkI hzI ⊢
    constructor <;> linarith [hkI.1, hkI.2, hzI.1, hzI.2]
  · intro hsub
    apply (mem_latticeCube_iff _ _ k).mpr
    intro i
    let a : Vertex d := fun j => k j + if j = i then h else 0
    let b : Vertex d := fun j => k j - if j = i then h else 0
    have hnonneg : (0 : ℝ) ≤ h := by exact_mod_cast (le_of_lt hh)
    have ha : a ∈ apOuter k N := by
      apply (mem_apOuter_iff _ _ _).mpr
      intro j
      rw [← he]
      by_cases hj : j = i
      · simp [a, hj, abs_of_nonneg hnonneg]
      · simp [a, hj, le_of_lt hh]
    have hb : b ∈ apOuter k N := by
      apply (mem_apOuter_iff _ _ _).mpr
      intro j
      rw [← he]
      by_cases hj : j = i
      · simp [b, hj, abs_of_nonneg hnonneg]
      · simp [b, hj, le_of_lt hh]
    have ha' := ((mem_latticeCube_iff _ _ a).mp (hsub ha)) i
    have hb' := ((mem_latticeCube_iff _ _ b).mp (hsub hb)) i
    change |(k i : ℝ) - c i| ≤ r.val - (h : ℝ)
    rw [abs_le] at ha' hb' ⊢
    simp only [a, b, ite_true, Int.cast_add, Int.cast_sub] at ha' hb'
    constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]

/-- The centre cube contains the coordinatewise floors of its real centre. -/
theorem apCentres_nonempty (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (N : {n : ℕ // 0 < n})
    (hr : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) + 1 ≤ r.val)
    (hr' : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) < r.val) :
    (apCentres c r N hr').Nonempty := by
  refine ⟨fun i => ⌊c i⌋, ?_⟩
  apply (mem_latticeCube_iff _ _ _).mpr
  intro i
  have ha := Int.floor_le (c i)
  have hb := Int.lt_floor_add_one (c i)
  rw [abs_le]
  constructor <;> linarith

/-- The actual nearest-neighbor graph induced by the centre cube is connected. -/
theorem apCentres_connected (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (N : {n : ℕ // 0 < n})
    (hr : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) + 1 ≤ r.val)
    (hr' : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) < r.val) :
    ((nearestNeighborGraph d).induce (apCentres c r N hr' : Set (Vertex d))).Connected := by
  have hn := apCentres_nonempty c r N hr hr'
  have hc := latticeCube_allOpen_connected c
    ⟨r.val - ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ), by simp only [Set.mem_Ioi]; linarith⟩ hn
  simpa only [openGraph_allOpen, apCentres] using hc

/-- Clamping any cube vertex produces a centre in the full admissible family,
covering the vertex and retaining the margins at every exitable coordinate face. -/
theorem apCentres_clamped_cover (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (N : {n : ℕ // 0 < n}) (hdiv : N.val % 8 = 0)
    (hr : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) + 1 ≤ r.val)
    (hr' : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) < r.val)
    (v : Vertex d) (hv : v ∈ latticeCube c r) :
    let h : ℤ := 5 * (N.val : ℤ) / 4
    let l : Vertex d := fun i => ⌈c i - r.val⌉
    let u : Vertex d := fun i => ⌊c i + r.val⌋
    let k := boxCenterClamp l u v h
    k ∈ apCentres c r N hr' ∧ v ∈ apOuter k N ∧
      ∀ i, (l i < k i - h → h ≤ v i - (k i - h)) ∧
        (k i + h < u i → h ≤ (k i + h) - v i) := by
  dsimp only
  let h : ℤ := 5 * (N.val : ℤ) / 4
  let l : Vertex d := fun i => ⌈c i - r.val⌉
  let u : Vertex d := fun i => ⌊c i + r.val⌋
  let k := boxCenterClamp l u v h
  have hh : 0 < h := (ap_outer_integer_radius N hdiv).1
  have he : (h : ℝ) = 5 * (N.val : ℝ) / 4 := (ap_outer_integer_radius N hdiv).2
  have hv' : ∀ i, l i ≤ v i ∧ v i ≤ u i :=
    (mem_latticeCubeSet_iff c r v).mp ((finite_latticeCubeSet c r).mem_toFinset.mp hv)
  have hw : ∀ i, l i + 2 * h ≤ u i := by
    intro i
    have hc := Int.ceil_lt_add_one (c i - r.val)
    have hf := Int.lt_floor_add_one (c i + r.val)
    have hi : (l i : ℝ) + 2 * (h : ℝ) ≤ (u i : ℝ) := by
      dsimp [l, u]
      linarith
    exact_mod_cast hi
  have hs := boxCenterClamp_spec l u v h (le_of_lt hh) hw hv'
  have hkQ : apOuter k N ⊆ latticeCube c r := by
    intro z hz
    have hz' := (mem_apOuter_iff _ _ _).mp hz
    have hzi : ∀ i, |z i - k i| ≤ h := by
      intro i
      have hzI := hz' i
      rw [← he] at hzI
      exact_mod_cast hzI
    have hbox := hs.2 hzi
    apply (finite_latticeCubeSet c r).mem_toFinset.mpr
    exact (mem_latticeCubeSet_iff c r z).mpr hbox
  have hvB : v ∈ apOuter k N := by
    apply (mem_apOuter_iff _ _ _).mpr
    intro i
    have hvI := (hs.1 i).2.2.1
    have hvR : |(v i : ℝ) - (k i : ℝ)| ≤ (h : ℝ) := by exact_mod_cast hvI
    simpa only [he] using hvR
  refine ⟨(mem_apCentres_iff c r N hdiv hr' k).mpr hkQ, hvB, ?_⟩
  intro i
  exact ⟨(hs.1 i).2.2.2.1, (hs.1 i).2.2.2.2⟩

/-- The local crossing components in every admissible AP box lie in one actual
component of the ambient cube. -/
theorem apCentres_backbone [NeZero d] (ω : Configuration d)
    (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) (N : {n : ℕ // 0 < n})
    (hdiv : N.val % 8 = 0)
    (hr : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) + 1 ≤ r.val)
    (hr' : ((5 * (N.val : ℤ) / 4 : ℤ) : ℝ) < r.val)
    (hp : ∀ k ∈ apCentres c r N hr',
      apProjectedProperty k N ((openGraph ω).induce (apOuter k N : Set (Vertex d)))) :
    ∃ H : ((openGraph ω).induce (latticeCube c r : Set (Vertex d))).ConnectedComponent,
      ∀ k, k ∈ apCentres c r N hr' →
        ∃ C : ((openGraph ω).induce (apOuter k N : Set (Vertex d))).ConnectedComponent,
          latticeCubeComponentCrosses (fun i => (k i : ℝ))
            ⟨5 * (N.val : ℝ) / 4, by
              simp only [Set.mem_Ioi]
              have hn : (0 : ℝ) < N.val := by exact_mod_cast N.property
              positivity⟩ ((openGraph ω).induce (apOuter k N : Set (Vertex d))) C ∧
          ∀ D : ((openGraph ω).induce (apOuter k N : Set (Vertex d))).ConnectedComponent,
            latticeCubeComponentCrosses (fun i => (k i : ℝ))
              ⟨5 * (N.val : ℝ) / 4, by
                simp only [Set.mem_Ioi]
                have hn : (0 : ℝ) < N.val := by exact_mod_cast N.property
                positivity⟩ ((openGraph ω).induce (apOuter k N : Set (Vertex d))) D →
            ∀ x : {z : Vertex d // z ∈ apOuter k N}, x ∈ D.supp →
              ∃ hx : x.val ∈ latticeCube c r,
                (⟨x.val, hx⟩ : {z : Vertex d // z ∈ latticeCube c r}) ∈ H.supp := by
  have hQ : ∀ k ∈ apCentres c r N hr', apOuter k N ⊆ latticeCube c r := by
    intro k hk
    exact (mem_apCentres_iff c r N hdiv hr' k).mp hk
  obtain ⟨H, hH⟩ := ap_connected_family_backbone ω N (apCentres c r N hr')
    (latticeCube c r) (apCentres_nonempty c r N hr hr')
    (apCentres_connected c r N hr hr') hQ hp
  refine ⟨H, ?_⟩
  intro k hk
  obtain ⟨C, hc, ha⟩ := hH k hk
  refine ⟨C, hc, ?_⟩
  intro D hd x hx
  exact ⟨hQ k hk x.property, ha D hd x hx⟩

end
end LatticeProb.Percolation
