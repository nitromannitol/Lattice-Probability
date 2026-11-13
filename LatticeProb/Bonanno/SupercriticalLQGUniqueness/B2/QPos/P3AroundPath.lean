/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3AroundPath at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Circuit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitInput

 








set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

theorem latticeRadius_cast (v : ℤ × ℤ) : (latticeRadius v : ℤ) = max |v.1| |v.2| := by
  simp [latticeRadius, Int.natCast_natAbs]

theorem two_pow_eq_scale (n : ℕ) (hn : 16 ≤ n) : (2 : ℤ) ^ n = 65536 * (2 ^ (n - 16) : ℕ) := by
  have : n = (n - 16) + 16 := by omega
  conv_lhs => rw [this, pow_add]
  push_cast; ring

theorem inner_radius_eq (n : ℕ) (hn : 16 ≤ n) :
    (dgffInnerRadius n : ℤ) = 32768 * (2 ^ (n - 16) : ℕ) := by
  unfold dgffInnerRadius
  have : n - 1 = (n - 16) + 15 := by omega
  rw [this, pow_add]
  push_cast; ring

theorem interiorRadius_eq (n : ℕ) (hn : 16 ≤ n) :
    interiorRadius n = 65536 * (2 ^ (n - 16) : ℕ) - 1 := by
  unfold interiorRadius
  rw [two_pow_eq_scale n hn]

 
theorem outer_radius_ge (n : ℕ) (hn : 16 ≤ n) :
    46080 * (2 ^ (n - 16) : ℕ) ≤ dgffOuterRadius n := by
  unfold dgffOuterRadius
  apply Nat.le_floor
  have h1 : (2 : ℝ) ^ ((n : ℝ) - 1 / 2) = 2 ^ n / Real.sqrt 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [h1]
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [le_div_iff₀ hs]
  have h2 : (2 : ℝ) ^ n = 65536 * ((2 ^ (n - 16) : ℕ) : ℝ) := by
    have : n = (n - 16) + 16 := by omega
    conv_lhs => rw [this, pow_add]
    push_cast; ring
  rw [h2]
  have h3 : Real.sqrt 2 ≤ 65536 / 46080 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h5 : 46080 * Real.sqrt 2 ≤ 65536 := by
    rw [le_div_iff₀ (by norm_num)] at h3; linarith
  have h4 : (0 : ℝ) ≤ ((2 ^ (n - 16) : ℕ) : ℝ) := by positivity
  rw [Nat.cast_mul]
  calc ((46080 : ℕ) : ℝ) * ((2 ^ (n - 16) : ℕ) : ℝ) * Real.sqrt 2
      = ((2 ^ (n - 16) : ℕ) : ℝ) * (46080 * Real.sqrt 2) := by push_cast; ring
    _ ≤ ((2 ^ (n - 16) : ℕ) : ℝ) * 65536 := mul_le_mul_of_nonneg_left h5 h4
    _ = 65536 * ((2 ^ (n - 16) : ℕ) : ℝ) := by ring

theorem inShell_mem_interior (n : ℕ) (hn : 16 ≤ n) {v : ℤ × ℤ}
    (hv : InShell (2 ^ (n - 16)) v) : v ∈ interiorSites n := by
  obtain ⟨h1, h2, _⟩ := hv
  have hj : (1 : ℤ) ≤ ((2 ^ (n - 16) : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_two_pow
  have hR := interiorRadius_eq n hn
  generalize ((2 ^ (n - 16) : ℕ) : ℤ) = J at *
  have hmem : -interiorRadius n ≤ v.1 ∧ v.1 ≤ interiorRadius n ∧
      -interiorRadius n ≤ v.2 ∧ v.2 ≤ interiorRadius n := by
    rw [abs_le] at h1 h2
    rw [hR]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  simpa [interiorSites, Finset.mem_product, Finset.mem_Icc, and_assoc] using hmem

theorem mem_dropLast_of_closed {l : List (ℤ × ℤ)} (hcl : IsClosed l) (hne : l.dropLast ≠ [])
    {v : ℤ × ℤ} (hv : v ∈ l) : v ∈ l.dropLast := by
  have hdl := List.dropLast_append_getLast hcl.1
  rw [← hdl, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hv
  · simp at hv
    obtain ⟨hne', h1⟩ := hcl
    rw [List.getLast?_eq_getLast hne'] at h1
    have h2 : l.head? = l.dropLast.head? := by
      conv_lhs => rw [← hdl]
      rw [List.head?_append]
      obtain ⟨a, ha⟩ : ∃ a, l.dropLast.head? = some a := ⟨_, List.head?_eq_head hne⟩
      rw [ha]; rfl
    rw [h2, List.head?_eq_head hne] at h1
    have := Option.some_injective _ h1
    rw [hv, ← this]
    exact List.head_mem hne

 

theorem aroundPath_of_loop_gen (n : ℕ) (ρ₁ ρ₂ : ℤ) (h1 : (dgffInnerRadius n : ℤ) + 1 < ρ₁)
    (h2 : ρ₂ < (dgffOuterRadius n : ℤ)) (h3 : ρ₂ ≤ interiorRadius n) (l : List (ℤ × ℤ))
    (hch : l.IsChain latticeAdjacent) (hcl : IsClosed l) (hnd : l.dropLast.Nodup)
    (hw : wind (0, 0) l ≠ 0)
    (hshell : ∀ v ∈ l, |v.1| ≤ ρ₂ ∧ |v.2| ≤ ρ₂ ∧ (ρ₁ ≤ |v.1| ∨ ρ₁ ≤ |v.2|)) :
    ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ p.map Subtype.val = l.dropLast := by
  obtain ⟨hpne, hpch, z0, w0, hz0, hw0, hadj⟩ := simple_loop_cyclic hch hcl (0, 0) hw
  have hsub : ∀ v ∈ l.dropLast, v ∈ l := fun v hv => List.dropLast_subset l hv
  have hint : ∀ v ∈ l.dropLast, v ∈ interiorSites n := by
    intro v hv
    obtain ⟨a, b, _⟩ := hshell v (hsub v hv)
    rw [abs_le] at a b
    simpa [interiorSites, Finset.mem_product, Finset.mem_Icc, and_assoc] using
      (show -interiorRadius n ≤ v.1 ∧ v.1 ≤ interiorRadius n ∧
        -interiorRadius n ≤ v.2 ∧ v.2 ≤ interiorRadius n by omega)
  set p : List (DGFFSite n) := l.dropLast.pmap (fun v hv => ⟨v, hv⟩) hint with hp
  have hmap : p.map Subtype.val = l.dropLast := by
    rw [hp, List.map_pmap]; simp
  refine ⟨p, ⟨?_, ?_, ?_, ?_, ?_⟩, hmap⟩
  · exact List.Nodup.pmap (fun a _ b _ h => congrArg Subtype.val h) hnd
  · rw [← List.isChain_map (f := Subtype.val), hmap]; exact hpch
  · intro z hz
    rw [hp, List.mem_pmap] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    obtain ⟨a, b, c⟩ := hshell v (hsub v hv)
    have hr := latticeRadius_cast v
    have hm1 := le_max_left |v.1| |v.2|
    have hm2 := le_max_right |v.1| |v.2|
    unfold inDGFFAnnulus
    simp only
    constructor
    · have : (dgffInnerRadius n : ℤ) < (latticeRadius v : ℤ) := by
        rw [hr]; rcases c with c | c <;> omega
      exact_mod_cast this
    · have : (latticeRadius v : ℤ) ≤ (dgffOuterRadius n : ℤ) := by
        rw [hr]; apply max_le <;> omega
      exact_mod_cast this
  · have h1' : (p.map Subtype.val).head? = some z0 := by rw [hmap]; exact hz0
    have h2' : (p.map Subtype.val).getLast? = some w0 := by rw [hmap]; exact hw0
    rw [List.head?_map] at h1'
    rw [List.getLast?_map] at h2'
    obtain ⟨z, hz, hz'⟩ := Option.map_eq_some_iff.mp h1'
    obtain ⟨w, hw', hw''⟩ := Option.map_eq_some_iff.mp h2'
    exact ⟨z, w, hz, hw', by rw [hz', hw'']; exact hadj⟩
  · intro q hq
    obtain ⟨hqch, hqann, a, b, hqa, hqb, hra, hrb⟩ := hq
    obtain ⟨q', rfl⟩ : ∃ q', q = a :: q' := by
      cases q with
      | nil => simp at hqa
      | cons x q' => simp at hqa; exact ⟨q', by rw [hqa]⟩
    have hqZch : (a.1 :: q'.map Subtype.val).IsChain latticeAdjacent := by
      have := (List.isChain_map (R := latticeAdjacent) (f := Subtype.val) (l := a :: q')).mpr hqch
      simpa using this
    have hlast : (a.1 :: q'.map Subtype.val).getLast (by simp) = b.1 := by
      have h := congrArg (Option.map Subtype.val) hqb
      rw [← List.getLast?_map] at h
      simp only [List.map_cons, Option.map_some] at h
      rw [List.getLast?_eq_getLast (by simp)] at h
      exact Option.some_injective _ h
    have hra' : (latticeRadius a.1 : ℤ) = dgffInnerRadius n + 1 := by exact_mod_cast hra
    have hrb' : (latticeRadius b.1 : ℤ) = dgffOuterRadius n := by exact_mod_cast hrb
    rw [latticeRadius_cast] at hra' hrb'
    have hA : |a.1.1| ≤ (dgffInnerRadius n : ℤ) + 1 ∧ |a.1.2| ≤ (dgffInnerRadius n : ℤ) + 1 :=
      ⟨by have := le_max_left |a.1.1| |a.1.2|; omega,
        by have := le_max_right |a.1.1| |a.1.2|; omega⟩
    have hB : (dgffOuterRadius n : ℤ) ≤ |b.1.1| ∨ (dgffOuterRadius n : ℤ) ≤ |b.1.2| := by
      rcases le_total |b.1.1| |b.1.2| with h | h
      · right; rw [max_eq_right h] at hrb'; omega
      · left; rw [max_eq_left h] at hrb'; omega
    obtain ⟨v, hvq, hvl⟩ := blocking hch hcl (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      (r₁ := (dgffInnerRadius n : ℤ) + 1) (r₂ := (dgffOuterRadius n : ℤ))
      (fun v hv => ⟨(hshell v hv).1, (hshell v hv).2.1⟩) (fun v hv => (hshell v hv).2.2) hw
      h1 h2 a.1 (q'.map Subtype.val) hqZch hA (by rw [hlast]; exact hB)
    have hvp : v ∈ l.dropLast := mem_dropLast_of_closed hcl hpne hvl
    have hvq' : v ∈ (a :: q').map Subtype.val := by simpa using hvq
    obtain ⟨y, hy, hyv⟩ := List.mem_map.mp hvq'
    refine ⟨y, ?_, hy⟩
    rw [hp, List.mem_pmap]
    exact ⟨v, hvp, Subtype.ext hyv.symm⟩

 
theorem aroundPath_of_loop (n : ℕ) (hn : 16 ≤ n) (l : List (ℤ × ℤ))
    (hch : l.IsChain latticeAdjacent) (hcl : IsClosed l) (hnd : l.dropLast.Nodup)
    (hw : wind (0, 0) l ≠ 0) (hshell : ∀ v ∈ l, InShell (2 ^ (n - 16)) v) :
    ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ p.map Subtype.val = l.dropLast := by
  have hj : (1 : ℤ) ≤ ((2 ^ (n - 16) : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_two_pow
  have hin := inner_radius_eq n hn
  have hout : 46080 * ((2 ^ (n - 16) : ℕ) : ℤ) ≤ (dgffOuterRadius n : ℤ) := by
    have := outer_radius_ge n hn; exact_mod_cast this
  have hR := interiorRadius_eq n hn
  exact aroundPath_of_loop_gen n (36735 * ((2 ^ (n - 16) : ℕ) : ℤ))
    (44161 * ((2 ^ (n - 16) : ℕ) : ℤ)) (by omega) (by omega) (by omega) l hch hcl hnd hw hshell

end SupercriticalLQGUniqueness.B2.QPos.P3
