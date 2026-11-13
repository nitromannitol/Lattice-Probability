/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Continuation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3AroundPath

 










set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 
def tubeLen (n : ℕ) : ℕ := 64 * (2 ^ (n - 16)) ^ 2 * (6 * mB)

 
def contConst : ℝ := (1 / 16384 : ℝ) ^ (6 * mB)

theorem contConst_pos : 0 < contConst := by unfold contConst; positivity

 
def InTarget (n : ℕ) (z : ℤ × ℤ) : Prop :=
  41 * (1024 * ((2 ^ (n - 16) : ℕ) : ℤ)) ≤ z.1 ∧ z.1 ≤ 43 * (1024 * ((2 ^ (n - 16) : ℕ) : ℤ)) ∧
    |z.2| ≤ 1024 * ((2 ^ (n - 16) : ℕ) : ℤ)

 
def ContEvent (n N : ℕ) (z : ℤ × ℤ) (ω : Fin N → Bool × Bool) : Prop :=
  (∀ k ≤ N, wpos z ω k ∈ interiorSites n) ∧
    ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ ∀ v ∈ p, ∃ k ≤ N, wpos z ω k = v.1

theorem tube_contEvent (n : ℕ) (hn : 17 ≤ n) (z : ℤ × ℤ) (hz : InTarget n z)
    (ω : Fin (tubeLen n) → Bool × Bool)
    (hT : TubeGood (2 ^ (n - 16)) (64 * (2 ^ (n - 16)) ^ 2)
      (routeP (1024 * ((2 ^ (n - 16) : ℕ) : ℤ)) z mB) z (6 * mB) ω) :
    ContEvent n (tubeLen n) z ω := by
  have hj : 1 ≤ 2 ^ (n - 16) := Nat.one_le_two_pow
  obtain ⟨hshell, l, hch, hcl, hnd, hw, hvis⟩ := tube_circuit (2 ^ (n - 16)) hj z hz ω hT
  refine ⟨fun k hk => inShell_mem_interior n (by omega) (hshell k hk), ?_⟩
  obtain ⟨p, hp, hmap⟩ := aroundPath_of_loop n (by omega) l hch hcl hnd hw (by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := hvis v hv
    exact hshell k hk)
  refine ⟨p, hp, fun v hv => ?_⟩
  have : v.1 ∈ l.dropLast := by
    rw [← hmap]; exact List.mem_map_of_mem hv
  exact hvis v.1 (List.dropLast_subset l this)

open Classical in
 

theorem continuation (n : ℕ) (hn : 17 ≤ n) (z : ℤ × ℤ) (hz : InTarget n z) :
    contConst * 4 ^ tubeLen n ≤
      ((univ.filter fun ω : Fin (tubeLen n) → Bool × Bool => ContEvent n (tubeLen n) z ω).card : ℝ) := by
  classical
  set j := 2 ^ (n - 16) with hjdef
  have hj : 0 < j := by positivity
  have hjeven : j = 2 * 2 ^ (n - 17) := by
    rw [hjdef, show n - 16 = (n - 17) + 1 by omega, pow_succ]; ring
  set ℓ : ℤ := 1024 * (j : ℤ) with hℓ
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hzℓ : 41 * ℓ ≤ z.1 ∧ z.1 ≤ 43 * ℓ ∧ |z.2| ≤ ℓ := hz
  
  have hJ : 75 * ℓ ≤ (mB : ℤ) * ((2 ^ (n - 17) : ℕ) : ℤ) := by
    rw [hℓ, hjeven, mB]; push_cast; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) (n - 17)]
  have hstep := routeP_step ℓ hℓ0 z hzℓ mB_pos _ hJ
  have hP : ∀ i < 6 * mB,
      |((routeP ℓ z mB (i + 1)).1 + (routeP ℓ z mB (i + 1)).2) -
          ((routeP ℓ z mB i).1 + (routeP ℓ z mB i).2)| ≤ j ∧
        |((routeP ℓ z mB (i + 1)).1 - (routeP ℓ z mB (i + 1)).2) -
          ((routeP ℓ z mB i).1 - (routeP ℓ z mB i).2)| ≤ j := by
    intro i _
    obtain ⟨h1, h2⟩ := hstep i
    rw [abs_le] at h1 h2
    have : (j : ℤ) = 2 * ((2 ^ (n - 17) : ℕ) : ℤ) := by rw [hjeven]; push_cast; ring
    rw [abs_le, abs_le, this]
    constructor <;> constructor <;> linarith
  have hz0 : |(z.1 + z.2) - ((routeP ℓ z mB 0).1 + (routeP ℓ z mB 0).2)| ≤ j ∧
      |(z.1 - z.2) - ((routeP ℓ z mB 0).1 - (routeP ℓ z mB 0).2)| ≤ j := by
    have : routeP ℓ z mB 0 = z := by
      have := routeP_node ℓ z mB_pos 0
      simpa [routeW] using this
    rw [this]; simp
  have htube := tube2D j hj (routeP ℓ z mB) (6 * mB) hP z hz0
  have hsub' : (univ.filter fun ω : Fin (tubeLen n) → Bool × Bool =>
        TubeGood j (64 * j ^ 2) (routeP ℓ z mB) z (6 * mB) ω) ⊆
      (univ.filter fun ω : Fin (tubeLen n) → Bool × Bool => ContEvent n (tubeLen n) z ω) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨mem_univ _, tube_contEvent n hn z hz ω hω.2⟩
  have hsub : ((univ.filter fun ω : Fin (tubeLen n) → Bool × Bool =>
        TubeGood j (64 * j ^ 2) (routeP ℓ z mB) z (6 * mB) ω).card : ℝ) ≤
      ((univ.filter fun ω : Fin (tubeLen n) → Bool × Bool =>
        ContEvent n (tubeLen n) z ω).card : ℝ) := by
    exact_mod_cast card_le_card hsub'
  calc contConst * 4 ^ tubeLen n
      = ((1 / 16384 : ℝ) * 4 ^ (64 * j ^ 2)) ^ (6 * mB) := by
        rw [contConst, tubeLen, mul_pow, pow_mul (4 : ℝ) (64 * (2 ^ (n - 16)) ^ 2) (6 * mB)]
    _ ≤ _ := htube
    _ ≤ _ := hsub

end SupercriticalLQGUniqueness.B2.QPos.P3
