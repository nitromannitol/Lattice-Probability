/-
The optimal stopping representation of the odometer: the two halves of
`thm:RW`, that the odometer is an upper bound for every bounded stopping rule
and that it is the value of one of them.
-/
import LatticeProb.Graph.WalkLemmas
import LatticeProb.Graph.Recursion

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Infinite V]

theorem zero_mem_stopValues (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (x : V) :
    (0 : ℝ) ∈ stopValues G ξ n x := by
  refine ⟨fun _ => 0, fun _ _ _ _ h => h, fun _ => Nat.zero_le _, ?_⟩
  rw [show (fun X : ℕ → V => payoff G ξ 0 X) = (fun _ => (0 : ℝ)) from rfl,
    walkExp_const hG]

omit [Infinite V] in
theorem scenery_eq (σ : V → ℝ) (x : V) :
    excess σ x / (G.degree x : ℝ) = scenery G σ x := rfl

/-- The odometer bounds every bounded stopping rule, and is the value of one. -/
theorem odometer_isLUB (hG : G.Connected) (σ : V → ℝ) :
    ∀ (n : ℕ) (x : V),
      (∀ a ∈ stopValues G (excess σ) n x, a ≤ odometer G σ n x) ∧
        odometer G σ n x ∈ stopValues G (excess σ) n x := by
  intro n
  induction n with
  | zero =>
      intro x
      refine ⟨?_, ?_⟩
      · rintro a ⟨τ, -, hle, rfl⟩
        have : τ (fun _ => x) = 0 := Nat.le_zero.mp (hle _)
        simp [walkExp, this, payoff, odometer]
      · simpa [odometer] using zero_mem_stopValues hG (excess σ) 0 x
  | succ n ih =>
      intro x
      have hrec := LatticeProb.Graph.odometerRecursion hG σ n x
      have hstep : ∀ y : V,
          (∀ a ∈ stopValues G (excess σ) n y, a ≤ odometer G σ n y) ∧
            odometer G σ n y ∈ stopValues G (excess σ) n y := ih
      constructor
      · rintro a ⟨τ, hτ, hle, rfl⟩
        by_cases h0 : τ (fun _ => x) = 0
        · have hz : walkExp G (n + 1) x (fun X => payoff G (excess σ) (τ X) X)
              = walkExp G (n + 1) x (fun _ => (0 : ℝ)) := by
            refine walkExp_congr fun X hX => ?_
            rw [stopping_of_zero hτ hX h0]
            rfl
          rw [hz, walkExp_const hG]
          exact odometer_nonneg σ (n + 1) x
        · have hne : ∀ X : ℕ → V, X 0 = x → τ X ≠ 0 := fun X hX =>
            stopping_ne_zero hτ hX h0
          rw [walkExp_payoff_succ hG (excess σ) n x hne, scenery_eq]
          have hbound : ∀ y : V,
              walkExp G n y (fun X' => payoff G (excess σ) (τ (cons x X') - 1) X')
                ≤ odometer G σ n y := by
            intro y
            refine (hstep y).1 _ ⟨fun X' => τ (cons x X') - 1,
              isStopping_shift hτ x hne, fun X' => ?_, rfl⟩
            show τ (cons x X') - 1 ≤ n
            have := hle (cons x X')
            omega
          have := walkOp_mono (G := G) hbound x
          rw [hrec]
          have hle' : scenery G σ x
              + walkOp G (fun y => walkExp G n y
                  (fun X' => payoff G (excess σ) (τ (cons x X') - 1) X')) x
              ≤ walkOp G (odometer G σ n) x + scenery G σ x := by linarith
          exact hle'.trans (le_max_left _ _)
      · by_cases hpos : 0 < walkOp G (odometer G σ n) x + scenery G σ x
        · choose τ hτ hτle hτval using fun y => (hstep y).2
          refine ⟨fun X => 1 + τ (X 1) (shift X), isStopping_prepend hτ, fun X => ?_, ?_⟩
          · show 1 + τ (X 1) (shift X) ≤ n + 1
            have := hτle (X 1) (shift X)
            omega
          · have hne : ∀ X : ℕ → V, X 0 = x → (1 + τ (X 1) (shift X)) ≠ 0 := by
              intro X _; omega
            rw [walkExp_payoff_succ hG (excess σ) n x hne, scenery_eq]
            have hy : ∀ y ∈ G.neighborFinset x,
                walkExp G n y (fun X' => payoff G (excess σ)
                    ((1 + τ ((cons x X') 1) (shift (cons x X'))) - 1) X')
                  = odometer G σ n y := by
              intro y _
              rw [show walkExp G n y (fun X' => payoff G (excess σ)
                    ((1 + τ ((cons x X') 1) (shift (cons x X'))) - 1) X')
                  = walkExp G n y (fun X' => payoff G (excess σ) (τ y X') X') from
                walkExp_congr (by
                  intro X' hX'
                  simp only [cons_succ, shift_cons, Nat.add_sub_cancel_left, hX'])]
              exact (hτval y).symm
            rw [show walkOp G (fun y => walkExp G n y (fun X' => payoff G (excess σ)
                  ((1 + τ ((cons x X') 1) (shift (cons x X'))) - 1) X')) x
                = walkOp G (odometer G σ n) x from by
              simp only [walkOp]
              rw [Finset.sum_congr rfl hy]]
            rw [hrec, max_eq_left (by linarith)]
            ring
        · have : odometer G σ (n + 1) x = 0 := by
            rw [hrec, max_eq_right (by linarith [not_lt.mp hpos])]
          rw [this]
          exact zero_mem_stopValues hG (excess σ) (n + 1) x


theorem isLUB_odometer (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    IsLUB (stopValues G (excess σ) n x) (odometer G σ n x) :=
  ⟨fun _ ha => (odometer_isLUB hG σ n x).1 _ ha,
    fun _ hb => hb (odometer_isLUB hG σ n x).2⟩

theorem value_eq (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    value G (excess σ) n x = odometer G σ n x :=
  (isLUB_odometer hG σ n x).csSup_eq ⟨_, (odometer_isLUB hG σ n x).2⟩

omit [Infinite V] in
theorem odometer_zero (σ : V → ℝ) (z : V) : odometer G σ 0 z = 0 := rfl

/-- The set the optimal stopping time minimizes over. -/
def stopSet (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ) (X : ℕ → V) : Set ℕ :=
  {k : ℕ | k ≤ n ∧ value G ξ (n - k) (X k) = 0}

omit [Infinite V] in
theorem optimalStop_eq_sInf (ξ : V → ℝ) (n : ℕ) (X : ℕ → V) :
    optimalStop G ξ n X = sInf (stopSet G ξ n X) := rfl

theorem stopSet_nonempty (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (X : ℕ → V) :
    (stopSet G (excess σ) n X).Nonempty :=
  ⟨n, le_rfl, by rw [Nat.sub_self, value_eq hG, odometer_zero]⟩

theorem isStopping_optimalStop (hG : G.Connected) (σ : V → ℝ) (n : ℕ) :
    IsStopping (optimalStop G (excess σ) n) := by
  intro k X Y hXY hk
  rw [optimalStop_eq_sInf] at hk ⊢
  have hkX : k ∈ stopSet G (excess σ) n X := hk ▸ Nat.sInf_mem (stopSet_nonempty hG σ n X)
  have hlt : ∀ j, j < k → j ∉ stopSet G (excess σ) n X := fun j hj hmem =>
    absurd (Nat.sInf_le hmem) (by rw [hk]; exact not_le.mpr hj)
  have hkY : k ∈ stopSet G (excess σ) n Y :=
    ⟨hkX.1, by rw [← hXY k le_rfl]; exact hkX.2⟩
  refine le_antisymm (Nat.sInf_le hkY) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hm := Nat.sInf_mem (stopSet_nonempty hG σ n Y)
  exact hlt _ hcon ⟨hm.1, by rw [hXY _ hcon.le]; exact hm.2⟩

theorem optimalStop_zero (hG : G.Connected) (σ : V → ℝ) (X : ℕ → V) :
    optimalStop G (excess σ) 0 X = 0 :=
  Nat.eq_zero_of_le_zero
    (Nat.sInf_le ⟨le_rfl, by rw [Nat.zero_sub, value_eq hG, odometer_zero]⟩)

theorem optimalStop_le (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (X : ℕ → V) :
    optimalStop G (excess σ) n X ≤ n :=
  Nat.sInf_le ⟨le_rfl, by rw [Nat.sub_self, value_eq hG, odometer_zero]⟩

theorem optimalStop_cons (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V)
    (hne : value G (excess σ) (n + 1) x ≠ 0) (X' : ℕ → V) :
    optimalStop G (excess σ) (n + 1) (cons x X') = optimalStop G (excess σ) n X' + 1 := by
  have hmem : ∀ j : ℕ, (j + 1 ∈ stopSet G (excess σ) (n + 1) (cons x X'))
      ↔ j ∈ stopSet G (excess σ) n X' := by
    intro j
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by simpa using h2⟩
  have hzero : (0 : ℕ) ∉ stopSet G (excess σ) (n + 1) (cons x X') := by
    rintro ⟨-, h2⟩
    exact hne (by simpa using h2)
  rw [optimalStop_eq_sInf, optimalStop_eq_sInf]
  have hA := Nat.sInf_mem (stopSet_nonempty hG σ (n + 1) (cons x X'))
  have hpos : sInf (stopSet G (excess σ) (n + 1) (cons x X')) ≠ 0 := by
    intro h
    exact hzero (h ▸ hA)
  obtain ⟨m, hm⟩ : ∃ m, sInf (stopSet G (excess σ) (n + 1) (cons x X')) = m + 1 :=
    ⟨sInf (stopSet G (excess σ) (n + 1) (cons x X')) - 1, by omega⟩
  have hmB : m ∈ stopSet G (excess σ) n X' := (hmem m).1 (hm ▸ hA)
  have h1 : sInf (stopSet G (excess σ) n X') ≤ m := Nat.sInf_le hmB
  have h2 : sInf (stopSet G (excess σ) (n + 1) (cons x X'))
      ≤ sInf (stopSet G (excess σ) n X') + 1 :=
    Nat.sInf_le ((hmem _).2 (Nat.sInf_mem (stopSet_nonempty hG σ n X')))
  omega


theorem walkExp_optimalStop (hG : G.Connected) (σ : V → ℝ) :
    ∀ (n : ℕ) (x : V),
      walkExp G n x (fun X => payoff G (excess σ) (optimalStop G (excess σ) n X) X)
        = odometer G σ n x := by
  intro n
  induction n with
  | zero =>
      intro x
      have hz : walkExp G 0 x
            (fun X => payoff G (excess σ) (optimalStop G (excess σ) 0 X) X)
          = walkExp G 0 x (fun _ => (0 : ℝ)) :=
        walkExp_congr (by intro X _; rw [optimalStop_zero hG]; rfl)
      rw [hz, walkExp_const hG, odometer_zero]
  | succ n ih =>
      intro x
      by_cases hz : value G (excess σ) (n + 1) x = 0
      · have hzero : ∀ X : ℕ → V, X 0 = x → optimalStop G (excess σ) (n + 1) X = 0 := by
          intro X hX
          exact Nat.eq_zero_of_le_zero
            (Nat.sInf_le ⟨Nat.zero_le _, by rw [hX]; simpa using hz⟩)
        have hcong : walkExp G (n + 1) x
              (fun X => payoff G (excess σ) (optimalStop G (excess σ) (n + 1) X) X)
            = walkExp G (n + 1) x (fun _ => (0 : ℝ)) :=
          walkExp_congr (by intro X hX; rw [hzero X hX]; rfl)
        rw [hcong, walkExp_const hG, ← value_eq hG]
        exact hz.symm
      · have hne : ∀ X : ℕ → V, X 0 = x → optimalStop G (excess σ) (n + 1) X ≠ 0 := by
          intro X hX h
          apply hz
          have hmem := Nat.sInf_mem (stopSet_nonempty hG σ (n + 1) X)
          rw [optimalStop_eq_sInf] at h
          rw [h] at hmem
          simpa [hX] using hmem.2
        rw [walkExp_payoff_succ hG (excess σ) n x hne, scenery_eq]
        have hy : ∀ y ∈ G.neighborFinset x,
            walkExp G n y (fun X' => payoff G (excess σ)
                (optimalStop G (excess σ) (n + 1) (cons x X') - 1) X')
              = odometer G σ n y := by
          intro y _
          rw [show walkExp G n y (fun X' => payoff G (excess σ)
                (optimalStop G (excess σ) (n + 1) (cons x X') - 1) X')
              = walkExp G n y
                (fun X' => payoff G (excess σ) (optimalStop G (excess σ) n X') X') from
            walkExp_congr (by
              intro X' _
              rw [optimalStop_cons hG σ n x hz X']
              simp)]
          exact ih y
        rw [show walkOp G (fun y => walkExp G n y (fun X' => payoff G (excess σ)
              (optimalStop G (excess σ) (n + 1) (cons x X') - 1) X')) x
            = walkOp G (odometer G σ n) x from by
          simp only [walkOp]
          rw [Finset.sum_congr rfl hy]]
        have hA : 0 ≤ walkOp G (odometer G σ n) x + scenery G σ x := by
          by_contra hc
          rw [not_le] at hc
          exact hz (by rw [value_eq hG, LatticeProb.Graph.odometerRecursion hG σ n x, max_eq_right hc.le])
        rw [LatticeProb.Graph.odometerRecursion hG σ n x, max_eq_left hA]
        ring

end LatticeProb.Graph
