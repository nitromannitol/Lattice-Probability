import LatticeProb.Prob.NetworkBackwardFirstFailure

/-! # Ball selectors for finite-network excursion couplings -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set Metric BouRabeeGwynne
open scoped Topology ENNReal

namespace LatticeProb

local instance (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤

/-- Backward cells admit selectors active on a covered set, with a fixed ball
margin and a uniform finite-network first-failure bound. -/
theorem exists_network_ball_selectors_first_failure
    {d : ℕ} (hd : 1 ≤ d) (centers : Finset (Euc d)) {r : ℝ} (hr : 0 < r)
    [MeasurableSpace (Option ↥centers)] [MeasurableSingletonClass (Option ↥centers)]
    (C K : Set (Euc d)) (hK : IsCompact K) (hCK : C ⊆ K)
    (hcover : ∀ x ∈ C, ∃ c ∈ centers, x ∈ ball c (r / 4))
    (hballK : ∀ j : centers, closure (ball j.val r) ⊆ K)
    (ρ : Measure (BrownianPath d)) [IsProbabilityMeasure ρ] (hρ : IsStandardBrownianLaw ρ)
    (V : ℕ → Type*) [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    (N : ∀ n, FiniteConductanceNetwork (V n)) (pos : ∀ n, V n → Euc d)
    (hpos : ∀ n, Measurable (pos n)) (hinj : ∀ n, Function.Injective (pos n))
    (B : ∀ n, centers → Set (V n))
    (hB : ∀ n j v, v ∈ B n j → 0 < (N n).totalConductance v)
    (ν : ∀ j : centers, closedBall j.val (r / 2) → ProbabilityMeasure (Euc d))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (ball j.val r) z.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j : centers, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : pos n v ∈ closedBall j.val (r / 2),
      levyProkhorovDist (((N n).discreteHarmonicMeasure (B n j) (hB n j) v).map (pos n))
        (ν j (⟨pos n v, hv⟩ : closedBall j.val (r / 2)) : Measure (Euc d)) < ε)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (L : ℕ) :
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ)
      (hdisj : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
      (hmeas : ∀ i k, MeasurableSet (E i k))
      (choice : ∀ i, Fin (m i) → Option ↥centers),
      (∀ i, 0 < δ i) ∧
      (∀ i, K ⊆ ⋃ k, E i k) ∧
      (∀ i x, x ∈ C → cellSelector (E i) (choice i) x ≠ none) ∧
      (∀ i x j, cellSelector (E i) (choice i) x = some j →
        ball x (r / 2) ⊆ ball j.val r) ∧
      ∀ᶠ n in atTop, ∀ (initial : centers) (v₀ : V n) (z : Euc d),
        pos n v₀ ∈ closedBall initial.val (r / 2) →
        z ∈ closedBall initial.val (r / 2) →
        dist (pos n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun q => ⟨min q L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun q => m (ix q)
        let E' : ∀ q, Fin (m' q) → Set (Euc d) := fun q => E (ix q)
        let select := fun q => cellSelector (E' q) (choice (ix q))
        let hs : ∀ q, Measurable (select q) := fun q =>
          measurable_cellSelector (E' q) (choice (ix q)) (hdisj (ix q)) (hmeas (ix q))
        (N n).walkBrownianJointLaw (pos n) (hinj n) (B n) (hB n)
          (fun j : centers => ball j.val r) (fun _ => isOpen_ball) ρ select hs
          m' E' (fun q => hmeas (ix q)) (fun q => hdisj (ix q)) initial v₀ z
          {p | ∃ i ≤ L, (p.1 i, p.2 i) ∉ goodExcursionPair (pos n) (E' i) (min a (r / 4))} ≤
            (L + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  have hmin : 0 < min a (r / 4) := lt_min ha (by positivity)
  obtain ⟨m, E, δ, hdE, hmE, hδ, hEK, hbounded, hdiam, hfail⟩ :=
    exists_network_backward_cells_first_failure hd
      (fun j : centers => ball j.val r) (fun j : centers => closedBall j.val (r / 2))
      (fun _ => isOpen_ball) (fun _ => isBounded_ball) (fun _ => isCompact_closedBall _ _)
      (fun _ => closedBall_subset_ball (half_lt_self hr))
      ρ hρ V N pos hpos hinj B hB ν hνlaw hν hLP K hK hballK
      (min a (r / 4)) b hmin hb L
  have hex (i : Fin (L + 1)) : ∃ ch : Fin (m i) → Option ↥centers,
      (∀ k, ch k = none ↔ E i k ∩ C = ∅) ∧
      ∀ k j, ch k = some j → E i k ⊆ ball j.val (r / 2) :=
    exists_cell_ball_choices (E i) hcover
      (fun k x hx y hy => (hdiam i k x hx y hy).trans (min_le_right _ _))
  choose choice hnone hinner using hex
  refine ⟨m, E, δ, hdE, hmE, choice, hδ, hEK, ?_, ?_, ?_⟩
  · intro i x hx hn
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hEK i (hCK hx))
    have hlabel := (cellLabel_eq_some_iff (E i) (hdE i) x k).mpr hk
    have hch : choice i k = none := (cellSelector_of_label (E i) (choice i) hlabel).symm.trans hn
    exact (Set.notMem_empty x) ((hnone i k).mp hch ▸ (show x ∈ E i k ∩ C from ⟨hk, hx⟩))
  · intro i x j hj y hy
    obtain ⟨k, hx, hchoice⟩ := cellSelector_some_mem (E i) (choice i) hj
    have hxj := hinner i k j hchoice hx
    change dist y j.val < r
    calc
      dist y j.val ≤ dist y x + dist x j.val := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hy hxj
      _ = r := by ring
  · filter_upwards [hfail] with n hn
    apply hn choice
    intro i k j hj
    exact (hinner i k j hj).trans ball_subset_closedBall

end LatticeProb
