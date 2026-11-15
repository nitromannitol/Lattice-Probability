import LatticeProb.Prob.NetworkBackwardCellErrors
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianFailure

/-! # First-failure bounds from backward endpoint cells -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne
open scoped Topology ENNReal

namespace LatticeProb

local instance (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤

/-- Backward endpoint cells chosen independently of the network scale and the
selectors yield an actual walk–Brownian first-failure bound. -/
theorem exists_network_backward_cells_first_failure
    {d : ℕ} (hd : 1 ≤ d) {J : Type*} [Fintype J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U I : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (hI : ∀ j, IsCompact (I j))
    (hIU : ∀ j, I j ⊆ U j)
    (ρ : Measure (BrownianPath d)) [IsProbabilityMeasure ρ] (hρ : IsStandardBrownianLaw ρ)
    (V : ℕ → Type*) [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    (N : ∀ n, FiniteConductanceNetwork (V n)) (pos : ∀ n, V n → Euc d)
    (hpos : ∀ n, Measurable (pos n)) (hinj : ∀ n, Function.Injective (pos n))
    (B : ∀ n, J → Set (V n))
    (hB : ∀ n j v, v ∈ B n j → 0 < (N n).totalConductance v)
    (ν : ∀ j, I j → ProbabilityMeasure (Euc d))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) z.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : pos n v ∈ I j,
      levyProkhorovDist (((N n).discreteHarmonicMeasure (B n j) (hB n j) v).map (pos n))
        (ν j ⟨pos n v, hv⟩ : Measure (Euc d)) < ε)
    (K : Set (Euc d)) (hK : IsCompact K) (hKU : ∀ j, closure (U j) ⊆ K)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (L : ℕ) :
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ)
      (hdisj : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
      (hmeas : ∀ i k, MeasurableSet (E i k)),
      (∀ i, 0 < δ i) ∧
      (∀ i, K ⊆ ⋃ k, E i k) ∧
      (∀ i k, Bornology.IsBounded (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      ∀ᶠ n in atTop, ∀ (choice : ∀ i, Fin (m i) → Option J),
        (∀ i k j, choice i k = some j → E i k ⊆ I j) →
        ∀ (initial : J) (v₀ : V n) (z : Euc d),
        pos n v₀ ∈ I initial → z ∈ I initial →
        dist (pos n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun q => ⟨min q L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun q => m (ix q)
        let E' : ∀ q, Fin (m' q) → Set (Euc d) := fun q => E (ix q)
        let choice' : ∀ q, Fin (m' q) → Option J := fun q => choice (ix q)
        let select := fun q => cellSelector (E' q) (choice' q)
        let hs : ∀ q, Measurable (select q) := fun q =>
          measurable_cellSelector (E' q) (choice' q) (hdisj (ix q)) (hmeas (ix q))
        (N n).walkBrownianJointLaw (pos n) (hinj n) (B n) (hB n) U hU ρ select hs
          m' E' (fun q => hmeas (ix q)) (fun q => hdisj (ix q)) initial v₀ z
          {p | ∃ i ≤ L, (p.1 i, p.2 i) ∉ goodExcursionPair (pos n) (E' i) a} ≤
            (L + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  obtain ⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, hdiam, hback, hnull, herr⟩ :=
    exists_network_backward_cells_with_errors hd U I hU hUb hI hIU ρ hρ V N pos hpos B hB
      ν hνlaw hν hLP K hK a b ha hb L
  refine ⟨m, E, δ, hdisj, hmeas, hδ, hcover, hbounded, hdiam, ?_⟩
  filter_upwards [herr] with n hn
  intro choice hinner initial v₀ z hv hz hnear
  have he := hn choice hinner initial v₀ z hv hz hnear
  exact (N n).walkBrownianJointLaw_firstFailure_le hd (pos n) (hinj n) (B n) (hB n)
    U hU hUb ρ hρ _ _ _ _ _ _ _ (fun _ => rfl) L hb.le
    (fun q _ => hdiam _) (fun q _ k j h => (hinner _ k j h).trans (hIU j))
    (fun q _ j => (hKU j).trans (hcover _)) he.1 initial v₀ z (hIU initial hz) he.2

end LatticeProb
