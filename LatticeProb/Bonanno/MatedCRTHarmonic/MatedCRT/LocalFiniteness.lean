/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.LocalFiniteness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianPathFacts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite

/-!
# Almost-sure local finiteness of the mated-CRT graph

The proof reduces local finiteness to the fact that each coordinate goes below every level on
both time tails. A low value in the interval between a fixed vertex and a sufficiently distant
vertex violates the mated-CRT side condition.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

private theorem intervalInf_le_eval_of_continuous {X : ℝ → ℝ} (hX : Continuous X)
    {a b t : ℝ} (ht : t ∈ Icc a b) : intervalInf X a b ≤ X t := by
  rw [intervalInf]
  exact csInf_le (isCompact_Icc.bddBelow_image hX.continuousOn) ⟨t, ht, rfl⟩

private theorem no_far_right_sideCond {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ}
    (hε : 0 < ε) (x : ℤ)
    (hbelow : ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧ X (n : ℝ) < -(m : ℝ)) :
    ∃ N : ℕ, ∀ y : ℤ, (N : ℤ) < y → ¬ SideCond ε X x y := by
  let a := intervalInf X (ε * ((x : ℝ) - 1)) (ε * x)
  obtain ⟨m, hm⟩ := exists_nat_gt (-a)
  obtain ⟨k, hk⟩ := exists_nat_gt (ε * (x : ℝ))
  obtain ⟨n, hnk, hlow⟩ := hbelow m k
  have hkn : ε * (x : ℝ) ≤ (k : ℝ) := le_of_lt (by exact_mod_cast hk)
  have hnt : ε * (x : ℝ) ≤ (n : ℝ) := by
    exact hkn.trans (by exact_mod_cast hnk)
  have hlow' : X (n : ℝ) < a := by
    have hm' : -(m : ℝ) < a := by linarith
    exact hlow.trans hm'
  obtain ⟨N, hN⟩ := exists_nat_gt ((n : ℝ) / ε + 1)
  refine ⟨N, ?_⟩
  intro y hy hside
  have hyreal : (N : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hntop : (n : ℝ) ≤ ε * ((y : ℝ) - 1) := by
    have hq : (n : ℝ) / ε < (y : ℝ) - 1 := by linarith
    have hmul := (div_lt_iff₀ hε).mp hq
    linarith
  have htmem : (n : ℝ) ∈ Icc (ε * (x : ℝ)) (ε * ((y : ℝ) - 1)) := ⟨hnt, hntop⟩
  have hmiddle : intervalInf X (ε * (x : ℝ)) (ε * ((y : ℝ) - 1)) ≤ X (n : ℝ) :=
    intervalInf_le_eval_of_continuous hX htmem
  have hleft : a ≤ intervalInf X (ε * (x : ℝ)) (ε * ((y : ℝ) - 1)) := by
    unfold SideCond at hside
    exact (le_max_left _ _).trans hside
  linarith

private theorem no_far_left_sideCond {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ}
    (hε : 0 < ε) (x : ℤ)
    (hbelow : ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧ X (-(n : ℝ)) < -(m : ℝ)) :
    ∃ N : ℕ, ∀ y : ℤ, y < -(N : ℤ) → ¬ SideCond ε X y x := by
  let a := intervalInf X (ε * ((x : ℝ) - 1)) (ε * x)
  obtain ⟨m, hm⟩ := exists_nat_gt (-a)
  obtain ⟨k, hk⟩ := exists_nat_gt (-(ε * ((x : ℝ) - 1)))
  obtain ⟨n, hnk, hlow⟩ := hbelow m k
  have hkn : -(ε * ((x : ℝ) - 1)) ≤ (k : ℝ) := le_of_lt (by exact_mod_cast hk)
  have hnt : -(n : ℝ) ≤ ε * ((x : ℝ) - 1) := by
    have hnk' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnk
    linarith
  have hlow' : X (-(n : ℝ)) < a := by
    have hm' : -(m : ℝ) < a := by linarith
    exact hlow.trans hm'
  obtain ⟨N, hN⟩ := exists_nat_gt ((n : ℝ) / ε + 1)
  refine ⟨N, ?_⟩
  intro y hy hside
  have hyreal : (y : ℝ) < -(N : ℝ) := by exact_mod_cast hy
  have hnbot : ε * (y : ℝ) ≤ -(n : ℝ) := by
    have hq : (y : ℝ) < -((n : ℝ) / ε) := by linarith
    have hmul := mul_lt_mul_of_pos_left hq hε
    have hdiv : ε * ((n : ℝ) / ε) = (n : ℝ) := by field_simp
    simp only [mul_neg] at hmul
    rw [hdiv] at hmul
    linarith
  have htmem : (-(n : ℝ)) ∈ Icc (ε * (y : ℝ)) (ε * ((x : ℝ) - 1)) := ⟨hnbot, hnt⟩
  have hmiddle : intervalInf X (ε * (y : ℝ)) (ε * ((x : ℝ) - 1)) ≤ X (-(n : ℝ)) :=
    intervalInf_le_eval_of_continuous hX htmem
  have hright : a ≤ intervalInf X (ε * (y : ℝ)) (ε * ((x : ℝ) - 1)) := by
    unfold SideCond at hside
    exact (le_max_right _ _).trans hside
  linarith

private theorem coordinate_continuous (ω : Path2) (i : Fin 2) :
    Continuous (fun t : ℝ => lrCoord i t ω) := by
  unfold lrCoord
  split_ifs with hi
  · exact continuous_fst.comp ω.continuous
  · exact continuous_snd.comp ω.continuous

/-- Two-sided coordinate recurrence implies local finiteness of the frozen edge relation. -/
theorem locallyFinite_of_unboundedBelowInt {ε : ℝ} {ω : Path2} (hε : 0 < ε)
    (hplus : ∀ i : Fin 2, ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      lrCoord i (n : ℝ) ω < -(m : ℝ))
    (hminus : ∀ i : Fin 2, ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      lrCoord i (-(n : ℝ)) ω < -(m : ℝ)) :
    IsLocallyFinite ε ω := by
  intro x
  let S : Set (Edge ε ω) := {e | e.1.1 = x ∨ e.1.2.1 = x}
  obtain ⟨Nr0, hNr0⟩ := no_far_right_sideCond (coordinate_continuous ω 0) hε x (hplus 0)
  obtain ⟨Nr1, hNr1⟩ := no_far_right_sideCond (coordinate_continuous ω 1) hε x (hplus 1)
  obtain ⟨Nl0, hNl0⟩ := no_far_left_sideCond (coordinate_continuous ω 0) hε x (hminus 0)
  obtain ⟨Nl1, hNl1⟩ := no_far_left_sideCond (coordinate_continuous ω 1) hε x (hminus 1)
  let Nright := max Nr0 Nr1
  let Nleft := max Nl0 Nl1
  let lo : ℤ := min (-(Nleft : ℤ)) (x - 1)
  let hi : ℤ := max (Nright : ℤ) (x + 1)
  have hxlo : lo ≤ x := by
    dsimp [lo]
    exact (min_le_right _ _).trans (by omega)
  have hxhi : x ≤ hi := by
    dsimp [hi]
    exact (by omega : x ≤ x + 1).trans (le_max_right _ _)
  have hbounded : ∀ e : Edge ε ω, e ∈ S →
      e.1.1 ∈ Icc lo hi ∧ e.1.2.1 ∈ Icc lo hi := by
    intro e he
    change e.1.1 = x ∨ e.1.2.1 = x at he
    rcases e.2 with ⟨hlt, hkind⟩
    rcases he with hsrc | htgt
    · have htargetLower : x < e.1.2.1 := by simpa [hsrc] using hlt
      have htargetUpper : e.1.2.1 ≤ hi := by
        rcases hkind with hsucc | hside
        · have htargetEq : e.1.2.1 = x + 1 := by simpa [hsrc] using hsucc.1
          rw [htargetEq]
          exact le_max_right _ _
        · rcases hside with ⟨_, hside⟩
          by_cases htag : e.1.2.2
          · have hs : SideCond ε (fun t => lrCoord 1 t ω) x e.1.2.1 := by
              simpa [hsrc, htag, lrCoord] using hside
            by_contra hlarge
            have hNrle : (Nr1 : ℤ) ≤ hi := by
              have hcast : (Nr1 : ℤ) ≤ (Nright : ℤ) := by
                dsimp [Nright]
                exact_mod_cast (le_max_right Nr0 Nr1)
              have hhi : (Nright : ℤ) ≤ hi := by
                dsimp [hi]
                exact le_max_left _ _
              exact hcast.trans hhi
            exact hNr1 _ (lt_of_le_of_lt hNrle (lt_of_not_ge hlarge)) hs
          · have hs : SideCond ε (fun t => lrCoord 0 t ω) x e.1.2.1 := by
              simpa [hsrc, htag, lrCoord] using hside
            by_contra hlarge
            have hNrle : (Nr0 : ℤ) ≤ hi := by
              have hcast : (Nr0 : ℤ) ≤ (Nright : ℤ) := by
                dsimp [Nright]
                exact_mod_cast (le_max_left Nr0 Nr1)
              have hhi : (Nright : ℤ) ≤ hi := by
                dsimp [hi]
                exact le_max_left _ _
              exact hcast.trans hhi
            exact hNr0 _ (lt_of_le_of_lt hNrle (lt_of_not_ge hlarge)) hs
      constructor
      · rw [hsrc]
        exact ⟨hxlo, hxhi⟩
      · exact ⟨le_trans hxlo (le_of_lt htargetLower), htargetUpper⟩
    · have hsourceUpper : e.1.1 < x := by simpa [htgt] using hlt
      have hsourceLower : lo ≤ e.1.1 := by
        rcases hkind with hsucc | hside
        · have hsourceEq : e.1.1 = x - 1 := by
            have htargetEq : e.1.2.1 = x := htgt
            omega
          rw [hsourceEq]
          exact min_le_right _ _
        · rcases hside with ⟨_, hside⟩
          by_cases htag : e.1.2.2
          · have hs : SideCond ε (fun t => lrCoord 1 t ω) e.1.1 x := by
              simpa [htgt, htag, lrCoord] using hside
            by_contra hsmall
            have hloNl : lo ≤ -((Nl1 : ℕ) : ℤ) := by
              change min (-(Nleft : ℤ)) (x - 1) ≤ -((Nl1 : ℕ) : ℤ)
              have hcast : (Nl1 : ℤ) ≤ (Nleft : ℤ) := by
                dsimp [Nleft]
                exact_mod_cast (le_max_right Nl0 Nl1)
              exact (min_le_left _ _).trans (neg_le_neg hcast)
            exact hNl1 _ (lt_of_lt_of_le (lt_of_not_ge hsmall) hloNl) hs
          · have hs : SideCond ε (fun t => lrCoord 0 t ω) e.1.1 x := by
              simpa [htgt, htag, lrCoord] using hside
            by_contra hsmall
            have hloNl : lo ≤ -((Nl0 : ℕ) : ℤ) := by
              change min (-(Nleft : ℤ)) (x - 1) ≤ -((Nl0 : ℕ) : ℤ)
              have hcast : (Nl0 : ℤ) ≤ (Nleft : ℤ) := by
                dsimp [Nleft]
                exact_mod_cast (le_max_left Nl0 Nl1)
              exact (min_le_left _ _).trans (neg_le_neg hcast)
            exact hNl0 _ (lt_of_lt_of_le (lt_of_not_ge hsmall) hloNl) hs
      constructor
      · exact ⟨hsourceLower, le_trans (le_of_lt hsourceUpper) hxhi⟩
      · rw [htgt]
        exact ⟨hxlo, hxhi⟩
  have hfiniteProduct : (Icc lo hi ×ˢ (Icc lo hi ×ˢ (Set.univ : Set Bool))).Finite := by
    exact (finite_Icc lo hi).prod ((finite_Icc lo hi).prod Set.finite_univ)
  have hfiniteImage : (Subtype.val '' S).Finite := hfiniteProduct.subset (by
    rintro z ⟨e, he, rfl⟩
    rcases hbounded e he with ⟨ha, hb⟩
    exact ⟨ha, hb, trivial⟩)
  exact hfiniteImage.of_finite_image (by
    intro e he₁ f he₂ h
    exact Subtype.val_injective h)

end MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic

/-- Almost-sure local finiteness of the ε-mated-CRT graph for every positive mesh. -/
theorem ae_isLocallyFinite_holds :
    ∀ (γ : ℝ) (μ : Measure MatedCRT.Path2), MatedCRT.IsCorrelatedBM2 γ μ →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, MatedCRT.IsLocallyFinite ε ω := by
  intro γ μ hμ ε hε
  have hp0 := MatedCRT.BrownianPathFacts.ae_unboundedBelowInt
    (MatedCRT.coordinate_isPreBrownianReal hμ 0)
    (fun t => MatedCRT.measurable_lrCoord (0, (t : ℝ)))
  have hp1 := MatedCRT.BrownianPathFacts.ae_unboundedBelowInt
    (MatedCRT.coordinate_isPreBrownianReal hμ 1)
    (fun t => MatedCRT.measurable_lrCoord (1, (t : ℝ)))
  have hn0 := MatedCRT.BrownianPathFacts.ae_unboundedBelowInt
    (MatedCRT.coordinate_neg_isPreBrownianReal hμ 0)
    (fun t => MatedCRT.measurable_lrCoord (0, -(t : ℝ)))
  have hn1 := MatedCRT.BrownianPathFacts.ae_unboundedBelowInt
    (MatedCRT.coordinate_neg_isPreBrownianReal hμ 1)
    (fun t => MatedCRT.measurable_lrCoord (1, -(t : ℝ)))
  filter_upwards [hp0, hp1, hn0, hn1] with ω hp0 hp1 hn0 hn1
  have hp0' : ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      MatedCRT.lrCoord 0 (n : ℝ) ω < -(m : ℝ) := by
    simpa [MatedCRT.BrownianPathFacts.unboundedBelowInt] using hp0
  have hp1' : ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      MatedCRT.lrCoord 1 (n : ℝ) ω < -(m : ℝ) := by
    simpa [MatedCRT.BrownianPathFacts.unboundedBelowInt] using hp1
  have hn0' : ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      MatedCRT.lrCoord 0 (-(n : ℝ)) ω < -(m : ℝ) := by
    simpa [MatedCRT.BrownianPathFacts.unboundedBelowInt] using hn0
  have hn1' : ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      MatedCRT.lrCoord 1 (-(n : ℝ)) ω < -(m : ℝ) := by
    simpa [MatedCRT.BrownianPathFacts.unboundedBelowInt] using hn1
  have hplus : ∀ i : Fin 2, ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      MatedCRT.lrCoord i (n : ℝ) ω < -(m : ℝ) := by
    intro i m k
    fin_cases i
    · exact hp0' m k
    · exact hp1' m k
  have hminus : ∀ i : Fin 2, ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧
      MatedCRT.lrCoord i (-(n : ℝ)) ω < -(m : ℝ) := by
    intro i m k
    fin_cases i
    · exact hn0' m k
    · exact hn1' m k
  exact MatedCRT.locallyFinite_of_unboundedBelowInt hε hplus hminus

end MatedCRTHarmonic
