/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.BrownianG0 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianPathFacts
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Main
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle

/-!
# Brownian-only inputs for the Route M Peanosphere bundle

The almost-sure lower and upper excursions at both ends of each coordinate follow from the
one-sided Brownian path lemma in `BrownianPathFacts`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

/-- On the positive half-line, `twoSidedMin` is the ordinary minimum kernel. -/
private theorem twoSidedMin_of_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    twoSidedMin s t = min s t := by
  simp [twoSidedMin, max_eq_left hs, max_eq_left ht,
    max_eq_right (by linarith : -s ≤ 0), max_eq_right (by linarith : -t ≤ 0)]

/-- On the negative half-line, `twoSidedMin` is the minimum kernel after reflection. -/
private theorem twoSidedMin_of_nonpos {s t : ℝ} (hs : s ≤ 0) (ht : t ≤ 0) :
    twoSidedMin s t = min (-s) (-t) := by
  simp [twoSidedMin, max_eq_right hs, max_eq_right ht,
    max_eq_left (by linarith : 0 ≤ -s), max_eq_left (by linarith : 0 ≤ -t)]

/-- `twoSidedMin` vanishes when its arguments have opposite signs. -/
private theorem twoSidedMin_cross {s t : ℝ} (hs : s ≤ 0) (ht : 0 ≤ t) :
    twoSidedMin s t = 0 := by
  simp [twoSidedMin, max_eq_right hs, max_eq_left ht,
    max_eq_left (by linarith : 0 ≤ -s), max_eq_right (by linarith : -t ≤ 0),
    min_eq_left (show 0 ≤ t by exact ht), min_eq_right (show 0 ≤ -s by linarith)]

private theorem twoSidedMin_comm (s t : ℝ) : twoSidedMin s t = twoSidedMin t s := by
  simp [twoSidedMin, min_comm]

/-- Translating both arguments of the two-sided Brownian covariance by ordered nonnegative time
increments gives the ordinary Brownian covariance of the increments. -/
private theorem twoSidedMin_increment_of_le {a s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s ≤ t) :
    twoSidedMin (a + s) (a + t) - twoSidedMin (a + s) a -
      twoSidedMin (a + t) a + twoSidedMin a a = min s t := by
  by_cases ha : 0 ≤ a
  · have h1 := twoSidedMin_of_nonneg (by linarith : 0 ≤ a + s) (by linarith : 0 ≤ a + t)
    have h2 := twoSidedMin_of_nonneg (by linarith : 0 ≤ a + s) ha
    have h3 := twoSidedMin_of_nonneg (by linarith : 0 ≤ a + t) ha
    have h4 := twoSidedMin_of_nonneg ha ha
    rw [h1, h2, h3, h4, min_eq_left hst]
    simp [min_eq_left (show a + s ≤ a + t by linarith), min_eq_right (show a ≤ a + s by linarith),
      min_eq_right (show a ≤ a + t by linarith)]
  · have ha' : a < 0 := lt_of_not_ge ha
    by_cases has : 0 ≤ a + s
    · have hat : 0 ≤ a + t := by linarith
      have h1 := twoSidedMin_of_nonneg has hat
      have h2' := twoSidedMin_cross (le_of_lt ha') has
      have h2 : twoSidedMin (a + s) a = 0 := by
        rw [twoSidedMin_comm]
        exact h2'
      have h3' := twoSidedMin_cross (le_of_lt ha') hat
      have h3 : twoSidedMin (a + t) a = 0 := by
        rw [twoSidedMin_comm]
        exact h3'
      have h4 := twoSidedMin_of_nonpos (s := a) (t := a) (le_of_lt ha') (le_of_lt ha')
      rw [h1, h2, h3, h4, min_eq_left hst]
      rw [min_eq_left (show a + s ≤ a + t by linarith), min_self]
      linarith
    · have has' : a + s < 0 := lt_of_not_ge has
      by_cases hat : a + t ≤ 0
      · have h1 := twoSidedMin_of_nonpos (s := a + s) (t := a + t) (le_of_lt has') hat
        have h2 := twoSidedMin_of_nonpos (s := a + s) (t := a) (le_of_lt has') (le_of_lt ha')
        have h3 := twoSidedMin_of_nonpos (s := a + t) (t := a) hat (le_of_lt ha')
        have h4 := twoSidedMin_of_nonpos (s := a) (t := a) (le_of_lt ha') (le_of_lt ha')
        rw [h1, h2, h3, h4, min_eq_left hst]
        rw [min_eq_right (show -(a + t) ≤ -(a + s) by linarith),
          min_eq_left (show -(a + s) ≤ -a by linarith),
          min_eq_left (show -(a + t) ≤ -a by linarith), min_self]
        linarith
      · have hat' : 0 < a + t := lt_of_not_ge hat
        have h1 := twoSidedMin_cross (le_of_lt has') (le_of_lt hat')
        have h2 := twoSidedMin_of_nonpos (s := a + s) (t := a) (le_of_lt has') (le_of_lt ha')
        have h3' := twoSidedMin_cross (le_of_lt ha') (le_of_lt hat')
        have h3 : twoSidedMin (a + t) a = 0 := by
          rw [twoSidedMin_comm]
          exact h3'
        have h4 := twoSidedMin_of_nonpos (s := a) (t := a) (le_of_lt ha') (le_of_lt ha')
        rw [h1, h2, h3, h4, min_eq_left hst]
        rw [min_eq_left (show -(a + s) ≤ -a by linarith), min_self]
        linarith

/-- Translating both arguments of the two-sided Brownian covariance by nonnegative time
increments gives the ordinary Brownian covariance of the increments. -/
private theorem twoSidedMin_increment {a s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    twoSidedMin (a + s) (a + t) - twoSidedMin (a + s) a -
      twoSidedMin (a + t) a + twoSidedMin a a = min s t := by
  rcases le_total s t with hst | hts
  · exact twoSidedMin_increment_of_le hs ht hst
  · calc
      twoSidedMin (a + s) (a + t) - twoSidedMin (a + s) a -
          twoSidedMin (a + t) a + twoSidedMin a a =
        twoSidedMin (a + t) (a + s) - twoSidedMin (a + t) a -
          twoSidedMin (a + s) a + twoSidedMin a a := by
            rw [twoSidedMin_comm (a + s) (a + t)]
            ring
      _ = min t s := twoSidedMin_increment_of_le (a := a) (s := t) (t := s) ht hs hts
      _ = min s t := by rw [min_comm]

/-- A deterministic-time shift of a correlated coordinate, recentered at the shift time. -/
def shiftedCoordinate (i : Fin 2) (a : ℝ) : ℝ≥0 → Path2 → ℝ :=
  fun t ω => lrCoord i (a + (t : ℝ)) ω - lrCoord i a ω

/-- Recentered future increments of either correlated coordinate form a standard Brownian motion. -/
theorem shiftedCoordinate_isBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (a : ℝ) :
    IsBrownianReal (shiftedCoordinate i a) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let X : ℝ → Path2 → ℝ := fun t ω => lrCoord i t ω
  have hX : IsGaussianProcess X μ := hμ.isGaussianProcess.comp_right (fun t : ℝ => (i, t))
  have hshift : IsGaussianProcess
      (fun t : ℝ≥0 => fun ω => X (a + (t : ℝ)) ω - X a ω) μ :=
    (hX.shift a).comp_right (fun t : ℝ≥0 => (t : ℝ))
  have hmean : ∀ t : ℝ≥0, ∫ ω, X (a + (t : ℝ)) ω - X a ω ∂μ = 0 := by
    intro t
    have h1 : Integrable (X (a + (t : ℝ))) μ :=
      (hX.hasGaussianLaw_eval (a + (t : ℝ))).memLp_two.integrable (by norm_num)
    have h2 : Integrable (X a) μ := (hX.hasGaussianLaw_eval a).memLp_two.integrable (by norm_num)
    rw [integral_sub h1 h2, hμ.integral_eq_zero i (a + (t : ℝ)), hμ.integral_eq_zero i a, sub_self]
  have hcov : ∀ s t : ℝ≥0, s ≤ t →
      cov[fun ω => X (a + (s : ℝ)) ω - X a ω,
        fun ω => X (a + (t : ℝ)) ω - X a ω; μ] = s := by
    intro s t hst
    have hs : MemLp (X (a + (s : ℝ))) 2 μ :=
      (hX.hasGaussianLaw_eval (a + (s : ℝ))).memLp_two
    have ht : MemLp (X (a + (t : ℝ))) 2 μ :=
      (hX.hasGaussianLaw_eval (a + (t : ℝ))).memLp_two
    have ha : MemLp (X a) 2 μ := (hX.hasGaussianLaw_eval a).memLp_two
    rw [covariance_fun_sub_fun_sub hs ha ht ha,
      hμ.covariance_eq i i (a + (s : ℝ)) (a + (t : ℝ)),
      hμ.covariance_eq i i (a + (s : ℝ)) a,
      hμ.covariance_eq i i a (a + (t : ℝ)), hμ.covariance_eq i i a a]
    simp [lrCov]
    rw [twoSidedMin_comm a (a + (t : ℝ)),
      twoSidedMin_increment (a := a) (s := (s : ℝ)) (t := (t : ℝ)) s.2 t.2,
      min_eq_left (by exact_mod_cast hst)]
  have hpre : IsPreBrownianReal (shiftedCoordinate i a) μ := by
    apply hshift.isPreBrownianReal_of_covariance hmean
    intro s t hst
    simpa [shiftedCoordinate, X] using hcov s t hst
  refine ⟨hpre, ?_⟩
  apply ae_of_all
  intro ω
  have hx : Continuous (fun t : ℝ => lrCoord i t ω) := by
    by_cases hi : i = 0
    · subst i
      simp only [lrCoord, ↓reduceIte]
      exact continuous_fst.comp ω.continuous
    · simp only [lrCoord, hi, ↓reduceIte]
      exact continuous_snd.comp ω.continuous
  change Continuous (fun t : ℝ≥0 => lrCoord i (a + (t : ℝ)) ω - lrCoord i a ω)
  exact (hx.comp (continuous_const.add continuous_subtype_val)).sub continuous_const

private theorem shifted_path_localMinOn_of_global {i : Fin 2} {ω : Path2} {p a : ℝ}
    (hpa : p ≤ a) (ha : IsLocalMin (lrCoord i · ω) a) :
    IsLocalMinOn (MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i p) ω)
      (Ici 0) (a - p) := by
  have haI : IsLocalMinOn (lrCoord i · ω) (Ici p) a := ha.isLocalMinOn _
  have hcomp : IsLocalMinOn (fun t => lrCoord i (t + p) ω) (Ici 0) (a - p) := by
    have haI' : IsLocalMinOn (lrCoord i · ω) (Ici p) ((a - p) + p) := by
      simpa [sub_add_cancel] using haI
    have h := haI'.comp_continuousOn
      (s := Ici 0) (g := fun t => t + p)
      (by intro t ht; change 0 ≤ t at ht; change p ≤ t + p; linarith)
      (by fun_prop) (by change 0 ≤ a - p; linarith)
    have heq : ((lrCoord i · ω) ∘ (fun t => t + p)) =ᶠ[𝓝[Ici 0] (a - p)]
        (fun t => lrCoord i (t + p) ω) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rfl
    exact h.congr heq (Set.mem_Ici.mpr (by linarith))
  have hsub : IsLocalMinOn (fun t => lrCoord i (t + p) ω - lrCoord i p ω)
      (Ici 0) (a - p) :=
    hcomp.comp_mono (fun x y hxy => sub_le_sub_right hxy _)
  have heq : (fun t => MatedCRTHarmonic.MoTPort.BMLocalMin.path
      (shiftedCoordinate i p) ω t) =ᶠ[𝓝[Ici 0] (a - p)]
      (fun t => lrCoord i (t + p) ω - lrCoord i p ω) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [MatedCRTHarmonic.MoTPort.BMLocalMin.path, shiftedCoordinate,
      Real.coe_toNNReal t ht, add_comm]
  have hmem : a - p ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  exact hsub.congr heq.symm hmem

/-- Under every correlated two-sided Brownian law, distinct local minima of either coordinate have
distinct values. The proof applies the one-sided Brownian local-minimum theorem after shifting the
origin to an earlier integer time. -/
theorem ae_locMinDistinct {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, ∀ a b : ℝ, a ≠ b →
      IsLocalMin (lrCoord i · ω) a → IsLocalMin (lrCoord i · ω) b →
      lrCoord i a ω ≠ lrCoord i b ω := by
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hgood : ∀ᵐ ω ∂μ, ∀ i : Fin 2, ∀ p : ℤ,
      MatedCRTHarmonic.MoTPort.BMLocalMin.LocMinGood
        (MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i (p : ℝ)) ω)
        (Ici 0) := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun p => ?_
    exact MatedCRTHarmonic.MoTPort.BMLocalMin.ae_locMinGood_Ici
      (shiftedCoordinate_isBrownianReal hμ i (p : ℝ))
  filter_upwards [hgood] with ω hω
  intro i a b hab hmina hminb
  let p : ℤ := ⌊min a b⌋
  have hpa : (p : ℝ) ≤ a := le_trans (Int.floor_le (min a b)) (min_le_left a b)
  have hpb : (p : ℝ) ≤ b := le_trans (Int.floor_le (min a b)) (min_le_right a b)
  have hmina' := shifted_path_localMinOn_of_global hpa hmina
  have hminb' := shifted_path_localMinOn_of_global hpb hminb
  have hne' : a - (p : ℝ) ≠ b - (p : ℝ) := by
    intro h
    apply hab
    linarith
  have hvalues := (hω i p).2.1 (a - (p : ℝ)) (Set.mem_Ici.mpr (by linarith))
    (b - (p : ℝ)) (Set.mem_Ici.mpr (by linarith)) hmina' hminb' hne'
  intro heq
  apply hvalues
  have haEq : MatedCRTHarmonic.MoTPort.BMLocalMin.path
      (shiftedCoordinate i (p : ℝ)) ω (a - (p : ℝ)) =
      lrCoord i a ω - lrCoord i (p : ℝ) ω := by
    simp [MatedCRTHarmonic.MoTPort.BMLocalMin.path, shiftedCoordinate,
      Real.toNNReal_of_nonneg (by linarith : 0 ≤ a - (p : ℝ)),
      add_sub_cancel_right]
  have hbEq : MatedCRTHarmonic.MoTPort.BMLocalMin.path
      (shiftedCoordinate i (p : ℝ)) ω (b - (p : ℝ)) =
      lrCoord i b ω - lrCoord i (p : ℝ) ω := by
    simp [MatedCRTHarmonic.MoTPort.BMLocalMin.path, shiftedCoordinate,
      Real.toNNReal_of_nonneg (by linarith : 0 ≤ b - (p : ℝ)),
      add_sub_cancel_right]
  rw [haEq, hbEq, heq]

namespace BrownianPathFacts

variable {γ : ℝ} {μ : Measure Path2}

/-- Each coordinate of a correlated two-sided Brownian path has arbitrarily low values at
arbitrarily remote integer times, on both half-lines. -/
theorem ae_coordinate_unboundedBelowInt_both (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    ∀ᵐ ω ∂μ,
      ω ∈ unboundedBelowInt (fun n ω => lrCoord i (n : ℝ) ω) ∧
      ω ∈ unboundedBelowInt (fun n ω => lrCoord i (-(n : ℝ)) ω) := by
  have hpos := ae_unboundedBelowInt (coordinate_isPreBrownianReal hμ i)
    (fun n => measurable_lrCoord (i, (n : ℝ)))
  have hneg := ae_unboundedBelowInt (coordinate_neg_isPreBrownianReal hμ i)
    (fun n => measurable_lrCoord (i, -(n : ℝ)))
  filter_upwards [hpos, hneg] with ω hpos hneg
  exact ⟨hpos, hneg⟩

/-- A Brownian coordinate visits every lower level after every time, and before every negative
time, almost surely. -/
theorem ae_coordinate_liminf_both (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    ∀ᵐ ω ∂μ,
      (∀ M T : ℝ, ∃ t ≥ T, lrCoord i t ω < M) ∧
      (∀ M T : ℝ, ∃ t ≤ -T, lrCoord i t ω < M) := by
  filter_upwards [ae_coordinate_unboundedBelowInt_both hμ i] with ω hω
  constructor
  · intro M T
    obtain ⟨m, hm⟩ := exists_nat_gt (-M)
    let k : ℕ := ⌈max T 0⌉₊
    obtain ⟨n, hkn, hn⟩ := hω.1 m k
    have hkT : T ≤ (k : ℝ) := le_trans (le_max_left T 0) (Nat.le_ceil (max T 0))
    have hTn : T ≤ (n : ℝ) := hkT.trans (by exact_mod_cast hkn)
    refine ⟨(n : ℝ), hTn, ?_⟩
    have hm' : -(m : ℝ) < M := by linarith
    exact lt_of_lt_of_le hn (le_of_lt hm')
  · intro M T
    obtain ⟨m, hm⟩ := exists_nat_gt (-M)
    let k : ℕ := ⌈max T 0⌉₊
    obtain ⟨n, hkn, hn⟩ := hω.2 m k
    have hkT : T ≤ (k : ℝ) := le_trans (le_max_left T 0) (Nat.le_ceil (max T 0))
    have hTn : T ≤ (n : ℝ) := hkT.trans (by exact_mod_cast hkn)
    refine ⟨-(n : ℝ), ?_, ?_⟩
    · linarith
    · have hm' : -(m : ℝ) < M := by linarith
      exact lt_of_lt_of_le hn (le_of_lt hm')

end BrownianPathFacts

variable {γ : ℝ} {μ : Measure Path2}

/-- BM1's lower-excursion fields for the left coordinate, in the exact form consumed by
`RouteM.Peanosphere.liminf_L`. -/
theorem ae_liminf_L (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ M T : ℝ,
      (∃ t ≥ T, (ω t).1 < M) ∧ (∃ t ≤ -T, (ω t).1 < M) := by
  filter_upwards [BrownianPathFacts.ae_coordinate_liminf_both hμ (0 : Fin 2)] with ω hω
  intro M T
  simpa [lrCoord] using And.intro (hω.1 M T) (hω.2 M T)

/-- BM1's lower-excursion fields for the right coordinate, in the exact form consumed by
`RouteM.Peanosphere.liminf_R`. -/
theorem ae_liminf_R (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ M T : ℝ,
      (∃ t ≥ T, (ω t).2 < M) ∧ (∃ t ≤ -T, (ω t).2 < M) := by
  filter_upwards [BrownianPathFacts.ae_coordinate_liminf_both hμ (1 : Fin 2)] with ω hω
  intro M T
  simpa [lrCoord] using And.intro (hω.1 M T) (hω.2 M T)

end MatedCRTHarmonic.MatedCRT
