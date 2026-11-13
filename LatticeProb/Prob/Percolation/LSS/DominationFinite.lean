import LatticeProb.Prob.Percolation.LSS.Defs
import LatticeProb.Prob.Percolation.LSS.Thin

/-!
# Domination by product measures: from finitely many coordinates

Ported from the Exploding-Sandpiles formalization, `Support/ExtLSSProof.lean`.

The finite-coordinate thinning of `LatticeProb.Percolation.LSS.Thin` and the one-site
marginals of the field give, on every finite set of coordinates, a coupling of the field
with the product law that is dominated by it. The passage from finitely many coordinates
to an arbitrary measurable increasing event is isolated as the explicit hypothesis
`xlss_finite_to_countable`. Under that hypothesis, `xlss_proved` establishes the
bounded-degree domination `LiggettSchonmannStaceyBoundedDegree` of Liggett, Schonmann and
Stacey: the product density `ρ` is recovered from the one-site marginals through the
thinning parameter `1 - ρ / (1 - ε)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation.LSS

variable {S : Type}

/-- The one-site complement bound used to pass from the `ENNReal` one-site marginals of the
cited statement to the real one-site marginals of the thinning.  If each site is occupied with
probability at least `p`, then it is empty with probability at most `1 - p`. -/
theorem xlss_real_false_le (μ : Measure (S → Bool)) [IsProbabilityMeasure μ] (p : ℝ)
    (hp0 : 0 ≤ p) (h : ∀ s : S, ENNReal.ofReal p ≤ μ {ω | ω s = true}) (s : S) :
    μ.real {ω | ω s = false} ≤ 1 - p := by
  have hreal : p ≤ μ.real {ω | ω s = true} := by
    have hfin : μ {ω | ω s = true} ≠ ⊤ := by
      have hle : μ {ω | ω s = true} ≤ 1 := by
        rw [← measure_univ (μ := μ)]
        exact measure_mono (Set.subset_univ _)
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    have hmono := ENNReal.toReal_mono hfin (h s)
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_ofReal hp0] using hmono
  have hcompl : {ω : S → Bool | ω s = false} =
      ((fun f : S → Bool => f s) ⁻¹' {true})ᶜ := by
    ext ω
    simp [Bool.not_eq_true]
  rw [hcompl, MeasureTheory.measureReal_compl (measurable_pi_apply s (measurableSet_singleton true)),
    MeasureTheory.probReal_univ]
  have hreal' : p ≤ μ.real ((fun f : S → Bool => f s) ⁻¹' {true}) := hreal
  linarith

/-- The finite-to-countable estimate, isolated as an explicit hypothesis: if for every finite
set of coordinates there is a thinning of `μ` with product density `ρ` and parameter `γ`, then
the product law of density `ρ` is dominated by `μ` on every measurable increasing event. -/
def xlss_finite_to_countable : Prop :=
  ∀ (S : Type) [Countable S] [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ), (∀ T : Finset S, ∃ w, XlssThin μ ρ γ T w) →
    ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A →
      bernoulliProduct S ρ A ≤ μ A

/-- **Corollary 1.4 of Liggett, Schonmann and Stacey**, the bounded-degree domination of a
dependent field of bits by a product measure, proved from the weighted local-lemma estimate,
the finite thinning, and the finite-to-countable estimate `xlss_finite_to_countable`. -/
theorem xlss_proved (h : xlss_finite_to_countable) :
    LiggettSchonmannStaceyBoundedDegree := by
  classical
  intro S _ G Δ hΔ hdeg _hcomp ρ hρ0 hρ1
  rcases eq_or_lt_of_le hρ0 with hρzero | hρpos
  · -- the degenerate density `ρ = 0`, where the product law is the point mass at all-empty
    rw [← hρzero]
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro μ _hμ _hdep _hmarg A hA hinc
    have hdirac : bernoulliProduct S (0 : ℝ) = Measure.dirac (fun _ : S => false) := by
      rw [bernoulliProduct]
      have hbit : (fun _ : S => bitLaw (0 : ℝ)) = fun _ : S => Measure.dirac false := by
        funext _
        rw [bitLaw]
        simp
      rw [hbit, Measure.infinitePi_dirac]
    rw [hdirac]
    by_cases hmem : (fun _ : S => false) ∈ A
    · have hAuniv : A = Set.univ := by
        ext ω
        exact ⟨fun _ => trivial, fun _ =>
          hinc (fun _ : S => false) ω hmem (fun s h => by cases h)⟩
      rw [hAuniv]
      simp
    · rw [Measure.dirac_apply' _ hA, Set.indicator_of_notMem hmem]
      simp
  · -- the nondegenerate density `0 < ρ < 1`
    set ε : ℝ := min ((1 - ρ) / 2) (1 / (2 * (Δ : ℝ))) with hεdef
    have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ
    have hε : 0 < ε := by
      rw [hεdef]
      exact lt_min (by linarith) (by positivity)
    have hερ : ε < 1 - ρ := by
      have h := min_le_left ((1 - ρ) / 2) (1 / (2 * (Δ : ℝ)))
      rw [hεdef]
      linarith
    have hΔε : (Δ : ℝ) * ε < 1 := by
      have h := min_le_right ((1 - ρ) / 2) (1 / (2 * (Δ : ℝ)))
      rw [hεdef]
      calc (Δ : ℝ) * ε ≤ (Δ : ℝ) * (1 / (2 * (Δ : ℝ))) :=
            mul_le_mul_of_nonneg_left h hΔpos.le
        _ = 1 / 2 := by field_simp
        _ < 1 := by norm_num
    have hε1 : (0 : ℝ) < 1 - ε := by linarith
    have hγ0 : 0 < 1 - ρ / (1 - ε) := by
      rw [sub_pos, div_lt_one hε1]
      linarith
    set g : ℝ := min ρ (1 - ρ / (1 - ε)) with hgdef
    set q : ℝ := ε * g ^ Δ * (1 - (Δ : ℝ) * ε) with hqdef
    have hg0 : 0 < g := by rw [hgdef]; exact lt_min hρpos hγ0
    have hqpos : 0 < q := by
      rw [hqdef]
      exact mul_pos (mul_pos hε (pow_pos hg0 _)) (by linarith)
    have hq1 : q ≤ 1 := by
      have hg1 : g ≤ 1 := (min_le_left _ _).trans hρ1.le
      have hgpow : g ^ Δ ≤ 1 := pow_le_one₀ hg0.le hg1
      have hε1' : ε ≤ 1 := by linarith
      have hfac1 : 1 - (Δ : ℝ) * ε ≤ 1 := by
        have := mul_nonneg hΔpos.le hε.le
        linarith
      rw [hqdef]
      calc ε * g ^ Δ * (1 - (Δ : ℝ) * ε) ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have hp0 : 0 ≤ 1 - q := by linarith
    refine ⟨1 - q, by linarith, ?_⟩
    intro μ _hμ hdep hmarg A hA hinc
    have hmarg' : ∀ s : S, μ.real {x | x s = false} ≤ q := by
      intro s
      have := xlss_real_false_le μ (1 - q) hp0 hmarg s
      linarith
    have hthin : ∀ T : Finset S, ∃ w, XlssThin μ ρ (1 - ρ / (1 - ε)) T w := by
      intro T
      exact xlss_thin_exists G μ Δ hdeg hdep q ρ ε hρpos hρ1 hε hερ hmarg'
        (by rw [hqdef, hgdef]) T
    exact h S μ ρ (1 - ρ / (1 - ε)) hthin A hA hinc

end LatticeProb.Percolation.LSS
