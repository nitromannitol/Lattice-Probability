import LatticeProb.Prob.TrivialSigmaJoin
import LatticeProb.Prob.BrownianOutwardExcursion
import LatticeProb.Prob.BrownianGermZeroOne

/-!
# Germ 0-1 law for planar Brownian motion from the coordinate germ laws

For a planar Brownian motion `W = (W¹, W²)` (`IsPlanarBrownian`, whose two coordinates are
independent), the germ σ-algebra `⨅ n, σ(W_s : s ≤ 1/(n+1))` is contained in the join of the germ
σ-algebras of the two coordinates, and the two coordinate pasts are independent at each time.
The join lemma `LatticeProb.isTrivialSigma_iInf_sup` (independent joins of decreasing
σ-algebras with trivial germs) then gives the planar germ 0-1 law from the two coordinate germ
0-1 laws (Mörters–Peres, *Brownian Motion*, Theorem 2.7, in dimension two).

The coordinate germ 0-1 laws enter as hypotheses of the general statements below; for a real
Brownian motion they are `LatticeProb.isTrivialSigma_iInf_bmPast`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.PlanarBrownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- The joint past of a planar path is contained in the join of the pasts of its real and
imaginary parts. -/
lemma pathSigmaTo_le_sup_re_im (W : ℝ≥0 → Ω → ℂ) (u : ℝ≥0) :
    pathSigmaTo W u ≤
      pathSigmaTo (fun t ω => (W t ω).re) u ⊔ pathSigmaTo (fun t ω => (W t ω).im) u := by
  -- the join is the ambient σ-algebra for the next step (instance used by `measurable_pi_iff`)
  let S : MeasurableSpace Ω :=
    pathSigmaTo (fun t ω => (W t ω).re) u ⊔ pathSigmaTo (fun t ω => (W t ω).im) u
  have hm : Measurable (fun ω (t : Set.Iic u) => W t ω) := by
    refine measurable_pi_iff.2 fun t => ?_
    have hre := measurable_pathSigmaTo_coord (X := fun t ω => (W t ω).re) (u := u)
      (s := (t : ℝ≥0)) (Set.mem_Iic.1 t.2)
    have him := measurable_pathSigmaTo_coord (X := fun t ω => (W t ω).im) (u := u)
      (s := (t : ℝ≥0)) (Set.mem_Iic.1 t.2)
    exact Complex.measurableEquivRealProd.symm.measurable.comp
      ((hre.mono le_sup_left le_rfl).prodMk (him.mono le_sup_right le_rfl))
  exact hm.comap_le

/-- A path with measurable coordinates has its past inside the ambient σ-algebra. -/
lemma pathSigmaTo_le_ambient {E : Type*} [MeasurableSpace E] {X : ℝ≥0 → Ω → E}
    (hX : ∀ t, Measurable (X t)) (u : ℝ≥0) : pathSigmaTo X u ≤ mΩ := by
  have hm : Measurable (fun ω (t : Set.Iic u) => X t ω) :=
    measurable_pi_iff.2 fun t => hX (t : ℝ≥0)
  exact hm.comap_le

omit mΩ in
/-- The pasts `σ(X_s : s ≤ 1/(n+1))` decrease in `n`. -/
lemma pathSigmaTo_freqEps_anti {E : Type*} [MeasurableSpace E] (X : ℝ≥0 → Ω → E) :
    Antitone fun n : ℕ => pathSigmaTo X (freqEps n) :=
  fun _ _ hab => pathSigmaTo_mono X (freqEps_anti hab)

/-- The real and imaginary parts of a planar Brownian motion have independent pasts at every
time (independence of the two coordinate processes). -/
lemma indep_pathSigmaTo_re_im {W : ℝ≥0 → Ω → ℂ} {P : Measure Ω} (hW : IsPlanarBrownian W P)
    (u : ℝ≥0) :
    Indep (pathSigmaTo (fun t ω => (W t ω).re) u) (pathSigmaTo (fun t ω => (W t ω).im) u) P := by
  have hR : Measurable (fun (x : ℝ≥0 → ℝ) (t : Set.Iic u) => x t) :=
    measurable_pi_iff.2 fun t => measurable_pi_apply _
  exact (IndepFun_iff_Indep _ _ P).1 (hW.indep.comp hR hR)

/-- **Germ 0-1 law for planar Brownian motion, from the coordinate germ laws.** If the germ
σ-algebras `⨅ n, σ(Re W_s : s ≤ 1/(n+1))` and `⨅ n, σ(Im W_s : s ≤ 1/(n+1))` of the two
coordinates are trivial, then so is the germ σ-algebra `⨅ n, σ(W_s : s ≤ 1/(n+1))` of `W`.
Mörters–Peres, *Brownian Motion*, Theorem 2.7 (`d = 2`). -/
theorem isTrivialSigma_iInf_pathSigmaTo_planar {W : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (hre : IsTrivialSigma (⨅ n : ℕ, pathSigmaTo (fun t ω => (W t ω).re) (freqEps n)) P)
    (him : IsTrivialSigma (⨅ n : ℕ, pathSigmaTo (fun t ω => (W t ω).im) (freqEps n)) P) :
    IsTrivialSigma (⨅ n : ℕ, pathSigmaTo W (freqEps n)) P := by
  have hre' : ∀ n : ℕ, pathSigmaTo (fun t ω => (W t ω).re) (freqEps n) ≤ mΩ := fun n =>
    pathSigmaTo_le_ambient (fun t => Complex.measurable_re.comp (hW.measurable t)) _
  have him' : ∀ n : ℕ, pathSigmaTo (fun t ω => (W t ω).im) (freqEps n) ≤ mΩ := fun n =>
    pathSigmaTo_le_ambient (fun t => Complex.measurable_im.comp (hW.measurable t)) _
  have hJ := isTrivialSigma_iInf_sup (P := P)
    (𝒜 := fun n : ℕ => pathSigmaTo (fun t ω => (W t ω).re) (freqEps n))
    (ℬ := fun n : ℕ => pathSigmaTo (fun t ω => (W t ω).im) (freqEps n))
    hre' him' (pathSigmaTo_freqEps_anti _) (pathSigmaTo_freqEps_anti _)
    (indep_pathSigmaTo_re_im hW (freqEps 0)) hre him
  refine hJ.mono (le_iInf fun n => (iInf_le _ n).trans ?_)
  exact pathSigmaTo_le_sup_re_im W (freqEps n)

/-- **Planar random direction, coordinate form.** If `N ≠ 0` a.s. is independent of a planar
Brownian motion `W`, and the coordinate germ laws of `W` are trivial, then almost surely
`⟪N, W_s⟫ > 0` for arbitrarily small `s > 0`. This is `ae_frequently_pos_of_indepFun` with its
germ hypothesis discharged by `isTrivialSigma_iInf_pathSigmaTo_planar`. -/
theorem ae_frequently_pos_of_indepFun_of_coordinates {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℂ} (hW : IsPlanarBrownian W P)
    (hre : IsTrivialSigma (⨅ n : ℕ, pathSigmaTo (fun t ω => (W t ω).re) (freqEps n)) P)
    (him : IsTrivialSigma (⨅ n : ℕ, pathSigmaTo (fun t ω => (W t ω).im) (freqEps n)) P)
    {N : Ω → ℂ} (hN : AEMeasurable N P)
    (hNW : IndepFun N (fun ω (s : ℝ≥0) => W s ω) P) (hN0 : ∀ᵐ ω ∂P, N ω ≠ 0) :
    ∀ᵐ ω ∂P, ∃ᶠ s in 𝓝[>] (0 : ℝ≥0), 0 < pairing (N ω) (W s ω) :=
  ae_frequently_pos_of_indepFun hW (isTrivialSigma_iInf_pathSigmaTo_planar hW hre him) hN hNW hN0

/-- **Planar random direction, unconditional.** If `N ≠ 0` a.s. is independent of a planar
Brownian motion `W`, then almost surely `⟪N, W_s⟫ > 0` for arbitrarily small `s > 0`. The coordinate
germ laws `⨅ n, σ(Re W_s : s ≤ 1/(n+1))` and `⨅ n, σ(Im W_s : s ≤ 1/(n+1))` are trivial by
Blumenthal's zero-one law `isTrivialSigma_iInf_bmPast` applied to the two real coordinates. -/
theorem ae_frequently_pos_of_indepFun_planar {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℂ} (hW : IsPlanarBrownian W P)
    {N : Ω → ℂ} (hN : AEMeasurable N P)
    (hNW : IndepFun N (fun ω (s : ℝ≥0) => W s ω) P) (hN0 : ∀ᵐ ω ∂P, N ω ≠ 0) :
    ∀ᵐ ω ∂P, ∃ᶠ s in 𝓝[>] (0 : ℝ≥0), 0 < pairing (N ω) (W s ω) :=
  ae_frequently_pos_of_indepFun_of_coordinates hW
    (isTrivialSigma_iInf_bmPast hW.re fun t => Complex.measurable_re.comp (hW.measurable t))
    (isTrivialSigma_iInf_bmPast hW.im fun t => Complex.measurable_im.comp (hW.measurable t))
    hN hNW hN0

end LatticeProb.PlanarBrownian
