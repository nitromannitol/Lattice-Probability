/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylPathLength at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength

/-!
# Lengths of paths for a Weyl-scaled metric (GM.S5.W)

Let `D' = e^{ξ f}·D` be a continuous metric (GM (1.6), `uniqueness-final.tex` l. 300–302).
Blueprint GM.S5.W (used throughout GM l. 3403–3550): "f ≤ c on a set ⇒ lengths of paths inside
scale by ≤ e^{ξ c}", and the corresponding lower bound on open sets:

* `curveLength_weyl_le`: if `ξ f ≤ b` on a set containing the path `P|[s,t]`, then
  `len(P; D') ≤ e^b len(P; D)`;
* `le_curveLength_weyl`: if `a ≤ ξ f` on an open set `V` containing `P|[s,t]`, then
  `e^a len(P; D) ≤ len(P; D')`;
* `curveLength_weyl_eq_of_eq_const`: `len(P; D') = e^c len(P; D)` when `ξ f ≡ c` on an open set
  containing the path (so `D`-geodesics in `U` and `D'`-geodesics in `U` agree up to the time
  change `t ↦ e^c t`).

Own elementary proofs: the upper bound reparametrizes `P` by `D`-length and uses
`D'(P s, P t) ≤ ∫_s^t e^{ξ f(P)}` (`weylScaleOn_le_sub`); the lower bound compares each partition
sum term-wise via internal metrics on `V` (`internal_mem_Icc_of_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

/-- Sum of lengths over consecutive pieces of a partition. -/
theorem sum_curveLength_eq' {X : Type*} [PseudoEMetricSpace X] (P : ℝ → X) {u : ℕ → ℝ}
    (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, curveLength P (u i) (u (i + 1)) = curveLength P (u 0) (u n) := by
  induction n with
  | zero => simp [curveLength_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, curveLength_add P (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]

variable {ξ : ℝ} {f : C(ℂ, ℝ)} {D : ContMetric} (D' : ContMetric)
  (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
include hD'

/-- The `D'`-length of a `D`-length-parametrized path is at most its Weyl cost. -/
theorem curveLength_le_weylCost {L : ℝ} {P : ℝ → ℂ} (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) :
    curveLength (D'.pt ∘ P) 0 L ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
  refine eVariationOn_le_lintegral fun s t hs hst ht => ?_
  rw [setLIntegral_congr Ioc_ae_eq_Icc]
  show edist (D'.pt (P s)) (D'.pt (P t)) ≤ _
  rw [edist_dist]
  refine le_of_eq_of_le (hD' (P s) (P t)) ?_
  rw [← weylScaleOn_univ]
  exact weylScaleOn_le_sub hu (fun _ _ => mem_univ _) hs hst ht

/-- **Upper bound** (GM.S5.W): if `ξ f ≤ b` on `V ⊇ P([s, t])` then
`len(P; D') ≤ e^b len(P; D)`. -/
theorem curveLength_weyl_le {P : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    (hc : ContinuousOn (D.pt ∘ P) (Icc s t)) {V : Set ℂ} (hPV : ∀ τ ∈ Icc s t, P τ ∈ V)
    {b : ℝ} (hb : ∀ x ∈ V, ξ * f x ≤ b) :
    curveLength (D'.pt ∘ P) s t ≤ ENNReal.ofReal (Real.exp b) * curveLength (D.pt ∘ P) s t := by
  by_cases hfin : curveLength (D.pt ∘ P) s t = ∞
  · rw [hfin, ENNReal.mul_top (by simpa using Real.exp_pos b)]; exact le_top
  set ℓ := curveLength (D.pt ∘ P) s t
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℂ, D.pt ∘ Q = lengthParam (D.pt ∘ P) s t :=
    ⟨lengthParam (X := D.Space) (D.pt ∘ P) s t, rfl⟩
  set σ := variationOnFromTo (D.pt ∘ P) (Icc s t) s
  have hbv : BoundedVariationOn (D.pt ∘ P) (Icc s t) := hfin
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hσmono : MonotoneOn σ (Icc s t) :=
    variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn hs
  have himg : σ '' Icc s t = Icc 0 ℓ.toReal := variationOnFromTo_image_Icc hst hc hfin
  have hu : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 ℓ.toReal) := by
    rw [hQ]; exact hasUnitSpeedOn_lengthParam hst hc hfin
  have hQσ : ∀ τ ∈ Icc s t, Q (σ τ) = P τ := fun τ hτ => by
    have h := lengthParam_variationOnFromTo hfin hτ
    rw [← hQ] at h
    exact h
  have hQP : EqOn (D'.pt ∘ P) ((D'.pt ∘ Q) ∘ σ) (Icc s t) := fun τ hτ => by
    simp only [Function.comp_apply, hQσ τ hτ]
  have hQV : ∀ u ∈ Icc 0 ℓ.toReal, Q u ∈ V := by
    intro u hu'
    rw [← himg] at hu'
    obtain ⟨τ, hτ, rfl⟩ := hu'
    rw [hQσ τ hτ]; exact hPV τ hτ
  rw [curveLength_congr hQP, curveLength_comp_of_monotoneOn _ hσmono himg]
  refine (curveLength_le_weylCost D' hD' hu).trans ?_
  calc ∫⁻ u in Icc 0 ℓ.toReal, ENNReal.ofReal (Real.exp (ξ * f (Q u)))
      ≤ ∫⁻ _ in Icc 0 ℓ.toReal, ENNReal.ofReal (Real.exp b) :=
        setLIntegral_mono' measurableSet_Icc fun u hu' =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hb _ (hQV u hu')))
    _ = ENNReal.ofReal (Real.exp b) * ℓ := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hfin]

/-- **Lower bound** (GM.S5.W): if `a ≤ ξ f` on an open `V ⊇ P([s, t])` then
`e^a len(P; D) ≤ len(P; D')`. -/
theorem le_curveLength_weyl {P : ℝ → ℂ} {s t : ℝ}
    (hc : ContinuousOn (D.pt ∘ P) (Icc s t)) {V : Set ℂ} (hV : IsOpen V)
    (hPV : ∀ τ ∈ Icc s t, P τ ∈ V) {a : ℝ} (ha : ∀ x ∈ V, a ≤ ξ * f x) :
    ENNReal.ofReal (Real.exp a) * curveLength (D.pt ∘ P) s t ≤ curveLength (D'.pt ∘ P) s t := by
  have hcP : ContinuousOn P (Icc s t) := (continuous_weylToC D).comp_continuousOn hc
  have hc' : ContinuousOn (D'.pt ∘ P) (Icc s t) := (continuous_weylPt D').comp_continuousOn hcP
  unfold curveLength eVariationOn
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  rw [Finset.mul_sum]
  refine le_trans ?_ (le_trans (le_of_eq (sum_curveLength_eq' (D'.pt ∘ P) hu n))
    (curveLength_mono _ (hus 0).1 (hus n).2))
  refine Finset.sum_le_sum fun i _ => ?_
  have hi : u i ≤ u (i + 1) := hu (Nat.le_succ i)
  have hsub : Icc (u i) (u (i + 1)) ⊆ Icc s t := Icc_subset_Icc (hus i).1 (hus (i + 1)).2
  -- `D'`-internal distance on `V` between the ends of the piece ≤ its `D'`-length
  obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hi (hc'.mono hsub)
  have hint : D'.internal V (P (u i)) (P (u (i + 1))) ≤ curveLength (D'.pt ∘ P) (u i) (u (i + 1)) :=
    (internalEDist_le_pathLength γ fun τ => by
      obtain ⟨r, hr, hrτ⟩ := hrange (mem_range_self τ)
      exact ⟨P r, hPV r (hsub hr), hrτ⟩).trans hγ.le
  have hlow : ENNReal.ofReal (Real.exp a) * D.internal V (P (u i)) (P (u (i + 1))) ≤
      D'.internal V (P (u i)) (P (u (i + 1))) := by
    rw [← weylScaleOn_eq_internal D' hD' hV]; exact le_weylScaleOn_of_le ha
  refine le_trans ?_ (hlow.trans hint)
  rw [edist_comm]
  gcongr
  exact edist_le_internalEDist _ _ _

end LQGMetric
