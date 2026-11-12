/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylPathLength

/-!
# Locality of Weyl scaling

`(e^{ξ f}·D)(·,·;U)` depends only on the internal metric `D(·,·;U)` and on `ξ f|_U`
(GM, arXiv:1905.00383v3, used with Axioms II–III, e.g. blueprint GM.S2.3 and GM.S5.W;
GM (1.5)–(1.6), `uniqueness-final.tex` l. 270–272, 300–302):

* `curveLength_eq_of_internal_eq`: two continuous metrics with the same internal metric on `U`
  give the same length to every path in `U` (partition sums of `D(·,·;U)`);
* `weylScaleOn_eq_of_internal_eq`: hence the same Weyl infimum over paths in `U`;
* `internal_weyl_eq_of_internal_eq`: for `Dᵢ' = e^{ξ fᵢ}·Dᵢ` with `D₁(·,·;U) = D₂(·,·;U)` and
  `ξ f₁ = ξ f₂` on the open set `U`, `D₁'(·,·;U) = D₂'(·,·;U)`.

Own elementary proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

variable {ξ : ℝ} {D₁ D₂ : ContMetric} {U : Set ℂ}

theorem curveLength_le_of_internal_eq
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y)
    {P : ℝ → ℂ} {s t : ℝ} (hc : ContinuousOn P (Icc s t)) (hPU : ∀ τ ∈ Icc s t, P τ ∈ U) :
    curveLength (D₁.pt ∘ P) s t ≤ curveLength (D₂.pt ∘ P) s t := by
  have hc₂ : ContinuousOn (D₂.pt ∘ P) (Icc s t) := (continuous_weylPt D₂).comp_continuousOn hc
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc ∑ i ∈ Finset.range n, edist (D₁.pt (P (u (i + 1)))) (D₁.pt (P (u i)))
      ≤ ∑ i ∈ Finset.range n, D₂.internal U (P (u i)) (P (u (i + 1))) :=
        Finset.sum_le_sum fun i _ => by
          rw [edist_comm, ← hD _ (hPU _ (hus i)) _ (hPU _ (hus (i + 1)))]
          exact edist_le_internalEDist _ _ _
    _ ≤ ∑ i ∈ Finset.range n, curveLength (D₂.pt ∘ P) (u i) (u (i + 1)) :=
        Finset.sum_le_sum fun i _ => by
          have hi : u i ≤ u (i + 1) := hu (Nat.le_succ i)
          have hsub : Icc (u i) (u (i + 1)) ⊆ Icc s t := Icc_subset_Icc (hus i).1 (hus (i + 1)).2
          obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hi (hc₂.mono hsub)
          refine (internalEDist_le_pathLength γ fun τ => ?_).trans hγ.le
          obtain ⟨r, hr, hrτ⟩ := hrange (mem_range_self τ)
          exact ⟨P r, hPU r (hsub hr), hrτ⟩
    _ = curveLength (D₂.pt ∘ P) (u 0) (u n) := sum_curveLength_eq' _ hu n
    _ ≤ curveLength (D₂.pt ∘ P) s t := curveLength_mono _ (hus 0).1 (hus n).2

/-- Same internal metric on `U` ⇒ same lengths of paths in `U`. -/
theorem curveLength_eq_of_internal_eq
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y)
    {P : ℝ → ℂ} {s t : ℝ} (hc : ContinuousOn P (Icc s t)) (hPU : ∀ τ ∈ Icc s t, P τ ∈ U) :
    curveLength (D₁.pt ∘ P) s t = curveLength (D₂.pt ∘ P) s t :=
  le_antisymm (curveLength_le_of_internal_eq hD hc hPU)
    (curveLength_le_of_internal_eq (fun x hx y hy => (hD x hx y hy).symm) hc hPU)

theorem weylScaleOn_le_of_internal_eq {f : C(ℂ, ℝ)} {z w : ℂ}
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y) :
    weylScaleOn ξ f D₁ U z w ≤ weylScaleOn ξ f D₂ U z w := by
  refine le_weylScaleOn fun L P hL hc hu h0 h1 hPU => ?_
  have hcP : ContinuousOn P (Icc 0 L) := (continuous_weylToC D₂).comp_continuousOn hc
  have hu₁ : HasUnitSpeedOn (D₁.pt ∘ P) (Icc 0 L) := by
    rw [hasUnitSpeedOn_Icc_iff] at hu ⊢
    intro s t hs hst ht
    rw [curveLength_eq_of_internal_eq hD (hcP.mono (Icc_subset_Icc hs ht))
      (fun τ hτ => hPU τ ⟨hs.trans hτ.1, hτ.2.trans ht⟩)]
    exact hu s t hs hst ht
  exact weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn hu₁) hu₁ h0 h1 hPU

/-- `(e^{ξ f}·D)_U` depends on `D` only through `D(·,·;U)`. -/
theorem weylScaleOn_eq_of_internal_eq {f : C(ℂ, ℝ)} {z w : ℂ}
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y) :
    weylScaleOn ξ f D₁ U z w = weylScaleOn ξ f D₂ U z w :=
  le_antisymm (weylScaleOn_le_of_internal_eq hD)
    (weylScaleOn_le_of_internal_eq fun x hx y hy => (hD x hx y hy).symm)

/-- **Locality of Weyl scaling**: if `D₁(·,·;U) = D₂(·,·;U)` and `ξ f₁ = ξ f₂` on the open set
`U`, then `(e^{ξ f₁}·D₁)(·,·;U) = (e^{ξ f₂}·D₂)(·,·;U)`. -/
theorem internal_weyl_eq_of_internal_eq (hU : IsOpen U) {f₁ f₂ : C(ℂ, ℝ)}
    {D₁' D₂' : ContMetric}
    (h₁ : ∀ x y : ℂ, ENNReal.ofReal (D₁'.1 (x, y)) = weylScale ξ f₁ D₁ x y)
    (h₂ : ∀ x y : ℂ, ENNReal.ofReal (D₂'.1 (x, y)) = weylScale ξ f₂ D₂ x y)
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y)
    (hf : ∀ x ∈ U, ξ * f₁ x = ξ * f₂ x) (z w : ℂ) :
    D₁'.internal U z w = D₂'.internal U z w := by
  rw [← weylScaleOn_eq_internal D₁' h₁ hU, ← weylScaleOn_eq_internal D₂' h₂ hU,
    weylScaleOn_eq_of_internal_eq hD, weylScaleOn_congr hf]

end LQGMetric
