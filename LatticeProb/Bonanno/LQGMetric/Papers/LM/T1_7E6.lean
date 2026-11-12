/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7E6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E4
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7G1

/-!
# LM Lemma 5.4 for the grid squares (kernel form)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 5.4 (`lem-square-ind`, l. 992–997), for a fixed mesh `ε > 0`
and a fixed shift `θ` (LM: "We condition on `θ`, which determines `𝒮^ε_θ`, then apply Lemma 2.4"):
for any finite set `s` of indices, for `law(h)`-a.e. `g`, the internal metrics of `d ~ κ_g` on
the open squares `t17Square ε θ k`, `k ∈ s` (`T1_7G1.lean`), are independent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

lemma t17e_abs_le_of_mem_Ioo {lo hi x : ℝ} (h1 : lo < x) (h2 : x < hi) : |x| ≤ |lo| + |hi| := by
  rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rw [hx]
  · linarith [le_abs_self hi, abs_nonneg lo]
  · linarith [neg_abs_le lo, abs_nonneg hi]

lemma t17e_square_bounded (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) :
    Bornology.IsBounded (t17Square ε θ k) := by
  refine (Metric.isBounded_closedBall (x := (0 : ℂ))
    (r := |ε * (k.1 + θ.1)| + |ε * (k.1 + 1 + θ.1)| + (|ε * (k.2 + θ.2)| + |ε * (k.2 + 1 + θ.2)|))).subset
    fun x hx => ?_
  obtain ⟨a1, a2, a3, a4⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Complex.norm_le_abs_re_add_abs_im x).trans
    (add_le_add (t17e_abs_le_of_mem_Ioo a1 a2) (t17e_abs_le_of_mem_Ioo a3 a4))

/-- **LM Lemma 5.4**, grid squares, kernel form -/
theorem t17e_lem5_4_grid {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} {D : Ω → ContMetric} (hh : IsWholePlaneGFF h P) (hloc : IsLocalMetric P h D)
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ × ℝ) (s : Finset (ℤ × ℤ)) :
    ∀ᵐ g ∂P.map h, (condDistrib D h P g).map (fun d (k : s) => t17eEnc (t17Square ε θ k) d) =
      Measure.pi fun k : s => (condDistrib D h P g).map (t17eEnc (t17Square ε θ k)) :=
  t17e_lem5_4 hh hloc (fun k : s => t17Square ε θ k) (fun k => t17_isOpen_square ε θ k)
    (fun k => t17e_square_bounded ε θ k)
    (fun _k _l hkl => t17Square_disjoint hε θ (fun h => hkl (Subtype.ext h)))

end LQGMetric.LM
