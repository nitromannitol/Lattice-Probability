/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.Defs at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP

/-!
# GM §1.4: definitions for the proof of Theorems 1.1 and 1.2 (blueprint M1, §2, row 1)

Source: Gwynne–Miller, *Existence and uniqueness of the LQG metric for γ ∈ (0,2)*,
arXiv:1905.00383v3 (GM), `literature/src/1905.00383/uniqueness-final.tex` §1.4, l. 484–593.

* `ContMetric.smulPos C hC D` = `C D` for a constant `C > 0` (GM l. 588);
* `ContMetric.rescale b hb D` = `D(b ·, b ·)` for `b > 0`;
* `GM.smulMetric C hC D` = `h ↦ C D_h`; `GM.dilateMetric b hb D` = `D^{(b)}`,
  `D^{(b)}_h := D_{h(·/b)}(b ·, b ·)` (GM (1.16), l. 491);
* `GM.crossFn d` = `d(left side, right side)` of `[0,1]²`;
* `GM.EqSmulAS D' D k`: a.s. `D'_h = k D_h` for every whole-plane GFF plus a continuous function;
* `GM.ExistsNormalizedGFF`: a normalized whole-plane GFF exists.

Code verbatim from `blueprint/M1.md` §5 (task P2-M1A).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- `C · D` for a constant `C > 0` -/
def ContMetric.smulPos (C : ℝ) (hC : 0 < C) (D : ContMetric) : ContMetric :=
  ⟨C • D.1,
    { self_eq_zero := fun x => by simp [D.2.self_eq_zero x]
      eq_of_eq_zero := fun x y h => D.2.eq_of_eq_zero x y (by simpa [hC.ne'] using h)
      symm := fun x y => by simp [D.2.symm x y]
      triangle := fun x y z => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_add]
        exact mul_le_mul_of_nonneg_left (D.2.triangle x y z) hC.le
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, H⟩ := D.2.euclidean_of_small x ε hε
        refine ⟨C * δ, mul_pos hC hδ, fun y hy => H y ?_⟩
        simp only [ContinuousMap.smul_apply, smul_eq_mul] at hy
        exact lt_of_mul_lt_mul_left hy hC.le }⟩

/-- `D(b ·, b ·)` for `b > 0` -/
def ContMetric.rescale (b : ℝ) (hb : 0 < b) (D : ContMetric) : ContMetric :=
  ⟨D.1.comp (scaleArgs b),
    { self_eq_zero := fun x => show D.1 ((b : ℂ) * x, (b : ℂ) * x) = 0 from D.2.self_eq_zero _
      eq_of_eq_zero := fun x y h =>
        mul_left_cancel₀ (by exact_mod_cast hb.ne' : (b : ℂ) ≠ 0)
          (D.2.eq_of_eq_zero ((b : ℂ) * x) ((b : ℂ) * y) h)
      symm := fun x y => show D.1 ((b : ℂ) * x, (b : ℂ) * y) = D.1 ((b : ℂ) * y, (b : ℂ) * x)
        from D.2.symm _ _
      triangle := fun x y z => show D.1 ((b : ℂ) * x, (b : ℂ) * z) ≤
        D.1 ((b : ℂ) * x, (b : ℂ) * y) + D.1 ((b : ℂ) * y, (b : ℂ) * z) from D.2.triangle _ _ _
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, H⟩ := D.2.euclidean_of_small ((b : ℂ) * x) (b * ε) (mul_pos hb hε)
        refine ⟨δ, hδ, fun y hy => ?_⟩
        have h1 := H ((b : ℂ) * y) hy
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le] at h1
        exact lt_of_mul_lt_mul_left h1 hb.le }⟩

theorem ContMetric.smulPos_apply (C : ℝ) (hC : 0 < C) (D : ContMetric) (p : ℂ × ℂ) :
    (D.smulPos C hC).1 p = C * D.1 p := rfl

theorem ContMetric.rescale_apply (b : ℝ) (hb : 0 < b) (D : ContMetric) (u v : ℂ) :
    (D.rescale b hb).1 (u, v) = D.1 ((b : ℂ) * u, (b : ℂ) * v) := rfl

namespace GM

/-- `h ↦ C · D_h` -/
def smulMetric (C : ℝ) (hC : 0 < C) (D : DistC → ContMetric) : DistC → ContMetric :=
  fun h => (D h).smulPos C hC

/-- `D^{(b)}_h := D_{h(·/b)}(b ·, b ·)` (GM (1.16), l. 491) -/
def dilateMetric (b : ℝ) (hb : 0 < b) (D : DistC → ContMetric) : DistC → ContMetric :=
  fun h => (D (affineComp b⁻¹ 0 h)).rescale b hb

/-- `d(left side, right side)` of `[0,1]²` for a function `d` on `ℂ × ℂ` -/
def crossFn (d : ℂ × ℂ → ℝ) : ℝ := sInf (d '' (leftSide ×ˢ rightSide))

/-- `D' = k D` a.s. for every whole-plane GFF plus a continuous function -/
def EqSmulAS (D' D : DistC → ContMetric) (k : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ u v : ℂ, (D' (h ω)).1 (u, v) = k * (D (h ω)).1 (u, v)

/-- a normalized whole-plane GFF exists on some probability space -/
def ExistsNormalizedGFF : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (h : Ω → DistC), IsNormalizedWPGFF h P

end GM
end LQGMetric
