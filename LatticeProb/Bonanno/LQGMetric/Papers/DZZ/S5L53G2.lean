/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G1
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# DZZ Lemma 5.3, part 1, node 2: a.e.-measurable `μIn`, and openness for `μIn` from a proxy
(P2-DZZ53G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2452–2502.

**Doubt B1 of P2-DZZ53E** (the ball masses of `μIn` are only `AEMeasurable` in `ω`):
* `l53_modification`: a family `ν` with a.e.-measurable rational ball masses agrees, off a
  measurable null set `N`, with `ν' = if ω ∈ N then 0 else ν ω`, whose rational ball masses are
  measurable (countably many null sets; `lgdDZZ` only reads rational balls, `lgdDZZ_eq_lgdRat`).
* **`nullMeasurableSet_l53ZBad`**, **`l53ZBad_le_ae`**: the bad event of (eq-z-open) is
  null-measurable and `a b μ(l53ZBad) ≤ p 𝓛₁(∂𝖡)²` (outer measure) under a.e.-measurability.
* **`l53ZBad_dzzMuIn_le`**: the same for `ν = μIn` and every `μ ≪ P` (e.g. `P.restrict A` or
  `P[·|A]` for an `𝓕*`-event `A`: the conditioning).

**Openness for `μIn` from a local proxy** (DZZ l. 2453, `𝓔_{𝖡,open} ∩ 𝓔₄ ⊆ {𝖡 open}`, with the
domination (eq-M-A-upper-bound-bis), l. 2458):
* `lgdRat_mono`, **`lgdDZZ_wall_mono_ball`**: domination of the ball masses inside a closed wall
  `K` gives domination of the walled LGD.
* **`l53_hopen_of_not_bad`**: if `ω ∉ l53ZBad νB δ T ∂𝖡 a b` and `ν ω ≤ νB ω` on the balls inside a
  region `B*` containing every `𝕍̃_{z,z'}` (`z, z' ∈ ∂𝖡`), and every `𝕍̃_{z,z'} ⊆ K`, then `𝖡`
  is open for `D^K[ν ω]` exactly in the form of the hypothesis `hopen` of `l53_open_chain`
  (S5L53E4). With `K = 𝕍̃_{u,v}` this is the wall of `l53Bad` / `L53ChainDesirable` (S5L53F4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*}

/-! ### Domination of walled distances -/

lemma lgdRat_mono {m m' : ℚ × ℚ → ℚ → ℝ≥0∞} (h : ∀ c q, m c q ≤ m' c q) (δ : ℝ) (A B : Set ℂ) :
    lgdRat m δ A B ≤ lgdRat m' δ A B := by
  unfold lgdRat
  refine iInf_mono fun N => iInf_mono' fun hN => ⟨?_, le_rfl⟩
  obtain ⟨c, q, hcov, hi⟩ := hN
  exact ⟨c, q, hcov, fun i => ⟨(hi i).1, (h _ _).trans (hi i).2⟩⟩

/-- Points have zero `1`-dimensional Hausdorff measure in `ℂ`. -/
lemma l53_hausdorff_singleton (x : ℂ) : μH[1] ({x} : Set ℂ) = 0 := by
  have h := hausdorffMeasure_of_dimH_lt (X := ℂ) (s := {x}) (d := 1)
    (by rw [dimH_singleton]; norm_num)
  simpa using h

/-- **Geometry of `B*`** (DZZ l. 2437: `𝖡* = {x : ‖x − ∂𝖡‖_∞ ≤ 2s_i/K}`): for `z ≠ z'` in the
closed box `𝕍_{c,t}`, `𝕍̃_{z,z'} ⊆ 𝕍_{c,5t}` (which is `𝖡*` for `𝖡 = 𝕍_{c,t}`). Own elementary
proof. -/
lemma tildeBox_subset_sqBox_five {c z z' : ℂ} {t : ℝ} (hz : z ∈ sqBox c t) (hz' : z' ∈ sqBox c t)
    (hne : z ≠ z') : tildeBox z z' ⊆ sqBox c (5 * t) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  set d : ℂ := z' - z with hd
  set w : ℂ := (x - (z + z') / 2) * starRingEnd ℂ d with hw
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hn : (0 : ℝ) < ‖d‖ ^ 2 := by positivity
  have hxw : x - (z + z') / 2 = w * d / ((‖d‖ ^ 2 : ℝ) : ℂ) := by
    rw [hw, mul_assoc, Complex.conj_mul', eq_div_iff (by exact_mod_cast hn.ne')]
    push_cast; ring
  have hre : (x - (z + z') / 2).re = (w.re * d.re - w.im * d.im) / ‖d‖ ^ 2 := by
    rw [hxw, Complex.div_ofReal_re, Complex.mul_re]
  have him : (x - (z + z') / 2).im = (w.re * d.im + w.im * d.re) / ‖d‖ ^ 2 := by
    rw [hxw, Complex.div_ofReal_im, Complex.mul_im]
  obtain ⟨a1, a2⟩ := hz
  obtain ⟨b1, b2⟩ := hz'
  have hdre : |d.re| ≤ t := by
    rw [hd, Complex.sub_re]; rw [abs_le] at a1 b1 ⊢; constructor <;> linarith
  have hdim : |d.im| ≤ t := by
    rw [hd, Complex.sub_im]; rw [abs_le] at a2 b2 ⊢; constructor <;> linarith
  have key : ∀ p q : ℝ, |p| ≤ ‖d‖ ^ 2 → |q| ≤ ‖d‖ ^ 2 → ∀ r s : ℝ, |r| ≤ t → |s| ≤ t →
      |(p * r + q * s) / ‖d‖ ^ 2| ≤ 2 * t := by
    intro p q hp hq r s hr hs
    rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
    calc |p * r + q * s| ≤ |p| * |r| + |q| * |s| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ‖d‖ ^ 2 * t + ‖d‖ ^ 2 * t := by gcongr
      _ = 2 * t * ‖d‖ ^ 2 := by ring
  have hx1 : |(x - (z + z') / 2).re| ≤ 2 * t := by
    rw [hre, sub_eq_add_neg, ← neg_mul, show -w.im * d.im = w.im * (-d.im) by ring]
    exact key _ _ h1 h2 _ _ hdre (by rwa [abs_neg])
  have hx2 : |(x - (z + z') / 2).im| ≤ 2 * t := by
    rw [him]; exact key _ _ h1 h2 _ _ hdim hdre
  simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.sub_im,
    Complex.add_im, Complex.div_ofNat_im] at hx1 hx2
  refine ⟨?_, ?_⟩
  · rw [abs_le] at a1 b1 hx1 ⊢; constructor <;> linarith
  · rw [abs_le] at a2 b2 hx2 ⊢; constructor <;> linarith

/-! ### a.e.-measurable ball masses (doubt B1) -/

section AE

variable [MeasurableSpace Ω]

end AE

end DZZ
end LQGMetric
