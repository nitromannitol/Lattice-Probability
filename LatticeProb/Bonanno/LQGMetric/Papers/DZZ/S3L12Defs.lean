/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12Defs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3D6
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# DZZ §3.4 "Regularity of the random partition": definitions and statements (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1272–1500.

* `epsStarN`, `epsStar`: `ε* = max{2^{-n} : 2^{-n} ≤ exp(−α* √(log δ⁻¹) log log δ⁻¹)}` (eq-def-epsilon*, l. 1275).
* Definition 3.11 (l. 1279–1286): `SideRatio`, `IsGoodSeq` (good sequence of neighbouring boxes),
  `IsGoodPoint`.
* `JoinsCells`, `eventRegular` = `𝓔_{δ,α*,u,v}` (eq-def-E-delta-alpha*-u-v, l. 1289–1294).
* `DZZLemma312` (Lemma 3.12, l. 1300–1302).
* `cellSigma` (`σ(𝒱_δ)`), `fineIdx`, `fineField`, `L313Seq`, `DZZLemma313` (Lemma 3.13, l. 1314–1324).
* `encEventCell` = `𝓔_{δ,B}` (Definition 3.14, l. 1348–1357).
* `DZZLemma316` (Lemma 3.16, l. 1365–1375).

Readings (see the docstrings): a good sequence is a `Neighbour` chain whose consecutive side ratios are in
`[ε*, 1/ε*]` (equivalent to DZZ's per-index definition with `B_0 = B_1`, `B_{d+1} = B_d`, since the relation
is symmetric and `ε* ≤ 1`); `𝓔_{δ,α}` is `eventEDeltaAlpha` (D64) in `𝓔_{δ,α*,u,v}` and `eventEFine` in
Lemma 3.16 (as in L3.7); "the law conditioned on `𝒱_δ` coincides with the unconditional one" is stated
with `condExp` on indicators of measurable sets of the fine field, on `𝓔_{δ,α*,u,v} ∩ {seq = l₀}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- `exp(−α* √(log δ⁻¹) log log δ⁻¹)`, the threshold in (eq-def-epsilon*). -/
def epsStarThr (αs δ : ℝ) : ℝ :=
  Real.exp (-(αs * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)))

lemma exists_two_pow_le_epsStarThr (αs δ : ℝ) : ∃ n : ℕ, (2 : ℝ)⁻¹ ^ n ≤ epsStarThr αs δ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (Real.exp_pos _) (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact ⟨n, hn.le⟩

open Classical in
/-- `ε* = 2^{-epsStarN}`: the least `n` with `2^{-n} ≤ exp(−α* √(log δ⁻¹) log log δ⁻¹)`. -/
def epsStarN (αs δ : ℝ) : ℕ := Nat.find (exists_two_pow_le_epsStarThr αs δ)

/-- **`ε*_δ`** (eq-def-epsilon*, l. 1275). -/
def epsStar (αs δ : ℝ) : ℝ := (2 : ℝ)⁻¹ ^ epsStarN αs δ

lemma epsStar_le_thr (αs δ : ℝ) : epsStar αs δ ≤ epsStarThr αs δ :=
  Nat.find_spec (exists_two_pow_le_epsStarThr αs δ)

/-- The side-ratio condition of Definition 3.11: `s_{b'} ∈ [ε s_b, s_b / ε]`. -/
def SideRatio (ε : ℝ) (b b' : DyBox) : Prop := ε * b.side ≤ b'.side ∧ b'.side ≤ b.side / ε

lemma SideRatio.symm {ε : ℝ} (hε : 0 < ε) {b b' : DyBox} (h : SideRatio ε b b') :
    SideRatio ε b' b := by
  have hb : 0 < b.side := by unfold DyBox.side; positivity
  have hb' : 0 < b'.side := by unfold DyBox.side; positivity
  obtain ⟨h1, h2⟩ := h
  rw [le_div_iff₀ hε] at h2
  refine ⟨by linarith, ?_⟩
  rw [le_div_iff₀ hε]; linarith

/-- **Definition 3.11, good sequence** (l. 1279–1284): a sequence of neighbouring boxes in which every
box is good, i.e. consecutive side lengths have ratio in `[ε, 1/ε]`. -/
def IsGoodSeq (ε : ℝ) (l : List DyBox) : Prop :=
  l.IsChain fun b b' => Neighbour b b' ∧ SideRatio ε b b'

/-- The open box concentric with `B` of side `2 s_B` (the interior of `B_large`). -/
def DyBox.largeBoxOpen (b : DyBox) : Set ℂ :=
  {z | |z.re - b.center.re| < b.side ∧ |z.im - b.center.im| < b.side}

/-- **Definition 3.11, good point** (l. 1284–1285): for every cell `𝖢 ∈ 𝒱_δ` with `x ∈ 𝖢_large` and every
`w ∈ 𝖢_large` (in `𝕍`), `s_{w,δ} ≥ ε s_𝖢`. Reading: `w` ranges over the open box `𝖢_large°` (with the
half-open cells `𝖢_{w,δ}`, a point `w` on the right or top edge of `𝖢_large` lies in a cell outside
`𝖢_large`, which (eq-B-good) does not control). -/
def IsGoodPoint (m : DyBox → ℝ) (δ ε : ℝ) (x : ℂ) : Prop :=
  ∀ C : DyBox, IsCell m δ C → x ∈ C.largeBox → ∀ w ∈ C.largeBoxOpen, w ∈ dzzV →
    ε * C.side ≤ cellSide m δ w

/-- A nonempty sequence of cells of `𝒱_δ` joining `u` (in the first) and `v` (in the last). -/
def JoinsCells (m : DyBox → ℝ) (δ : ℝ) (u v : ℂ) (l : List DyBox) : Prop :=
  ∃ hl : l ≠ [], (∀ c ∈ l, IsCell m δ c) ∧ (l.head hl).Mem u ∧ (l.getLast hl).Mem v

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`𝓔_{δ,α*,u,v}`** (eq-def-E-delta-alpha*-u-v, l. 1289–1294): `𝓔_{δ,α*}`, `u` and `v` good, and a good
sequence of cells `𝖢_1, …, 𝖢_d` joining `u`, `v` with `d ≤ D'_{γ,δ}(u,v) e^{(log δ⁻¹)^{0.6}}`. -/
def eventRegular (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs δ : ℝ) (u v : ℂ) : Set Ω :=
  eventEDeltaAlpha γ W αs δ ∩
    {ω | IsGoodPoint (approxLQG γ W ω) δ (epsStar αs δ) u ∧
      IsGoodPoint (approxLQG γ W ω) δ (epsStar αs δ) v ∧
      ∃ l : List DyBox, JoinsCells (approxLQG γ W ω) δ u v l ∧ IsGoodSeq (epsStar αs δ) l ∧
        ((l.length : ℕ∞) : ℝ≥0∞) ≤ ((approxLGD γ W δ u v ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)))}

/-- **Statement of DZZ Lemma 3.12** (l. 1300–1302): there is `α* ≥ α₀` (here: `𝓔_{δ,α*}` occurs with high
probability, the role of `α₀` from Lemma 3.4) such that `P(𝓔_{δ,α*,u,v}) ≥ 1 − e^{−(log δ⁻¹)^{1/4}}` for all
small `δ`, uniformly in `u, v ∈ 𝕍`. -/
def DZZLemma312 (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) : Prop :=
  ∃ αs : ℝ, 0 < αs ∧ HighProb P (fun δ => eventEDeltaAlpha γ W αs δ) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ u ∈ dzzV, ∀ v ∈ dzzV,
      P (eventRegular γ W αs δ u v)ᶜ ≤
        ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (1 / 4 : ℝ))))

set_option warn.classDefReducibility false in
/-- `σ(𝒱_δ)`: the σ-algebra generated by the partition (which boxes are cells). -/
def cellSigma (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (b : DyBox) => IsCell (approxLQG γ W ω) δ b) inferInstance

end DZZ
end LQGMetric
