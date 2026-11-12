/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_4B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4A
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.LiftPos
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal

/-!
# CONF Lemma 2.4: existence of one-sided limits of geodesics

Source: CONF = Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, proof of Lemma 2.4
(l. 548–556): "We can choose a sequence `y_n^-` of points in the clockwise arc of `∂𝓑^•_s` from
`z` to `y` which converge to `y` from the left … the Arzelà–Ascoli theorem implies that after
possibly passing to a subsequence, we can arrange that the paths … converge uniformly to a
continuous path `P_y^-`. The path `P_y^-` is a `D_h`-geodesic from 0 to `y`."

With leftmost read by `Blueprint.IsSideGeod` (the one-sided-limit reading of CONFDefs), this
gives the existence clause of `CONFLem2_4`. The positively oriented Jordan parametrization of
`∂𝓑^•_s` is `DD.posLift_filledBall` (S-PosLift) with J1b (`GM.gm_j1b`, now unconditional).
Here the points `y_n` are `φ(t₀ ± 1/(n+1))` and the geodesics to them come from GM.S1.1 (the
rational points `q_n^-` of CONF are needed only for the approximation clause).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

section Det
variable {D : ContMetric} {z : ℂ} {s : ℝ}

/-- closed `D`-balls are compact when closed `D`-bounded sets are -/
theorem isCompact_dBall
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (z : ℂ) (s : ℝ) : IsCompact {u | D.1 (z, u) ≤ s} := by
  refine hbc _ (isClosed_le (DD.cl_continuous_distFrom D z) continuous_const)
    ⟨2 * s, fun u hu v hv => ?_⟩
  have h1 := D.2.triangle u z v
  have h2 := D.2.symm u z
  simp only [mem_ofPred_eq] at hu hv
  linarith

theorem isBounded_ballM_of_bc
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (z : ℂ) (s : ℝ) : Bornology.IsBounded (ballM D z s) :=
  (isCompact_dBall hbc z s).isBounded.subset fun w (hw : D.1 (z, w) < s) =>
    show D.1 (z, w) ≤ s from hw.le

/-- a geodesic of length `s` from `z` to each point of `∂𝓑^•_s` -/
theorem exists_geodL_frontier
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hs : 0 < s) {x : ℂ}
    (hx : x ∈ frontier (filledBall D z s)) : ∃ P : ℝ → ℂ, IsGeodesicL D P s z x := by
  have hd : D.1 (z, x) = s := GM.jp_frontier_subset_sphere (isBounded_ballM_of_bc hbc z s) hx
  have hzx : z ≠ x := fun h0 => by
    rw [h0, D.2.self_eq_zero] at hd
    linarith
  obtain ⟨η, hη⟩ := hgeo z x
  exact ⟨_, hd ▸ GM.gm_geodL_isGeodesicL hη hzx⟩

/-- the DEC-D positive Jordan lift gives a CONFDefs positive Jordan parametrization -/
theorem isPosJordanParam_of_lift {Γ : Set ℂ} {φ : ℝ → ℂ} {θ : ℝ → ℝ}
    (h : DD.IsPosJordanLift Γ z φ θ) : IsPosJordanParam Γ z φ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, θ, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- `t₀ ± 1/(n+1)` -/
def sideSeq (left : Bool) (t₀ : ℝ) (n : ℕ) : ℝ :=
  if left then t₀ + 1 / ((n : ℝ) + 1) else t₀ - 1 / ((n : ℝ) + 1)

theorem tendsto_sideSeq (left : Bool) (t₀ : ℝ) : Tendsto (sideSeq left t₀) atTop (𝓝 t₀) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  cases left
  · show Tendsto (fun n : ℕ => t₀ - 1 / ((n : ℝ) + 1)) atTop (𝓝 t₀)
    simpa using (tendsto_const_nhds (x := t₀)).sub h
  · show Tendsto (fun n : ℕ => t₀ + 1 / ((n : ℝ) + 1)) atTop (𝓝 t₀)
    simpa using (tendsto_const_nhds (x := t₀)).add h

theorem sideSeq_side (left : Bool) (t₀ : ℝ) (n : ℕ) :
    if left then t₀ < sideSeq left t₀ n else sideSeq left t₀ n < t₀ := by
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  cases left <;> simp [sideSeq] <;> linarith

/-- **CONF Lemma 2.4, existence** (proof l. 548–556): one-sided limits of geodesics exist. -/
theorem exists_sideGeod
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hs : 0 < s) {y : ℂ}
    (hy : y ∈ frontier (filledBall D z s)) {φ : ℝ → ℂ}
    (hφ : IsPosJordanParam (frontier (filledBall D z s)) z φ) {t₀ : ℝ} (ht₀ : φ t₀ = y)
    (left : Bool) : ∃ Q, IsSideGeod left D z s y Q := by
  have hmem : ∀ t, φ t ∈ frontier (filledBall D z s) := fun t => hφ.2.2.2.1 ▸ mem_range_self t
  choose Pn hPn using fun n : ℕ => exists_geodL_frontier hbc hgeo hs (hmem (sideSeq left t₀ n))
  obtain ⟨ψ, Q, hψ, hconv⟩ := exists_subseq_supDist hbc hs.le hPn
  have htψ : Tendsto (fun n => sideSeq left t₀ (ψ n)) atTop (𝓝 t₀) :=
    (tendsto_sideSeq left t₀).comp hψ.tendsto_atTop
  have hyψ : Tendsto (fun n => φ (sideSeq left t₀ (ψ n))) atTop (𝓝 y) :=
    ht₀ ▸ (hφ.1.tendsto t₀).comp htψ
  have hQ : IsGeodesicL D Q s z y :=
    geod_of_tendsto (fun n => hPn (ψ n)) hs.le hyψ fun t ht => tendsto_of_supDistOn hconv ht
  exact ⟨Q, hy, hQ, φ, hφ, t₀, ht₀, fun n => sideSeq left t₀ (ψ n), fun n => Pn (ψ n), htψ,
    fun n => sideSeq_side left t₀ (ψ n), fun n => hPn (ψ n), hconv⟩

/-- **CONF Lemma 2.4, existence**, deterministic form with the Jordan parametrization built in
(S-PosLift + J1b). -/
theorem exists_sideGeod' (hL : D.IsLength)
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hs : 0 < s) {y : ℂ}
    (hy : y ∈ frontier (filledBall D z s)) (left : Bool) : ∃ Q, IsSideGeod left D z s y Q := by
  have hbd := isBounded_ballM_of_bc hbc z s
  obtain ⟨φ, θ, hφθ⟩ := DD.posLift_filledBall hs hL hbd (GM.gm_j1b D z s hs hL hbd)
  have hφ := isPosJordanParam_of_lift hφθ
  obtain ⟨t₀, ht₀⟩ : y ∈ range φ := hφ.2.2.2.1 ▸ hy
  exact exists_sideGeod hbc hgeo hs hy hφ ht₀ left

end Det

end LQGMetric.CONF
