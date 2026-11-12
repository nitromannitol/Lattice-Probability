/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CaraExt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExtModulus
import Mathlib.Topology.ExtendFrom

/-!
# EXT-CA C3: continuous extension of a conformal map of `H` (Carathéodory, quantitative)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 C3. Under the standing hypotheses `(Hψ)`
(`CarHyp ψ D E R₀` and `Topo.ULC E`), `ψ` extends to a function `F`, continuous on `Hbar`, with
`F x ∈ frontier D` for real `x`, and `ψ z` converges (to a point of `frontier D`) as `z → ∞` in
`H`. The modulus of continuity of `F` on `Hbar` depends only on `R₀`, the ULC modulus of `E`
and a lower bound `η` for `infDist (ψ I) E` (`extension_modulus`; the uniform statement for `ψ`
on `H` is `exists_modulus`, the one at `∞` is `exists_radius_infty`).

Source: Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.1, proof of
(iv) ⇒ (i), printed pp. 21–22 ("f is uniformly continuous in 𝔻 and therefore has a continuous
extension"), and Prop. 2.3, p. 22 (equicontinuity under a uniform ULC modulus). Half-plane form
with reference point `I` and the point `∞` handled by `z ↦ -1/z` (blueprint C3). The passage
from uniform continuity to the extension (`extendFrom`, Cauchy filters) is standard.
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped Real

namespace QuantumZipper.CA.Car

open QuantumZipper.CA.Topo

/-- Under `(Hψ)`, the reference value `ψ I` has positive distance from `E`. -/
theorem infDist_pos {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀) :
    0 < infDist (ψ I) E := by
  have hID : ψ I ∈ D := h.bij.mapsTo (show (0 : ℝ) < I.im by simp)
  have hE : E.Nonempty := by
    by_contra hE
    rw [not_nonempty_iff_eq_empty] at hE
    have hfr : frontier D = ∅ := subset_empty_iff.1 (hE ▸ h.frontier_sub)
    rcases isClopen_iff.1 (isClopen_iff_frontier_eq_empty.2 hfr) with h0 | h1
    · exact (h0 ▸ hID : ψ I ∈ (∅ : Set ℂ))
    · have := h.bdd (h1 ▸ mem_univ ((|R₀| : ℝ) : ℂ))
      rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_abs] at this
      exact lt_irrefl _ (this.trans_le (le_abs_self R₀) |>.trans_le (le_abs_self _) |>.trans_le
        (by rw [abs_abs]))
  exact (h.isClosed.notMem_iff_infDist_pos hE).1 fun hmem => h.sub_compl hmem hID

private theorem exists_tendsto_of_small {f : ℂ → ℂ} {l : Filter ℂ} [l.NeBot]
    (hl : ∀ ε > 0, ∃ t ∈ l, ∀ z ∈ t, ∀ w ∈ t, dist (f z) (f w) ≤ ε) :
    ∃ y, Tendsto f l (𝓝 y) := by
  refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩)
  obtain ⟨t, ht, hf⟩ := hl (ε / 2) (half_pos hε)
  refine ⟨f '' t, image_mem_map ht, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  exact (hf z hz w hw).trans_lt (half_lt_self hε)

private theorem Hbar_subset_closure_H : Hbar ⊆ closure H := by
  intro x hx
  have hx0 : 0 ≤ x.im := hx
  refine mem_closure_of_tendsto (f := fun n : ℕ => x + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)
    (b := atTop) ?_ (Eventually.of_forall fun n => ?_)
  · have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).ofReal.mul_const I).const_add x
    simpa using this
  · show 0 < (x + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- Qualitative form of the modulus: uniform continuity of `ψ` on `H`, and oscillation `≤ ε`
far out. -/
private theorem uniform_of_ulc {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    (hE : ULC E) {ε : ℝ} (hε : 0 < ε) :
    (∃ δ > 0, ∀ z ∈ H, ∀ w ∈ H, dist z w < δ → dist (ψ z) (ψ w) ≤ ε) ∧
    (∃ Rb > 0, ∀ z ∈ H, ∀ w ∈ H, Rb < ‖z‖ → Rb < ‖w‖ → dist (ψ z) (ψ w) ≤ ε) := by
  set η := infDist (ψ I) E
  have hη := infDist_pos h
  obtain ⟨δU, hδU, hU⟩ := hE (min (ε / 8) (η / 4)) (lt_min (by positivity) (by positivity))
  obtain ⟨δ, hδ, hmod⟩ := exists_modulus R₀ η ε δU hη hε hδU
  obtain ⟨Rb, hRb, hinf⟩ := exists_radius_infty R₀ η ε δU hη hε hδU
  exact ⟨⟨δ, hδ, hmod ψ D E h hU le_rfl⟩, ⟨Rb, hRb, hinf ψ D E h hU le_rfl⟩⟩

/-- **C3 (Carathéodory's continuity theorem, half-plane form).** Under `(Hψ)` there is `F`
with `F = ψ` on `H`, continuous on `Hbar`, with `F x ∈ frontier D` for every real `x`, and
`ψ z` converges to a point of `frontier D` as `z → ∞` in `H`. -/
theorem continuousOn_extension {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    (hE : ULC E) :
    ∃ F : ℂ → ℂ, EqOn F ψ H ∧ ContinuousOn F Hbar ∧ (∀ x : ℝ, F x ∈ frontier D) ∧
      ∃ wInf ∈ frontier D, Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf) := by
  -- limits at the points of `Hbar`
  have hlim : ∀ x ∈ Hbar, ∃ y, Tendsto ψ (𝓝[H] x) (𝓝 y) := by
    intro x hx
    have : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (Hbar_subset_closure_H hx)
    refine exists_tendsto_of_small fun ε hε => ?_
    obtain ⟨⟨δ, hδ, hmod⟩, -⟩ := uniform_of_ulc h hE hε
    refine ⟨H ∩ ball x (δ / 2), inter_mem_nhdsWithin H (ball_mem_nhds x (half_pos hδ)),
      fun z hz w hw => hmod z hz.1 w hw.1 ?_⟩
    calc dist z w ≤ dist z x + dist x w := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (mem_ball.1 hz.2) (by rw [dist_comm]; exact mem_ball.1 hw.2)
      _ = δ := add_halves δ
  set F := extendFrom H ψ with hF
  have hEq : EqOn F ψ H := extendFrom_extends h.holo.continuousOn
  refine ⟨F, hEq, continuousOn_extendFrom Hbar_subset_closure_H hlim, fun x => ?_, ?_⟩
  · -- boundary values are in `frontier D` (C1)
    have hx : ((x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp
    have hT := tendsto_extendFrom (hlim _ hx)
    set z : ℕ → ℂ := fun n => (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hz
    have hzH : ∀ n, z n ∈ H := fun n => by
      show 0 < (z n).im
      simp only [hz, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero, zero_add]
      positivity
    have hzx : Tendsto z atTop (𝓝 (x : ℂ)) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).ofReal.mul_const I).const_add
        (x : ℂ)
      simpa [hz] using this
    have hzw : Tendsto z atTop (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hzx, Eventually.of_forall hzH⟩
    exact frontier_mem_of_tendsto h hzH hzx (hT.comp hzw).mapClusterPt
  · -- the limit at `∞`
    set z : ℕ → ℂ := fun n => (((n : ℝ) + 1 : ℝ) : ℂ) * I with hz
    have hzH : ∀ n, z n ∈ H := fun n => by
      show 0 < (z n).im
      simp only [hz, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      positivity
    have hzc : Tendsto z atTop (Bornology.cobounded ℂ) := by
      refine tendsto_norm_atTop_iff_cobounded.1 ?_
      have : (fun n => ‖z n‖) = fun n : ℕ => (n : ℝ) + 1 := funext fun n => by
        simp only [hz, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by positivity)
      rw [this]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hzl : Tendsto z atTop (Bornology.cobounded ℂ ⊓ 𝓟 H) :=
      tendsto_inf.2 ⟨hzc, tendsto_principal.2 (Eventually.of_forall hzH)⟩
    have : (Bornology.cobounded ℂ ⊓ 𝓟 H).NeBot := hzl.neBot
    obtain ⟨w, hw⟩ : ∃ w, Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 w) := by
      refine exists_tendsto_of_small fun ε hε => ?_
      obtain ⟨-, ⟨Rb, hRb, hinf⟩⟩ := uniform_of_ulc h hE hε
      refine ⟨{y | Rb + 1 ≤ ‖y‖} ∩ H, inter_mem_inf (eventually_cobounded_le_norm (Rb + 1))
        (mem_principal_self H), fun y hy y' hy' => hinf y hy.2 y' hy'.2 ?_ ?_⟩
      · have := hy.1; simp only [mem_ofPred_eq] at this; linarith
      · have := hy'.1; simp only [mem_ofPred_eq] at this; linarith
    exact ⟨w, frontier_mem_of_tendsto_cobounded h hzH hzc (hw.comp hzl).mapClusterPt, hw⟩

/-- Boundary values of the extension as limits of `ψ` from inside `H` (for `limUnder`-type
definitions of boundary values, e.g. `revMapBdry` in R3). -/
theorem tendsto_nhdsWithin_H_of_extension {ψ F : ℂ → ℂ} (hEq : EqOn F ψ H)
    (hF : ContinuousOn F Hbar) {x : ℂ} (hx : x ∈ Hbar) : Tendsto ψ (𝓝[H] x) (𝓝 (F x)) :=
  ((hF x hx).tendsto.mono_left (nhdsWithin_mono x H_subset_Hbar)).congr'
    (eventuallyEq_nhdsWithin_of_eqOn hEq)

end QuantumZipper.CA.Car
