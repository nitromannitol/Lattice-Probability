/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W6Fub at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Meas

/-!
# W6 (part 2): replacing `Ŷ'` by the reversed hitting path of an independent copy

Node W6 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), assembly step. With `X = dpath σ (-μ) b`,
`Y' = dpath σ μ b'`, `X' = dpath σ (-μ) b'` (`b, b'` independent), the glued path
`Z_c = glued c X Y'` killed at its last passage at `c + d` has the same killed
finite-dimensional expectations as `concatPre c (revHit X c) (revHit X' d)` killed at its
lifetime (`lintegral_phiZ_eq_phiR`).

Route: condition on `X` (independence and Fubini on the space `CPath × CPath` of pairs of
continuous paths, where every functional is measurable); for a fixed path `x`, the killed
functional of `Z_c` is a killed finite-dimensional functional of `Ŷ'` at the shifted times
`uᵢ - T_c(x)` (`phiZ_eq_hatKill`), and the same holds for the reversed side (`phiR_eq_revKill`);
W5(ii) at level `d` (`lintegral_hatKill_eq_revKill`) finishes. This replaces the blueprint's
W5(iii) (law of `preLast Ŷ d` = law of `revHit X' d`): only killed finite-dimensional laws are
needed. Own bookkeeping (the blueprint's W6 sketch; Williams 1974, Rogers–Pitman 1981 Thm 1).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

/-! ## Deterministic reduction for a fixed first path -/

section Det

variable {c d : ℝ} {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞)
  (x : ℝ≥0 → ℝ)

/-- The function of the second-piece values used once the first path is fixed. -/
def gShift (c : ℝ) (T : ℝ≥0) (r : ℝ≥0 → ℝ) (z : Fin n → ℝ) : ℝ≥0∞ :=
  g (fun i => if u i ≤ T then r (u i) else c + z i)

theorem measurable_gShift (hg : Measurable g) (c : ℝ) (T : ℝ≥0) (r : ℝ≥0 → ℝ) :
    Measurable (gShift u g c T r) := by
  refine hg.comp (measurable_pi_iff.2 fun i => ?_)
  by_cases h : u i ≤ T
  · simp only [h, ↓reduceIte]; exact measurable_const
  · simp only [h, ↓reduceIte]; exact measurable_const.add (measurable_pi_apply i)

theorem phiZ_eq_hatKill (hTU : hitLevel x (-c) ≤ U) (y : ℝ≥0 → ℝ) :
    phiZ c d u U g x y = hatKill d (fun i => u i - hitLevel x (-c)) (U - hitLevel x (-c))
      (gShift u g c (hitLevel x (-c)) (revHit x c).2) y := by
  unfold phiZ hatKill
  simp only [tsub_lt_iff_left hTU]
  rfl

theorem phiR_eq_revKill (hTU : hitLevel x (-c) ≤ U) (x' : ℝ≥0 → ℝ) :
    phiR c d u U g x x' = revKill d (fun i => u i - hitLevel x (-c)) (U - hitLevel x (-c))
      (gShift u g c (hitLevel x (-c)) (revHit x c).2) x' := by
  unfold phiR revKill
  simp only [tsub_lt_iff_left hTU]
  rfl

theorem phiZ_of_lt (hUT : U < hitLevel x (-c)) (y : ℝ≥0 → ℝ) (hu : ∀ i, u i ≤ U) :
    phiZ c d u U g x y = g (fun i => (revHit x c).2 (u i)) := by
  unfold phiZ glued
  rw [if_pos (lt_of_lt_of_le hUT le_self_add)]
  congr 1
  funext i
  rw [if_pos ((hu i).trans hUT.le)]

theorem phiR_of_lt (hUT : U < hitLevel x (-c)) (x' : ℝ≥0 → ℝ) (hu : ∀ i, u i ≤ U) :
    phiR c d u U g x x' = g (fun i => (revHit x c).2 (u i)) := by
  unfold phiR concatPre
  rw [if_pos (lt_of_lt_of_le hUT le_self_add)]
  congr 1
  funext i
  exact if_pos (show u i ≤ hitLevel x (-c) from (hu i).trans hUT.le)

end Det

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b b' : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- For a fixed first path `x`, the killed functionals of `Z_c` and of the concatenated
reversed path have equal expectations (W5(ii) at level `d` for `b'`). -/
theorem lintegral_phiZ_eq_phiR_fixed (hb' : GoodBM b' P) (hσ : 0 < σ) (hμ : 0 < μ) {c d : ℝ}
    (hd : 0 < d) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) (x : ℝ≥0 → ℝ) :
    ∫⁻ ω, phiZ c d u U g x (dpath σ μ b' ω) ∂P = ∫⁻ ω, phiR c d u U g x (dpath σ (-μ) b' ω) ∂P := by
  by_cases hUT : U < hitLevel x (-c)
  · refine lintegral_congr fun ω => ?_
    rw [phiZ_of_lt u U g x hUT _ hu, phiR_of_lt u U g x hUT _ hu]
  · have hTU : hitLevel x (-c) ≤ U := not_lt.1 hUT
    simp only [phiZ_eq_hatKill u U g x hTU, phiR_eq_revKill u U g x hTU]
    exact lintegral_hatKill_eq_revKill hb' hσ hμ hd _ _ (fun i => tsub_le_tsub_right (hu i) _)
      (measurable_gShift u g hg c _ _)

/-- Fubini along two independent random continuous paths. -/
theorem lintegral_indep_cPath [IsProbabilityMeasure P] {A B B' : Ω → CPath}
    (hA : Measurable A) (hB : Measurable B) (hB' : Measurable B')
    (hAB : IndepFun A B P) (hAB' : IndepFun A B' P)
    {F F' : CPath × CPath → ℝ≥0∞} (hF : Measurable F) (hF' : Measurable F')
    (h : ∀ x, ∫⁻ ω, F (x, B ω) ∂P = ∫⁻ ω, F' (x, B' ω) ∂P) :
    ∫⁻ ω, F (A ω, B ω) ∂P = ∫⁻ ω, F' (A ω, B' ω) ∂P := by
  have e1 : ∫⁻ ω, F (A ω, B ω) ∂P = ∫⁻ x, ∫⁻ ω, F (x, B ω) ∂P ∂(P.map A) := by
    rw [← lintegral_map hF (hA.prodMk hB),
      hAB.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable,
      lintegral_prod _ hF.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_map (hF.comp (measurable_const.prodMk measurable_id)) hB
  have e2 : ∫⁻ ω, F' (A ω, B' ω) ∂P = ∫⁻ x, ∫⁻ ω, F' (x, B' ω) ∂P ∂(P.map A) := by
    rw [← lintegral_map hF' (hA.prodMk hB'),
      hAB'.map_prod_eq_prod_map_map hA.aemeasurable hB'.aemeasurable,
      lintegral_prod _ hF'.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_map (hF'.comp (measurable_const.prodMk measurable_id)) hB'
  rw [e1, e2]
  exact lintegral_congr fun x => h x

theorem indepFun_futureC (hb : GoodBM b P) (hb' : GoodBM b' P)
    (hind : IndepFun (pathOf b) (pathOf b') P) (σ₁ μ₁ σ₂ μ₂ : ℝ) :
    IndepFun (futureC hb σ₁ μ₁) (futureC hb' σ₂ μ₂) P := by
  have hind_ind : Indep (MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b t ω) MeasurableSpace.pi)
      (MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => b' t ω) MeasurableSpace.pi) P :=
    (IndepFun_iff_Indep (fun ω t => b t ω) (fun ω t => b' t ω) P).mp hind
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left
    (indep_of_indep_of_le_right hind_ind (Measurable.comap_le (measurable_futureC_comap hb' σ₂ μ₂)))
    (Measurable.comap_le (measurable_futureC_comap hb σ₁ μ₁))

/-- **W6, independence step.** -/
theorem lintegral_phiZ_eq_phiR (hb : GoodBM b P) (hb' : GoodBM b' P) (hσ : 0 < σ) (hμ : 0 < μ)
    (hind : IndepFun (pathOf b) (pathOf b') P) {c d : ℝ} (hd : 0 < d) {n : ℕ}
    (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U) {g : (Fin n → ℝ) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ ω, phiZ c d u U g (dpath σ (-μ) b ω) (dpath σ μ b' ω) ∂P
      = ∫⁻ ω, phiR c d u U g (dpath σ (-μ) b ω) (dpath σ (-μ) b' ω) ∂P := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hF : Measurable fun p : CPath × CPath =>
      phiZ c d u U g (p.1 : ℝ≥0 → ℝ) (p.2 : ℝ≥0 → ℝ) :=
    measurable_phiZ_gen (fun p => p.1.2) cPath_fst_meas (fun p => p.2.2) cPath_snd_meas c d u U hg
  have hF' : Measurable fun p : CPath × CPath =>
      phiR c d u U g (p.1 : ℝ≥0 → ℝ) (p.2 : ℝ≥0 → ℝ) :=
    measurable_phiR_gen (fun p => p.1.2) cPath_fst_meas (fun p => p.2.2) cPath_snd_meas c d u U hg
  exact lintegral_indep_cPath (A := futureC hb σ (-μ)) (B := futureC hb' σ μ)
    (B' := futureC hb' σ (-μ)) (measurable_futureC hb σ (-μ)) (measurable_futureC hb' σ μ)
    (measurable_futureC hb' σ (-μ)) (indepFun_futureC hb hb' hind _ _ _ _)
    (indepFun_futureC hb hb' hind _ _ _ _) hF hF'
    (fun x => lintegral_phiZ_eq_phiR_fixed hb' hσ hμ hd u U hu hg (x : ℝ≥0 → ℝ))

end QuantumZipper.Williams
