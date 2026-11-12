/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W6Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Fub
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Coc
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Tail
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Red
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.PathLaw

/-!
# W6 (part 4): assembly of `WilliamsDriftDecomposition` (L14)

Node W6 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), assembly, and the discharge of
`WilliamsDriftDecomposition` (`Proofs/LQG/WedgeTranslation.lean`).

For `X = dpath σ (-μ) b`, `Y' = dpath σ μ b'` (`b, b'` independent), `Ŷ' = postLast Y' 0` and
the glued path `Z_c = glued c X Y'`, and every level `d > 0`:

`E[g(Z_c(uᵢ)); U < T_c + λ_d(Ŷ')]`
` = E[g(concatPre c (revHit X c) (revHit X' d) (uᵢ)); U < T_c + T'_d]`   (independence, W5(ii) at `d`)
` = E[g(revHit X' (c+d) (uᵢ)); U < T'_{c+d}]`                            (cocycle, gluing)
` = E[g(Ŷ'(uᵢ)); U < λ_{c+d}(Ŷ')]`                                        (W5(ii) at `c + d`)

(`lintegral_phiZ_eq_hatKill`). Letting `d → ∞` (dominated convergence; `λ_a(Ŷ') → ∞` a.s.,
`W6Tail.lean`) gives equal finite-dimensional laws of `Z_c` and `Ŷ'`
(`map_fd_glued_eq`), hence equal path laws (W7, `map_eq_of_forall_finset`), which is
`WilliamsDriftDecomposition` after the reductions `williamsDrift_of_good` (W0) and
`williamsDrift_of_good_hit` (W6Red).

Sources: D. Williams, *Path decomposition and continuity of local time for one-dimensional
diffusions I*, Proc. LMS 28 (1974); L. C. G. Rogers, J. W. Pitman, *Markov functions*, Ann.
Probab. 9 (1981), Thm 1; Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII §4. The
route (blueprint W6, with the killed finite-dimensional functionals replacing the law identity
W5(iii)) is the blueprint's; the bookkeeping is own.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b b' : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- **W6, killed identity at level `c + d`.** -/
theorem lintegral_phiZ_eq_hatKill (hb : GoodBM b P) (hb' : GoodBM b' P) (hσ : 0 < σ)
    (hμ : 0 < μ) (hind : IndepFun (pathOf b) (pathOf b') P) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hhit : ∀ ω, ∃ t, dpath σ (-μ) b ω t = -c) (hhit' : ∀ ω, ∃ t, dpath σ (-μ) b' ω t = -d)
    {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U) {g : (Fin n → ℝ) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ ω, phiZ c d u U g (dpath σ (-μ) b ω) (dpath σ μ b' ω) ∂P
      = ∫⁻ ω, hatKill (c + d) u U g (dpath σ μ b' ω) ∂P :=
  (lintegral_phiZ_eq_phiR hb hb' hσ hμ hind hd u U hu hg).trans
    ((lintegral_phiR_eq_revKill hb hb' hind hc hd hhit hhit' u U hg).trans
      (lintegral_hatKill_eq_revKill hb' hσ hμ (add_pos hc hd) u U hu hg).symm)

theorem measurable_glued_dpath (hb : GoodBM b P) (hb' : GoodBM b' P) (σ μ c : ℝ) (v : ℝ≥0) :
    Measurable fun ω => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) v := by
  have hT := measurable_hitLevel_dpath hb σ (-μ) (-c)
  exact Measurable.ite (measurableSet_le measurable_const hT)
    (measurable_revHit_eval hb σ (-μ) c v)
    (measurable_const.add (measurable_postLast_gen (continuous_dpath hb' σ μ)
      (measurable_dpath hb' σ μ) (measurable_const.sub hT)))

/-- **W6, removal of the killing** (`d → ∞`, dominated convergence). -/
theorem lintegral_glued_eq_postLast (hb : GoodBM b P) (hb' : GoodBM b' P) (hσ : 0 < σ)
    (hμ : 0 < μ) (hind : IndepFun (pathOf b) (pathOf b') P) {c : ℝ} (hc : 0 < c)
    (hhit : ∀ ω, ∃ t, dpath σ (-μ) b ω t = -c)
    (hhit' : ∀ ω (d : ℝ), 0 < d → ∃ t, dpath σ (-μ) b' ω t = -d)
    {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U) {g : (Fin n → ℝ) → ℝ≥0∞}
    (hg : Measurable g) {M : ℝ≥0∞} (hM : M ≠ ∞) (hgM : ∀ x, g x ≤ M) :
    ∫⁻ ω, g (fun i => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) (u i)) ∂P
      = ∫⁻ ω, g (fun i => postLast (dpath σ μ b' ω) 0 (u i)) ∂P := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hdk : ∀ k : ℕ, (0 : ℝ) < k + 1 := fun k => by positivity
  have hfin : ∫⁻ _, M ∂P ≠ ∞ := by simp [lintegral_const, hM]
  have hae := ae_tendsto_lastPass_postLast (σ := σ) hb' hμ
  have h1 : Tendsto (fun k : ℕ => ∫⁻ ω, phiZ c ((k : ℝ) + 1) u U g (dpath σ (-μ) b ω)
      (dpath σ μ b' ω) ∂P) atTop
      (𝓝 (∫⁻ ω, g (fun i => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) (u i)) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => M) (fun k => ?_) (fun k => ?_)
      hfin ?_
    · exact measurable_phiZ_gen (continuous_dpath hb σ (-μ)) (measurable_dpath hb σ (-μ))
        (continuous_dpath hb' σ μ) (measurable_dpath hb' σ μ) c _ u U hg
    · refine Eventually.of_forall fun ω => ?_
      simp only [phiZ]
      split_ifs
      · exact hgM _
      · exact zero_le
    · filter_upwards [hae] with ω hω
      obtain ⟨A, hA⟩ := hω U
      obtain ⟨N, hN⟩ := exists_nat_ge A
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk => ?_
      have hlt := hA ((k : ℝ) + 1) (hN.trans (by exact_mod_cast (hk.trans (Nat.le_succ k))))
      simp only [phiZ]
      rw [if_pos (lt_of_lt_of_le hlt le_add_self)]
  have h2 : Tendsto (fun k : ℕ => ∫⁻ ω, hatKill (c + ((k : ℝ) + 1)) u U g (dpath σ μ b' ω) ∂P)
      atTop (𝓝 (∫⁻ ω, g (fun i => postLast (dpath σ μ b' ω) 0 (u i)) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => M) (fun k => ?_) (fun k => ?_)
      hfin ?_
    · exact measurable_hatKill_gen (continuous_dpath hb' σ μ) (measurable_dpath hb' σ μ) _ u U hg
    · refine Eventually.of_forall fun ω => ?_
      simp only [hatKill]
      split_ifs
      · exact hgM _
      · exact zero_le
    · filter_upwards [hae] with ω hω
      obtain ⟨A, hA⟩ := hω U
      obtain ⟨N, hN⟩ := exists_nat_ge A
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk => ?_
      have hlt := hA (c + ((k : ℝ) + 1)) (by
        have : (N : ℝ) ≤ k := by exact_mod_cast hk
        linarith)
      simp only [hatKill]
      rw [if_pos hlt]
  have heq : (fun k : ℕ => ∫⁻ ω, phiZ c ((k : ℝ) + 1) u U g (dpath σ (-μ) b ω)
      (dpath σ μ b' ω) ∂P) =
      fun k : ℕ => ∫⁻ ω, hatKill (c + ((k : ℝ) + 1)) u U g (dpath σ μ b' ω) ∂P :=
    funext fun k => lintegral_phiZ_eq_hatKill hb hb' hσ hμ hind hc (hdk k) hhit
      (fun ω => hhit' ω _ (hdk k)) u U hu hg
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- **W6, finite-dimensional laws** (`Fin n`-indexed times). -/
theorem map_fd_glued_eq (hb : GoodBM b P) (hb' : GoodBM b' P) (hσ : 0 < σ)
    (hμ : 0 < μ) (hind : IndepFun (pathOf b) (pathOf b') P) {c : ℝ} (hc : 0 < c)
    (hhit : ∀ ω, ∃ t, dpath σ (-μ) b ω t = -c)
    (hhit' : ∀ ω (d : ℝ), 0 < d → ∃ t, dpath σ (-μ) b' ω t = -d) {n : ℕ} (u : Fin n → ℝ≥0) :
    P.map (fun ω i => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) (u i))
      = P.map (fun ω i => postLast (dpath σ μ b' ω) 0 (u i)) := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hφ₁ : Measurable fun ω (i : Fin n) => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) (u i) :=
    measurable_pi_iff.2 fun i => measurable_glued_dpath hb hb' σ μ c (u i)
  have hφ₂ : Measurable fun ω (i : Fin n) => postLast (dpath σ μ b' ω) 0 (u i) :=
    measurable_pi_iff.2 fun i => measurable_postLast_eval hb' σ μ (u i)
  refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f => ?_
  have hfm : Measurable fun x : Fin n → ℝ => (f x : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp f.continuous).measurable
  rw [lintegral_map hfm hφ₁, lintegral_map hfm hφ₂]
  exact lintegral_glued_eq_postLast hb hb' hσ hμ hind hc hhit hhit' u (∑ i, u i)
    (fun i => Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)) hfm
    ENNReal.coe_ne_top (fun x => ENNReal.coe_le_coe.2 (BoundedContinuousFunction.NNReal.upper_bound f x))

/-- **W6, path laws.** Under the hitting hypotheses, `Z_c` and `Ŷ'` have the same law. -/
theorem map_glued_eq_map_postLast (hb : GoodBM b P) (hb' : GoodBM b' P) (hσ : 0 < σ)
    (hμ : 0 < μ) (hind : IndepFun (pathOf b) (pathOf b') P) {c : ℝ} (hc : 0 < c)
    (hhit : ∀ ω, ∃ t, dpath σ (-μ) b ω t = -c)
    (hhit' : ∀ ω (d : ℝ), 0 < d → ∃ t, dpath σ (-μ) b' ω t = -d) :
    P.map (fun ω u => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) u)
      = P.map (fun ω u => postLast (dpath σ μ b' ω) 0 u) := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  refine map_eq_of_forall_finset
    (measurable_pi_iff.2 fun v => measurable_glued_dpath hb hb' σ μ c v).aemeasurable
    (measurable_pi_iff.2 fun v => measurable_postLast_eval hb' σ μ v).aemeasurable fun I => ?_
  set e := I.equivFin
  set ρ : (Fin I.card → ℝ) → (I → ℝ) := fun v i => v (e i) with hρ
  have hρm : Measurable ρ := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hfd := map_fd_glued_eq hb hb' hσ hμ hind hc hhit hhit' (fun j => (e.symm j : ℝ≥0))
  have hφ₁ : Measurable fun ω (j : Fin I.card) =>
      glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) (e.symm j : ℝ≥0) :=
    measurable_pi_iff.2 fun j => measurable_glued_dpath hb hb' σ μ c _
  have hφ₂ : Measurable fun ω (j : Fin I.card) => postLast (dpath σ μ b' ω) 0 (e.symm j : ℝ≥0) :=
    measurable_pi_iff.2 fun j => measurable_postLast_eval hb' σ μ _
  have e1 : (fun ω => I.restrict (fun u => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) u))
      = ρ ∘ fun ω (j : Fin I.card) =>
          glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) (e.symm j : ℝ≥0) := by
    funext ω i
    simp [hρ, Finset.restrict]
  have e2 : (fun ω => I.restrict (fun u => postLast (dpath σ μ b' ω) 0 u))
      = ρ ∘ fun ω (j : Fin I.card) => postLast (dpath σ μ b' ω) 0 (e.symm j : ℝ≥0) := by
    funext ω i
    simp [hρ, Finset.restrict]
  rw [e1, e2, ← Measure.map_map hρm hφ₁, ← Measure.map_map hρm hφ₂, hfd]

/-- **L14 (`WilliamsDriftDecomposition`) holds.** Williams (1974); Rogers–Pitman (1981), Thm 1;
Revuz–Yor VII §4. -/
theorem williamsDriftDecomposition_holds : WilliamsDriftDecomposition :=
  williamsDrift_of_good_hit fun _μ _σ _c hμ hσ hc _Ω _ _P _ _b _b' hb hb' hind hhit hhit' =>
    map_glued_eq_map_postLast hb hb' hσ hμ hind hc hhit hhit'

/-- **B4(c): wedge translation invariance, unconditionally.** -/
theorem wedge_translation_uncond {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {α Q : ℝ} {A : ℝ → Ω → ℝ}
    (hA : IsWedgeProcess α Q A P) (hαQ : α < Q) {c : ℝ} (hc : 0 < c) :
    P.map (fun ω t => A (sInf {s | 0 ≤ s ∧ A s ω ≤ -c} + t) ω + c) =
      P.map (fun ω t => A t ω) :=
  WedgeTrans.wedge_translation williamsDriftDecomposition_holds hA hαQ hc

end QuantumZipper.Williams
