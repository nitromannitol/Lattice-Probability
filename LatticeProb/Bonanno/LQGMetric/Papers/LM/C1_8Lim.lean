/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8Lim at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Bdd
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocNest
import Mathlib.Probability.Martingale.Convergence

/-!
# LM Lemma 1.4 for all open sets, by exhaustion with bounded open sets (task P2-LMC18)

LM (Gwynne–Miller, arXiv:1905.00379, `local-metrics-final.tex`) Lemma 1.4 (l. 253–274) is proved
in `C1_8Bdd.lean` at bounded open `V` (where LM l. 534 is available, `GermSplit.locGermSplitBdd`).
For an arbitrary open `V` we exhaust `V` by the bounded open sets `W_n = V ∩ B_{n+1}(0)`, as LM
do for Lemma 2.3 (l. 545–548: "Letting `W` increase to all of `V`"):

* the internal metrics on `W_n` determine those on `V` (`c18_internal_eq_iInf`) and
  `σ(h|_V) = ⋁_n σ(h|_{W_n})` (`c18_fieldSigma_le_iSup`);
* the conditional independence given `h|_{W_n}` passes to the limit given `h|_V` (Lévy's upward
  theorem, mathlib `MeasureTheory.tendsto_ae_condExp`; `c18_condIndepEv_levy`), and then to the
  increasing union of the `σ(D_j(·,·;W_m))` (`LM.condIndepEv_iSup_of_monotone`).

Main results: `c18_jl_of_bdd`, **`lmLem1_4 : Blueprint.LMLem1_4`** (no hypotheses).
The exhaustion argument is own routine measure theory (LM's own argument for Lemma 2.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

section Levy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- conditional independence given an increasing sequence passes to the limit (Lévy upward) -/
theorem c18_condIndepEv_levy {G : ℕ → MeasurableSpace Ω} (hmono : Monotone G)
    (hle : ∀ n, G n ≤ mΩ) {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ) (m : ℕ)
    (h : ∀ n, m ≤ n → CondIndepEv (G n) A B μ) : CondIndepEv (⨆ n, G n) A B μ := by
  let ℱ : Filtration ℕ mΩ := ⟨G, hmono, hle⟩
  intro a b ha hb
  have ha' := hA a ha
  have hb' := hB b hb
  have L : ∀ s : Set Ω, ∀ᵐ x ∂μ, Tendsto (fun n => (μ⟦s | G n⟧) x) atTop
      (𝓝 ((μ⟦s | ⨆ n, G n⟧) x)) := fun s => tendsto_ae_condExp (ℱ := ℱ) _
  have E : ∀ᵐ x ∂μ, ∀ n, m ≤ n → (μ⟦a ∩ b | G n⟧) x = (μ⟦a | G n⟧ * μ⟦b | G n⟧) x := by
    rw [ae_all_iff]
    intro n
    by_cases hn : m ≤ n
    · filter_upwards [h n hn a b ha hb] with x hx _
      exact hx
    · exact Eventually.of_forall fun x h' => absurd h' hn
  filter_upwards [L (a ∩ b), L a, L b, E] with x h1 h2 h3 h4
  refine tendsto_nhds_unique h1 ((h2.mul h3).congr' ?_)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact (h4 n hn).symm

end Levy

/-! ## The bounded exhaustion `W_n = V ∩ B_{n+1}(0)` -/

/-- `W_n = V ∩ B_{n+1}(0)` -/
def c18W (V : TopologicalSpace.Opens ℂ) (n : ℕ) : TopologicalSpace.Opens ℂ :=
  ⟨(V : Set ℂ) ∩ ball 0 ((n : ℝ) + 1), V.isOpen.inter isOpen_ball⟩

lemma c18W_bdd (V : TopologicalSpace.Opens ℂ) (n : ℕ) :
    Bornology.IsBounded (c18W V n : Set ℂ) :=
  isBounded_ball.subset inter_subset_right

lemma c18W_le (V : TopologicalSpace.Opens ℂ) (n : ℕ) : c18W V n ≤ V :=
  fun _ hx => hx.1

lemma c18W_mono (V : TopologicalSpace.Opens ℂ) : Monotone (c18W V) := fun m n hmn x hx => by
  have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
  exact ⟨hx.1, mem_ball.2 (lt_of_lt_of_le (mem_ball.1 hx.2) (by linarith))⟩

/-- `D(u,v;V) = inf_n D(u,v;W_n)`: a path in `V` has compact range (proof of
`LM.internal_eq_iInf_exhaust`, with `W_n` bounded) -/
theorem c18_internal_eq_iInf (D : ContMetric) (V : TopologicalSpace.Opens ℂ) (u v : ℂ) :
    D.internal V u v = ⨅ n : ℕ, D.internal (c18W V n) u v := by
  refine le_antisymm (le_iInf fun n =>
    MetricGeometry.internalEDist_anti (image_mono (c18W_le V n)) _ _) ?_
  unfold ContMetric.internal MetricGeometry.internalEDist
  refine le_iInf fun γ => ?_
  set K : Set ℂ := range (D.unpt ∘ γ.1)
  have hKc : IsCompact K := isCompact_range (D.continuous_unpt.comp γ.1.continuous)
  have hKV : K ⊆ V := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy, hyt⟩ := γ.2 t
    simp only [Function.comp_apply, ← hyt, ContMetric.unpt_pt]
    exact hy
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hKW : K ⊆ c18W V n := fun z hz =>
    ⟨hKV hz, mem_ball.2 ((mem_ball.1 (hR hz)).trans_le (by linarith))⟩
  exact iInf_le_of_le n (iInf_le_of_le ⟨γ.1, fun t => ⟨D.unpt (γ.1 t),
    hKW ⟨t, rfl⟩, ContMetric.pt_unpt _ _⟩⟩ le_rfl)

section Exhaust

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
theorem c18_famSigma_le_iSup (D : Ω → ContMetric) (V : TopologicalSpace.Opens ℂ) :
    famSigma (internalFam D) V ≤ ⨆ n : ℕ, famSigma (internalFam D) (c18W V n) :=
  Measurable.comap_le (@measurable_of_eq_iInf Ω (⨆ n : ℕ, famSigma (internalFam D) (c18W V n))
    (fun ω => internalFam D ω V) (fun n ω => internalFam D ω (c18W V n))
    (fun n => (comap_measurable (fun ω => internalFam D ω (c18W V n))).mono
      (le_iSup (fun m => famSigma (internalFam D) (c18W V m)) n) le_rfl)
    (fun ω u v => c18_internal_eq_iInf (D ω) V u v))

omit mΩ in
/-- `σ(h|_V) = ⋁_n σ(h|_{W_n})`: a test function in `V` has compact support, inside some `W_n` -/
theorem c18_fieldSigma_le_iSup (h : Ω → DistC) (V : TopologicalSpace.Opens ℂ) :
    fieldSigma h V ≤ ⨆ n : ℕ, fieldSigma h (c18W V n) := by
  show MeasurableSpace.comap (fun ω => restrictTo V (h ω)) inferInstance ≤ _
  rw [← measurable_iff_comap_le]
  refine (@measurable_distOn_iff V Ω (⨆ n : ℕ, fieldSigma h (c18W V n)) _).2 fun φ => ?_
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_ge R
  let φ' : TestOn (c18W V n) :=
    { toFun := φ
      contDiff' := φ.contDiff
      hasCompactSupport' := φ.hasCompactSupport
      tsupport_subset' := fun z hz =>
        ⟨φ.tsupport_subset hz, mem_ball.2 ((mem_ball.1 (hR hz)).trans_le (by linarith))⟩ }
  have e : (fun ω => restrictTo V (h ω) φ) = fun ω => restrictTo (c18W V n) (h ω) φ' := by
    funext ω
    change h ω (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ) =
      h ω (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := c18W V n) (Ω₂ := ⊤) φ')
    congr 1
    ext x
    simp [TestFunction.monoCLM_apply]
    rfl
  rw [e]
  exact ((measurable_distOn_apply φ').comp (comap_measurable _)).mono
    (le_iSup (fun m => fieldSigma h (c18W V m)) n) le_rfl

omit mΩ in
lemma c18_fieldSigmaClosed_mono (h : Ω → DistC) {K K' : Set ℂ} (hKK' : K ⊆ K') :
    fieldSigmaClosed h K ≤ fieldSigmaClosed h K' :=
  le_iInf₂ fun ε hε => (iInf₂_le ε hε).trans
    (GM.fieldSigma_mono h fun _ hx => Metric.thickening_subset_of_subset ε hKK' hx)

/-- **joint locality from joint locality at bounded open sets** (exhaustion, LM l. 545–548) -/
theorem c18_jl_of_bdd [IsProbabilityMeasure P] {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hm : Measurable h) (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hl₁ : ∀ᵐ ω ∂P, (D₁ ω).IsLength) (hl₂ : ∀ᵐ ω ∂P, (D₂ ω).IsLength)
    (H : ∀ V : TopologicalSpace.Opens ℂ, Bornology.IsBounded (V : Set ℂ) →
      CondIndepEv (fieldSigma h V) (famSigma (internalFam D₁) V ⊔ famSigma (internalFam D₂) V)
        (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ famSigma (internalFam D₁) (closure (V : Set ℂ))ᶜ ⊔
          famSigma (internalFam D₂) (closure (V : Set ℂ))ᶜ) P) :
    IsJointlyLocalFam P h (internalFam D₁) (internalFam D₂) := by
  intro V
  have hWo : ∀ n, IsOpen (c18W V n : Set ℂ) := fun n => (c18W V n).isOpen
  have hO : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have hOn : ∀ n, IsOpen (closure (c18W V n : Set ℂ))ᶜ := fun _ => isClosed_closure.isOpen_compl
  let G : ℕ → MeasurableSpace Ω := fun n => fieldSigma h (c18W V n)
  have hGm : Monotone G := fun m n hmn => GM.fieldSigma_mono h (c18W_mono V hmn)
  have hGle : ∀ n, G n ≤ mΩ := fun n => fieldSigma_le hm _
  let A : ℕ → MeasurableSpace Ω := fun n => chainSigma D₁ (c18W V n) ⊔ chainSigma D₂ (c18W V n)
  let A' : ℕ → MeasurableSpace Ω := fun m => ⨆ (k : ℕ) (_ : k ≤ m), A k
  -- a function of `Unit`, so that it is not a local instance
  let Bf : Unit → MeasurableSpace Ω := fun _ => fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔
    chainSigma D₁ (closure (V : Set ℂ))ᶜ ⊔ chainSigma D₂ (closure (V : Set ℂ))ᶜ
  have hAle : ∀ n, A n ≤ mΩ := fun n => sup_le (chainSigma_le hD₁ _) (chainSigma_le hD₂ _)
  have hA'le : ∀ m, A' m ≤ mΩ := fun m => iSup₂_le fun k _ => hAle k
  have hBle : (Bf ()) ≤ mΩ :=
    sup_le (sup_le (fieldSigmaClosed_le hm _) (chainSigma_le hD₁ _)) (chainSigma_le hD₂ _)
  have hA'mono : Monotone A' := fun m n hmn => iSup₂_le fun k hk =>
    le_iSup₂ (f := fun k (_ : k ≤ n) => A k) k (hk.trans hmn)
  have hBn : ∀ n, (Bf ()) ≤ aeClosure P (fieldSigmaClosed h (c18W V n : Set ℂ)ᶜ ⊔
      famSigma (internalFam D₁) (closure (c18W V n : Set ℂ))ᶜ ⊔
      famSigma (internalFam D₂) (closure (c18W V n : Set ℂ))ᶜ) := fun n => by
    have hsub : (closure (V : Set ℂ))ᶜ ⊆ (closure (c18W V n : Set ℂ))ᶜ :=
      compl_subset_compl.2 (closure_mono (c18W_le V n))
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (c18_fieldSigmaClosed_mono h (compl_subset_compl.2 (c18W_le V n))).trans
        ((le_sup_left.trans le_sup_left).trans (le_aeClosure _))
    · exact le_aeClosure_trans (chainSigma_le_famSigma hl₁ hO)
        ((locInternalNest P D₁ hD₁ hl₁ _ _ hO (hOn n) hsub).trans
          (aeClosure_mono (le_sup_right.trans le_sup_left)))
    · exact le_aeClosure_trans (chainSigma_le_famSigma hl₂ hO)
        ((locInternalNest P D₂ hD₂ hl₂ _ _ hO (hOn n) hsub).trans (aeClosure_mono le_sup_right))
  have S1 : ∀ m n, m ≤ n → CondIndepEv (G n) (A' m) (Bf ()) P := fun m n hmn => by
    refine CondIndepEv.of_le_aeClosure (H (c18W V n) (c18W_bdd V n)) ?_ (hBn n)
    refine iSup₂_le fun k hk => sup_le ?_ ?_
    · exact le_aeClosure_trans (chainSigma_le_famSigma hl₁ (hWo k))
        ((locInternalNest P D₁ hD₁ hl₁ _ _ (hWo k) (hWo n) (c18W_mono V (hk.trans hmn))).trans
          (aeClosure_mono le_sup_left))
    · exact le_aeClosure_trans (chainSigma_le_famSigma hl₂ (hWo k))
        ((locInternalNest P D₂ hD₂ hl₂ _ _ (hWo k) (hWo n) (c18W_mono V (hk.trans hmn))).trans
          (aeClosure_mono le_sup_right))
  have S3 : ∀ m, CondIndepEv (⨆ n, G n) (A' m) (Bf ()) P := fun m =>
    c18_condIndepEv_levy hGm hGle (hA'le m) hBle m fun n hn => S1 m n hn
  have S4 := condIndepEv_iSup_of_monotone (iSup_le hGle) hA'le hBle hA'mono S3
  have hGeq : (⨆ n, G n) = fieldSigma h V :=
    le_antisymm (iSup_le fun n => GM.fieldSigma_mono h (c18W_le V n)) (c18_fieldSigma_le_iSup h V)
  rw [hGeq] at S4
  have hAin : ∀ n, A n ≤ ⨆ m, A' m := fun n =>
    (le_iSup₂ (f := fun k (_ : k ≤ n) => A k) n le_rfl).trans (le_iSup A' n)
  refine CondIndepEv.of_le_aeClosure S4 (sup_le ?_ ?_) ?_
  · exact (c18_famSigma_le_iSup D₁ V).trans (iSup_le fun n =>
      (famSigma_le_chainSigma hl₁ (hWo n)).trans (aeClosure_mono (le_sup_left.trans (hAin n))))
  · exact (c18_famSigma_le_iSup D₂ V).trans (iSup_le fun n =>
      (famSigma_le_chainSigma hl₂ (hWo n)).trans (aeClosure_mono (le_sup_right.trans (hAin n))))
  · refine sup_le (sup_le ((le_sup_left.trans le_sup_left).trans (le_aeClosure _)) ?_) ?_
    · exact (famSigma_le_chainSigma hl₁ hO).trans (aeClosure_mono (le_sup_right.trans le_sup_left))
    · exact (famSigma_le_chainSigma hl₂ hO).trans (aeClosure_mono le_sup_right)

end Exhaust

/-- **LM Lemma 1.4** (`lem-jointly-local`, l. 253–274), `n = 2`, `U = ℂ`: proved (bounded open
sets by `c18_jointlyLocalAt_bdd` with `GermSplit.locGermSplitBdd`, all open sets by
`c18_jl_of_bdd`) -/
theorem lmLem1_4 : LMLem1_4 := fun P _ h _ _ hh hl₁ hl₂ hci =>
  ⟨hl₁.1, hl₂.1, hl₁.2.1.and hl₂.2.1, c18_jl_of_bdd hh.measurable hl₁.1 hl₂.1 hl₁.2.1 hl₂.2.1
    fun V hVb => c18_jointlyLocalAt_bdd GermSplit.locGermSplitBdd hh hl₁ hl₂ hci V hVb⟩

end LQGMetric.LM
