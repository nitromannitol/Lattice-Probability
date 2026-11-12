/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3J at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3I
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case `B_r(z) ⊂ V`: the proof (`lem2_17Core_proof`)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17
(T:1218–1282) with decision D80 (conditioning on `h|_{cl V}` on the left of
(eqn-limit-metric-ind)) and D90 (`hconv` in the coordinates `pairJ ⊤`).

Step 1 (T:1220–1225): the Markov decomposition of `h̃ = h − h_r(z)` in `ℂ ∖ V̄`
(`markov_normAt`, LM Lemma 2.1); the harmonic part is a function `g` of the coordinates
(Doob–Dynkin). Steps 2–4 for each stage (`condIndepEv_law_stage`, with the data of
`exists_stage_data` for the stage families `dyFin V k`, `dyFin (ℂ ∖ V̄) k`), the monotone limit
(`condIndepEv_iSup_of_monotone`) on the law of `(J h, e^{−ξh_r(z)} D_h)`, the pull-back to `Ω`
(`condIndepEv_comap_of_map`), and the identification of the σ-algebras of Def 2.15
(`famSigma_normFam_le`, `comap_le_aeClosure_sup_of_add`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip

set_option warn.classDefReducibility false in
/-- the σ-algebra of the internal metrics `D(·,·;W)`, `W ∈ dyFin A k`, on the coordinate space -/
def stA (A : Set ℂ) (k : ℕ) : MeasurableSpace ((CoordJ → ℝ) × C(ℂ × ℂ, ℝ)) :=
  ⨆ W ∈ dyFin A k, MeasurableSpace.comap
    (fun q : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) => intFn W q.2) inferInstance

theorem stA_le (A : Set ℂ) (k : ℕ) :
    stA A k ≤ (inferInstance : MeasurableSpace ((CoordJ → ℝ) × C(ℂ × ℂ, ℝ))) :=
  iSup₂_le fun W _ => ((measurable_intFn W).comp measurable_snd).comap_le

theorem stA_mono (A : Set ℂ) : Monotone (stA A) := fun _ _ hkl =>
  iSup₂_le fun W hW => le_iSup₂_of_le (f := fun W (_ : W ∈ dyFin A _) => MeasurableSpace.comap
    (fun q : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) => intFn W q.2) inferInstance) W (dyFin_mono A hkl hW)
      le_rfl

/-- `σ(D(·,·;W)) ≤ σ(Ψ)`-pullback of `⨆ₖ stA A k` when `W̄ ⊆ A` -/
theorem comap_intFn_le_stA {Ω : Type} {Ψ : Ω → (CoordJ → ℝ) × C(ℂ × ℂ, ℝ)} {A : Set ℂ}
    {W : dyadicDomainsC} (hW : closure (W : Set ℂ) ⊆ A) :
    MeasurableSpace.comap (fun ω => intFn W (Ψ ω).2) inferInstance ≤
      MeasurableSpace.comap Ψ (⨆ k, stA A k) := by
  obtain ⟨k, hk⟩ := exists_mem_dyFin hW
  refine le_trans ?_ (MeasurableSpace.comap_mono (le_iSup _ k))
  refine le_trans ?_ (MeasurableSpace.comap_mono (le_iSup₂_of_le (f := fun W (_ : W ∈ dyFin A k) =>
    MeasurableSpace.comap (fun q : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) => intFn W q.2) inferInstance)
      W hk le_rfl))
  rw [MeasurableSpace.comap_comp]
  exact le_rfl

/-- **DFGPS Lemma 2.17, case `B_r(z) ⊂ V`** (T:1218–1282). -/
theorem lem2_17Core_proof (hLM : LMLem2_1) (h28 : Lem2_8) (HG : Lem2_1GffApprox.{0}) :
    Lem2_17Core := by
  intro γ hγ hγ2 Ω mΩ P _ h Dh εn hh hDm hεp hε0 hconv z r V hr hb
  set X : Ω → CoordJ → ℝ := fun ω => pairJ ⊤ (h ω) with hXdef
  have hX : Measurable X := (measurable_pairJ ⊤).comp hh.1.measurable
  have hNX : ∀ ω, normField (pairJInv ⊤) z r (X ω) = normField h z r ω := fun ω =>
    normField_pairJInv_pairJ z r ω
  have hNm : Measurable (normField (pairJInv ⊤) z r) :=
    (isGFFPlusBddCont_normField_pairJInv hh hr z).1
  have hrec := isNormalizedAt_recenter hh.1 hr z
  -- Step 1: the Markov decomposition in `ℂ ∖ V̄`
  set Uc : Opens ℂ := ⟨(closure (V : Set ℂ))ᶜ, isClosed_closure.isOpen_compl⟩ with hUcdef
  have hUcc : ((Uc : Set ℂ))ᶜ = closure (V : Set ℂ) := compl_compl _
  have hdisj : Disjoint (Uc : Set ℂ) (sphere z r) := by
    refine Set.disjoint_compl_left_iff_subset.2 ?_
    calc sphere z r ⊆ closedBall z r := sphere_subset_closedBall
      _ = closure (ball z r) := (closure_ball z hr.ne').symm
      _ ⊆ closure (V : Set ℂ) := closure_mono hb
  obtain ⟨hh', hz, hsum, hharm, ⟨G₀, hG₀m, hG₀ae⟩, -, -, -, hind⟩ :=
    markov_normAt hLM P (normField h z r) hrec.1 hr z hrec.2 Uc hdisj
  rw [hUcc] at hG₀m hind
  -- the harmonic part as a function of the coordinates (Doob–Dynkin)
  have hGX : fieldSigmaClosed (normField h z r) (closure (V : Set ℂ)) ≤
      MeasurableSpace.comap X (MeasurableSpace.map X
        (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance) := by
    intro s hs
    have hle : MeasurableSpace.comap (fun ω => pairJ ⊤ (normField h z r ω)) inferInstance ≤
        MeasurableSpace.comap X inferInstance := by
      rw [show (fun ω => pairJ ⊤ (normField h z r ω)) =
          (fun x => pairJ ⊤ (normField (pairJInv ⊤) z r x)) ∘ X from
        funext fun ω => by simp only [Function.comp, hNX], ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono ((measurable_pairJ ⊤).comp hNm).comap_le
    obtain ⟨t, ht, rfl⟩ := hle s (fieldSigmaClosed_le_comap_pairJ _ _ s hs)
    exact ⟨t, MeasurableSpace.measurableSet_inf.2 ⟨hs, ht⟩, rfl⟩
  obtain ⟨g, hg, hG₀eq⟩ := Measurable.exists_eq_measurable_comp (mY := MeasurableSpace.map X
    (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance)
    (hG₀m.mono hGX le_rfl)
  have hae : hh' =ᵐ[P] fun ω => g (X ω) := hG₀ae.trans (EventuallyEq.of_eq hG₀eq)
  have hgm : Measurable g := hg.mono inf_le_right le_rfl
  have hNgm : Measurable fun x => normField (pairJInv ⊤) z r x - g x :=
    measurable_distOn_iff.2 fun ψ =>
      ((measurable_distOn_apply ψ).comp hNm).sub ((measurable_distOn_apply ψ).comp hgm)
  have hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength := ae_isLength_of_conv h28 hγ hγ2 hh hDm hεp hε0 hconv
  -- the law of `(J h, e^{−ξh_r(z)} D_h)`
  set Ψ : Ω → (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) := fun ω =>
    (X ω, Real.exp (-xiGamma γ * circleAvg (h ω) r z) • (Dh ω).1) with hΨdef
  have hcm : Measurable fun ω => -xiGamma γ * circleAvg (h ω) r z :=
    ((measurable_circleAvg_left r z).comp hh.1.measurable).const_mul _
  have hΨ : Measurable Ψ :=
    hX.prodMk (measurable_subtype_coe.comp (measurable_smulPos_rand hDm hcm))
  have : IsProbabilityMeasure (P.map Ψ) :=
    (Measure.isProbabilityMeasure_map_iff hΨ.aemeasurable).2 inferInstance
  -- Steps 2–4 for every stage
  have hstage : ∀ k, CondIndepEv ((MeasurableSpace.map X
        (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance).comap
          (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ))
      (stA V k)
      ((MeasurableSpace.comap (fun x => normField (pairJInv ⊤) z r x - g x) inferInstance).comap
          (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ⊔ stA (closure (V : Set ℂ))ᶜ k)
      (P.map Ψ) := fun k => by
    obtain ⟨φ, U₁, δ, m, hφc, hU₁, hφ1, hδ, hφU, hWV, hWU⟩ := exists_stage_data V.isOpen
      Uc.isOpen hε0 (dyFin V k) (dyFin (closure (V : Set ℂ))ᶜ k) (fun W hW => (mem_dyFin.1 hW).2)
      (fun W hW => (mem_dyFin.1 hW).2)
    exact condIndepEv_law_stage h28 HG hγ hγ2 hh hDm hεp hε0 hconv hr hsum hharm hg hae hind
      hφc hδ hφU hU₁ hφ1 _ _ m hWV hWU
  have h𝒢T : (MeasurableSpace.map X
        (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance).comap
          (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ≤
        (inferInstance : MeasurableSpace ((CoordJ → ℝ) × C(ℂ × ℂ, ℝ))) :=
    (MeasurableSpace.comap_mono inf_le_right).trans measurable_fst.comap_le
  have hℋT : (MeasurableSpace.comap (fun x => normField (pairJInv ⊤) z r x - g x)
      inferInstance).comap (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ≤
        (inferInstance : MeasurableSpace ((CoordJ → ℝ) × C(ℂ × ℂ, ℝ))) :=
    (MeasurableSpace.comap_mono hNgm.comap_le).trans measurable_fst.comap_le
  -- the monotone limit (Step 4, "letting `W`, `W'` increase") and the pull-back to `Ω`
  have hlim := condIndepEv_iSup_of_monotone h𝒢T (stA_le V)
    (fun k => sup_le hℋT (stA_le _ k)) (stA_mono V)
    (fun _ _ hkl => sup_le_sup_left (stA_mono _ hkl) _) hstage
  have hpull := condIndepEv_comap_of_map hΨ h𝒢T (iSup_le (stA_le V))
    (iSup_le fun k => sup_le hℋT (stA_le _ k)) hlim
  -- the σ-algebras of Def 2.15 (`LocalAt`)
  have hGm : MeasurableSpace.comap Ψ ((MeasurableSpace.map X
      (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance).comap
        (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ)) ≤ mΩ :=
    (MeasurableSpace.comap_mono h𝒢T).trans hΨ.comap_le
  have hAm : MeasurableSpace.comap Ψ (⨆ k, stA V k) ≤ mΩ :=
    (MeasurableSpace.comap_mono (iSup_le (stA_le V))).trans hΨ.comap_le
  have hBm : MeasurableSpace.comap Ψ (⨆ k, (MeasurableSpace.comap
      (fun x => normField (pairJInv ⊤) z r x - g x) inferInstance).comap
        (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ⊔ stA (closure (V : Set ℂ))ᶜ k) ≤ mΩ :=
    (MeasurableSpace.comap_mono (iSup_le fun k => sup_le hℋT (stA_le _ k))).trans hΨ.comap_le
  have H3 := L219.condIndepEv_sup_cond hGm hAm hBm hpull
  have hGeq : MeasurableSpace.comap Ψ ((MeasurableSpace.map X
      (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance).comap
        (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ)) = MeasurableSpace.comap X
      (MeasurableSpace.map X (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓
        inferInstance) := by
    rw [MeasurableSpace.comap_comp]; rfl
  have hGc1 : MeasurableSpace.comap X (MeasurableSpace.map X
      (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance) ≤
        fieldSigmaClosed (normField h z r) (closure (V : Set ℂ)) :=
    (MeasurableSpace.comap_mono inf_le_left).trans MeasurableSpace.comap_map_le
  -- the `V` side
  have hA' : famSigma (normFam (xiGamma γ) h Dh z r) V ≤ aeClosure P
      (MeasurableSpace.comap Ψ (⨆ k, stA V k) ⊔ MeasurableSpace.comap Ψ ((MeasurableSpace.map X
        (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance).comap
          (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ))) :=
    (famSigma_normFam_le (P := P) (xiGamma γ) h Dh z r hlen V.isOpen).trans
      (aeClosure_mono (iSup₂_le fun W hW => le_sup_of_le_left (comap_intFn_le_stA (Ψ := Ψ) hW)))
  -- the `ℂ ∖ V̄` side
  have hzae : hz =ᵐ[P] fun ω => normField (pairJInv ⊤) z r (X ω) - g (X ω) := by
    filter_upwards [hae] with ω hω
    rw [hNX ω, hsum ω, show g (X ω) = hh' ω from hω.symm, add_sub_cancel_left]
  have hB0 : ∀ k, MeasurableSpace.comap Ψ (stA (closure (V : Set ℂ))ᶜ k) ≤
      MeasurableSpace.comap Ψ (⨆ k, (MeasurableSpace.comap
        (fun x => normField (pairJInv ⊤) z r x - g x) inferInstance).comap
          (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ⊔
            stA (closure (V : Set ℂ))ᶜ k) := fun k =>
    MeasurableSpace.comap_mono (le_sup_right.trans (le_iSup (fun k => (MeasurableSpace.comap
      (fun x => normField (pairJInv ⊤) z r x - g x) inferInstance).comap
        (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ⊔
          stA (closure (V : Set ℂ))ᶜ k) k))
  have hB' : MeasurableSpace.comap (normField h z r) inferInstance ⊔
      famSigma (normFam (xiGamma γ) h Dh z r) (closure (V : Set ℂ))ᶜ ≤ aeClosure P
        (MeasurableSpace.comap Ψ (⨆ k, (MeasurableSpace.comap
          (fun x => normField (pairJInv ⊤) z r x - g x) inferInstance).comap
            (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ⊔
              stA (closure (V : Set ℂ))ᶜ k) ⊔
          MeasurableSpace.comap Ψ ((MeasurableSpace.map X
            (fieldSigmaClosed (normField h z r) (closure (V : Set ℂ))) ⊓ inferInstance).comap
              (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ))) := by
    refine sup_le ?_ ?_
    · refine (comap_le_aeClosure_sup_of_add hsum hG₀m hG₀ae).trans
        ((aeClosure_mono (sup_le ?_ ?_)).trans (aeClosure_aeClosure_le _))
      · rw [hGeq]
        exact (hGX.trans le_sup_right).trans (le_aeClosure _)
      · refine (L219.comap_le_aeClosure_of_ae_eq (comap_measurable _) hzae).trans
          (aeClosure_mono (le_sup_of_le_left ?_))
        refine le_trans ?_ (MeasurableSpace.comap_mono (le_sup_left.trans
          (le_iSup (fun k => (MeasurableSpace.comap
            (fun x => normField (pairJInv ⊤) z r x - g x) inferInstance).comap
              (Prod.fst : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → CoordJ → ℝ) ⊔
                stA (closure (V : Set ℂ))ᶜ k) 0)))
        rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
        exact le_rfl
    · refine (famSigma_normFam_le (P := P) (xiGamma γ) h Dh z r hlen
        isClosed_closure.isOpen_compl).trans (aeClosure_mono (iSup₂_le fun W hW => ?_))
      refine le_sup_of_le_left ?_
      exact (comap_intFn_le_stA (Ψ := Ψ) hW).trans
        (MeasurableSpace.comap_mono (iSup_mono fun k => le_sup_right))
  have H4 := GM.Bilip.CondIndepEv.of_le_aeClosure H3 hA' hB'
  refine condIndepEv_congr_cond hGm (fieldSigmaClosed_le hrec.1.measurable _) ?_ ?_
    (hA'.trans (aeClosure_mono (sup_le hAm hGm))) (hB'.trans (aeClosure_mono (sup_le hBm hGm))) H4
  · rw [hGeq]; exact hGc1.trans (le_aeClosure _)
  · rw [hGeq]; exact hGX.trans (le_aeClosure _)

end L217

open Blueprint in
/-- **DFGPS Lemma 2.17, case `B_r(z) ⊂ V`** (`Lem2_17Core`, T:1218–1282), from LM Lemma 2.1
(Markov property), Lemma 2.8 and the GFF approximation input of Lemma 2.1. -/
theorem lem2_17Core (hLM : LMLem2_1) (h28 : Lem2_8) (HG : Lem2_1GffApprox.{0}) : Lem2_17Core :=
  L217.lem2_17Core_proof hLM h28 HG

end LQGMetric.DFGPS
