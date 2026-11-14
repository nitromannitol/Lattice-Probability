/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2EfronStein at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Inputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.ConditionalVariance
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.EfronBlocks
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.BlockReconstruction
import LatticeProb.Bonanno.LQGMetric.Prob.EfronSteinCopy

 










set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise J2Defs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 
theorem j2_measurable_condLogLen (hW : IsWhiteNoise P W) (Qψ : PsiParams) (ξ : ℝ) (K : ℕ) :
    Measurable (condLogLen ξ Qψ W P K) := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have h0K := isPsiVersion_psiMN (Q := Qψ) hW (Nat.zero_le K)
  have hYc : Measurable fun ω' : Ω => T20B.restrD (fun x => psiMN Qψ W P 0 K x ω') :=
    T20B.measurable_restrD.comp (measurable_pi_iff.2 h0K.meas)
  have hfam : Measurable fun q : (T20B.nearIdx K → T20B.dyD → ℝ) × Ω =>
      fun o : Option (T20B.nearIdx K) =>
        o.elim (T20B.restrD (fun x => psiMN Qψ W P 0 K x q.2)) q.1 := by
    refine measurable_pi_iff.2 fun o => ?_
    rcases o with _ | b
    · exact hYc.comp measurable_snd
    · exact (measurable_pi_apply b).comp measurable_fst
  have hΦ : StronglyMeasurable fun q : (T20B.nearIdx K → T20B.dyD → ℝ) × Ω =>
      T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
        o.elim (T20B.restrD (fun x => psiMN Qψ W P 0 K x q.2)) q.1) :=
    ((T20B.measurable_fLen ξ).comp hfam).stronglyMeasurable
  exact (hΦ.integral_prod_right' (ν := P)).measurable

 

theorem j2_condLogLen_ae_eq (hW : IsWhiteNoise P W) (Qψ : PsiParams) (hQ : PsiSmall Qψ)
    (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) :
    (fun ω => condLogLen ξ Qψ W P K (fineBlocks Qψ W P K n ω)) =ᵐ[P]
      P[L24.logLenPsi ξ Qψ W P n |
        (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))] := by
  have h0K := isPsiVersion_psiMN (Q := Qψ) hW (Nat.zero_le K)
  have hB := fun b => T20B.blkKn_spec hW Qψ hKn b
  filter_upwards [psi_condExp_eq_coarse_integral hW Qψ ξ hKn,
    T20B.sum_blkKn_ae hW Qψ hQ hKn] with ω hce hsum
  rw [hce]
  refine integral_congr_ae (Eventually.of_forall fun ω' => ?_)
  have hcont : Continuous fun x =>
      psiMN Qψ W P 0 K x ω' + ∑ b : T20B.nearIdx K, T20B.blkKn Qψ W P K n b.1 x ω :=
    (h0K.cont ω').add (continuous_finsetSum _ fun b _ => (hB b.1).1 ω)
  change T20B.fLen ξ _ = _
  rw [T20B.fLen_eq hcont (fun c => by
    rw [Fintype.sum_option]
    simp only [Option.elim, fineBlocks, T20B.restrD, Finset.sum_apply])]
  simp only [L23.logLen]
  congr 2
  refine rectLen_congr _ fun x hx => ?_
  have hx' : x ∈ L23.sq01 := hx
  rw [Finset.sum_coe_sort (T20B.nearIdx K) (fun b => T20B.blkKn Qψ W P K n b x ω),
    hsum x hx']
  ring

 


theorem j2_efron_stein (hW : IsWhiteNoise P W) (Qψ : PsiParams) (hQ : PsiSmall Qψ)
    (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) :
    Var[P[L24.logLenPsi ξ Qψ W P n |
        (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))]; P] ≤
      ∑ b : T20B.nearIdx K,
        ∫ z, max (efronDiff ξ Qψ W P K n b z) 0 ^ 2 ∂(P.prod P) := by
  classical
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hB := fun b => T20B.blkKn_spec hW Qψ hKn b
  let R : T20B.nearIdx K → Ω → (T20B.dyD → ℝ) := fun b ω => fineBlocks Qψ W P K n ω b
  have hR : ∀ b, Measurable (R b) := fun b =>
    measurable_pi_iff.2 fun c => (hB b.1).2.1 c
  have hindR : iIndepFun R P := by
    have h := (iIndepFun_psi_piece hW Qψ hKn).precomp (Option.some_injective _)
    exact h
  let X : T20B.nearIdx K → Ω × Ω → (T20B.dyD → ℝ) := fun b z => R b z.1
  let X' : T20B.nearIdx K → Ω × Ω → (T20B.dyD → ℝ) := fun b z => R b z.2
  have hX : ∀ b, Measurable (X b) := fun b => (hR b).comp measurable_fst
  have hX' : ∀ b, Measurable (X' b) := fun b => (hR b).comp measurable_snd
  have hind : iIndep (esCopySigma X X') (P.prod P) := by
    have h := (iIndepFun_iff_iIndep _ _ _).1 (T20B.iIndepFun_sumElim_prod hR hindR)
    convert h using 2 with k
    rcases k with i | i <;> rfl
  have hlaw : ∀ b, (P.prod P).map (X' b) = (P.prod P).map (X b) := fun b =>
    (T20B.map_comp_snd (hR b)).trans (T20B.map_comp_fst (hR b)).symm
  have hf := j2_measurable_condLogLen hW Qψ ξ K
  
  have hae1 := j2_condLogLen_ae_eq hW Qψ hQ ξ hKn
  have hFae : (fun z : Ω × Ω => condLogLen ξ Qψ W P K (fun j => X j z)) =ᵐ[P.prod P]
      fun z => P[L24.logLenPsi ξ Qψ W P n | (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))] z.1 :=
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hae1
  have hmem : MemLp (L24.logLenPsi ξ Qψ W P n) 2 P :=
    ((L24.psi_memLp_variance hW Qψ ξ).choose_spec.2 n).1
  have hcmem : MemLp (P[L24.logLenPsi ξ Qψ W P n | (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))]) 2 P := hmem.condExp one_le_two
  have hFmem : MemLp (fun z : Ω × Ω => condLogLen ξ Qψ W P K (fun j => X j z)) 2
      (P.prod P) :=
    (hcmem.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).ae_eq
      hFae.symm
  have hES := efron_stein_independent_blocks X X' hX hX' hind hlaw hf hFmem
  have hmF : AEMeasurable (P[L24.logLenPsi ξ Qψ W P n | (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))]) ((P.prod P).map Prod.fst) := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact hcmem.aestronglyMeasurable.aemeasurable
  have hvar : Var[fun z : Ω × Ω => condLogLen ξ Qψ W P K (fun j => X j z); P.prod P] =
      Var[P[L24.logLenPsi ξ Qψ W P n | (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))]; P] := by
    rw [variance_congr hFae,
      show (fun z : Ω × Ω => P[L24.logLenPsi ξ Qψ W P n | (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))] z.1) =
        P[L24.logLenPsi ξ Qψ W P n | (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))] ∘ Prod.fst from rfl,
      ← variance_map hmF measurable_fst.aemeasurable,
      Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hvar]
  exact hES

end SupercriticalLQGUniqueness.B2.DG20Conc
