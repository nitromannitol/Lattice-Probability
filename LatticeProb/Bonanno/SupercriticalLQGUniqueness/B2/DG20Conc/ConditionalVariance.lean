/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.ConditionalVariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.ConditionalLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.CoarseGaussian
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L24

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

private def crossPair (ξ : ℝ) (v : (T20B.dyD → ℝ) × (T20B.dyD → ℝ)) : ℝ :=
  T20B.fLen ξ (fun i : Fin 2 => if i = 0 then v.1 else v.2)

private lemma measurable_crossPair (ξ : ℝ) : Measurable (crossPair ξ) := by
  unfold crossPair
  apply (T20B.measurable_fLen ξ).comp
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i = 0
  · simp [hi, measurable_fst]
  · simp [hi, measurable_snd]

private lemma crossPair_eq (ξ : ℝ) {V Y : ℂ → ℝ}
    (hV : Continuous V) (hY : Continuous Y) :
    crossPair ξ (T20B.restrD V, T20B.restrD Y) =
      L23.logLen ξ (fun x => V x + Y x) := by
  apply T20B.fLen_eq (hV.add hY)
  intro c
  simp [Fin.sum_univ_two, T20B.restrD]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

 


theorem psi_condVar_le (hW : IsWhiteNoise P W) (Q : PsiParams)
    (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) :
    Var[L24.logLenPsi ξ Q W P n; P |
      (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
        (fun ω => T20B.restrD (fun x => psiMN Q W P K n x ω))] ≤ᵐ[P]
      fun _ => ξ ^ 2 * (K * Real.log 2) := by
  let X : Ω → T20B.dyD → ℝ :=
    fun ω => T20B.restrD (fun x => psiMN Q W P K n x ω)
  let Y : Ω → T20B.dyD → ℝ :=
    fun ω => T20B.restrD (fun x => psiMN Q W P 0 K x ω)
  let f : (T20B.dyD → ℝ) × (T20B.dyD → ℝ) → ℝ := crossPair ξ
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hK := isPsiVersion_psiMN (Q := Q) hW hKn
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hXm : Measurable X :=
    T20B.measurable_restrD.comp (measurable_pi_iff.2 hK.meas)
  have hYm : Measurable Y :=
    T20B.measurable_restrD.comp (measurable_pi_iff.2 h0K.meas)
  have hXY : IndepFun X Y P := by
    exact (T20B.indepFun_psiMN_scales hW Q hKn).symm.comp
      T20B.measurable_restrD T20B.measurable_restrD
  have hEq : (fun ω => f (X ω, Y ω)) =ᵐ[P] L24.logLenPsi ξ Q W P n := by
    filter_upwards [T20B.psiMN_add_ae hW Q hKn] with ω hω
    change crossPair ξ (T20B.restrD (fun x => psiMN Q W P K n x ω),
      T20B.restrD (fun x => psiMN Q W P 0 K x ω)) = _
    rw [crossPair_eq ξ (hK.cont ω) (h0K.cont ω)]
    simp only [L24.logLenPsi, L23.logLen, lenObs]
    rw [show (fun x => psiMN Q W P K n x ω + psiMN Q W P 0 K x ω) =
      (fun x => psiMN Q W P 0 n x ω) from funext fun x => (hω x).symm]
  have hL : MemLp (fun ω => f (X ω, Y ω)) 2 P := by
    exact (memLp_congr_ae hEq).2
      ((L24.psi_memLp_variance hW Q ξ).choose_spec.2 n).1
  have hvar : ∀ᵐ ω ∂P,
      MemLp (fun y => f (X ω, y)) 2 (P.map Y) ∧
        Var[fun y => f (X ω, y); P.map Y] ≤ ξ ^ 2 * (K * Real.log 2) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    let V : ℂ → ℝ := fun x => psiMN Q W P K n x ω
    let g : (T20B.dyD → ℝ) → ℝ := fun y => f (X ω, y)
    let H : Ω → ℝ := fun ω' => L23.logLen ξ
      (fun x => V x + psiMN Q W P 0 K x ω')
    have hgm : StronglyMeasurable g :=
      (measurable_crossPair ξ).comp
        (measurable_const.prodMk measurable_id) |>.stronglyMeasurable
    have hcomp : (fun ω' => g (Y ω')) = H := by
      funext ω'
      exact crossPair_eq ξ (hK.cont ω) (h0K.cont ω')
    have hc := coarse_psi_variance_fixed_background hW Q ξ K V (hK.cont ω)
    have hgL : MemLp g 2 (P.map Y) :=
      (memLp_map_measure_iff hgm.aestronglyMeasurable hYm.aemeasurable).2
        (by change MemLp (fun ω' => g (Y ω')) 2 P
            rw [hcomp]
            exact hc.1)
    have hgV : Var[g; P.map Y] ≤ ξ ^ 2 * (K * Real.log 2) := by
      rw [variance_map hgm.measurable.aemeasurable hYm.aemeasurable]
      change Var[fun ω' => g (Y ω'); P] ≤ _
      rw [hcomp]
      exact hc.2
    exact ⟨hgL, hgV⟩
  have h := condVar_le_of_indepFun hXm hYm.aemeasurable hXY
    (measurable_crossPair ξ).stronglyMeasurable hL hvar
  filter_upwards [h, condVar_congr_ae (m := (inferInstance : MeasurableSpace
    (T20B.dyD → ℝ)).comap X) hEq] with ω hb heq
  rw [← heq]
  exact hb

 


theorem psi_condExp_eq_coarse_integral (hW : IsWhiteNoise P W) (Q : PsiParams)
    (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) :
    P[L24.logLenPsi ξ Q W P n |
      (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
        (fun ω => T20B.restrD (fun x => psiMN Q W P K n x ω))] =ᵐ[P]
      fun ω => ∫ ω', L23.logLen ξ (fun x =>
        psiMN Q W P K n x ω + psiMN Q W P 0 K x ω') ∂P := by
  let X : Ω → T20B.dyD → ℝ :=
    fun ω => T20B.restrD (fun x => psiMN Q W P K n x ω)
  let Y : Ω → T20B.dyD → ℝ :=
    fun ω => T20B.restrD (fun x => psiMN Q W P 0 K x ω)
  let f : (T20B.dyD → ℝ) × (T20B.dyD → ℝ) → ℝ := crossPair ξ
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hK := isPsiVersion_psiMN (Q := Q) hW hKn
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hXm : Measurable X :=
    T20B.measurable_restrD.comp (measurable_pi_iff.2 hK.meas)
  have hYm : Measurable Y :=
    T20B.measurable_restrD.comp (measurable_pi_iff.2 h0K.meas)
  have hXY : IndepFun X Y P :=
    (T20B.indepFun_psiMN_scales hW Q hKn).symm.comp
      T20B.measurable_restrD T20B.measurable_restrD
  have hEq : (fun ω => f (X ω, Y ω)) =ᵐ[P] L24.logLenPsi ξ Q W P n := by
    filter_upwards [T20B.psiMN_add_ae hW Q hKn] with ω hω
    change crossPair ξ (T20B.restrD (fun x => psiMN Q W P K n x ω),
      T20B.restrD (fun x => psiMN Q W P 0 K x ω)) = _
    rw [crossPair_eq ξ (hK.cont ω) (h0K.cont ω)]
    simp only [L24.logLenPsi, L23.logLen, lenObs]
    rw [show (fun x => psiMN Q W P K n x ω + psiMN Q W P 0 K x ω) =
      (fun x => psiMN Q W P 0 n x ω) from funext fun x => (hω x).symm]
  have hInt : Integrable (fun ω => f (X ω, Y ω)) P :=
    ((memLp_congr_ae hEq).2
      ((L24.psi_memLp_variance hW Q ξ).choose_spec.2 n).1).integrable one_le_two
  have hbase := condExp_eq_integral_of_indepFun hXm hYm.aemeasurable hXY
    (measurable_crossPair ξ).stronglyMeasurable hInt
  have hmap : ∀ ω, (∫ y, f (X ω, y) ∂(P.map Y)) =
      ∫ ω', L23.logLen ξ (fun x => psiMN Q W P K n x ω +
        psiMN Q W P 0 K x ω') ∂P := by
    intro ω
    have hsec : AEStronglyMeasurable (fun y => f (X ω, y)) (P.map Y) :=
      (((measurable_crossPair ξ).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    rw [integral_map hYm.aemeasurable hsec]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω' =>
      crossPair_eq ξ (hK.cont ω) (h0K.cont ω')
  calc
    P[L24.logLenPsi ξ Q W P n | _] =ᵐ[P]
        P[fun ω => f (X ω, Y ω) | _] := condExp_congr_ae hEq.symm
    _ =ᵐ[P] (fun ω => ∫ y, f (X ω, y) ∂(P.map Y)) := hbase
    _ =ᵐ[P] (fun ω => ∫ ω', L23.logLen ξ (fun x =>
        psiMN Q W P K n x ω + psiMN Q W P 0 K x ω') ∂P) :=
      Filter.Eventually.of_forall hmap


end SupercriticalLQGUniqueness.B2.DG20Conc
