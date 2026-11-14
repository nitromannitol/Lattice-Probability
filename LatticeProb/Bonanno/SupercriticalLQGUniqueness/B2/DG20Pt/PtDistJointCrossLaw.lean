/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistJointCrossLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistJointLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.OpenCrossingLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw

 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem map_pair_pathC_eq {Ω Ω₂ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂}
    {Y : Sum ℂ ℂ → Ω → ℝ} {Y₂ : Sum ℂ ℂ → Ω₂ → ℝ}
    (hc₁ : ∀ ω, Continuous fun x => Y (.inl x) ω)
    (hc₂ : ∀ ω, Continuous fun x => Y (.inr x) ω)
    (hc₁' : ∀ ω, Continuous fun x => Y₂ (.inl x) ω)
    (hc₂' : ∀ ω, Continuous fun x => Y₂ (.inr x) ω)
    (hm : ∀ i, Measurable (Y i))
    (hm' : ∀ i, Measurable (Y₂ i))
    (hlaw : P.map (fun ω i => Y i ω) = P₂.map (fun ω i => Y₂ i ω)) :
    P.map (fun ω => (LQGMetric.DFGPS.pathC (fun x => Y (.inl x)) hc₁ ω,
        LQGMetric.DFGPS.pathC (fun x => Y (.inr x)) hc₂ ω)) =
      P₂.map (fun ω => (LQGMetric.DFGPS.pathC (fun x => Y₂ (.inl x)) hc₁' ω,
        LQGMetric.DFGPS.pathC (fun x => Y₂ (.inr x)) hc₂' ω)) := by
  obtain ⟨qseq, hq⟩ := TopologicalSpace.exists_dense_seq ℂ
  let J : C(ℂ, ℝ) × C(ℂ, ℝ) → (Sum ℕ ℕ → ℝ) := fun p i =>
    match i with
    | .inl n => p.1 (qseq n)
    | .inr n => p.2 (qseq n)
  have hJc : Continuous J := by
    apply continuous_pi
    intro i
    cases i with
    | inl n => exact (continuous_eval_const (qseq n)).comp continuous_fst
    | inr n => exact (continuous_eval_const (qseq n)).comp continuous_snd
  have hJi : Function.Injective J := by
    intro p q h
    apply Prod.ext
    · apply ContinuousMap.ext
      intro x
      exact congrFun (Continuous.ext_on hq p.1.continuous q.1.continuous
        (by rintro _ ⟨n, rfl⟩; exact congrFun h (.inl n))) x
    · apply ContinuousMap.ext
      intro x
      exact congrFun (Continuous.ext_on hq p.2.continuous q.2.continuous
        (by rintro _ ⟨n, rfl⟩; exact congrFun h (.inr n))) x
  have hJ : MeasurableEmbedding J := hJc.measurableEmbedding hJi
  let R : (Sum ℂ ℂ → ℝ) → (Sum ℕ ℕ → ℝ) := fun f i =>
    match i with
    | .inl n => f (.inl (qseq n))
    | .inr n => f (.inr (qseq n))
  have hRm : Measurable R := by
    apply measurable_pi_iff.2
    intro i
    cases i with
    | inl n => exact measurable_pi_apply (Sum.inl (qseq n))
    | inr n => exact measurable_pi_apply (Sum.inr (qseq n))
  have hp : Measurable (fun ω => (LQGMetric.DFGPS.pathC (fun x => Y (.inl x)) hc₁ ω,
      LQGMetric.DFGPS.pathC (fun x => Y (.inr x)) hc₂ ω)) :=
    (LQGMetric.DFGPS.measurable_pathC hc₁ (fun x => hm (.inl x))).prodMk
      (LQGMetric.DFGPS.measurable_pathC hc₂ (fun x => hm (.inr x)))
  have hp' : Measurable (fun ω => (LQGMetric.DFGPS.pathC (fun x => Y₂ (.inl x)) hc₁' ω,
      LQGMetric.DFGPS.pathC (fun x => Y₂ (.inr x)) hc₂' ω)) :=
    (LQGMetric.DFGPS.measurable_pathC hc₁' (fun x => hm' (.inl x))).prodMk
      (LQGMetric.DFGPS.measurable_pathC hc₂' (fun x => hm' (.inr x)))
  have hmap : (P.map (fun ω => (LQGMetric.DFGPS.pathC (fun x => Y (.inl x)) hc₁ ω,
      LQGMetric.DFGPS.pathC (fun x => Y (.inr x)) hc₂ ω))).map J =
      (P₂.map (fun ω => (LQGMetric.DFGPS.pathC (fun x => Y₂ (.inl x)) hc₁' ω,
        LQGMetric.DFGPS.pathC (fun x => Y₂ (.inr x)) hc₂' ω))).map J := by
    rw [Measure.map_map hJ.measurable hp, Measure.map_map hJ.measurable hp']
    have hraw := congrArg (fun μ : Measure (Sum ℂ ℂ → ℝ) => μ.map R) hlaw
    rw [Measure.map_map hRm (measurable_pi_iff.2 hm),
      Measure.map_map hRm (measurable_pi_iff.2 hm')] at hraw
    convert hraw using 1
    · congr 1
    · congr 1
  ext s hs
  have he := congrArg (fun μ : Measure (Sum ℕ ℕ → ℝ) => μ (J '' s)) hmap
  rwa [hJ.map_apply, hJ.map_apply, preimage_image_eq _ hJi] at he

 



theorem measure_crossLenIn_coarse_eq {Ω Ω₂ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂}
    {Y : Sum ℂ ℂ → Ω → ℝ} {Y₂ : Sum ℂ ℂ → Ω₂ → ℝ}
    (hc₁ : ∀ ω, Continuous fun x => Y (.inl x) ω)
    (hc₂ : ∀ ω, Continuous fun x => Y (.inr x) ω)
    (hc₁' : ∀ ω, Continuous fun x => Y₂ (.inl x) ω)
    (hc₂' : ∀ ω, Continuous fun x => Y₂ (.inr x) ω)
    (hm : ∀ i, Measurable (Y i))
    (hm' : ∀ i, Measurable (Y₂ i))
    (hlaw : P.map (fun ω i => Y i ω) = P₂.map (fun ω i => Y₂ i ω))
    (ξ : ℝ) (U : Opens ℂ) (A B : Set ℂ) (x : ℂ)
    {S : Set (ℝ≥0∞ × ℝ)} (hS : MeasurableSet S) :
    P {ω | (crossLenIn ξ (fun z => Y (.inl z) ω) U A B,
      Y (.inr x) ω) ∈ S} =
    P₂ {ω | (crossLenIn ξ (fun z => Y₂ (.inl z) ω) U A B,
      Y₂ (.inr x) ω) ∈ S} := by
  let E : Set (C(ℂ, ℝ) × C(ℂ, ℝ)) := {p |
    (crossLenIn ξ (fun z => p.1 z) U A B, p.2 x) ∈ S}
  have hCross : Measurable (fun p : C(ℂ, ℝ) × C(ℂ, ℝ) =>
      crossLenIn ξ (fun z => p.1 z) U A B) :=
    measurable_crossLenIn_open ξ U A B
      (fun z (p : C(ℂ, ℝ) × C(ℂ, ℝ)) => p.1 z)
      (fun p => p.1.continuous)
      (fun z => (continuous_eval_const z).measurable.comp measurable_fst)
  have hE : MeasurableSet E :=
    (hCross.prodMk ((continuous_eval_const x).measurable.comp measurable_snd)) hS
  have hp : Measurable (fun ω => (LQGMetric.DFGPS.pathC (fun z => Y (.inl z)) hc₁ ω,
      LQGMetric.DFGPS.pathC (fun z => Y (.inr z)) hc₂ ω)) :=
    (LQGMetric.DFGPS.measurable_pathC hc₁ (fun z => hm (.inl z))).prodMk
      (LQGMetric.DFGPS.measurable_pathC hc₂ (fun z => hm (.inr z)))
  have hp' : Measurable (fun ω => (LQGMetric.DFGPS.pathC (fun z => Y₂ (.inl z)) hc₁' ω,
      LQGMetric.DFGPS.pathC (fun z => Y₂ (.inr z)) hc₂' ω)) :=
    (LQGMetric.DFGPS.measurable_pathC hc₁' (fun z => hm' (.inl z))).prodMk
      (LQGMetric.DFGPS.measurable_pathC hc₂' (fun z => hm' (.inr z)))
  have hpathlaw := map_pair_pathC_eq hc₁ hc₂ hc₁' hc₂' hm hm' hlaw
  change P ((fun ω => (LQGMetric.DFGPS.pathC (fun z => Y (.inl z)) hc₁ ω,
      LQGMetric.DFGPS.pathC (fun z => Y (.inr z)) hc₂ ω)) ⁻¹' E) =
    P₂ ((fun ω => (LQGMetric.DFGPS.pathC (fun z => Y₂ (.inl z)) hc₁' ω,
      LQGMetric.DFGPS.pathC (fun z => Y₂ (.inr z)) hc₂' ω)) ⁻¹' E)
  rw [← Measure.map_apply hp hE, ← Measure.map_apply hp' hE, hpathlaw]

 



theorem measure_crossLenIn_phiMN_coarse_motion {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (n k : ℕ) (hkn : k ≤ n) (ξ : ℝ)
    (U : Opens ℂ) (A B : Set ℂ) (x : ℂ)
    (u : Circle) (c : ℂ) {S : Set (ℝ≥0∞ × ℝ)}
    (hS : MeasurableSet S) :
    P {ω | (crossLenIn ξ (fun z => phiMN W P 0 n z ω)
        ((fun z => (u : ℂ) * z + c) '' U)
        ((fun z => (u : ℂ) * z + c) '' A)
        ((fun z => (u : ℂ) * z + c) '' B),
      phiMN W P 0 k ((u : ℂ) * x + c) ω) ∈ S} =
    P {ω | (crossLenIn ξ (fun z => phiMN W P 0 n z ω) U A B,
      phiMN W P 0 k x ω) ∈ S} := by
  have hn := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hk := isPhiVersion_phiMN hW (Nat.zero_le k)
  simp_rw [crossLenIn_image_motion]
  exact measure_crossLenIn_coarse_eq
    (Y := fun i ω => match i with
      | .inl z => phiMN W P 0 n ((u : ℂ) * z + c) ω
      | .inr z => phiMN W P 0 k ((u : ℂ) * z + c) ω)
    (Y₂ := fun i ω => match i with
      | .inl z => phiMN W P 0 n z ω
      | .inr z => phiMN W P 0 k z ω)
    (fun ω => (hn.cont ω).comp ((continuous_const.mul continuous_id).add continuous_const))
    (fun ω => (hk.cont ω).comp ((continuous_const.mul continuous_id).add continuous_const))
    hn.cont hk.cont
    (by intro i; cases i with | inl z => exact hn.meas _ | inr z => exact hk.meas _)
    (by intro i; cases i with | inl z => exact hn.meas z | inr z => exact hk.meas z)
    (map_phiMN_pair_motion hW n k hkn u c)
    ξ U A B x hS

 

theorem measure_crossLenIn_phiMN_coarse_upper_motion {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (n k : ℕ) (hkn : k ≤ n) (ξ a : ℝ)
    (U : Opens ℂ) (A B : Set ℂ) (x : ℂ)
    (u : Circle) (c : ℂ) :
    P {ω | ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k ((u : ℂ) * x + c) ω)) *
        ENNReal.ofReal a <
        crossLenIn ξ (fun z => phiMN W P 0 n z ω)
          ((fun z => (u : ℂ) * z + c) '' U)
          ((fun z => (u : ℂ) * z + c) '' A)
          ((fun z => (u : ℂ) * z + c) '' B)} =
    P {ω | ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k x ω)) *
        ENNReal.ofReal a <
        crossLenIn ξ (fun z => phiMN W P 0 n z ω) U A B} := by
  let S : Set (ℝ≥0∞ × ℝ) := {p |
    ENNReal.ofReal (Real.exp (ξ * p.2)) * ENNReal.ofReal a < p.1}
  have hS : MeasurableSet S := by
    exact measurableSet_lt
      ((ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp (measurable_const.mul measurable_snd))).mul
        measurable_const) measurable_fst
  simpa only [S, Set.mem_ofPred_eq] using
    measure_crossLenIn_phiMN_coarse_motion hW n k hkn ξ U A B x u c hS

end SupercriticalLQGUniqueness.B2.DG20Pt
