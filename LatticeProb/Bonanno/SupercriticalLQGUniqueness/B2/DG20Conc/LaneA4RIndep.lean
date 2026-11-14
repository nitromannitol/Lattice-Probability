/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RIndep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RInputs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep3

 











set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneA4R_supportedIn_mono {A A' : Set (ℝ × ℂ)} (h : A ⊆ A') {f : WNSpace}
    (hf : SupportedIn A f) : SupportedIn A' f :=
  ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.mpr h) hf

theorem laneA4R_blockKernelL2_univ (Q : PsiParams) {a : ℝ} (ha : 0 < a) (b : ℝ) (x : ℂ) :
    Q.blockKernelL2 a b univ x = Q.psiKernelL2 a b x := by
  refine Lp.ext ?_
  filter_upwards [Q.coeFn_blockKernelL2 a b ha MeasurableSet.univ x,
    Q.coeFn_psiKernelL2 a b ha x] with p h1 h2
  rw [h1, h2]
  simp [PsiParams.blockKernel]

 
theorem laneFineStar_indep_coarse_proved.{u} : LaneFineStarIndepCoarse.{u} := by
  intro Ω _ P W hW Q K n hKn
  have := hW.isProbabilityMeasure
  set a : ℝ := (2 : ℝ)⁻¹ ^ n with ha_def
  set b : ℝ := (2 : ℝ)⁻¹ ^ K with hb_def
  set c : ℝ := (2 : ℝ)⁻¹ ^ 0 with hc_def
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  set Ac : Set (ℝ × ℂ) := Icc (b ^ 2) (c ^ 2) ×ˢ univ with hAc
  set Af : Set (ℝ × ℂ) := Ico (a ^ 2) (b ^ 2) ×ˢ univ with hAf
  have hdisj : Disjoint Ac Af := by
    rw [hAc, hAf, Set.disjoint_prod]
    left
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h1.1 (not_le.mpr h2.2)
  have hI := hW.indepFun_of_disjoint hdisj
  
  let G : ({f // SupportedIn Ac f} → ℝ) → Bool × ℂ → ℝ := fun F t =>
    match t with
    | (true, x) => Real.sqrt Real.pi * F ⟨phiKernelL2 b c x, supportedIn_phiKernelL2' hb x⟩
    | (false, x) => Real.sqrt Real.pi * F ⟨Q.psiKernelL2 b c x,
        Q.supportedIn_psiKernelL2 hb c x⟩
  let H : ({g // SupportedIn Af g} → ℝ) → Option (ℤ × ℤ) × ℂ → ℝ := fun F s =>
    match s with
    | (none, x) => Real.sqrt Real.pi * F ⟨Q.blockKernelL2 a b univ x,
        Q.supportedIn_blockKernelL2 ha b MeasurableSet.univ x⟩
    | (some β, x) => Real.sqrt Real.pi * F ⟨Q.blockKernelL2 a b (T20B.hoBlock K β) x,
        laneA4R_supportedIn_mono (prod_mono subset_rfl (subset_univ _))
          (Q.supportedIn_blockKernelL2 ha b (T20B.measurableSet_hoBlock K β) x)⟩
  have hG : Measurable G := by
    refine measurable_pi_iff.mpr fun t => ?_
    rcases t with ⟨_ | _, x⟩
    · exact (measurable_pi_apply _).const_mul _
    · exact (measurable_pi_apply _).const_mul _
  have hH : Measurable H := by
    refine measurable_pi_iff.mpr fun s => ?_
    rcases s with ⟨_ | β, x⟩
    · exact (measurable_pi_apply _).const_mul _
    · exact (measurable_pi_apply _).const_mul _
  let Fc : Ω → {f // SupportedIn Ac f} → ℝ := fun ω f => W f ω
  let Ff : Ω → {g // SupportedIn Af g} → ℝ := fun ω g => W g ω
  let X : Bool × ℂ → Ω → ℝ := fun t ω => G (Fc ω) t
  let Z : Option (ℤ × ℤ) × ℂ → Ω → ℝ := fun s ω => H (Ff ω) s
  have hind : IndepFun (fun ω t => X t ω) (fun ω s => Z s ω) P := hI.comp hG hH
  
  let X' : Bool × ℂ → Ω → ℝ := fun t =>
    match t with
    | (true, x) => phiMN W P 0 K x
    | (false, x) => psiMN Q W P 0 K x
  let Z' : Option (ℤ × ℤ) × ℂ → Ω → ℝ := fun s =>
    match s with
    | (none, x) => psiMN Q W P K n x
    | (some β, x) => T20B.blkKn Q W P K n β x
  have hphi := isPhiVersion_phiMN (W := W) (P := P) hW (Nat.zero_le K)
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hKn' := isPsiVersion_psiMN (Q := Q) hW hKn
  have hB := fun β => T20B.blkKn_spec hW Q hKn β
  have hXm : ∀ t, Measurable (X t) := fun t => (measurable_pi_apply t).comp
    (hG.comp (measurable_pi_iff.mpr fun f => hW.measurable _))
  have hZm : ∀ s, Measurable (Z s) := fun s => (measurable_pi_apply s).comp
    (hH.comp (measurable_pi_iff.mpr fun f => hW.measurable _))
  have hX'm : ∀ t, Measurable (X' t) := by
    rintro ⟨_ | _, x⟩
    · exact h0K.meas x
    · exact hphi.meas x
  have hZ'm : ∀ s, Measurable (Z' s) := by
    rintro ⟨_ | β, x⟩
    · exact hKn'.meas x
    · exact (hB β).2.1 x
  have h1 : ∀ t, X' t =ᵐ[P] X t := by
    rintro ⟨_ | _, x⟩
    · exact h0K.ae_eq x
    · exact hphi.ae_eq x
  have h2 : ∀ s, Z' s =ᵐ[P] Z s := by
    rintro ⟨_ | β, x⟩
    · filter_upwards [hKn'.ae_eq x] with ω h
      show psiMN Q W P K n x ω = Real.sqrt Real.pi * W (Q.blockKernelL2 a b univ x) ω
      rw [h, laneA4R_blockKernelL2_univ Q ha b x]
      rfl
    · exact (hB β).2.2 x
  have hmod := indepFun_modification hXm hX'm hZm hZ'm h1 h2 hind
  have hInd : Indep (MeasurableSpace.comap (fun ω t => X' t ω) inferInstance)
      (MeasurableSpace.comap (fun ω s => Z' s ω) inferInstance) P := hmod
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hInd ?_) ?_
  · refine sup_le ?_ ?_
    · have hp : Measurable fun f : Bool × ℂ → ℝ => fun x => f (true, x) :=
        measurable_pi_iff.mpr fun x => measurable_pi_apply _
      exact (hp.comp (comap_measurable (fun ω t => X' t ω))).comap_le
    · have hp : Measurable fun f : Bool × ℂ → ℝ => fun x => f (false, x) :=
        measurable_pi_iff.mpr fun x => measurable_pi_apply _
      exact (hp.comp (comap_measurable (fun ω t => X' t ω))).comap_le
  · refine sup_le ?_ (iSup₂_le fun β _ => ?_)
    · have hp : Measurable fun f : Option (ℤ × ℤ) × ℂ → ℝ => fun x => f (none, x) :=
        measurable_pi_iff.mpr fun x => measurable_pi_apply _
      exact (hp.comp (comap_measurable (fun ω s => Z' s ω))).comap_le
    · have hp : Measurable fun f : Option (ℤ × ℤ) × ℂ → ℝ => fun x => f (some β, x) :=
        measurable_pi_iff.mpr fun x => measurable_pi_apply _
      exact (hp.comp (comap_measurable (fun ω s => Z' s ω))).comap_le

end SupercriticalLQGUniqueness.B2.DG20Conc
