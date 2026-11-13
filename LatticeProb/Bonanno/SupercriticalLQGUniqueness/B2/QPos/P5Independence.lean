/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5Independence at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5Nested
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFDistance

 













set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

 
def AnnDet {m : ℕ} (B : Set (EuclideanSpace ℝ (DGFFSite m))) : Prop :=
  ∀ g g' : EuclideanSpace ℝ (DGFFSite m),
    (∀ c, inDGFFAnnulus m c → g c = g' c) → (g ∈ B ↔ g' ∈ B)

theorem AnnDet.compl {m : ℕ} {B : Set (EuclideanSpace ℝ (DGFFSite m))} (hB : AnnDet B) :
    AnnDet Bᶜ := fun g g' h => not_congr (hB g g' h)

 
def ExtDet {n : ℕ} (S : Finset (DGFFSite n)) (E : Set (EuclideanSpace ℝ (DGFFSite n))) : Prop :=
  ∀ h h' : EuclideanSpace ℝ (DGFFSite n), (∀ c, c ∉ S → h c = h' c) → (h ∈ E ↔ h' ∈ E)

 

theorem extDet_preimage {n : ℕ} (S : Finset (DGFFSite n)) {E : Set (EuclideanSpace ℝ (DGFFSite n))}
    (hE : ExtDet S E) (hm : MeasurableSet E) :
    ∃ T : Set (EuclideanSpace ℝ {c : DGFFSite n // c ∉ S}), MeasurableSet T ∧
      E = (fun h => (boxResidualField n (boxInnerOuterEquiv n S) h).2) ⁻¹' T := by
  set sp := boxSplitFieldEquiv n (boxInnerOuterEquiv n S)
  set g0 : EuclideanSpace ℝ {c : DGFFSite n // c ∉ S} → EuclideanSpace ℝ (DGFFSite n) :=
    fun g => sp.symm (0, g)
  have hg0 : Continuous g0 := sp.symm.continuous.comp (continuous_const.prodMk continuous_id)
  refine ⟨g0 ⁻¹' E, hg0.measurable hm, ?_⟩
  ext h
  simp only [Set.mem_preimage]
  apply hE
  intro c hc
  have h1 : (sp (g0 ((boxResidualField n (boxInnerOuterEquiv n S) h).2))).2 =
      (boxResidualField n (boxInnerOuterEquiv n S) h).2 := by
    simp [g0]
  have h2 := congrArg (fun v : EuclideanSpace ℝ {c : DGFFSite n // c ∉ S} => v ⟨c, hc⟩) h1
  simp only at h2
  rw [boxSplitField_apply_right, boxResidualField_apply_right, boxSplitField_apply_right] at h2
  exact h2.symm
theorem ExtDet.inter {n : ℕ} {S : Finset (DGFFSite n)} {E F : Set (EuclideanSpace ℝ (DGFFSite n))}
    (hE : ExtDet S E) (hF : ExtDet S F) : ExtDet S (E ∩ F) := fun h h' hh =>
  and_congr (hE h h' hh) (hF h h' hh)


theorem annDet_extDet {n : ℕ} {z : ℤ × ℤ} {j k : ℕ} (hjk : j < k) (hkn : k ≤ n)
    (hj : GoodScale n z j) {B : Set (EuclideanSpace ℝ (DGFFSite (n - j)))} (hB : AnnDet B) :
    ExtDet (scaleSites n z k) (tresCLM hj ⁻¹' B) := by
  intro h h' hh
  simp only [Set.mem_preimage]
  apply hB
  intro c hc
  rw [tresCLM_apply, tresCLM_apply]
  
  have hout : shiftSite hj c ∉ scaleSites n z k := by
    intro hmem
    unfold scaleSites boxSites siteFilter at hmem
    rw [Finset.mem_filter, mem_sqBox, shiftSite_val] at hmem
    obtain ⟨-, h1, h2⟩ := hmem
    simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_right] at h1 h2
    have hr := hc.1
    unfold dgffInnerRadius latticeRadius at hr
    have hpow : (2 : ℤ) ^ (n - k) ≤ ((2 ^ (n - j - 1) : ℕ) : ℤ) := by
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hlt : max c.1.1.natAbs c.1.2.natAbs < 2 ^ (n - k) := by
      have e1 : (c.1.1.natAbs : ℤ) = |c.1.1| := Int.natCast_natAbs _
      have e2 : (c.1.2.natAbs : ℤ) = |c.1.2| := Int.natCast_natAbs _
      have : (max c.1.1.natAbs c.1.2.natAbs : ℤ) < 2 ^ (n - k) := by
        push_cast
        exact max_lt h1 h2
      exact_mod_cast this
    have : 2 ^ (n - k) ≤ 2 ^ (n - j - 1) := by exact_mod_cast hpow
    omega
  have hval : h (shiftSite hj c) = h' (shiftSite hj c) := hh _ hout
  
  have hmemj := shiftSite_mem hj c
  obtain ⟨α, hα0, hα⟩ := hfun_eq_sum n (scaleSites n z j) hmemj
  have hSS : scaleSites n z k ⊆ scaleSites n z j := scaleSites_anti hjk.le hkn
  have hharm : hfun n (scaleSites n z j) h (shiftSite hj c) =
      hfun n (scaleSites n z j) h' (shiftSite hj c) := by
    rw [hα, hα]
    apply Finset.sum_congr rfl
    intro c' _
    by_cases hc' : c' ∈ scaleSites n z j
    · rw [hα0 c' hc', zero_mul, zero_mul]
    · rw [hh c' (fun h'' => hc' (hSS h''))]
  have e1 := hfun_add_resid n (scaleSites n z j) h (shiftSite hj c)
  have e2 := hfun_add_resid n (scaleSites n z j) h' (shiftSite hj c)
  linarith

 
def scaleEvent (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ) (hW : ∀ k ∈ W, GoodScale n z k)
    (B : ∀ k : ℕ, Set (EuclideanSpace ℝ (DGFFSite (n - k)))) (k : ℕ) :
    Set (EuclideanSpace ℝ (DGFFSite n)) :=
  if hk : k ∈ W then tresCLM (hW k hk) ⁻¹' B k else Set.univ

 
theorem nested_iIndepSet (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ) (hW : ∀ k ∈ W, GoodScale n z k)
    (B : ∀ k : ℕ, Set (EuclideanSpace ℝ (DGFFSite (n - k))))
    (hBm : ∀ k ∈ W, MeasurableSet (B k)) (hBd : ∀ k ∈ W, AnnDet (B k)) :
    iIndepSet (scaleEvent n z W hW B) (boxDGFF n) := by
  classical
  have hmeas : ∀ k, MeasurableSet (scaleEvent n z W hW B k) := by
    intro k
    unfold scaleEvent
    split_ifs with hk
    · exact (tresCLM (hW k hk)).continuous.measurable (hBm k hk)
    · exact MeasurableSet.univ
  rw [iIndepSet_iff_meas_biInter hmeas]
  intro s
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert k s hlt ih =>
    rw [Finset.prod_insert (fun hk => lt_irrefl k (hlt k hk))]
    rw [Finset.set_biInter_insert]
    by_cases hk : k ∈ W
    · have hkW := hW k hk
      
      have hEk : scaleEvent n z W hW B k =
          (fun h => (boxResidualField n (boxInnerOuterEquiv n (scaleSites n z k)) h).1) ⁻¹'
            ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (scaleEquiv hkW)) ⁻¹' B k) := by
        unfold scaleEvent
        rw [dif_pos hk]
        rfl
      
      have hdet : ExtDet (scaleSites n z k) (⋂ j ∈ s, scaleEvent n z W hW B j) := by
        intro h h' hh
        simp only [Set.mem_iInter]
        apply forall_congr'
        intro j
        apply forall_congr'
        intro hj
        unfold scaleEvent
        split_ifs with hjW
        · exact annDet_extDet (hlt j hj) (by have := hkW.1; omega) (hW j hjW) (hBd j hjW) h h' hh
        · simp
      have hmint : MeasurableSet (⋂ j ∈ s, scaleEvent n z W hW B j) :=
        MeasurableSet.biInter s.countable_toSet fun j _ => hmeas j
      obtain ⟨T, hTm, hT⟩ := extDet_preimage (scaleSites n z k) hdet hmint
      have hind := box_inner_outer_residual_indep n (scaleSites n z k)
      have hBm' : MeasurableSet ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (scaleEquiv hkW)) ⁻¹' B k) :=
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (scaleEquiv hkW)).continuous.measurable (hBm k hk)
      rw [hT, hEk, hind.measure_inter_preimage_eq_mul _ _ hBm' hTm, ← hEk, ← hT, ih]
    · have hEk : scaleEvent n z W hW B k = Set.univ := by
        unfold scaleEvent; rw [dif_neg hk]
      rw [hEk, Set.univ_inter, measure_univ, one_mul, ih]

end SupercriticalLQGUniqueness.B2.QPos.P5
