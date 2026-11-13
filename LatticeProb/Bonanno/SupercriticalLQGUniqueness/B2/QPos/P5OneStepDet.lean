/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5OneStepDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5BadScales
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5ScaleCounting

 















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

instance (n : ℕ) (z : ℤ × ℤ) (k : ℕ) : Decidable (GoodScale n z k) := by
  unfold GoodScale; infer_instance

 
def goodCentres (n K : ℕ) : Finset (ℤ × ℤ) :=
  (dgffGridCenters n K).filter fun z => ∀ k ∈ scaleWindow K, GoodScale n z k

 
def distBad (n : ℕ) (z : ℤ × ℤ) (K : ℕ) (ξ R : ℝ) : Set (EuclideanSpace ℝ (DGFFSite n)) :=
  if hz : ∀ k ∈ scaleWindow K, GoodScale n z k then
    {h | ∃ T : Finset ℕ, T ⊆ scaleWindow K ∧ T.card = K / 8 ∧
      ∀ k ∈ T, h ∈ scaleEvent n z (scaleWindow K) hz (fun k => (distEvent (n - k) ξ R)ᶜ) k}
  else ∅

 
def goodEvent (n K : ℕ) (ξ R A C : ℝ) : Set (EuclideanSpace ℝ (DGFFSite n)) :=
  highCircuit n A ∩ (⋂ z ∈ goodCentres n K, (bad35 n z K A C)ᶜ) ∩
    (⋂ z ∈ goodCentres n K, (distBad n z K ξ R)ᶜ)

 
theorem pathCost_ofFn_shift (m : ℕ) (ξ : ℝ) (g : EuclideanSpace ℝ (DGFFSite m))
    (f : ℕ → DGFFSite m) (s t : ℕ) (hst : s ≤ t) :
    dgffPathCost m ξ g (List.ofFn fun i : Fin (t - s + 1) => f (s + i)) =
      ∑ i ∈ Icc s t, Real.exp (ξ * g (f i)) := by
  unfold dgffPathCost inclusivePathCost
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => Real.exp (ξ * g (f (s + j)))) (t - s + 1)]
  have hI : Icc s t = (range (t - s + 1)).image (fun j => s + j) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hi; exact ⟨i - s, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [hI, Finset.sum_image (fun _ _ _ _ h => by omega)]

 
theorem goodEvent_sub (n K : ℕ) (hK32 : 32 ∣ K) (hK : 32 ≤ K) (hn : K + 3 ≤ n)
    (ξ R A C : ℝ) (hξ : 0 < ξ) (hR : 0 < R) :
    goodEvent n K ξ R A C ⊆ distEvent n ξ ((K / 4 : ℝ) * Real.exp (-ξ * C) * R) := by
  classical
  intro h hh
  obtain ⟨⟨hhigh, hbad⟩, hdist⟩ := hh
  obtain ⟨p₀, hp₀, hp₀A⟩ := hhigh
  set W := scaleWindow K
  have hWcard : W.card = K / 2 := scaleWindow_card K (by omega) (by omega)
  show (K / 4 : ℝ) * Real.exp (-ξ * C) * R ≤ dgffAnnulusDistance n ξ h
  haveI := dgff_annulusPath_nonempty n (by omega)
  apply le_ciInf
  rintro ⟨γ, hγ⟩
  show (K / 4 : ℝ) * Real.exp (-ξ * C) * R ≤ dgffPathCost n ξ h γ
  
  obtain ⟨v, hvp₀, hvγ⟩ := hp₀.2.2.2.2 γ hγ
  have hvA : inDGFFAnnulus n v := hγ.2.1 v hvγ
  obtain ⟨z, hzG, hz⟩ := grid_round n K hn v
  have hzgood : ∀ k ∈ W, GoodScale n z k := by
    intro k hk
    have hkb := window_le hk
    exact goodScale_of_near n K k (by omega) hn (by omega) (by omega) hvA.2 hz
  have hzmem : z ∈ goodCentres n K := Finset.mem_filter.mpr ⟨hzG, hzgood⟩
  have hnb : h ∉ bad35 n z K A C := by
    have := Set.mem_iInter₂.mp hbad z hzmem
    exact this
  have hnd : h ∉ distBad n z K ξ R := by
    have := Set.mem_iInter₂.mp hdist z hzmem
    exact this
  
  set HB := W.filter fun k => ∃ c ∈ annSites n z k, hfun n (scaleSites n z k) h c < -C
  have hHB : HB.card < K / 8 := by
    by_contra hge
    push_neg at hge
    exact hnb ⟨hge, p₀, hp₀, hp₀A, v, hvp₀, hz⟩
  set HG := W.filter fun k => ¬ ∃ c ∈ annSites n z k, hfun n (scaleSites n z k) h c < -C
  have hHGc : HG.card + HB.card = W.card := by
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _
  
  set DF := W.filter fun k => h ∈ scaleEvent n z W hzgood (fun k => (distEvent (n - k) ξ R)ᶜ) k
  have hDF : DF.card < K / 8 := by
    by_contra hge
    push_neg at hge
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hge
    apply hnd
    unfold distBad
    rw [dif_pos hzgood]
    exact ⟨T, hT.trans (Finset.filter_subset _ _), hTc,
      fun k hk => (Finset.mem_filter.mp (hT hk)).2⟩
  set DG := W.filter fun k => h ∉ scaleEvent n z W hzgood (fun k => (distEvent (n - k) ξ R)ᶜ) k
  have hDGc : DG.card + DF.card = W.card := by
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _
  set VG := HG ∩ DG
  have hVG : K ≤ 4 * VG.card :=
    many_good_scales_intersection W HG DG K (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (by omega) (by omega) (by omega)
  
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hvγ
  have hlen : 0 < γ.length := by omega
  have hVGW : ∀ k ∈ VG, k ∈ W := fun k hk =>
    (Finset.mem_filter.mp (Finset.mem_inter.mp hk).1).1
  have hR' : 0 ≤ Real.exp (-ξ * C) * R := by positivity
  have hmain := multi_scale_cost z γ hγ.1 (fun c => Real.exp (ξ * h c))
    (fun c => (Real.exp_pos _).le) a ha VG
    (fun k hk => (hzgood k (hVGW k hk)).1) (Real.exp (-ξ * C) * R)
    (fun k hk => by
      have hkb := window_le (hVGW k hk)
      unfold dgffInnerRadius
      exact hz.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (by
      rcases far_endpoint n (by omega) z hγ hlen with hf | hf
      · left
        intro k hk
        have hkb := window_le (hVGW k hk)
        have := dgffOuterRadius_lt_box (n - k)
        have : 2 ^ (n - k) ≤ 2 ^ (n - 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · right
        intro k hk
        have hkb := window_le (hVGW k hk)
        have := dgffOuterRadius_lt_box (n - k)
        have : 2 ^ (n - k) ≤ 2 ^ (n - 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
    (by
      intro k hk q s t hst hann hcross
      have hkW := hVGW k hk
      have hkHG := (Finset.mem_inter.mp hk).1
      have hkDG := (Finset.mem_inter.mp hk).2
      have hharm : ∀ c ∈ annSites n z k, -C ≤ hfun n (scaleSites n z k) h c := by
        intro c hc
        by_contra hlt
        push_neg at hlt
        exact (Finset.mem_filter.mp hkHG).2 ⟨c, hc, hlt⟩
      have hdk : R ≤ dgffAnnulusDistance (n - k) ξ (tresCLM (hzgood k hkW) h) := by
        have := (Finset.mem_filter.mp hkDG).2
        unfold scaleEvent at this
        rw [dif_pos hkW] at this
        simp only [Set.mem_preimage, Set.mem_compl_iff, not_not] at this
        exact this
      
      have hcost : dgffAnnulusDistance (n - k) ξ (tresCLM (hzgood k hkW) h) ≤
          ∑ i ∈ Icc s t, Real.exp (ξ * resid n (scaleSites n z k) h (q i)) := by
        have hle : dgffAnnulusDistance (n - k) ξ (tresCLM (hzgood k hkW) h) ≤
            dgffPathCost (n - k) ξ (tresCLM (hzgood k hkW) h)
              (List.ofFn fun i : Fin (t - s + 1) => unshiftOr n z k (q (s + i))) := by
          have hbelow : BddBelow (Set.range
              (fun p : {p : List (DGFFSite (n - k)) // IsDGFFAnnulusPath (n - k) p} =>
                dgffPathCost (n - k) ξ (tresCLM (hzgood k hkW) h) p.1)) := by
            refine ⟨0, ?_⟩
            rintro y ⟨p, rfl⟩
            exact inclusivePathCost_nonneg _ (fun c => (Real.exp_pos _).le) p.1
          exact ciInf_le hbelow ⟨_, hcross⟩
        rw [pathCost_ofFn_shift _ ξ _ (fun i => unshiftOr n z k (q i)) s t hst] at hle
        refine hle.trans (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Icc] at hi
        rw [tres_unshiftOr (hzgood k hkW) (hann i hi.1 hi.2)]
      have hpoint : ∀ i ∈ Icc s t, Real.exp (-ξ * C) *
          Real.exp (ξ * resid n (scaleSites n z k) h (q i)) ≤ Real.exp (ξ * h (q i)) := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have hqa : q i ∈ annSites n z k :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hann i hi.1 hi.2⟩
        have h1 := hharm _ hqa
        have h2 := hfun_add_resid n (scaleSites n z k) h (q i)
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc Real.exp (-ξ * C) * R
          ≤ Real.exp (-ξ * C) * ∑ i ∈ Icc s t,
              Real.exp (ξ * resid n (scaleSites n z k) h (q i)) := by
            gcongr; exact hdk.trans hcost
        _ = ∑ i ∈ Icc s t, Real.exp (-ξ * C) *
              Real.exp (ξ * resid n (scaleSites n z k) h (q i)) := by rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ Icc s t, Real.exp (ξ * h (q i)) := Finset.sum_le_sum hpoint)
  have hcostdef : dgffPathCost n ξ h γ = (γ.map fun c => Real.exp (ξ * h c)).sum := rfl
  rw [hcostdef]
  refine le_trans ?_ hmain
  have hK4 : (K / 4 : ℝ) ≤ VG.card := by
    have : (K : ℝ) ≤ 4 * VG.card := by exact_mod_cast hVG
    linarith
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right hK4 hR'

end SupercriticalLQGUniqueness.B2.QPos.P5
