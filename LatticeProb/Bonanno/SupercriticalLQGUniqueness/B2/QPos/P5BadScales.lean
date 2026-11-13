/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5BadScales at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5Events
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5IndependentTail

 



















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

 
def scaleWindow (K : ℕ) : Finset ℕ := Finset.Icc (K / 2) (K - 1)

theorem scaleWindow_card (K : ℕ) (hK : 2 ∣ K) (hK0 : 0 < K) : (scaleWindow K).card = K / 2 := by
  unfold scaleWindow
  rw [Nat.card_Icc]
  omega

 
def annSites (n : ℕ) (z : ℤ × ℤ) (k : ℕ) : Finset (DGFFSite n) :=
  Finset.univ.filter (AnnAt n z k)

theorem annSites_inReg {n : ℕ} {z : ℤ × ℤ} {k : ℕ} {c : DGFFSite n} (hc : c ∈ annSites n z k) :
    inReg n z k c := by
  unfold annSites at hc
  rw [Finset.mem_filter] at hc
  have h := hc.2.2
  have hq := outer_le_three_quarters (n - k)
  have h1 := fst_natAbs_le_latticeRadius (c.1 - z)
  have h2 := snd_natAbs_le_latticeRadius (c.1 - z)
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
  have e1 : ((c.1.1 - z.1).natAbs : ℤ) = |c.1.1 - z.1| := Int.natCast_natAbs _
  have e2 : ((c.1.2 - z.2).natAbs : ℤ) = |c.1.2 - z.2| := Int.natCast_natAbs _
  have hpow : ((2 ^ (n - k) : ℕ) : ℤ) = (2 : ℤ) ^ (n - k) := by norm_cast
  constructor
  · have : (8 * (c.1.1 - z.1).natAbs : ℕ) ≤ 6 * 2 ^ (n - k) := by omega
    have h' : ((8 * (c.1.1 - z.1).natAbs : ℕ) : ℤ) ≤ ((6 * 2 ^ (n - k) : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast at h'
    exact h'
  · have : (8 * (c.1.2 - z.2).natAbs : ℕ) ≤ 6 * 2 ^ (n - k) := by omega
    have h' : ((8 * (c.1.2 - z.2).natAbs : ℕ) : ℤ) ≤ ((6 * 2 ^ (n - k) : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast at h'
    exact h'

theorem annSites_nonempty {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) :
    (annSites n z k).Nonempty := by
  obtain ⟨p, hp⟩ := dgff_annulusPath_nonempty (n - k) (by have := hk.1; omega)
  obtain ⟨-, hmem, a, -, ha, -, -, -⟩ := hp
  have haa : a ∈ p := List.mem_of_mem_head? ha
  refine ⟨shiftSite hk a, ?_⟩
  unfold annSites
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, annAt_shiftSite hk (hmem a haa)⟩

 
def bad35 (n : ℕ) (z : ℤ × ℤ) (K : ℕ) (A C : ℝ) : Set (EuclideanSpace ℝ (DGFFSite n)) :=
  {h | K / 8 ≤ ((scaleWindow K).filter fun k =>
        ∃ c ∈ annSites n z k, hfun n (scaleSites n z k) h c < -C).card ∧
      ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ (∀ c ∈ p, -A ≤ h c) ∧
        ∃ c ∈ p, latticeRadius (c.1 - z) ≤ 2 ^ (n - K - 2)}

theorem window_le {K k : ℕ} (hk : k ∈ scaleWindow K) : K / 2 ≤ k ∧ k ≤ K - 1 := by
  unfold scaleWindow at hk; rw [Finset.mem_Icc] at hk; exact hk

 
theorem bad_scales_prob (c : ℝ) (hc : 0 < c)
    (hcir : ∀ m : ℕ, 4 ≤ m → ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (1 - Real.exp (-c * u ^ 2)) ≤ boxDGFF m (highCircuit m u))
    (C₂ : ℝ)
    (hosc : ∀ (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ) (K : ℕ),
      W.Nonempty → W.card ≤ K → (∀ k ∈ W, GoodScale n z k) →
      ∀ A : ℕ → Finset (DGFFSite n), (∀ k ∈ W, (A k).Nonempty) →
      (∀ k ∈ W, ∀ c ∈ A k, inReg n z k c) →
      boxDGFF n {h | (1 / 8 : ℝ) * K / 4 < ((W.filter fun k => C₂ < osc n z k (A k) h).card : ℝ)} ≤
        ENNReal.ofReal ((1 / 8 : ℝ) ^ K))
    (K n : ℕ) (hK32 : 32 ∣ K) (hK : 32 ≤ K) (hn : K + 3 ≤ n) (z : ℤ × ℤ)
    (hz : ∀ k ∈ scaleWindow K, GoodScale n z k) (A u : ℝ) (hA : 0 < A) (hu : 0 < u) :
    boxDGFF n (bad35 n z K A (A + 1 + u + C₂)) ≤
      ((Nat.choose (K / 2) (K / 32) : ℝ≥0∞)) * (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ (K / 32) +
        ENNReal.ofReal ((1 / 8 : ℝ) ^ K) := by
  classical
  set W := scaleWindow K
  have hWcard : W.card = K / 2 := scaleWindow_card K (by omega) (by omega)
  have hWne : W.Nonempty := Finset.card_pos.mp (by omega)
  
  set B : ∀ k : ℕ, Set (EuclideanSpace ℝ (DGFFSite (n - k))) := fun k => (lowCircuit (n - k) u)ᶜ
  have hind := nested_iIndepSet n z W hz B (fun k _ => (lowCircuit_measurable _ u).compl)
    (fun k _ => (lowCircuit_annDet _ u).compl)
  set F1 : Set (EuclideanSpace ℝ (DGFFSite n)) := {h | ∃ T : Finset ℕ, T ⊆ W ∧
      T.card = K / 32 ∧ ∀ k ∈ T, h ∈ scaleEvent n z W hz B k}
  have hF1 : boxDGFF n F1 ≤ ((Nat.choose (K / 2) (K / 32) : ℝ≥0∞)) *
      (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ (K / 32) := by
    have := independent_many_failures_bound (boxDGFF n) (scaleEvent n z W hz B) hind W (K / 32)
      (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ?_
    · rw [hWcard] at this; exact this
    intro k hk
    unfold scaleEvent
    rw [dif_pos hk]
    have hk4 : 4 ≤ n - k := by have := (hz k hk).1; omega
    have hlow := lowCircuit_prob (hz k hk) u
    have hpre : tresCLM (hz k hk) ⁻¹' B k = (tresCLM (hz k hk) ⁻¹' lowCircuit (n - k) u)ᶜ := rfl
    rw [hpre, prob_compl_eq_one_sub ((tresCLM (hz k hk)).continuous.measurable
      (lowCircuit_measurable _ u)), hlow]
    have hge := hcir (n - k) hk4 u hu
    have hexp : Real.exp (-c * u ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc 1 - boxDGFF (n - k) (highCircuit (n - k) u)
        ≤ 1 - ENNReal.ofReal (1 - Real.exp (-c * u ^ 2)) := tsub_le_tsub_left hge 1
      _ = ENNReal.ofReal (Real.exp (-c * u ^ 2)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
        congr 1; ring
  set F2 : Set (EuclideanSpace ℝ (DGFFSite n)) := {h | (1 / 8 : ℝ) * K / 4 <
      ((W.filter fun k => C₂ < osc n z k (annSites n z k) h).card : ℝ)}
  have hF2 : boxDGFF n F2 ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ K) :=
    hosc n z W K hWne (by rw [hWcard]; omega) hz (annSites n z)
      (fun k hk => annSites_nonempty (hz k hk)) (fun k _ c hc => annSites_inReg hc)
  
  have hsub : bad35 n z K A (A + 1 + u + C₂) ⊆ F1 ∪ F2 := by
    intro h hh
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    obtain ⟨hcard, p, hp, hpA, c₀, hc₀p, hc₀⟩ := hh
    set HB := W.filter fun k => ∃ c ∈ annSites n z k, hfun n (scaleSites n z k) h c < -(A + 1 + u + C₂)
    set LF := W.filter fun k => h ∈ scaleEvent n z W hz B k
    set OB := W.filter fun k => C₂ < osc n z k (annSites n z k) h
    have hLF : LF.card < K / 32 := by
      by_contra hle
      push_neg at hle
      obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hle
      exact hn1 ⟨T, hT.trans (Finset.filter_subset _ _), hTc,
        fun k hk => (Finset.mem_filter.mp (hT hk)).2⟩
    have hOB : OB.card ≤ K / 32 := by
      by_contra hlt
      push_neg at hlt
      apply hn2
      show (1 / 8 : ℝ) * K / 4 < (OB.card : ℝ)
      have : (K / 32 : ℕ) + 1 ≤ OB.card := hlt
      have h32 : ((K / 32 : ℕ) : ℝ) = (K : ℝ) / 32 := by
        rw [Nat.cast_div hK32 (by norm_num)]; norm_num
      have : ((K / 32 : ℕ) : ℝ) + 1 ≤ (OB.card : ℝ) := by exact_mod_cast this
      rw [h32] at this
      linarith
    
    obtain ⟨k, hkHB, hkn⟩ : ∃ k ∈ HB, k ∉ LF ∪ OB := by
      by_contra hall
      push_neg at hall
      have hsubs : HB ⊆ LF ∪ OB := hall
      have := Finset.card_le_card hsubs
      have := Finset.card_union_le LF OB
      omega
    rw [Finset.mem_union, not_or] at hkn
    obtain ⟨hkLF, hkOB⟩ := hkn
    have hkW : k ∈ W := (Finset.mem_filter.mp hkHB).1
    obtain ⟨cb, hcb, hcbv⟩ := (Finset.mem_filter.mp hkHB).2
    have hlowk : h ∈ tresCLM (hz k hkW) ⁻¹' lowCircuit (n - k) u := by
      by_contra hl
      apply hkLF
      rw [Finset.mem_filter]
      refine ⟨hkW, ?_⟩
      unfold scaleEvent
      rw [dif_pos hkW]
      exact hl
    have hosck : osc n z k (annSites n z k) h ≤ C₂ := by
      by_contra hlt
      push_neg at hlt
      exact hkOB (Finset.mem_filter.mpr ⟨hkW, hlt⟩)
    obtain ⟨Pk, hPk, hPku⟩ := hlowk
    
    have hkb := window_le hkW
    have hnear : latticeRadius (c₀.1 - z) ≤ dgffInnerRadius (n - k) := by
      unfold dgffInnerRadius
      exact hc₀.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨c₁, hc₁p, hc₁⟩ := around_far_vertex n (by omega) hp z
    have hfar : dgffOuterRadius (n - k) ≤ latticeRadius (c₁.1 - z) := by
      have := dgffOuterRadius_lt_box (n - k)
      have : 2 ^ (n - k) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hc₀p
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hc₁p
    obtain ⟨c, hcp, hcann, hcP⟩ := crossing_meets_around (hz k hkW) p hp.2.1 ha hb hnear hfar hPk
    
    have hcA := hpA c hcp
    have hres : resid n (scaleSites n z k) h c ≤ u := by
      have := hPku _ hcP
      rwa [tres_unshiftOr (hz k hkW) hcann] at this
    have hcmem : c ∈ annSites n z k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcann⟩
    have hoscge : hfun n (scaleSites n z k) h c - hfun n (scaleSites n z k) h cb ≤
        osc n z k (annSites n z k) h := by
      unfold osc
      have e1 := le_ciSup (f := fun x : {x // x ∈ annSites n z k} =>
        hfun n (scaleSites n z k) h x.1) (Set.finite_range _).bddAbove ⟨c, hcmem⟩
      have e2 := le_ciSup (f := fun x : {x // x ∈ annSites n z k} =>
        -hfun n (scaleSites n z k) h x.1) (Set.finite_range _).bddAbove ⟨cb, hcb⟩
      simp only at e1 e2
      linarith
    have hsplit := hfun_add_resid n (scaleSites n z k) h c
    linarith
  calc boxDGFF n (bad35 n z K A (A + 1 + u + C₂)) ≤ boxDGFF n (F1 ∪ F2) := measure_mono hsub
    _ ≤ boxDGFF n F1 + boxDGFF n F2 := measure_union_le _ _
    _ ≤ _ := add_le_add hF1 hF2

end SupercriticalLQGUniqueness.B2.QPos.P5
