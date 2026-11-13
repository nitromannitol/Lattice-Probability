/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3WalkMass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Absorb
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Continuation

 









set_option autoImplicit false
noncomputable section

open Finset
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P3

open Classical

 
def EncS (n : ℕ) (S : Set (ℤ × ℤ)) (γ : Excursion (DGFFSite n)) : Prop :=
  ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ ∀ v ∈ p, v.1 ∈ S ∨ γ.Visits v

 
def ContS (n : ℕ) (S : Set (ℤ × ℤ)) (N : ℕ) (y : ℤ × ℤ) (ω : Fin N → Bool × Bool) : Prop :=
  (∀ k ≤ N, wpos y ω k ∈ interiorSites n) ∧
    ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧
      ∀ v ∈ p, v.1 ∈ S ∨ ∃ k ≤ N, wpos y ω k = v.1

theorem encS_empty (n : ℕ) (γ : Excursion (DGFFSite n)) :
    EncS n ∅ γ ↔ ExcursionEncircles n γ := by
  simp [EncS, ExcursionEncircles]

theorem contS_empty (n N : ℕ) (y : ℤ × ℤ) (ω : Fin N → Bool × Bool) :
    ContS n ∅ N y ω ↔ ContEvent n N y ω := by
  simp [ContS, ContEvent]

theorem pathMass_mono_start (n : ℕ) {Φ Ψ : Excursion (DGFFSite n) → Prop} (y : DGFFSite n)
    (h : ∀ γ : Excursion (DGFFSite n), γ.2 0 = y → Φ γ → Ψ γ) :
    pathMass n Φ y ≤ pathMass n Ψ y := by
  unfold pathMass
  apply ENNReal.tsum_le_tsum
  intro γ
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h γ h1.1 h1.2⟩ h2
  · exact bot_le
  · exact le_rfl

 
theorem card_filter_cons2 (N : ℕ) (P : (Fin (N + 1) → Bool × Bool) → Prop) :
    ((univ.filter P).card : ℝ) =
      ∑ s : Bool × Bool, ((univ.filter fun ω : Fin N → Bool × Bool => P (Fin.cons s ω)).card : ℝ) := by
  have h : (univ.filter P).card =
      ∑ s : Bool × Bool, (univ.filter fun ω : Fin N → Bool × Bool => P (Fin.cons s ω)).card := by
    rw [card_eq_sum_ones, sum_filter, sum_cons]
    apply sum_congr rfl
    intro s _
    rw [card_eq_sum_ones, sum_filter]
  rw [h]; push_cast; rfl

theorem contS_cons (n : ℕ) (S : Set (ℤ × ℤ)) (N : ℕ) (y : ℤ × ℤ) (s : Bool × Bool)
    (ω : Fin N → Bool × Bool) (h : ContS n S (N + 1) y (Fin.cons s ω)) :
    y ∈ interiorSites n ∧ y + stepVec s ∈ interiorSites n ∧
      ContS n (insert y S) N (y + stepVec s) ω := by
  obtain ⟨hin, p, hp, hv⟩ := h
  have h0 := hin 0 (Nat.zero_le _)
  rw [wpos_zero] at h0
  have h1 : wpos (y + stepVec s) ω 0 ∈ interiorSites n := by
    have := hin (0 + 1) (by omega); rwa [wpos_cons_succ] at this
  rw [wpos_zero] at h1
  refine ⟨h0, h1, ?_, p, hp, ?_⟩
  · intro k hk
    have := hin (k + 1) (by omega)
    rwa [wpos_cons_succ] at this
  · intro v hvp
    rcases hv v hvp with h | ⟨k, hk, hk'⟩
    · exact Or.inl (Set.mem_insert_of_mem _ h)
    · cases k with
      | zero => rw [wpos_zero] at hk'; exact Or.inl (by rw [← hk']; exact Set.mem_insert _ _)
      | succ k =>
        rw [wpos_cons_succ] at hk'
        exact Or.inr ⟨k, by omega, hk'⟩

theorem encS_consExc (n : ℕ) (S : Set (ℤ × ℤ)) (y : DGFFSite n) (γ : Excursion (DGFFSite n))
    (h : EncS n (insert y.1 S) γ) : EncS n S (consExc y γ) := by
  obtain ⟨p, hp, hv⟩ := h
  refine ⟨p, hp, fun v hvp => ?_⟩
  rcases hv v hvp with h | ⟨j, hj⟩
  · rcases (Set.mem_insert_iff.mp h) with h | h
    · exact Or.inr ⟨0, by rw [show v = y from Subtype.ext h]; rfl⟩
    · exact Or.inl h
  · exact Or.inr ⟨j.succ, by rw [← hj]; rfl⟩

 
theorem pathMass_ge_count (n : ℕ) :
    ∀ (N : ℕ) (S : Set (ℤ × ℤ)) (y : DGFFSite n),
      ENNReal.ofReal (((univ.filter fun ω : Fin N → Bool × Bool => ContS n S N y.1 ω).card : ℝ) /
        4 ^ N) ≤ pathMass n (EncS n S) y
  | 0, S, y => by
    by_cases hC : ∃ ω : Fin 0 → Bool × Bool, ContS n S 0 y.1 ω
    · obtain ⟨ω₀, hω₀⟩ := hC
      have hall : ∀ γ : Excursion (DGFFSite n), γ.2 0 = y → True → EncS n S γ := by
        intro γ hγ _
        obtain ⟨_, p, hp, hv⟩ := hω₀
        refine ⟨p, hp, fun v hvp => ?_⟩
        rcases hv v hvp with h | ⟨k, hk, hk'⟩
        · exact Or.inl h
        · have : k = 0 := by omega
          subst this
          rw [wpos_zero] at hk'
          exact Or.inr ⟨0, by rw [hγ]; exact Subtype.ext hk'⟩
      calc ENNReal.ofReal (((univ.filter fun ω : Fin 0 → Bool × Bool =>
              ContS n S 0 y.1 ω).card : ℝ) / 4 ^ 0)
          ≤ 1 := by
            rw [ENNReal.ofReal_le_one]
            have : ((univ.filter fun ω : Fin 0 → Bool × Bool => ContS n S 0 y.1 ω).card : ℝ) ≤ 1 := by
              have := card_le_univ (univ.filter fun ω : Fin 0 → Bool × Bool => ContS n S 0 y.1 ω)
              simp at this ⊢
              exact_mod_cast this
            simpa using this
        _ = pathMass n (fun _ => True) y := (pathMass_true n y).symm
        _ ≤ pathMass n (EncS n S) y := pathMass_mono_start n y hall
    · have : (univ.filter fun ω : Fin 0 → Bool × Bool => ContS n S 0 y.1 ω) = ∅ := by
        apply filter_eq_empty_iff.mpr; intro ω _ h; exact hC ⟨ω, h⟩
      rw [this]; simp
  | N + 1, S, y => by
    
    let valid : Finset (Bool × Bool) := univ.filter fun s => y.1 + stepVec s ∈ interiorSites n
    let site : Bool × Bool → DGFFSite n := fun s =>
      if h : y.1 + stepVec s ∈ interiorSites n then ⟨_, h⟩ else y
    have hsite : ∀ s ∈ valid, (site s).1 = y.1 + stepVec s := by
      intro s hs
      simp only [valid, mem_filter, mem_univ, true_and] at hs
      simp [site, hs]
    
    have hcount : ((univ.filter fun ω : Fin (N + 1) → Bool × Bool =>
          ContS n S (N + 1) y.1 ω).card : ℝ) ≤
        ∑ s ∈ valid, ((univ.filter fun ω : Fin N → Bool × Bool =>
          ContS n (insert y.1 S) N (site s).1 ω).card : ℝ) := by
      rw [card_filter_cons2]
      rw [← sum_filter_add_sum_filter_not univ (fun s => y.1 + stepVec s ∈ interiorSites n)]
      have hnot : ∑ s ∈ univ.filter (fun s => ¬ (y.1 + stepVec s ∈ interiorSites n)),
          ((univ.filter fun ω : Fin N → Bool × Bool =>
            ContS n S (N + 1) y.1 (Fin.cons s ω)).card : ℝ) = 0 := by
        apply sum_eq_zero
        intro s hs
        simp only [mem_filter, mem_univ, true_and] at hs
        have : (univ.filter fun ω : Fin N → Bool × Bool =>
            ContS n S (N + 1) y.1 (Fin.cons s ω)) = ∅ := by
          apply filter_eq_empty_iff.mpr
          intro ω _ h
          exact hs (contS_cons n S N y.1 s ω h).2.1
        rw [this]; simp
      rw [hnot, add_zero]
      apply sum_le_sum
      intro s hs
      rw [hsite s hs]
      exact_mod_cast card_le_card (by
        intro ω hω
        rw [mem_filter] at hω ⊢
        exact ⟨mem_univ _, (contS_cons n S N y.1 s ω hω.2).2.2⟩)
    
    have hinj : Set.InjOn site valid := by
      intro s hs s' hs' h
      have := congrArg Subtype.val h
      rw [hsite s hs, hsite s' hs'] at this
      exact stepVec_injective (add_left_cancel this)
    have hP : ∀ s ∈ valid, (boxConductances n).killedTransition y (site s) = 1 / 4 := by
      intro s hs
      rw [box_killedTransition_apply, if_pos]
      rw [hsite s hs]
      exact latticeAdjacent_add_stepVec _ _
    have hmass : ∑ s ∈ valid, ENNReal.ofReal (1 / 4) *
          pathMass n (EncS n (insert y.1 S)) (site s) ≤ pathMass n (EncS n S) y := by
      calc ∑ s ∈ valid, ENNReal.ofReal (1 / 4) * pathMass n (EncS n (insert y.1 S)) (site s)
          = ∑ y' ∈ valid.image site, ENNReal.ofReal ((boxConductances n).killedTransition y y') *
              pathMass n (EncS n (insert y.1 S)) y' := by
            rw [sum_image hinj]
            apply sum_congr rfl
            intro s hs; rw [hP s hs]
        _ ≤ ∑ y' : DGFFSite n, ENNReal.ofReal ((boxConductances n).killedTransition y y') *
              pathMass n (EncS n (insert y.1 S)) y' :=
            sum_le_sum_of_subset (subset_univ _)
        _ ≤ ∑ y' : DGFFSite n, ENNReal.ofReal ((boxConductances n).killedTransition y y') *
              pathMass n (fun γ => EncS n S (consExc y γ)) y' := by
            apply sum_le_sum; intro y' _
            gcongr
            exact pathMass_mono_start n y' (fun γ _ h => encS_consExc n S y γ h)
        _ ≤ pathMass n (EncS n S) y := pathMass_first_step n (EncS n S) y
    calc ENNReal.ofReal (((univ.filter fun ω : Fin (N + 1) → Bool × Bool =>
            ContS n S (N + 1) y.1 ω).card : ℝ) / 4 ^ (N + 1))
        ≤ ENNReal.ofReal ((∑ s ∈ valid, ((univ.filter fun ω : Fin N → Bool × Bool =>
            ContS n (insert y.1 S) N (site s).1 ω).card : ℝ)) / 4 ^ (N + 1)) := by
          apply ENNReal.ofReal_le_ofReal
          exact div_le_div_of_nonneg_right hcount (by positivity)
      _ = ∑ s ∈ valid, ENNReal.ofReal (1 / 4) *
            ENNReal.ofReal (((univ.filter fun ω : Fin N → Bool × Bool =>
              ContS n (insert y.1 S) N (site s).1 ω).card : ℝ) / 4 ^ N) := by
          rw [sum_div, ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity)]
          apply sum_congr rfl; intro s _
          rw [← ENNReal.ofReal_mul (by norm_num), pow_succ]
          congr 1; field_simp
      _ ≤ ∑ s ∈ valid, ENNReal.ofReal (1 / 4) * pathMass n (EncS n (insert y.1 S)) (site s) := by
          apply sum_le_sum; intro s _
          gcongr
          exact pathMass_ge_count n N (insert y.1 S) (site s)
      _ ≤ pathMass n (EncS n S) y := hmass

 
theorem pathMass_enc_ge (n N : ℕ) (y : DGFFSite n) :
    ENNReal.ofReal (((univ.filter fun ω : Fin N → Bool × Bool => ContEvent n N y.1 ω).card : ℝ) /
      4 ^ N) ≤ pathMass n (ExcursionEncircles n) y := by
  have h := pathMass_ge_count n N ∅ y
  have e1 : (univ.filter fun ω : Fin N → Bool × Bool => ContS n ∅ N y.1 ω) =
      univ.filter fun ω : Fin N → Bool × Bool => ContEvent n N y.1 ω := by
    apply filter_congr; intro ω _; exact contS_empty n N y.1 ω
  have e2 : EncS n ∅ = ExcursionEncircles n := by
    funext γ; exact propext (encS_empty n γ)
  rw [e1, e2] at h
  exact h

end SupercriticalLQGUniqueness.B2.QPos.P3
