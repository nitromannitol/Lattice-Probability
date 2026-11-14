/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidRecursion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidTraceCriterion




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 



theorem finite_first_hit_recursion
    (D : LSCMetric) {P : ℝ → ℂ} {T η : ℝ}
    (hP : D.IsCurve P 0 T) (hPc : ContinuousOn P (Icc 0 T))
    (hfin : D.len P 0 T ≠ ∞) (hη : 0 < η)
    {ι : Type*} (K : ι → Set ℂ) (c : ι → ℂ) (I : ℝ → ι)
    (hK : ∀ i, IsClosed (K i))
    (hstart : ∀ s ∈ Icc (0 : ℝ) T,
      P s ∈ connectedComponentIn (K (I s))ᶜ (c (I s)))
    (hcost : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc s T,
      P t ∈ K (I s) → ENNReal.ofReal η ≤ D.len P s t) :
    ∃ (J : ℕ) (S : ℕ → ℝ),
      S 0 = 0 ∧ Monotone S ∧ (∀ n, S n ∈ Icc (0 : ℝ) T) ∧
      (∀ j < J, S j < S (j + 1) ∧ P (S (j + 1)) ∈ K (I (S j)) ∧
        ∀ u ∈ Ico (S j) (S (j + 1)),
          P u ∈ connectedComponentIn (K (I (S j)))ᶜ (c (I (S j)))) ∧
      (∀ u ∈ Icc (S J) T,
        P u ∈ connectedComponentIn (K (I (S J)))ᶜ (c (I (S J)))) := by
  classical
  let Ex : ℝ → Prop := fun s => ∃ t ∈ Icc s T, P t ∈ K (I s)
  have hfirst : ∀ s ∈ Icc (0 : ℝ) T, Ex s →
      ∃ t ∈ Icc s T, s < t ∧ P t ∈ K (I s) ∧
        ∀ u ∈ Ico s t,
          P u ∈ connectedComponentIn (K (I s))ᶜ (c (I s)) := by
    intro s hs hEx
    have hsub : Icc s T ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs.1 le_rfl
    have hsnot : P s ∉ K (I s) :=
      (connectedComponentIn_subset _ _ (hstart s hs))
    obtain ⟨t, ht, hst, htK, hbefore⟩ :=
      first_hit_stays_component (hK (I s)) (hPc.mono hsub) hs.2 hsnot hEx
    have heq : connectedComponentIn (K (I s))ᶜ (P s) =
        connectedComponentIn (K (I s))ᶜ (c (I s)) :=
      (connectedComponentIn_eq (hstart s hs)).symm
    exact ⟨t, ht, hst, htK, fun u hu => heq ▸ hbefore u hu⟩
  let nx : ℝ → ℝ := fun s =>
    if h : s ∈ Icc (0 : ℝ) T ∧ Ex s then Classical.choose (hfirst s h.1 h.2) else s
  have hnx : ∀ s ∈ Icc (0 : ℝ) T,
      nx s ∈ Icc s T ∧
      (Ex s → s < nx s ∧ P (nx s) ∈ K (I s) ∧
        ∀ u ∈ Ico s (nx s),
          P u ∈ connectedComponentIn (K (I s))ᶜ (c (I s))) := by
    intro s hs
    by_cases h : Ex s
    · have hh : s ∈ Icc (0 : ℝ) T ∧ Ex s := ⟨hs, h⟩
      have hspec := Classical.choose_spec (hfirst s hs h)
      simp only [nx, dite_eq_left hh]
      exact ⟨hspec.1, fun _ => hspec.2⟩
    · have hh : ¬ (s ∈ Icc (0 : ℝ) T ∧ Ex s) := fun h' => h h'.2
      simp only [nx, dite_eq_right hh]
      exact ⟨⟨le_rfl, hs.2⟩, fun h' => absurd h' h⟩
  let S : ℕ → ℝ := fun n => nx^[n] 0
  have hS0 : S 0 = 0 := rfl
  have hSs : ∀ n, S (n + 1) = nx (S n) :=
    fun n => Function.iterate_succ_apply' nx n 0
  have hSI : ∀ n, S n ∈ Icc (0 : ℝ) T := by
    intro n
    induction n with
    | zero => simpa [hS0] using (show (0 : ℝ) ∈ Icc 0 T from
          ⟨le_rfl, hP.1⟩)
    | succ n ih =>
        rw [hSs]
        have h := (hnx _ ih).1
        exact ⟨ih.1.trans h.1, h.2⟩
  have hSle : ∀ n, S n ≤ S (n + 1) := by
    intro n
    rw [hSs]
    exact (hnx _ (hSI n)).1.1
  have hSmono : Monotone S := monotone_nat_of_le_succ hSle
  have hstop : ∃ n, ¬ Ex (S n) := by
    by_contra hall
    push Not at hall
    apply no_infinite_paid_steps D hη hP.1 hfin S hS0 hSI hSle
    intro n
    have h := (hnx _ (hSI n)).2 (hall n)
    rw [← hSs] at h
    exact hcost (S n) (hSI n) (S (n + 1)) (by
      rw [hSs]; exact (hnx _ (hSI n)).1) h.2.1
  let J := Nat.find hstop
  have hJ : ¬ Ex (S J) := Nat.find_spec hstop
  have hbefore : ∀ j < J, Ex (S j) := by
    intro j hj
    have h := Nat.find_min hstop hj
    push Not at h
    exact h
  refine ⟨J, S, hS0, hSmono, hSI, ?_, ?_⟩
  · intro j hj
    have h := (hnx _ (hSI j)).2 (hbefore j hj)
    rwa [← hSs] at h
  · have hsub : Icc (S J) T ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc (hSI J).1 le_rfl
    have havoid : ∀ u ∈ Icc (S J) T, P u ∉ K (I (S J)) := by
      intro u hu huK
      exact hJ ⟨u, hu, huK⟩
    have hstay := no_hit_stays_component (hPc.mono hsub) (hSI J).2 havoid
    have heq : connectedComponentIn (K (I (S J)))ᶜ (P (S J)) =
        connectedComponentIn (K (I (S J)))ᶜ (c (I (S J))) :=
      (connectedComponentIn_eq (hstart (S J) (hSI J))).symm
    simpa only [heq] using hstay


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
