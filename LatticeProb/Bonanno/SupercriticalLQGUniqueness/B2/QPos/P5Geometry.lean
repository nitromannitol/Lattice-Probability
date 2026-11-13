/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5Geometry at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5Independence
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CenteredExtraction
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5ScaleSeparation
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointRadiusGap
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitInput

 

















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

 
def AnnAt (n : ℕ) (z : ℤ × ℤ) (k : ℕ) (c : DGFFSite n) : Prop :=
  dgffInnerRadius (n - k) < latticeRadius (c.1 - z) ∧
    latticeRadius (c.1 - z) ≤ dgffOuterRadius (n - k)

instance (n : ℕ) (z : ℤ × ℤ) (k : ℕ) (c : DGFFSite n) : Decidable (AnnAt n z k c) := by
  unfold AnnAt; infer_instance

theorem latticeRadius_lt_of_le_outer {m : ℕ} {c : ℤ × ℤ} (h : latticeRadius c ≤ dgffOuterRadius m) :
    c ∈ interiorSites m := by
  have hlt := dgffOuterRadius_lt_box m
  rw [mem_interiorSites_iff]
  unfold interiorRadius
  unfold latticeRadius at h
  have h1 : c.1.natAbs < 2 ^ m := by omega
  have h2 : c.2.natAbs < 2 ^ m := by omega
  have e1 : (c.1.natAbs : ℤ) = |c.1| := Int.natCast_natAbs _
  have e2 : (c.2.natAbs : ℤ) = |c.2| := Int.natCast_natAbs _
  have h1' : |c.1| < 2 ^ m := by rw [← e1]; exact_mod_cast h1
  have h2' : |c.2| < 2 ^ m := by rw [← e2]; exact_mod_cast h2
  rw [abs_lt] at h1' h2'
  omega

 
def unshiftOr (n : ℕ) (z : ℤ × ℤ) (k : ℕ) (c : DGFFSite n) : DGFFSite (n - k) :=
  if hc : c.1 - z ∈ interiorSites (n - k) then ⟨c.1 - z, hc⟩
  else ⟨0, by
    rw [mem_interiorSites_iff]; unfold interiorRadius
    have : (1 : ℤ) ≤ 2 ^ (n - k) := one_le_pow₀ (by norm_num)
    simp only [Prod.fst_zero, Prod.snd_zero]; omega⟩

theorem unshiftOr_val {n : ℕ} {z : ℤ × ℤ} {k : ℕ} {c : DGFFSite n} (hc : AnnAt n z k c) :
    (unshiftOr n z k c).1 = c.1 - z := by
  unfold unshiftOr
  rw [dif_pos (latticeRadius_lt_of_le_outer hc.2)]

theorem shiftSite_unshiftOr {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) {c : DGFFSite n}
    (hc : AnnAt n z k c) : shiftSite hk (unshiftOr n z k c) = c := by
  apply Subtype.ext
  rw [shiftSite_val, unshiftOr_val hc]
  abel

theorem inDGFFAnnulus_unshiftOr {n : ℕ} {z : ℤ × ℤ} {k : ℕ} {c : DGFFSite n} (hc : AnnAt n z k c) :
    inDGFFAnnulus (n - k) (unshiftOr n z k c) := by
  unfold inDGFFAnnulus
  rw [unshiftOr_val hc]
  exact hc

theorem tres_unshiftOr {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) {c : DGFFSite n}
    (hc : AnnAt n z k c) (h : EuclideanSpace ℝ (DGFFSite n)) :
    tresCLM hk h (unshiftOr n z k c) = resid n (scaleSites n z k) h c := by
  rw [tresCLM_apply, shiftSite_unshiftOr hk hc]

 
theorem annAt_shiftSite {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) {c : DGFFSite (n - k)}
    (hc : inDGFFAnnulus (n - k) c) : AnnAt n z k (shiftSite hk c) := by
  unfold AnnAt
  rw [shiftSite_val, add_sub_cancel_right]
  exact hc

theorem annAt_disjoint {n : ℕ} {z : ℤ × ℤ} {k l : ℕ} (hkl : k ≠ l) (hk : k ≤ n) (hl : l ≤ n)
    {c : DGFFSite n} (h1 : AnnAt n z k c) (h2 : AnnAt n z l c) : False := by
  rcases lt_or_gt_of_ne hkl with h | h
  · exact no_radius_in_distinct_annuli n k l _ h hl h1 h2
  · exact no_radius_in_distinct_annuli n l k _ h hk h2 h1

theorem latticeSupRadius_sub (a b : ℤ × ℤ) :
    latticeSupRadius (a - b) = (latticeRadius (a - b) : ℤ) :=
  latticeSupRadius_eq_latticeRadius (a - b)

 



theorem scale_crossing {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk4 : k + 4 ≤ n)
    (p : ℕ → DGFFSite n) (N : ℕ)
    (hstart : latticeRadius ((p 0).1 - z) ≤ dgffInnerRadius (n - k))
    (hend : dgffOuterRadius (n - k) ≤ latticeRadius ((p N).1 - z))
    (hpath : ∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1) :
    ∃ s t : ℕ, s ≤ t ∧ t ≤ N ∧ (∀ i, s ≤ i → i ≤ t → AnnAt n z k (p i)) ∧
      IsDGFFAnnulusPath (n - k)
        (List.ofFn fun i : Fin (t - s + 1) => unshiftOr n z k (p (s + i))) := by
  have hgap := dgff_radius_gap (n - k) (by omega)
  have hstart' : latticeSupRadius ((p 0).1 - z) ≤ (dgffInnerRadius (n - k) : ℤ) := by
    rw [latticeSupRadius_sub]; exact_mod_cast hstart
  have hend' : (dgffOuterRadius (n - k) : ℤ) ≤ latticeSupRadius ((p N).1 - z) := by
    rw [latticeSupRadius_sub]; exact_mod_cast hend
  have hgap' : (dgffInnerRadius (n - k) : ℤ) + 1 < (dgffOuterRadius (n - k) : ℤ) := by
    exact_mod_cast hgap
  obtain ⟨s, t, hs0, hst, htN, hs, ht, hband⟩ :=
    centered_lattice_annular_indices (fun i => (p i).1) N z
      (dgffInnerRadius (n - k)) (dgffOuterRadius (n - k)) hgap' hstart' hend' hpath
  have hann : ∀ i, s ≤ i → i ≤ t → AnnAt n z k (p i) := by
    intro i h1 h2
    have hh := hband i h1 h2
    rw [latticeSupRadius_sub] at hh
    constructor
    · have := hh.1; omega
    · exact_mod_cast hh.2
  refine ⟨s, t, hst, htN, hann, ?_⟩
  set f : Fin (t - s + 1) → DGFFSite (n - k) := fun i => unshiftOr n z k (p (s + i))
  have hfval : ∀ i : Fin (t - s + 1), (f i).1 = (p (s + i)).1 - z := fun i =>
    unshiftOr_val (hann _ (by omega) (by omega))
  refine ⟨?_, ?_, f 0, f (Fin.last _), ?_, ?_, ?_, ?_⟩
  · rw [List.isChain_ofFn]
    intro i hi
    rw [hfval, hfval]
    have := hpath (s + i) (by omega)
    simpa [Nat.add_assoc] using latticeAdjacent_sub_center _ _ z this
  · intro c hc
    rw [List.mem_ofFn] at hc
    obtain ⟨i, rfl⟩ := hc
    exact inDGFFAnnulus_unshiftOr (hann _ (by omega) (by omega))
  · have hne : (List.ofFn f) ≠ [] := by
      rw [Ne, List.ofFn_eq_nil_iff]; omega
    rw [List.head?_eq_some_head hne, List.head_ofFn]
    rfl
  · have hne : (List.ofFn f) ≠ [] := by
      rw [Ne, List.ofFn_eq_nil_iff]; omega
    rw [List.getLast?_eq_some_getLast hne, List.getLast_ofFn]
    congr 2
  · rw [hfval]
    have := hs
    rw [latticeSupRadius_sub] at this
    simp only [Fin.val_zero, add_zero]
    omega
  · rw [hfval]
    have := ht
    rw [latticeSupRadius_sub] at this
    simp only [Fin.val_last]
    rw [show s + (t - s) = t by omega]
    omega

end SupercriticalLQGUniqueness.B2.QPos.P5
