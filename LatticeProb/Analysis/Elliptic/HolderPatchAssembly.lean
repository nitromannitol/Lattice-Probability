import LatticeProb.Analysis.Elliptic.HolderCutoffV2
import LatticeProb.Analysis.Elliptic.HolderInteriorCutoff

/-!
# Assembly of local `C^{2,σ}` patches

Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Lemma 6.37
(printed pp. 136–137), extends a function with finite coordinate `C^{2,σ}` norm on a bounded
open set by covering the boundary with finitely many local patches, covering the remaining
compact core by an interior cutoff, and gluing the pieces with a finite smooth partition of
unity.

`HasLocalPatch σ U U' p` records a boundary patch at `p`: open sets `V ∋ p` and `W` with
`closure V ⊆ W` and `closure W ⊆ U'`, and a linear-in-norm construction of a compactly supported
`C²` function supported in `W`, equal to the given function on `V ∩ U`, whose whole-space
`C^{2,σ}` norm is controlled by the norm on `U`.

`assemble_local_patches` performs the gluing. Each glued piece is a smooth compactly supported
partition function times a patch, so its whole-space norm is controlled by the cutoff estimate,
and the whole-space norm of the finite sum is bounded by the sum of the whole-space norms. All
constants depend on the fixed cover and partition only.
-/

namespace LatticeProb.Elliptic.HolderExtension

open LatticeProb.Elliptic
open Set
open scoped ENNReal ContDiff Manifold Topology

noncomputable section

/-- A boundary patch at `p` for the extension of `C^{2,σ}` functions from `U` into `U'`. -/
def HasLocalPatch {d : ℕ} (σ : ℝ) (U U' : Set (Fin d → ℝ)) (p : Fin d → ℝ) : Prop :=
  ∃ V W : Set (Fin d → ℝ), IsOpen V ∧ IsOpen W ∧ p ∈ V ∧ closure V ⊆ W ∧
    closure W ⊆ U' ∧ ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
      ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
        tsupport v ⊆ W ∧ Set.EqOn v u (V ∩ U) ∧
        c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C * c2HolderNorm σ U u

namespace PatchAssembly

variable {d : ℕ}

/-- The supremum norm is monotone in the set. -/
theorem supNorm_mono {S T : Set (Fin d → ℝ)} (hST : S ⊆ T) (f : (Fin d → ℝ) → ℝ) :
    supNorm S f ≤ supNorm T f :=
  iSup₂_le fun x hx => le_iSup₂_of_le (f := fun x (_ : x ∈ T) => ENNReal.ofReal |f x|) x
    (hST hx) le_rfl

/-- The Hölder seminorm is monotone in the set. -/
theorem holderSeminorm_mono (σ : ℝ) {S T : Set (Fin d → ℝ)} (hST : S ⊆ T)
    (f : (Fin d → ℝ) → ℝ) : holderSeminorm σ S f ≤ holderSeminorm σ T f :=
  iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => le_iSup_of_le x (le_iSup_of_le (hST hx)
      (le_iSup_of_le y (le_iSup_of_le (hST hy) (le_iSup_of_le hxy le_rfl))))

/-- The coordinate `C^{2,σ}` norm is monotone in the set. -/
theorem c2HolderNorm_mono (σ : ℝ) {S T : Set (Fin d → ℝ)} (hST : S ⊆ T)
    (f : (Fin d → ℝ) → ℝ) : c2HolderNorm σ S f ≤ c2HolderNorm σ T f := by
  unfold c2HolderNorm
  gcongr with i _ i _ j _ i _ j _
  · exact supNorm_mono hST f
  · exact supNorm_mono hST _
  · exact supNorm_mono hST _
  · exact holderSeminorm_mono σ hST _

/-- The supremum norm is subadditive. -/
theorem supNorm_add_le (S : Set (Fin d → ℝ)) (f g : (Fin d → ℝ) → ℝ) :
    supNorm S (f + g) ≤ supNorm S f + supNorm S g := by
  refine iSup₂_le fun x hx => ?_
  calc ENNReal.ofReal |(f + g) x| ≤ ENNReal.ofReal (|f x| + |g x|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |f x| + ENNReal.ofReal |g x| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ supNorm S f + supNorm S g :=
        add_le_add (le_iSup₂_of_le (f := fun x (_ : x ∈ S) => ENNReal.ofReal |f x|) x hx le_rfl)
          (le_iSup₂_of_le (f := fun x (_ : x ∈ S) => ENNReal.ofReal |g x|) x hx le_rfl)

/-- The Hölder seminorm is subadditive. -/
theorem holderSeminorm_add_le (σ : ℝ) (S : Set (Fin d → ℝ)) (f g : (Fin d → ℝ) → ℝ) :
    holderSeminorm σ S (f + g) ≤ holderSeminorm σ S f + holderSeminorm σ S g := by
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
    iSup_le fun hxy => ?_
  have hr : 0 ≤ LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ :=
    Real.rpow_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg _) _
  have hf : ENNReal.ofReal (|f x - f y| / LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) ≤
      holderSeminorm σ S f :=
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy
      (le_iSup_of_le hxy le_rfl))))
  have hg : ENNReal.ofReal (|g x - g y| / LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) ≤
      holderSeminorm σ S g :=
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy
      (le_iSup_of_le hxy le_rfl))))
  refine le_trans ?_ (add_le_add hf hg)
  rw [← ENNReal.ofReal_add (div_nonneg (abs_nonneg _) hr) (div_nonneg (abs_nonneg _) hr),
    ← add_div]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hr)
  calc |(f + g) x - (f + g) y| = |(f x - f y) + (g x - g y)| := by
        simp only [Pi.add_apply]; ring_nf
    _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _

/-- The coordinate `C^{2,σ}` norm is subadditive on `C²` functions. -/
theorem c2HolderNorm_add_le (σ : ℝ) (S : Set (Fin d → ℝ)) {f g : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    c2HolderNorm σ S (f + g) ≤ c2HolderNorm σ S f + c2HolderNorm σ S g := by
  have h1 : ∀ i, partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := fun i =>
    funext fun x => InteriorCutoff.partialDeriv_add i (hf.differentiable (by simp) x)
      (hg.differentiable (by simp) x)
  have h2 : ∀ i j, secondPartial i j (f + g) = secondPartial i j f + secondPartial i j g :=
    fun i j => funext fun x => by
      simp only [secondPartial, iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt,
        add_apply, Pi.add_apply]
  calc c2HolderNorm σ S (f + g)
      ≤ (supNorm S f + supNorm S g) +
          ∑ i, (supNorm S (partialDeriv i f) + supNorm S (partialDeriv i g)) +
          ∑ i, ∑ j, (supNorm S (secondPartial i j f) + supNorm S (secondPartial i j g)) +
          ∑ i, ∑ j, (holderSeminorm σ S (secondPartial i j f) +
            holderSeminorm σ S (secondPartial i j g)) := by
        simp only [c2HolderNorm, h1, h2]
        gcongr with i _ i _ j _ i _ j _
        · exact supNorm_add_le S f g
        · exact supNorm_add_le S _ _
        · exact supNorm_add_le S _ _
        · exact holderSeminorm_add_le σ S _ _
    _ = c2HolderNorm σ S f + c2HolderNorm σ S g := by
        simp only [c2HolderNorm, Finset.sum_add_distrib]
        ring

/-- The coordinate `C^{2,σ}` norm of a finite sum of `C²` functions is at most the sum of the
norms. -/
theorem c2HolderNorm_sum_le {ι : Type*} [Fintype ι] [Nonempty ι] (σ : ℝ) (S : Set (Fin d → ℝ))
    (F : ι → (Fin d → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 2 (F i)) :
    c2HolderNorm σ S (∑ i, F i) ≤ ∑ i, c2HolderNorm σ S (F i) :=
  Finset.le_sum_nonempty_of_subadditive_on_pred (c2HolderNorm σ S) (fun f => ContDiff ℝ 2 f)
    (fun _ _ hf hg => c2HolderNorm_add_le σ S hf hg) (fun _ _ hf hg => hf.add hg) F
    Finset.univ Finset.univ_nonempty fun i _ => hF i

/-- A finite smooth partition of unity on a closed set, subordinate to a finite open cover. -/
theorem exists_smooth_partition {ι : Type*} [Fintype ι] {s : Set (Fin d → ℝ)}
    (hs : IsClosed s) (O : ι → Set (Fin d → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hsO : s ⊆ ⋃ i, O i) :
    ∃ χ : ι → (Fin d → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i, tsupport (χ i) ⊆ O i) ∧
      ∀ x ∈ s, ∑ i, χ i x = 1 := by
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, Fin d → ℝ)) hs O hO hsO
  refine ⟨fun i => ρ i, fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff, hρ, fun x hx => ?_⟩
  rw [← finsum_eq_sum_of_fintype]
  exact ρ.sum_eq_one hx

end PatchAssembly

open PatchAssembly

/-- Gilbarg–Trudinger, Lemma 6.37 (assembly): if every boundary point of a bounded open set `U`
has a local patch into `U'`, then a finite smooth partition of unity glues the patches and an
interior cutoff into a compactly supported `C²` extension supported in `U'`, with `C^{2,σ}` norm
on `U'` bounded by a constant independent of the function times the norm on `U`. The argument
does not use the openness of `U'`. -/
theorem assemble_local_patches {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1)
    {U U' : Set (Fin d → ℝ)} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hU' : IsOpen U') (hsub : closure U ⊆ U')
    (hpatch : ∀ p ∈ frontier U, HasLocalPatch σ U U' p) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
      ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
        tsupport v ⊆ U' ∧ Set.EqOn v u U ∧
        c2HolderNorm σ U' v ≤ ENNReal.ofReal C * c2HolderNorm σ U u := by
  classical
  have _ : IsOpen U' := hU'
  have hp : ∀ p : frontier U, HasLocalPatch σ U U' p := fun p => hpatch p p.2
  unfold HasLocalPatch at hp
  choose V W hVo hWo hpV hVW hWU' Cp hCp hT using hp
  have hfr : IsCompact (frontier U) :=
    hbounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨t, ht⟩ := hfr.elim_finite_subcover (fun p : frontier U => V p) hVo
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hpV ⟨x, hx⟩⟩
  obtain ⟨R, hR⟩ := hbounded.closure.subset_ball (0 : Fin d → ℝ)
  let O : Option t → Set (Fin d → ℝ) := fun i =>
    match i with
    | none => U
    | some p => V p ∩ Metric.ball 0 R
  have hO : ∀ i, IsOpen (O i) := by
    rintro (_ | p)
    · exact hU
    · exact (hVo p).inter Metric.isOpen_ball
  have hOball : ∀ i, O i ⊆ Metric.ball 0 R := by
    rintro (_ | p)
    · exact subset_closure.trans hR
    · exact inter_subset_right
  have hcover : closure U ⊆ ⋃ i, O i := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact mem_iUnion.2 ⟨none, hxU⟩
    · have hxfr : x ∈ frontier U := ⟨hx, by rwa [hU.interior_eq]⟩
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (ht hxfr)
      exact mem_iUnion.2 ⟨some ⟨p, hp⟩, hxp, hR hx⟩
  obtain ⟨χ, hχs, hχO, hχsum⟩ := exists_smooth_partition isClosed_closure O hO hcover
  have hχball : ∀ i, tsupport (χ i) ⊆ Metric.closedBall 0 R := fun i =>
    (hχO i).trans ((hOball i).trans Metric.ball_subset_closedBall)
  have hχc : ∀ i, HasCompactSupport (χ i) := fun i =>
    (isCompact_closedBall 0 R).of_isClosed_subset (isClosed_tsupport _) (hχball i)
  obtain ⟨C₀, hC₀, hint⟩ := interior_cutoff hσ hσ' U hU (tsupport (χ none)) (hχc none)
    (hχO none)
  choose Cχ hCχ hmul using fun i =>
    HolderCutoffV2.c2HolderNorm_mul_cutoff hσ hσ' (χ i) (hχs i) (hχc i)
  let Cw : Option t → ℝ := fun i =>
    match i with
    | none => C₀
    | some p => Cp p
  have hCw : ∀ i, 0 < Cw i := by
    rintro (_ | p)
    · exact hC₀
    · exact hCp p
  refine ⟨∑ i, Cχ i * Cw i,
    Finset.sum_pos (fun i _ => mul_pos (hCχ i) (hCw i)) Finset.univ_nonempty, ?_⟩
  intro u hu hun
  have hw : ∀ i, ∃ w : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 w ∧ HasCompactSupport w ∧
      tsupport w ⊆ U' ∧ (∀ x ∈ U, χ i x ≠ 0 → w x = u x) ∧
      c2HolderNorm σ Set.univ w ≤ ENNReal.ofReal (Cw i) * c2HolderNorm σ U u := by
    rintro (_ | p)
    · obtain ⟨w, hw2, hwc, hwU, hweq, hwn⟩ := hint u hu hun
      exact ⟨w, hw2, hwc, hwU.trans (subset_closure.trans hsub),
        fun x _ hx => hweq (subset_tsupport _ hx), hwn⟩
    · obtain ⟨w, hw2, hwc, hwW, hweq, hwn⟩ := hT p u hu hun
      refine ⟨w, hw2, hwc, hwW.trans (subset_closure.trans (hWU' p)),
        fun x hxU hx => hweq ⟨(hχO (some p) (subset_tsupport _ hx)).1, hxU⟩, hwn⟩
  choose w hw2 hwc hwU' hweq hwn using hw
  let F : Option t → (Fin d → ℝ) → ℝ := fun i x => χ i x * w i x
  have hF2 : ∀ i, ContDiff ℝ 2 (F i) := fun i =>
    ((hχs i).of_le (WithTop.coe_le_coe.2 le_top)).mul (hw2 i)
  have hFeval : ∀ x, (∑ i, F i) x = ∑ i, χ i x * w i x := fun x => Finset.sum_apply x _ _
  have hv2 : ContDiff ℝ 2 (∑ i, F i) := by
    rw [show (∑ i, F i) = fun x => ∑ i, F i x from funext fun x => Finset.sum_apply x _ _]
    exact ContDiff.sum fun i _ => hF2 i
  refine ⟨∑ i, F i, hv2, ?_, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => ?_
    rw [hFeval]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hχball i h), zero_mul]
  · refine (closure_minimal ?_
      (isClosed_iUnion_of_finite fun i => isClosed_tsupport (w i))).trans (iUnion_subset hwU')
    refine Function.support_subset_iff'.2 fun x hx => ?_
    rw [hFeval]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (mem_iUnion.2 ⟨i, h⟩), mul_zero]
  · intro x hx
    rw [hFeval]
    calc ∑ i, χ i x * w i x = ∑ i, χ i x * u x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : χ i x = 0
          · rw [h, zero_mul, zero_mul]
          · rw [hweq i x hx h]
      _ = u x := by rw [← Finset.sum_mul, hχsum x (subset_closure hx), one_mul]
  · have hwfin : ∀ i, c2HolderNorm σ Set.univ (w i) < ⊤ := fun i =>
      lt_of_le_of_lt (hwn i) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hun)
    calc c2HolderNorm σ U' (∑ i, F i)
        ≤ c2HolderNorm σ Set.univ (∑ i, F i) := c2HolderNorm_mono σ (subset_univ _) _
      _ ≤ ∑ i, c2HolderNorm σ Set.univ (F i) := c2HolderNorm_sum_le σ _ F hF2
      _ ≤ ∑ i, ENNReal.ofReal (Cχ i) * (ENNReal.ofReal (Cw i) * c2HolderNorm σ U u) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc c2HolderNorm σ Set.univ (F i)
              ≤ ENNReal.ofReal (Cχ i) * c2HolderNorm σ Set.univ (w i) :=
                hmul i (w i) (hw2 i) (hwfin i)
            _ ≤ ENNReal.ofReal (Cχ i) * (ENNReal.ofReal (Cw i) * c2HolderNorm σ U u) := by
                gcongr
                exact hwn i
      _ = ENNReal.ofReal (∑ i, Cχ i * Cw i) * c2HolderNorm σ U u := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => (mul_pos (hCχ i) (hCw i)).le,
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (hCχ i).le, mul_assoc]

end

end LatticeProb.Elliptic.HolderExtension
