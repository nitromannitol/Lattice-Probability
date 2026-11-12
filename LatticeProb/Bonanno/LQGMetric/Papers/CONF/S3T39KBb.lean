/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39KBb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K9a
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB3

/-!
# CONF Theorem 3.9, DEC-132 packet P-132B: saturation and membership of `t39k9Ban`

Decision `decisions/DEC-132.md` (D132) §2, N2–N3. CONF = arXiv:1905.00381 `confluence-final.tex`,
C:1559–1561 ("`𝓘_k` is determined by `(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`"); GM = arXiv:1905.00383,
(4.7) `arcOf`, l. 1705–1708 (the analytic-set argument). `t39k9Ban` (S3T39K9a, P-132A) is the
analytic form of `t39k5B` (S3T39K5g) with GM's relation `confPts`/`arcOf` in place of `t39gArc`.

* **`t39k9_Ban_sat`** (N2): `t39k9Ban` is saturated for the internal metric on `A` — proof as
  `t39k5_B_sat`, with `GM.gm_hitSet_transfer`, `GM.gm_arcOf_transfer` for the relation;
* **`t39k9_mem_Ban_iff`** (N3): for `D_g = C·d` and a bounded `𝓑^•_s(d) ⊆ A` (`A` open), membership
  of `(g, (pattern 𝓑^•_s(d), pattern 𝓑^•_τ(d)))` is GM's relation for `D_g` at radii `(Cτ, Cs)` —
  proof as `t39k5_mem_B_iff`, plus `IsCompact.exists_thickening_subset_open` for the thickening
  clause.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace

namespace LQGMetric.CONF

open Blueprint LocalEvent GM

/-- the thickening clause of `t39k9Ban` implies inclusion -/
theorem t39kb_subset_of_thick {K A : Set ℂ} {n : ℕ}
    (hn : K ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ = ∅) : K ⊆ A := fun w hw => by
  by_contra hwA
  have : w ∈ K ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ :=
    ⟨hw, self_subset_thickening (by positivity) _ hwA⟩
  rw [hn] at this
  exact this

/-- a compact subset of an open set misses a thickening of the complement -/
theorem t39kb_thick_of_subset {K A : Set ℂ} (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A) :
    ∃ n : ℕ, K ∩ Metric.thickening ((n : ℝ) + 1)⁻¹ Aᶜ = ∅ := by
  obtain ⟨δ, hδ, hδA⟩ := hK.exists_thickening_subset_open hA hKA
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, eq_empty_iff_forall_notMem.2 fun w ⟨hwK, hwT⟩ => ?_⟩
  obtain ⟨a, haA, hwa⟩ := mem_thickening_iff.1 hwT
  refine haA (hδA (mem_thickening_iff.2 ⟨w, hwK, ?_⟩))
  rw [dist_comm]
  rw [one_div] at hn
  exact hwa.trans hn

/-- **N2: `t39k9Ban` is saturated for the internal metric on `A`** (C:1559–1561) -/
theorem t39k9_Ban_sat (D : DistC → ContMetric) (z₀ : ℂ) (A : Opens ℂ) (arcs : Set ℂ → Set ℂ)
    (U : Set ℂ) : ∀ g₁ g₂ : DistC, D g₁ ∈ lenSet → D g₂ ∈ lenSet →
      (D g₁).internal A = (D g₂).internal A → ∀ ζ, (g₁, ζ) ∈ t39k9Ban D z₀ A arcs U →
        (g₂, ζ) ∈ t39k9Ban D z₀ A arcs U := by
  rintro g₁ g₂ h1 h2 heq ζ ⟨σ, σ', hσ', hσσ, hK, hK', ⟨n, hn⟩, x, hx, y, hyU, hxc, hya⟩
  have H := t39k5_agree_of_internal (isLength_of_mem_lenSet h1) (isLength_of_mem_lenSet h2)
    (hσ'.trans_le hσσ) A.isOpen (fun x _ y _ => by rw [heq]) (t39kb_subset_of_thick hn)
  refine ⟨σ, σ', hσ', hσσ, by rw [H.fb le_rfl]; exact hK, by rw [H.fb hσσ]; exact hK',
    ⟨n, by rw [H.fb le_rfl]; exact hn⟩, x, by rw [H.fb hσσ]; exact hx, y, hyU,
    gm_hitSet_transfer H hσσ le_rfl hxc, gm_arcOf_transfer H le_rfl hya⟩

/-- **N3: membership in `t39k9Ban` is GM's arc relation**, for `D_g = C·d` -/
theorem t39k9_mem_Ban_iff (D : DistC → ContMetric) {d : ContMetric} {z₀ : ℂ} {C : ℝ}
    (hC : 0 < C) {s τ : ℝ} (hτ : 0 < τ) (hτs : τ ≤ s)
    (hKb : Bornology.IsBounded (filledBall d z₀ s)) {A : Set ℂ} (hA : IsOpen A)
    (hKA : filledBall d z₀ s ⊆ A) (arcs : Set ℂ → Set ℂ) (U : Set ℂ) {g : DistC}
    (hg : D g = d.smul C hC) :
    (g, (t39k5Pat (filledBall d z₀ s), t39k5Pat (filledBall d z₀ τ))) ∈ t39k9Ban D z₀ A arcs U ↔
      ∃ x ∈ arcs (frontier (filledBall (D g) z₀ (C * τ))), ∃ y ∈ U,
        x ∈ GM.confPts (D g) z₀ (C * τ) (C * s) ∧ y ∈ GM.arcOf (D g) z₀ (C * s) x := by
  have hcl : ∀ (d' : ContMetric) σ, IsClosed (filledBall d' z₀ σ) :=
    fun d' σ => gm_filledBall_isClosed _ _ _
  have hfs : ∀ σ, filledBall (D g) z₀ (C * σ) = filledBall d z₀ σ := fun σ => by
    rw [hg]; exact t39k5_filledBall_smul hC d z₀ σ
  have hpat : ∀ σ σ₁, t39k5Pat (filledBall (D g) z₀ σ) = t39k5Pat (filledBall d z₀ σ₁) →
      filledBall (D g) z₀ σ = filledBall d z₀ σ₁ := fun σ σ₁ he => by
    rw [← t39k5_Kset_pat (hcl (D g) σ), he, t39k5_Kset_pat (hcl d σ₁)]
  constructor
  · rintro ⟨σ, σ', hσ', hσσ, hK, hK', -, x, hx, y, hyU, hxc, hya⟩
    have e1 := hpat _ _ hK
    have e2 := hpat _ _ hK'
    have hσs : σ = C * s :=
      t39k5_radius_eq (hσ'.trans_le hσσ) (by rw [e1]; exact hKb) (by rw [e1, hfs])
    have hσ't : σ' = C * τ :=
      t39k5_radius_eq hσ' (by rw [e2]; exact hKb.subset (gm_filledBall_mono d z₀ hτs))
        (by rw [e2, hfs])
    subst hσs hσ't
    exact ⟨x, hx, y, hyU, hxc, hya⟩
  · rintro ⟨x, hx, y, hyU, hxc, hya⟩
    obtain ⟨n, hn⟩ := t39kb_thick_of_subset
      (Metric.isCompact_of_isClosed_isBounded (hcl d s) hKb) hA hKA
    exact ⟨C * s, C * τ, mul_pos hC hτ, mul_le_mul_of_nonneg_left hτs hC.le,
      by rw [hfs], by rw [hfs], ⟨n, by rw [hfs]; exact hn⟩, x, hx, y, hyU, hxc, hya⟩

end LQGMetric.CONF
