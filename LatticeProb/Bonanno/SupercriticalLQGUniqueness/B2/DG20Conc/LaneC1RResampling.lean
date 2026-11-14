/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RResampling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RPhysical
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSupportAnnulus

 













set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
universe u

 
theorem laneC1R_le_of_frequently {X Y Z : ℝ} (hY : 0 ≤ Y)
    (h : ∀ N : ℕ, ∃ j ≥ N, X ≤ (1 + ((j : ℝ) + 1)⁻¹) * Y + Z) : X ≤ Y + Z := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (Y / ε)
  obtain ⟨j, hj, hX⟩ := h N
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hjN : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hsmall : ((j : ℝ) + 1)⁻¹ * Y < ε := by
    rw [inv_mul_lt_iff₀ hjpos]
    have : Y / ε < (j : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  nlinarith

 
theorem laneC_eventual_hit_resampling.{v} :
    ∀ (Q : PsiParams), Q.r₀ ≤ 1 / 100 → Q.ε₀ ≤ 1 / 100 →
      C1EventualHitResampling.{v} Q := by
  intro Q hR hε ξ
  obtain ⟨K₁, hK₁8, hK₁⟩ := laneC1R_largeK_resampling_le_source_around.{v} Q hR hε ξ
  obtain ⟨Kσ, hKσ⟩ := laneC_eventual_physical_scale_witness Q hR hε
  refine ⟨max K₁ Kσ, ?_⟩
  intro Ω _ P W hW n K hK hKn γ hγ
  have hK1 : K₁ ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := by omega
  set m := laneBCoarseIndex Q K with hmdef
  obtain ⟨hmLo, hmHi'⟩ := laneB_coarseIndex_radius Q K hK2
  have hmHi : (K : ℝ) ^ Q.ε₀ ≤ (2 : ℝ) ^ m := by
    simpa only [Real.rpow_natCast] using hmHi'
  have hmK : m + 1 ≤ K := laneB_coarseIndex_add_one_le Q K (hε.trans (by norm_num)) hK2
  obtain ⟨s, hσ, hr⟩ := hKσ K m n ((le_max_right _ _).trans hK) hKn hmK hmHi
  have hfield := laneC_resampled_field_eq_on_outer_region hW Q hKn hσ
    (fun b => T20.dyCenter K b) ((2 : ℝ)⁻¹ ^ K) (LaneCInputs.sourceRadius K m)
    (fun b _ => laneC_hoBlock_subset_center_ball K b) hr
  filter_upwards [hK₁ P W hW n K m hK1 hKn hmK hmLo hmHi, hfield] with z hdet hfz
  intro b hb
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  set f : ℂ → ℝ := fun x => psiMN Q W P 0 n x z.1 with hfdef
  set g : ℂ → ℝ := fun x => psiMN Q W P 0 n x z.1 -
    T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2 with hgdef
  have hffin : rectLen ξ f (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) (hψ.cont z.1)
  have hgcont : Continuous g :=
    ((hψ.cont z.1).sub ((T20B.blkKn_spec hW Q hKn b).1 z.1)).add
      ((T20B.blkKn_spec hW Q hKn b).1 z.2)
  have hgfin : rectLen ξ g (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) hgcont
  have hlfin : ∀ j : ℕ, lfppLen ξ f (γ j n z.1) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hffin) ((hγ j).near n z.1)
  have hnear : ∀ j : ℕ, (lfppLen ξ f (γ j n z.1)).toReal ≤
      (1 + ((j : ℝ) + 1)⁻¹) * (rectLen ξ f (rectAB 1 1)).toReal := by
    intro j
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hffin)
      ((hγ j).near n z.1)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  
  have hnohit : ∀ j : ℕ, z.1 ∉ laneCHits γ j n K m b →
      (rectLen ξ g (rectAB 1 1)).toReal ≤
        (1 + ((j : ℝ) + 1)⁻¹) * (rectLen ξ f (rectAB 1 1)).toReal + 0 := by
    intro j hj
    have hfar : ∀ t ∈ Icc (0 : ℝ) 1,
        LaneCInputs.sourceRadius K m ≤ dist (γ j n z.1 t) (T20.dyCenter K b) := by
      intro t ht
      by_contra hlt
      push Not at hlt
      exact hj ⟨t, ht, mem_ball.mpr hlt⟩
    have hle : rectLen ξ g (rectAB 1 1) ≤ lfppLen ξ f (γ j n z.1) := by
      calc rectLen ξ g (rectAB 1 1) ≤ lfppLen ξ g (γ j n z.1) :=
            crossLenIn_le_lfppLen ((hγ j).adm n z.1)
        _ = lfppLen ξ f (γ j n z.1) :=
            T20B.lfppLen_congr_path fun t ht => hfz b hb _ (hfar t ht)
    rw [add_zero]
    exact (ENNReal.toReal_mono (hlfin j) hle).trans (hnear j)
  by_cases hF : z.1 ∈ laneCEventualHit γ n K m b
  · rw [indicator_of_mem hF]
    by_cases hA : laneA3Around P W hW Q ξ n K b z.1 = ⊤
    · rw [hA, add_top]
      exact le_top
    obtain ⟨N₀, hN₀⟩ := hF
    have hhit : ∀ j : ℕ, N₀ ≤ j → (rectLen ξ g (rectAB 1 1)).toReal ≤
        (1 + ((j : ℝ) + 1)⁻¹) * (rectLen ξ f (rectAB 1 1)).toReal +
          (laneA3Around P W hW Q ξ n K b z.1).toReal := by
      intro j hj
      obtain ⟨t, ht, htball⟩ := hN₀ j hj
      have h := hdet b hb (γ j n z.1) ((hγ j).adm n z.1) (hlfin j) t ht (mem_ball.mp htball) hA
      exact h.trans (add_le_add (hnear j) le_rfl)
    have hreal := laneC1R_le_of_frequently ENNReal.toReal_nonneg
      (fun N => ⟨max N N₀, le_max_left _ _, hhit _ (le_max_right _ _)⟩)
    rw [← ENNReal.toReal_add hffin hA] at hreal
    exact (ENNReal.toReal_le_toReal hgfin (ENNReal.add_ne_top.mpr ⟨hffin, hA⟩)).mp hreal
  · rw [indicator_of_notMem hF, add_zero]
    have hfreq : ∀ N : ℕ, ∃ j ≥ N, (rectLen ξ g (rectAB 1 1)).toReal ≤
        (1 + ((j : ℝ) + 1)⁻¹) * (rectLen ξ f (rectAB 1 1)).toReal + 0 := by
      intro N
      by_contra hcon
      push Not at hcon
      apply hF
      refine ⟨N, fun j hj => ?_⟩
      by_contra hj'
      exact (hcon j hj).not_ge (hnohit j hj')
    have hreal := laneC1R_le_of_frequently ENNReal.toReal_nonneg hfreq
    rw [add_zero] at hreal
    exact (ENNReal.toReal_le_toReal hgfin hffin).mp hreal

end SupercriticalLQGUniqueness.B2.DG20Conc
