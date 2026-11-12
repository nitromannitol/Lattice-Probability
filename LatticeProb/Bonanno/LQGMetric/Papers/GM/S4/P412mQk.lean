/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412mQk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hQk2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412mSel

/-!
# The guard centres of GM L4.15 Step 3, a.s. on the boundary (decision D106, part 2)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3, l. 2155–2183 (the
points `z_y ∈ ∂𝓑^•_{t_k}`, `y ∈ 𝒴_k`, with (∗), chosen depending only on `(𝓑^•_{t_k}, h|)`);
GM.S4.1 (l. 1648–1654); decisions D98 §2, D106.

**`p412m_centres`**: the proof of `p412h_centres` (P412hQk2.lean) with the grid centres of
`p412m_grid_centres`, so without the hypothesis that `𝓑^•_{t_k}` is bounded at *every* `ω`: the
`2L` centres are surely `σ(𝓑^•_{t_k}, h|)`-measurable, lie on `∂𝓑^•_{t_k}` **a.s.** (where
`D_h ∈ lenSet`, `ae_mem_lenSet`), and a.s. on `{#Conf_k ≤ L}` cover `𝒴_k` in the sense (∗).
This is the a.s. form of `P412jCentres` (DV-D106), proved for every weak LQG metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology Bornology
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **P-Qk, a.s. form** (D106): measurable guard centres, a.s. on `∂𝓑^•_{t_k}`, covering `𝒴_k`
in the sense (∗), for every weak LQG metric -/
theorem p412m_centres (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c₀)
    (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β κ : ℝ} (hℓ𝕣 : 0 < ℓ * 𝕣) (h𝕣 : 0 < 𝕣)
    (hε : 0 < ε) (hβ : 0 ≤ β) (k L : ℕ) :
    ∃ x : ℕ → Ω → ℂ,
      (∀ j, @Measurable Ω ℂ (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)) _ (x j)) ∧
      (∀ᵐ ω ∂P, ∀ j, x j ω ∈ frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω))) ∧
      ∀ᵐ ω ∂P, (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω)
          (s4T D h 𝕫 ℓ 𝕣 ε β k ω)).encard ≤ L →
        ∀ e ∈ p412fEndSet (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω),
          ∃ j < 2 * L, ∃ z : ℂ,
            p412eGoodZ (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω)) e z (ε ^ κ * 𝕣) ∧
            dist z (x j ω) ≤ ε ^ κ * 𝕣 := by
  classical
  set R := ℓ * 𝕣
  set c₁ : ℝ := 1 + k * ε ^ β
  set ck : ℝ := 1 + k * ε ^ β + ε ^ (2 * β)
  have h1 : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hk : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) h1
  have hck : 1 < ck := show 1 < 1 + (k : ℝ) * ε ^ β + ε ^ (2 * β) by linarith
  have hlt : c₁ < ck := show 1 + (k : ℝ) * ε ^ β < 1 + (k : ℝ) * ε ^ β + ε ^ (2 * β) by linarith
  have hc₁ : c₁ ≤ ck := hlt.le
  have hc₁0 : 0 < c₁ := show 0 < 1 + (k : ℝ) * ε ^ β by linarith
  have hS : ∀ ω, s4S D h 𝕫 ℓ 𝕣 ε β k ω = tauD (D (h ω)) 𝕫 R * c₁ := gm_s4S_eq D h 𝕫 ℓ 𝕣 ε β k
  have hT : ∀ ω, s4T D h 𝕫 ℓ 𝕣 ε β k ω = tauD (D (h ω)) 𝕫 R * ck := gm_s4T_eq D h 𝕫 ℓ 𝕣 ε β k
  set ε' := ε ^ κ * 𝕣 with hε'def
  have hε' : 0 < ε' := mul_pos (Real.rpow_pos_of_pos hε κ) h𝕣
  set K : Ω → Set ℂ := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) with hKdef
  have hKeq : K = fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * ck) := by
    funext ω; simp only [hKdef, hT]
  set g : ℕ → ℂ := fun i => p412hG ε' (Denumerable.ofNat (ℤ × ℤ) i) with hgdef
  have hginj : Function.Injective g := (p412h_G_inj hε'.ne').comp
    (Denumerable.eqv (ℤ × ℤ)).symm.injective
  set Q : Ω → Set ℕ := fun ω => {i | (confPts (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * c₁)
    (tauD (D (h ω)) 𝕫 R * ck)).encard ≤ L ∧ D (h ω) ∈ p412hXq 𝕫 R c₁ ck ε' (g i)} with hQdef
  -- membership events
  have hQ : ∀ i, AEEventIn P (localSigma h K) {ω | i ∈ Q ω} := by
    intro i
    obtain ⟨F₁, hF₁, hE₁⟩ := p412i_confCount_aeEventIn h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hc₁ hck (L + 1)
    obtain ⟨F₂, hF₂, hE₂⟩ := p412h_Xq_aeEventIn h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hc₁ hck hε' (g i)
    refine ⟨F₁ᶜ ∩ F₂, ?_, ?_⟩
    · rw [hKeq]; exact hF₁.compl.inter hF₂
    · have e : {ω | i ∈ Q ω} = {ω | ((L + 1 : ℕ) : ℕ∞) ≤ (confPts (D (h ω)) 𝕫
          (tauD (D (h ω)) 𝕫 R * c₁) (tauD (D (h ω)) 𝕫 R * ck)).encard}ᶜ ∩
          {ω | D (h ω) ∈ p412hXq 𝕫 R c₁ ck ε' (g i)} := by
        ext ω
        simp only [hQdef, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_le, Nat.cast_add,
          Nat.cast_one]
        rw [ENat.lt_add_one_iff (ENat.natCast_ne_top L)]
      rw [e]
      exact hE₁.compl.inter hE₂
  -- the a.s. events
  have hS41 := gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hpos : ∀ ω, 0 < tauD (D (h ω)) 𝕫 R * c₁ ∧ tauD (D (h ω)) 𝕫 R * c₁ < tauD (D (h ω)) 𝕫 R * ck :=
    fun ω => ⟨mul_pos (gm_tauD_pos _ 𝕫 hℓ𝕣) hc₁0, mul_lt_mul_of_pos_left hlt (gm_tauD_pos _ 𝕫 hℓ𝕣)⟩
  have hYeq : ∀ᵐ ω ∂P, p412fEndSet (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * c₁)
      (tauD (D (h ω)) 𝕫 R * ck) = p412hYk (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * c₁)
      (tauD (D (h ω)) 𝕫 R * ck) := by
    filter_upwards [hS41] with ω hω
    obtain ⟨hfin, harc, hdis, hcov⟩ := hω _ _ (hpos ω).1 (hpos ω).2
    exact p412h_endSet_eq hfin harc hdis hcov
  have hN : ∀ᵐ ω ∂P, (Q ω).encard ≤ ((2 * L : ℕ) : ℕ∞) := by
    filter_upwards [hS41, hlen, hYeq] with ω hω hl hY
    obtain ⟨-, harc, -, -⟩ := hω _ _ (hpos ω).1 (hpos ω).2
    set d := D (h ω)
    set t := tauD d 𝕫 R * ck
    by_cases hC : (confPts d 𝕫 (tauD d 𝕫 R * c₁) t).encard ≤ L
    · have hsub : Q ω ⊆ g ⁻¹' ((fun e => p412hGd (filledBall d 𝕫 t) e ε') ''
          p412hYk d 𝕫 (tauD d 𝕫 R * c₁) t) := by
        rintro i ⟨-, e, he, hq⟩
        exact ⟨e, he, hq⟩
      have ht : 0 < t := lt_trans (hpos ω).1 (hpos ω).2
      have hbd : IsBounded (ballM d 𝕫 t) :=
        (gm_filledBall_isBounded_of_lenSet hl 𝕫 _).subset fun w hw => Or.inl (subset_closure hw)
      have hE := p412f_endSet_encard ht (isLength_of_mem_lenSet hl) hbd harc
      rw [hY] at hE
      calc (Q ω).encard ≤ (g ⁻¹' ((fun e => p412hGd (filledBall d 𝕫 t) e ε') ''
            p412hYk d 𝕫 (tauD d 𝕫 R * c₁) t)).encard := encard_le_encard hsub
        _ = (g '' (g ⁻¹' ((fun e => p412hGd (filledBall d 𝕫 t) e ε') ''
            p412hYk d 𝕫 (tauD d 𝕫 R * c₁) t))).encard := (hginj.encard_image _).symm
        _ ≤ ((fun e => p412hGd (filledBall d 𝕫 t) e ε') ''
            p412hYk d 𝕫 (tauD d 𝕫 R * c₁) t).encard := encard_le_encard (image_preimage_subset _ _)
        _ ≤ (p412hYk d 𝕫 (tauD d 𝕫 R * c₁) t).encard := encard_image_le _ _
        _ ≤ 2 * (confPts d 𝕫 (tauD d 𝕫 R * c₁) t).encard := hE
        _ ≤ 2 * (L : ℕ∞) := by gcongr
        _ = ((2 * L : ℕ) : ℕ∞) := by push_cast; ring
    · have : Q ω = ∅ := eq_empty_of_forall_notMem fun i hi => hC hi.1
      rw [this, encard_empty]; exact zero_le
  -- the centres
  have hz : ∀ ω, 𝕫 ∈ K ω := fun ω => jo_mem_filledBall_self (by
    show 0 < s4T D h 𝕫 ℓ 𝕣 ε β k ω
    rw [hT]; exact lt_trans (hpos ω).1 (hpos ω).2)
  obtain ⟨x, hxm, hxfr, hcov⟩ := p412m_grid_centres h K (fun ω => gm_filledBall_isClosed _ _ _)
    𝕫 hz g (8 * ε') Q hQ (2 * L) hN
  refine ⟨x, hxm, ?_, ?_⟩
  · filter_upwards [hlen] with ω hl j
    exact hxfr j ω (gm_filledBall_isBounded_of_lenSet hl 𝕫 _)
  · filter_upwards [hcov, hlen, hYeq] with ω hc hl hY
    intro hC e he
    rw [hS, hT] at hC he
    rw [hT]
    set d := D (h ω)
    set t := tauD d 𝕫 R * ck
    have ht : 0 < t := lt_trans (hpos ω).1 (hpos ω).2
    have hbd : IsBounded (ballM d 𝕫 t) :=
      (gm_filledBall_isBounded_of_lenSet hl 𝕫 _).subset fun w hw => Or.inl (subset_closure hw)
    have hefr : e ∈ frontier (filledBall d 𝕫 t) := by
      obtain ⟨x', -, he'⟩ := mem_iUnion₂.1 he
      exact isClosed_frontier.closure_subset (closure_mono sdiff_subset he'.2)
    have heY : e ∈ p412hYk d 𝕫 (tauD d 𝕫 R * c₁) t := by rw [← hY]; exact he
    obtain ⟨m, hm⟩ := p412h_gd_grid (filledBall d 𝕫 t) e ε'
    set i := Encodable.encode m with hidef
    have hgi : g i = p412hG ε' m := by
      simp only [hgdef, hidef]
      rw [show (Denumerable.ofNat (ℤ × ℤ) (Encodable.encode m)) = m from Denumerable.ofNat_encode m]
    have hiQ : i ∈ Q ω := ⟨hC, e, heY, by rw [hgi]; exact hm⟩
    obtain ⟨j, hj, hjB₀⟩ := hc i hiQ
    have hjB := hjB₀ (gm_filledBall_isBounded_of_lenSet hl 𝕫 _)
    have hjB' : (frontier (filledBall d 𝕫 t) ∩
        closedBall (p412hGd (filledBall d 𝕫 t) e ε') (8 * ε')).Nonempty →
        x j ω ∈ closedBall (p412hGd (filledBall d 𝕫 t) e ε') (8 * ε') := by
      have hK : K ω = filledBall d 𝕫 t :=
        show filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω) = filledBall d 𝕫 t from
          congrArg _ (hT ω)
      rw [hm, ← hgi, ← hK]
      exact hjB
    refine ⟨j, hj, x j ω, ?_, by rw [dist_self]; exact hε'.le⟩
    exact p412h_goodZ_filled ht (isLength_of_mem_lenSet hl) hbd hefr hε' (x j ω) hjB'

end LQGMetric.GM
