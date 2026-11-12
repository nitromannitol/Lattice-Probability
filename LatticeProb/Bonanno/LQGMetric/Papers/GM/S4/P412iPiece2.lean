/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iPiece2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iPiece
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3GeoC

/-!
# CONF l. 1302 / GM l. 2189: events of `σ^ε_{t,𝕣}` are piecewise local for `𝓑^•_{τ c_T}`

Source: CONF (arXiv:1905.00381, `confluence-final.tex`) l. 1300–1302 ("if `τ` is a stopping time
for `{(𝓑^•_t, h|_{𝓑^•_t})}`, then so is `σ^ε_{τ,𝕣}`"), used in GM (arXiv:1905.00383v3) L4.15
Step 4, l. 2189 ("The radius `σ_k` is a stopping time … so the event … belongs to
`σ(𝓑^•_{s_{k+1}}, h|_{𝓑^•_{s_{k+1}}})`"); decision D98 (b2), packet P-stop.

**`p412i_sig_piece`**: let `τ = τ_R(D_h)`, `t = τ c_t`, `σ = confSigma … δ t`, and `Θ(d, τ, x)` a
predicate with `Θ ⇒ x ≤ τ c_s` (`c_s < c_T`), stable under agreement of the filled balls up to
`τ c_T`, and Borel in (metric, coded events). Given CONF l. 1260 (`P412iEDet`), the event
`{Θ(D_h, τ, σ)}` is piecewise local (`gmPieceSig`) for `𝓑^•_{τ c_T}`. Proof: piece method with the
field coordinate `e(h|_U)` coding the local versions of the visible events `E_r(z)`
(`cl B_{5r}(z) ⊆ U`), the saturation `p412i_sig_congr` (CONF l. 1300: `𝓑^•_σ ⊇ B_{6ρ(z)}(z)`) and
the measurability `P412iBorel`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

theorem p412i_center_mem (d : ContMetric) (z : ℂ) {s : ℝ} (hs : 0 < s) : z ∈ filledBall d z s :=
  Or.inl (subset_closure (jb_mem_ballM d z s hs))

/-- **piecewise locality of the events of `σ^δ_{t,𝕣}`** (CONF l. 1302, GM l. 2189) -/
theorem p412i_sig_piece (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (ξ : ℝ) (cc : ℝ → ℝ)
    (p : CONFParams) (hEDet : P412iEDet ξ cc D P h p) (𝕫 : ℂ) {R ct cs cT 𝕣 δ : ℝ}
    (hR : 0 < R) (hct : 0 < ct) (hcs : ct ≤ cs) (hcT : cs < cT) (hcT1 : 1 < cT)
    (hδ : 0 < δ * 𝕣) (Θ : ContMetric → ℝ → ℝ≥0∞ → Prop)
    (hΘT : ∀ d τ x, Θ d τ x → x ≤ ENNReal.ofReal (τ * cs))
    (hΘsat : ∀ d₁ d₂ τ x, (∀ u ≤ τ * cT, filledBall d₂ 𝕫 u = filledBall d₁ 𝕫 u) →
      x < ENNReal.ofReal (τ * cT) → Θ d₁ τ x → Θ d₂ τ x)
    (hΘm : MeasurableSet {q : ContMetric × (ℤ × ℤ × ℤ → Bool) | Θ q.1 (gmTauB 𝕫 R q.1)
      (p412iSig q.1 𝕫 (p412iEe (δ * 𝕣) (δ * 𝕣 / 4) q.2) (confN p δ) 𝕣 δ
        (gmTauB 𝕫 R q.1 * ct))})
    (n : ℕ) (fs : Finset (ℤ × ℤ)) :
    MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * cT)) n
      (hullFin n fs) P]
      {ω | Θ (D (h ω)) (tauD (D (h ω)) 𝕫 R)
        (confSigma ξ cc D P h p 𝕫 𝕣 δ (tauD (D (h ω)) 𝕫 R * ct) ω)} := by
  classical
  set S' := hullFin n fs with hS'
  set U := interior S' with hUdef
  have hUo : IsOpen U := isOpen_interior
  have hUb : Bornology.IsBounded U := (p412i_isBounded_hullFin n fs).subset interior_subset
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hτpos : ∀ d : ContMetric, 0 < tauD d 𝕫 R := fun d => gm_tauD_pos d 𝕫 hR
  have hK : ∀ d : ContMetric, (filledBall d 𝕫 (tauD d 𝕫 R * ct)).Nonempty :=
    fun d => ⟨𝕫, p412i_center_mem d 𝕫 (mul_pos (hτpos d) hct)⟩
  have htT : ∀ d : ContMetric, tauD d 𝕫 R * ct ≤ tauD d 𝕫 R * cT :=
    fun d => mul_le_mul_of_nonneg_left (by linarith) (hτpos d).le
  have hsT : ∀ d : ContMetric, ENNReal.ofReal (tauD d 𝕫 R * cs) <
      ENNReal.ofReal (tauD d 𝕫 R * cT) := fun d =>
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos (hτpos d) (by linarith))).2
      (mul_lt_mul_of_pos_left hcT (hτpos d))
  have hKU : ∀ d : ContMetric, dyadicHull n (filledBall d 𝕫 (tauD d 𝕫 R * cT)) = S' →
      filledBall d 𝕫 (tauD d 𝕫 R * cT) ⊆ U := fun d hS => by
    have := subset_interior_dyadicHull n (filledBall d 𝕫 (tauD d 𝕫 R * cT))
    rw [hS] at this; exact this
  by_cases hU : U.Nonempty
  swap
  · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigma _ _), Eventually.of_forall fun ω hS => ?_⟩
    exact absurd ⟨𝕫, hKU _ hS (p412i_center_mem _ 𝕫 (by nlinarith [hτpos (D (h ω))]))⟩ hU
  -- local versions of the visible events `E_r(z)`
  have hA : ∀ i : ℤ × ℤ × ℤ, ∃ A : Set (DistOn (toOpens U hUo)), MeasurableSet A ∧
      (closedBall (p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2) (5 * ((2 : ℝ) ^ i.1 * (δ * 𝕣))) ⊆ U →
        confE ξ cc D P h p ((2 : ℝ) ^ i.1 * (δ * 𝕣)) (p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2) =ᵐ[P]
          (fun ω => restrictTo (toOpens U hUo) (h ω)) ⁻¹' A) := by
    intro i
    by_cases hi : closedBall (p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2) (5 * ((2 : ℝ) ^ i.1 * (δ * 𝕣))) ⊆ U
    · obtain ⟨F, hF, hEF⟩ := hEDet _ (by positivity) _ U hUo hi
      obtain ⟨A, hAm, rfl⟩ := hF
      exact ⟨A, hAm, fun _ => hEF⟩
    · exact ⟨∅, MeasurableSet.empty, fun h' => absurd h' hi⟩
  choose A hAm hAE using hA
  set e' : DistOn (toOpens U hUo) → (ℤ × ℤ × ℤ → Bool) :=
    fun x i => if x ∈ A i then true else false with he'def
  have he' : Measurable e' :=
    measurable_pi_iff.2 fun i => Measurable.ite (hAm i) measurable_const measurable_const
  set eg : DistC → (ℤ × ℤ × ℤ → Bool) := fun g => e' (restrictTo (toOpens U hUo) g) with hegdef
  have heg : Measurable eg := he'.comp (measurable_restrictTo _)
  set Bs : Set DistC := {g | dyadicHull n (filledBall (D g) 𝕫 (tauD (D g) 𝕫 R * cT)) = S' ∧
    Θ (D g) (tauD (D g) 𝕫 R) (p412iSig (D g) 𝕫 (p412iEe (δ * 𝕣) (δ * 𝕣 / 4) (eg g))
      (confN p δ) 𝕣 δ (tauD (D g) 𝕫 R * ct))} with hBs
  have hHs := ((gm_uMeas_of_an (gmE_hullAn 𝕫 R cT n S')).preimage
    hD.measurable).nullMeasurableSet (P.map h)
  have hM := hΘm.preimage (hD.measurable.prodMk heg)
  have hlen' : ∀ᵐ g ∂(P.map h), D g ∈ lenSet :=
    (ae_map_iff hh.measurable.aemeasurable (measurableSet_lenSet.preimage hD.measurable)).2 hlen
  have hnull : NullMeasurableSet Bs (P.map h) := by
    refine (hHs.inter hM.nullMeasurableSet).congr ?_
    filter_upwards [hlen'] with g hg
    have e1 := gm_tauD_eq_tauB hg 𝕫 R
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, hBs, e1]
    exact propext ⟨fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨hg, h1⟩, h2⟩⟩
  obtain ⟨F, hF, hEF⟩ := p412i_piece_aug hD P h (Tight.isGFFPlusCont_of_wp hh) hlen hUo hU he'
    hnull (by
      rintro g₁ g₂ h1 h2 heq hee ⟨hS, hΘ⟩
      have l1 := isLength_of_mem_lenSet h1
      have l2 := isLength_of_mem_lenSet h2
      obtain ⟨hτ, hball⟩ := gm_tk_congr l1 l2 hcT1 hUo heq (hτpos _) (hKU _ hS)
      have hfb : ∀ u ≤ tauD (D g₁) 𝕫 R * cT, filledBall (D g₂) 𝕫 u = filledBall (D g₁) 𝕫 u :=
        fun u hu => gm_filledBall_congr (hball u hu)
      have hlt := lt_of_le_of_lt (hΘT _ _ _ hΘ) (hsT (D g₁))
      have hσ := p412i_sig_congr (E₁ := p412iEe (δ * 𝕣) (δ * 𝕣 / 4) (eg g₁))
        (E₂ := p412iEe (δ * 𝕣) (δ * 𝕣 / 4) (eg g₁)) (N := confN p δ) hδ (htT _) hfb (hK _)
        (hKU _ hS) hUb (fun _ _ _ _ => Iff.rfl) hlt
      have heg' : eg g₂ = eg g₁ := hee.symm
      refine ⟨?_, ?_⟩
      · show dyadicHull n (filledBall (D g₂) 𝕫 (tauD (D g₂) 𝕫 R * cT)) = S'
        rw [hτ, hfb _ le_rfl]; exact hS
      · show Θ (D g₂) (tauD (D g₂) 𝕫 R) (p412iSig (D g₂) 𝕫 (p412iEe (δ * 𝕣) (δ * 𝕣 / 4) (eg g₂))
          (confN p δ) 𝕣 δ (tauD (D g₂) 𝕫 R * ct))
        rw [hτ, heg', hσ]
        exact hΘsat _ _ _ _ hfb hlt hΘ)
  refine ⟨F, hF, ?_⟩
  have hvis : ∀ᵐ ω ∂P, ∀ i : ℤ × ℤ × ℤ,
      closedBall (p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2) (5 * ((2 : ℝ) ^ i.1 * (δ * 𝕣))) ⊆ U →
      (ω ∈ confE ξ cc D P h p ((2 : ℝ) ^ i.1 * (δ * 𝕣)) (p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2) ↔
        restrictTo (toOpens U hUo) (h ω) ∈ A i) := by
    rw [ae_all_iff]
    intro i
    by_cases hi : closedBall (p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2) (5 * ((2 : ℝ) ^ i.1 * (δ * 𝕣))) ⊆ U
    · filter_upwards [hAE i hi] with ω hω _
      exact Iff.of_eq hω
    · exact Eventually.of_forall fun ω h' => absurd h' hi
  filter_upwards [hEF, hvis] with ω hω hv hS
  have hB := Iff.of_eq hω
  rw [← hB]
  set d := D (h ω) with hd
  set τ := tauD d 𝕫 R with hτdef
  simp only [mem_setOf_eq, mem_preimage, hBs]
  rw [p412i_confSigma_eq]
  have hQ : p412iSig d 𝕫 (fun r z => ω ∈ confE ξ cc D P h p r z) (confN p δ) 𝕣 δ (τ * ct) =
      p412iSig d 𝕫 (fun r z => ∃ i : ℤ × ℤ × ℤ, r = (2 : ℝ) ^ i.1 * (δ * 𝕣) ∧
        z = p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2 ∧ ω ∈ confE ξ cc D P h p r z)
        (confN p δ) 𝕣 δ (τ * ct) :=
    p412i_sig_congr_grid fun k a b =>
      ⟨fun h' => ⟨(k, a, b), rfl, rfl, h'⟩, fun ⟨_, _, _, h'⟩ => h'⟩
  have hE : ∀ r : ℝ, 0 < r → ∀ z, closedBall z (5 * r) ⊆ U →
      ((∃ i : ℤ × ℤ × ℤ, r = (2 : ℝ) ^ i.1 * (δ * 𝕣) ∧
        z = p412iGP (δ * 𝕣 / 4) i.2.1 i.2.2 ∧ ω ∈ confE ξ cc D P h p r z) ↔
        p412iEe (δ * 𝕣) (δ * 𝕣 / 4) (eg (h ω)) r z) := by
    intro r _ z hzU
    refine exists_congr fun i => ?_
    constructor
    · rintro ⟨hr, hz, h'⟩
      subst hr hz
      refine ⟨rfl, rfl, ?_⟩
      have := (hv i hzU).1 h'
      simp only [hegdef, he'def, this, if_true]
    · rintro ⟨hr, hz, h'⟩
      subst hr hz
      refine ⟨rfl, rfl, (hv i hzU).2 ?_⟩
      by_contra hnA
      simp only [hegdef, he'def, hnA, if_false] at h'
      exact Bool.false_ne_true h'
  constructor
  · intro hΘ
    refine ⟨hS, ?_⟩
    rw [hQ] at hΘ
    have hlt := lt_of_le_of_lt (hΘT _ _ _ hΘ) (hsT d)
    rw [p412i_sig_congr hδ (htT d) (fun _ _ => rfl) (hK d) (hKU d hS) hUb hE hlt]
    exact hΘ
  · rintro ⟨-, hΘ⟩
    have hlt := lt_of_le_of_lt (hΘT _ _ _ hΘ) (hsT d)
    rw [hQ, p412i_sig_congr hδ (htT d) (fun _ _ => rfl) (hK d) (hKU d hS) hUb
      (fun r hr z hz => (hE r hr z hz).symm) hlt]
    exact hΘ

end LQGMetric.GM
