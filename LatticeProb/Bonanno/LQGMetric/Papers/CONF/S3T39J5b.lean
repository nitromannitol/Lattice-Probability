/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J5b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39I4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J5a
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasF
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iCond
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9: `T39IterData'` from Lemma 3.7 with a.s. inputs (DEC-120 §5, packet J5)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1543–1556 (iteration), C:1588 (choice of `N₀`), C:1595–1617 (conditioning on `𝓕_k` and the kill
step). **`t39j_iterData_of`** is a copy-and-adapt of `t39i_iterData_of` (P2-CONFT39c, S3T39I4) for
the inputs of `T39JRestData` (D120 §5) on a **complete** probability space (DV-D120-4):

* the recursion `s_{k+1} = σ^{ε_k}_{s_k,𝕣}` holds only a.s. (no events `Cs k`); the event `G` of
  Lemma 3.7 (an a.s. event of `σ(𝓑^•_{σ^{ε_k}}, h|)`) is moved to `σ(𝓑^•_{s_{k+1}}, h|)` by the
  a.s. trace lemma `t39j_inter_localSigma0_ae` (S3T39J5a) on an event `F'` of `𝓕_{k+1}` a.s.
  equal to `{ε_k < 1}`;
* `𝓕_k ⊆ 𝓕_{k+1}` and the measurability of `n_k`, `x_{k,i}`, `Act k i` hold up to null sets; the
  filtration is `𝓕 k := gmAESigma σ(𝓑^•_{s_k}, h| mod const) P` (D98 (b), GM l. 2189), and Lemma
  3.7 is applied to measurable versions `n'_k`, `x'_{k,i}` (equal a.s., which is all the kill step
  needs);
* `σ(𝓑^•_{s_k}, h|) ≤ mΩ` is derived from `[P.IsComplete]` and `Measurable (s k)`
  (`gm_hullSigma_filledBall_le`, L47MeasF).
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Classical in
/-- **`T39IterData'` from Lemma 3.7, a.s. inputs, complete space** (C:1595–1617; module
docstring). Copy-and-adapt of `t39i_iterData_of` (S3T39I4). -/
theorem t39j_iterData_of {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {χ α C₀ a : ℝ} {N₀ : ℕ} (hL : T39HL37 γ D c p α C₀) (hDm : Measurable D) {Ω : Type}
    [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] [P.IsComplete]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {z₀ : ℂ} {R : ℝ} (hR : 0 < R) (ha : 0 < a) {ι : Type} [Fintype ι]
    (I₀ : ι → Ω → Set ℂ) (τ : Ω → ℝ) (s : ℕ → Ω → ℝ) (n : ℕ → Ω → ℕ)
    (x : ℕ → ι → Ω → ℂ) (Act : ℕ → ι → Set Ω)
    (hI₀ : ∀ i ω, I₀ i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)))
    (hs0 : ∀ ω, s 0 ω = τ ω)
    (hsucc : ∀ k, ∀ᵐ ω ∂P, ENNReal.ofReal (s (k + 1) ω) = confSigma (xiGamma γ) c D P h p z₀ R
        ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) (s k ω) ω)
    (hn : ∀ k ω, n k ω = (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty).card)
    (hsnn : ∀ k ω, 0 ≤ s k ω) (hsm : ∀ k, Measurable (s k))
    (hst : ∀ k, IsFilledBallStoppingTimeAE P D h z₀ (s k))
    (hloc : ∀ k, IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (s k ω)))
    (hmono : ∀ k, ∀ A : Set Ω,
      MeasurableSet[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))] A →
      AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s (k + 1) ω))) A)
    (hnm : ∀ k, ∃ g : Ω → ℕ,
      Measurable[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))] g ∧ n k =ᵐ[P] g)
    (hxm : ∀ k i, ∃ g : Ω → ℂ,
      Measurable[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))] g ∧
        x k i =ᵐ[P] g)
    (hxf : ∀ k i, ∀ᵐ ω ∂P, x k i ω ∈ frontier (filledBall (D (h ω)) z₀ (s k ω)))
    (hActm : ∀ k i,
      AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))) (Act k i))
    (hAct : ∀ k i ω, ω ∈ Act k i → 1 ≤ t39gExp (n k ω) ∧
      (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧
      x k i ω ∈ frontier (filledBall (D (h ω)) z₀ (s k ω)) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < (2 : ℝ)⁻¹ ^ t39gExp (n k ω) * R ∧
        DisconnectsFromInfty (filledBall (D (h ω)) z₀ (s k ω)) (ball (x k i ω) ρ)
          (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)))
    (hstar : ∀ᵐ ω ∂P, ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k,
      s k ω < tauR D h z₀ (3 * R) ω → N₀ ≤ n k ω → 4 * (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧ ω ∉ Act k i).card ≤ n k ω)
    (hgood : ∀ᵐ ω ∂P, 0 < τ ω ∧ tauR D h z₀ R ω ≤ τ ω ∧
      (∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w) ∧
      ∀ s' : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s'))
    (hN₀ : ∀ m : ℕ, N₀ ≤ m → 7 * ((2 : ℝ)⁻¹ ^ t39gExp m) ^ (1 / 2 : ℝ) ≤ a) :
    T39IterData' γ D c p χ α C₀ a N₀ P h z₀ R I₀ τ := by
  set 𝓕₀ : ℕ → MeasurableSpace Ω := fun k =>
    filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)) with h𝓕₀
  have h𝓕eq : ∀ k, filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)) =
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω)) :=
    fun k => t39h_fbs0_eq D h z₀ (hsnn k)
  -- `σ(𝓑^•_{s_k}, h|) ≤ mΩ` on a complete space
  have hsub : ∀ k, localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω)) ≤ m0 := fun k =>
    (localSigma0_le_localSigma h _).trans ((iInf_le _ 0).trans
      (gm_hullSigma_filledBall_le (P := P) hh (hDm.comp hh.measurable) (hsm k) z₀ 0))
  have hle : ∀ k, 𝓕₀ k ≤ m0 := fun k => le_of_eq_of_le (h𝓕eq k) (hsub k)
  -- measurable versions
  choose n' hn'm hnn' using hnm
  choose x' hx'm hxx' using hxm
  set g : ℕ → ℝ := fun m => if 1 ≤ t39gExp m then (2 : ℝ)⁻¹ ^ t39gExp m else 1 / 2 with hg
  set e : ℕ → Ω → ℝ := fun k ω => g (n' k ω) with he
  have hem : ∀ k, Measurable[localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω))] (e k) :=
    fun k => by
      have := hn'm k
      rw [h𝓕eq k] at this
      exact (measurable_from_nat (f := g)).comp this
  have he01 : ∀ k ω, e k ω ∈ Ioo 0 1 := fun k ω => by
    simp only [he, hg]
    split_ifs with h1
    · exact ⟨by positivity, pow_lt_one₀ (by norm_num) (by norm_num) (by omega)⟩
    · norm_num
  have hec : ∀ k, (Set.range (e k)).Countable := fun k =>
    (Set.countable_range g).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨n' k ω, rfl⟩)
  have hx'm' : ∀ k i,
      Measurable[localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω))] (x' k i) :=
    fun k i => by have := hx'm k i; rw [h𝓕eq k] at this; exact this
  have hxf' : ∀ k i, ∀ᵐ ω ∂P, x' k i ω ∈ frontier (filledBall (D (h ω)) z₀ (s k ω)) :=
    fun k i => by filter_upwards [hxf k i, hxx' k i] with ω h1 h2; rwa [← h2]
  choose G hGae hGA hGB using fun k i => hL P h hh z₀ R hR (s k) (hst k) (hloc k) (hsub k)
    (x' k i) (e k) (hx'm' k i) (hem k) (hxf' k i) (he01 k) (hec k)
  choose G₀ hG₀m hGG₀ using hGae
  -- the events `{ε_k < 1}`
  set E : ℕ → Set Ω := fun k => {ω | 1 ≤ t39gExp (n k ω)} with hE
  set E' : ℕ → Set Ω := fun k => {ω | 1 ≤ t39gExp (n' k ω)} with hE'
  have hE'm : ∀ k, MeasurableSet[𝓕₀ k] (E' k) := fun k =>
    hn'm k (MeasurableSet.of_discrete (s := {m : ℕ | 1 ≤ t39gExp m}))
  have hEE' : ∀ k, E k =ᵐ[P] E' k := fun k => by
    filter_upwards [hnn' k] with ω hω
    show (1 ≤ t39gExp (n k ω)) = (1 ≤ t39gExp (n' k ω))
    rw [hω]
  have heE : ∀ k ω, ω ∈ E' k → e k ω = (2 : ℝ)⁻¹ ^ t39gExp (n' k ω) := fun k ω hω => by
    simp only [he, hg]; exact ite_eq_left_iff.2 fun h => absurd hω h
  choose F' hF'm hE'F' using fun k => hmono k _ (hE'm k)
  -- `G ∩ E` is an a.s. event of `𝓕_{k+1}` (a.s. trace on `F'`)
  have hG₀F : ∀ k i, AEEventIn P (𝓕₀ (k + 1)) (G₀ k i ∩ F' k) := fun k i => by
    refine t39j_inter_localSigma0_ae P h
      (A := fun ω => filledBallE (D (h ω)) z₀
        (confSigma (xiGamma γ) c D P h p z₀ R (e k ω) (s k ω) ω))
      (A' := fun ω => filledBallE (D (h ω)) z₀ (ENNReal.ofReal (s (k + 1) ω)))
      (fun ω => p412i_filledBallE_isClosed _ _ _) (hF'm k) ?_ (hG₀m k i)
    filter_upwards [hsucc k, hnn' k, hE'F' k] with ω h1 h2 h3 hωF
    have hωE' : ω ∈ E' k := by
      have h3' : (ω ∈ E' k) = (ω ∈ F' k) := h3
      rw [h3']; exact hωF
    show filledBallE _ _ _ = filledBallE _ _ _
    rw [heE k ω hωE', ← h2, h1]
  set Gk : ℕ → ι → Set Ω := fun k i => G k i ∩ E k with hGk
  have hGkF : ∀ k i, Gk k i =ᵐ[P] G₀ k i ∩ F' k := fun k i =>
    Filter.EventuallyEqSet.inter (hGG₀ k i) ((hEE' k).trans (hE'F' k))
  have hGkae : ∀ k i, AEEventIn P (𝓕₀ (k + 1)) (Gk k i) := fun k i => by
    obtain ⟨B, hB, hGB'⟩ := hG₀F k i
    exact ⟨B, hB, (hGkF k i).trans hGB'⟩
  set 𝓕 : ℕ → MeasurableSpace Ω := fun k => gmAESigma (𝓕₀ k) P with h𝓕
  have hGkm : ∀ k i, MeasurableSet[𝓕 (k + 1)] (Gk k i) := fun k i =>
    p412i_aeSigma_of_aeEventIn _ (hle (k + 1)) (hGkae k i)
  have hGkm0 : ∀ k i, MeasurableSet[m0] (Gk k i) := fun k i =>
    gm_aeSigma_le (mΩ := m0) (μ := P) (𝓕₀ (k + 1)) _ (hGkm k i)
  refine ⟨s, n, 𝓕, Act, Gk, hI₀, hs0, hsucc, hn,
    monotone_nat_of_le_succ fun k => p412i_aeSigma_mono fun A hA =>
      p412i_aeSigma_of_aeEventIn _ (hle (k + 1)) (hmono k A hA),
    fun k => gm_aeSigma_le _, fun k => @measurable_to_countable' ℕ Ω _ _ (𝓕 k) (n k) fun j =>
      p412i_aeSigma_of_aeEventIn _ (hle k) ⟨n' k ⁻¹' {j}, hn'm k (MeasurableSet.of_discrete), by
        filter_upwards [hnn' k] with ω hω
        simp only [mem_preimage, mem_singleton_iff, hω]⟩,
    fun k i => p412i_aeSigma_of_aeEventIn _ (hle k) (hActm k i), hGkm, fun k i => ?_,
    fun k i ω hω => (hAct k i ω hω).2.1, hstar, ?_⟩
  · -- (3.24)
    have hE'm' : MeasurableSet[localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω))]
        (E' k) := (h𝓕eq k).le _ (hE'm k)
    have h1 := gm_condExp_ae_eq_aeSigma (μ := P) (hle k)
      (f := (Gk k i).indicator fun _ => (1 : ℝ))
      ((integrable_const (1 : ℝ)).indicator (hGkm0 k i))
    have h2 : P[(Gk k i).indicator (fun _ => (1 : ℝ)) | 𝓕₀ k] =ᵐ[P]
        P[(E' k).indicator ((G k i).indicator fun _ => (1 : ℝ)) |
          localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω))] := by
      rw [← h𝓕eq k]
      refine condExp_congr_ae ?_
      rw [Set.indicator_indicator, Set.inter_comm]
      exact indicator_ae_eq_of_ae_eq_set
        (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl (hEE' k))
    have h12 := h1.symm.trans h2
    by_cases hint : Integrable ((G k i).indicator fun _ => (1 : ℝ)) P
    · filter_upwards [h12, condExp_indicator hint hE'm', hGB k i, hnn' k] with ω h0 h3 h4 h5 hωA
      have hωE : ω ∈ E' k := by
        have := (hAct k i ω hωA).1
        simp only [hE', mem_ofPred_eq, ← h5]; exact this
      show _ ≤ P[(Gk k i).indicator (fun _ => (1 : ℝ)) | 𝓕 k] ω
      rw [h0, h3, Set.indicator_of_mem hωE]
      rw [heE k ω hωE, ← h5] at h4
      exact h4
    · have h0 : P[(G k i).indicator (fun _ => (1 : ℝ)) |
          localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω))] = 0 :=
        condExp_of_not_integrable hint
      have hnn := condExp_nonneg (μ := P) (m := 𝓕 k)
        (f := (Gk k i).indicator fun _ => (1 : ℝ))
        (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      filter_upwards [hGB k i, hnn, hnn' k] with ω h3 h4 h5 hωA
      rw [h0] at h3
      have hωE : ω ∈ E' k := by
        have := (hAct k i ω hωA).1
        simp only [hE', mem_ofPred_eq, ← h5]; exact this
      rw [heE k ω hωE, ← h5] at h3
      exact h3.trans h4
  · -- the kill step
    have hxall : ∀ᵐ ω ∂P, ∀ k i, x k i ω = x' k i ω :=
      ae_all_iff.2 fun k => ae_all_iff.2 fun i => hxx' k i
    filter_upwards [hgood, ae_all_iff.2 hsucc, ae_all_iff.2 hnn', hxall] with ω hgω hsω hnω hxω
    intro hω k hk3 hN i hωA hωG
    obtain ⟨hτ0, hτR, hgeo, hbd⟩ := hgω
    obtain ⟨hE1, -, hxk, ρ, hρ0, hρ, hdis⟩ := hAct k i ω hωA
    have hτs : τ ω ≤ s k ω := by
      have := t39h_le_iter (ξ := xiGamma γ) (cc := c) (D := D) (P := P) (h := h) (p := p)
        (z₀ := z₀) (R := R) (s := s) (e := fun k ω => (2 : ℝ)⁻¹ ^ t39gExp (n k ω)) (ω := ω)
        (by rw [hs0]; exact hτ0) hsω k
      rwa [hs0] at this
    have hA : T39HPropA γ D c p P h z₀ R (s k) (x' k i) (e k) ω := hGA k i ω hωG.1
    have hm := hN₀ _ hN
    have hωE' : ω ∈ E' k := by
      simp only [hE', mem_ofPred_eq, ← hnω k]; exact hE1
    have hee : e k ω = (2 : ℝ)⁻¹ ^ t39gExp (n k ω) := by rw [heE k ω hωE', ← hnω k]
    have hσ : confSigma (xiGamma γ) c D P h p z₀ R ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) (s k ω) ω =
        ENNReal.ofReal (s (k + 1) ω) := (hsω k).symm
    rw [hxω k i] at hxk hdis
    exact t39h_kill_of_propA (γ := γ) (D := D) (c := c) (p := p) (P := P) (h := h) (χ := χ)
      (z₀ := z₀) (R := R) (a := a) (ω := ω) (m := t39gExp (n k ω)) (s := s k) (x := x' k i)
      (e := e k) (τ := τ ω) (t' := s (k + 1) ω) (I := I₀ i ω) (ρ := ρ) hω hR ha hm hee hτ0 hτs
      (hτR.trans hτs) hk3 hσ hgeo hbd (hI₀ i ω) hxk hρ0 hρ hdis hA

end CONF
end LQGMetric
