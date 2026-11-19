import Mathlib

/-!
# Almost sure eventual statements along a subsequence

Two small measure-theoretic facts used to pass between "in probability" and "almost surely along a
subsequence" without any measurability assumption on the bad events.

* `exists_strictMono_ae_eventually_notMem_of_tendsto_measure`: if the *outer* measures of arbitrary sets
  `B n` tend to `0`, then along some subsequence almost every point lies in only finitely many `B (φ k)`
  (first Borel-Cantelli lemma; countable subadditivity of the outer measure needs no measurability).
* `exists_eps_measure_compl_le_of_ae_eventually_subseq`: reverse Fatou for a family of **measurable**
  events `M ε`: if along every positive sequence tending to `0` there is a subsequence along which `M`
  holds almost surely eventually, then `P (M ε)ᶜ` is small for all small `ε`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace LatticeProb

/-- **First Borel-Cantelli along a subsequence, for arbitrary sets.** If `μ (B n) → 0` (outer measure of
arbitrary sets), there is a strictly increasing `φ` such that almost every point lies in `B (φ k)` for only
finitely many `k`. -/
theorem exists_strictMono_ae_eventually_notMem_of_tendsto_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℕ → Set Ω) (h : Tendsto (fun n => μ (B n)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ B (φ k) := by
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop, μ (B n) < (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    h.eventually (gt_mem_nhds (ENNReal.pow_pos (by simp) k))
  obtain ⟨φ, hφ, hφk⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hsum : ∑' k, μ (B (φ k)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k) ?_
      (ENNReal.tsum_le_tsum fun k => (hφk k).le)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have h0 : μ (limsup (fun k => B (φ k)) atTop) = 0 := measure_limsup_atTop_eq_zero hsum
  have hae := (measure_eq_zero_iff_ae_notMem.1 h0)
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem] at hω
  simpa [Filter.not_frequently] using hω

/-- **Reverse Fatou, primitive form.** If measurable events `A n` hold almost surely eventually, then
`P (A n)ᶜ → 0`. -/
theorem tendsto_measure_compl_of_ae_eventually {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n) :
    Tendsto (fun n => P (A n)ᶜ) atTop (𝓝 0) := by
  set B : ℕ → Set Ω := fun n => ⋃ k ≥ n, (A k)ᶜ with hB
  have hBmeas : ∀ n, MeasurableSet (B n) := fun n =>
    MeasurableSet.biUnion (Set.to_countable _) fun k _ => (hA k).compl
  have hBanti : Antitone B := by
    intro m n hmn x hx
    simp only [hB, Set.mem_iUnion] at hx ⊢
    obtain ⟨k, hk, hx⟩ := hx
    exact ⟨k, hmn.trans hk, hx⟩
  have hlim : Tendsto (P ∘ B) atTop (𝓝 (P (⋂ n, B n))) :=
    tendsto_measure_iInter_atTop (fun n => (hBmeas n).nullMeasurableSet) hBanti
      ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n, B n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro ω hω
    simp only [Set.mem_iInter, hB, Set.mem_iUnion] at hω
    show ¬ ∀ᶠ n in atTop, ω ∈ A n
    rw [not_eventually, frequently_atTop]
    intro n
    obtain ⟨k, hk, hωk⟩ := hω n
    exact ⟨k, hk, hωk⟩
  rw [hnull] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le) ?_
  intro n
  exact measure_mono fun x hx => by
    simp only [hB, Set.mem_iUnion]
    exact ⟨n, le_refl n, hx⟩

/-- **Reverse Fatou along subsequences.** Let `M ε` be measurable events. If along every positive sequence
`e n → 0` there is a subsequence `e (φ n)` along which `M` holds almost surely eventually, then for every
`θ > 0` the complement `(M ε)ᶜ` has probability at most `θ` for all small `ε`. -/
theorem exists_eps_measure_compl_le_of_ae_eventually_subseq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (M : ℝ → Set Ω)
    (hM : ∀ ε, 0 < ε → MeasurableSet (M ε))
    (h : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ M (e (φ n)))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → P (M ε)ᶜ ≤ ENNReal.ofReal θ := by
  by_contra hcon
  push Not at hcon
  choose e he0 he1 hePM using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hetend : Tendsto e atTop (𝓝 0) :=
    squeeze_zero (fun n => (he0 n).le) (fun n => (he1 n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, hae⟩ := h e he0 hetend
  have ht := tendsto_measure_compl_of_ae_eventually P (fun n => M (e (φ n)))
    (fun n => hM _ (he0 _)) hae
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  exact absurd (hePM (φ n)) (not_lt.2 hn.le)

end LatticeProb
