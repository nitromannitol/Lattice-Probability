/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.InfimumFour at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.FixedBandUpperBound




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

private theorem le_inf_add_of_forall {α : Type*} (x K : ℝ≥0∞)
    (f : α → ℝ≥0∞) (H : ∀ i, x ≤ f i + K) :
    x ≤ (⨅ i, f i) + K := by
  rw [ENNReal.iInf_add]
  exact le_iInf H

theorem le_four_iInf {α β γ δ : Type*} (x : ℝ≥0∞)
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (h : γ → ℝ≥0∞) (k : δ → ℝ≥0∞)
    (H : ∀ a b c d, x ≤ f a + g b + h c + k d) :
    x ≤ (⨅ a, f a) + (⨅ b, g b) + (⨅ c, h c) + (⨅ d, k d) := by
  have h3 (a : α) (b : β) (c : γ) :
      x ≤ f a + g b + h c + (⨅ d, k d) := by
    have hh := le_inf_add_of_forall x (f a+g b+h c) k (fun d => by
      simpa only [add_assoc, add_comm, add_left_comm] using H a b c d)
    simpa only [add_assoc, add_comm, add_left_comm] using hh
  have h2 (a : α) (b : β) :
      x ≤ f a + g b + (⨅ c, h c) + (⨅ d, k d) := by
    have hh := le_inf_add_of_forall x (f a+g b+(⨅ d, k d)) h (fun c => by
      simpa only [add_assoc, add_comm, add_left_comm] using h3 a b c)
    simpa only [add_assoc, add_comm, add_left_comm] using hh
  have h1 (a : α) :
      x ≤ f a + (⨅ b, g b) + (⨅ c, h c) + (⨅ d, k d) := by
    have hh := le_inf_add_of_forall x (f a+(⨅ c, h c)+(⨅ d, k d)) g
      (fun b => by simpa only [add_assoc, add_comm, add_left_comm] using h2 a b)
    simpa only [add_assoc, add_comm, add_left_comm] using hh
  have hh := le_inf_add_of_forall x
    ((⨅ b, g b)+(⨅ c, h c)+(⨅ d, k d)) f
    (fun a => by simpa only [add_assoc, add_comm, add_left_comm] using h1 a)
  simpa only [add_assoc, add_comm, add_left_comm] using hh

theorem le_mul_four_iInf {α β γ δ : Type*} (x c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (h : γ → ℝ≥0∞) (k : δ → ℝ≥0∞)
    (H : ∀ a b d e, x ≤ c * (f a + g b + h d + k e)) :
    x ≤ c * ((⨅ a, f a) + (⨅ b, g b) +
      (⨅ d, h d) + (⨅ e, k e)) := by
  have hbase := le_four_iInf x (fun a => c*f a) (fun b => c*g b)
    (fun d => c*h d) (fun e => c*k e) (fun a b d e => by
      simpa only [mul_add] using H a b d e)
  rw [← ENNReal.mul_iInf_of_ne hc0 hct,
      ← ENNReal.mul_iInf_of_ne hc0 hct,
      ← ENNReal.mul_iInf_of_ne hc0 hct,
      ← ENNReal.mul_iInf_of_ne hc0 hct] at hbase
  simpa only [mul_add] using hbase


end SupercriticalLQGUniqueness.Exponent.InwardMap
