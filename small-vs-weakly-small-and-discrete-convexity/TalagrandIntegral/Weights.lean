import TalagrandIntegral.Scales

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def nonemptySubsets (H : Finset X) : Finset (Finset X) := H.powerset.erase ∅
def subsetMass (g : Finset X → ℝ) (H : Finset X) : ℝ := ∑ S ∈ nonemptySubsets H, g S
def rawWeights (g : Finset X → ℝ) (H : Finset X) (x : X) : ℝ :=
  ∑ S ∈ nonemptySubsets H, if x ∈ S then g S / S.card else 0
def subsetWeights (g : Finset X → ℝ) (H : Finset X) (x : X) : ℝ :=
  rawWeights g H x / subsetMass g H

theorem mem_nonemptySubsets {H S : Finset X} : S ∈ nonemptySubsets H ↔ S.Nonempty ∧ S ⊆ H := by
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty]

theorem rawWeights_nonneg {g : Finset X → ℝ} (hg : ∀ S, 0 ≤ g S) (H : Finset X) (x : X) :
    0 ≤ rawWeights g H x := by
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact div_nonneg (hg S) (Nat.cast_nonneg _)
  · exact le_rfl

theorem rawWeights_support (g : Finset X → ℝ) (H : Finset X) {x : X} (hx : x ∉ H) :
    rawWeights g H x = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  exact if_neg (fun h => hx ((mem_nonemptySubsets.mp hS).2 h))

theorem rawWeights_statistic (g : Finset X → ℝ) (H : Finset X) (f : X → ℝ) :
    (∑ x, rawWeights g H x * f x) =
      ∑ S ∈ nonemptySubsets H, g S * (∑ x ∈ S, f x) / S.card := by
  unfold rawWeights
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  calc
    _ = (g S / S.card) * (∑ x ∈ S, f x) := by
      simp only [ite_mul, zero_mul]
      rw [Finset.mul_sum, ← Finset.sum_filter]
      simp
    _ = _ := by ring

theorem rawWeights_sum (g : Finset X → ℝ) (H : Finset X) :
    (∑ x, rawWeights g H x) = subsetMass g H := by
  have h := rawWeights_statistic g H (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro S hS
  have hc : (S.card:ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr (mem_nonemptySubsets.mp hS).1)
  field_simp

theorem fractional_mass {r : ℝ} (hr : 0 ≤ r) {F : Finset (Finset X)} {g : Finset X → ℝ}
    (hg : FractionalCover r F g) {H : Finset X} (hH : H ∈ F) :
    1/2 ≤ subsetMass g H := by
  have he : g ∅ ≤ 1/2 := by
    have h := Finset.single_le_sum (s := (univ : Finset (Finset X)))
      (f := fun S => g S*r^S.card) (fun S _ => mul_nonneg (hg.1 S).1 (pow_nonneg hr _))
      (Finset.mem_univ (∅ : Finset X))
    simp only [Finset.card_empty, pow_zero, mul_one] at h
    exact h.trans hg.2.2
  have hm : subsetMass g H + g ∅ = ∑ S ∈ H.powerset, g S := by
    exact Finset.sum_erase_add _ _ (by simp)
  have hcov := hg.2.1 H hH
  linarith

theorem fractional_weights {r : ℝ} (hr : 0 ≤ r) {F : Finset (Finset X)} {g : Finset X → ℝ}
    (hg : FractionalCover r F g) :
    (∀ H ∈ F, ∀ x, 0 ≤ subsetWeights g H x) ∧
    (∀ H ∈ F, ∑ x, subsetWeights g H x = 1) ∧
    (∀ H ∈ F, ∀ x ∉ H, subsetWeights g H x = 0) := by
  have hm (H) (hH : H ∈ F) : 0 < subsetMass g H := by linarith [fractional_mass hr hg hH]
  refine ⟨?_, ?_, ?_⟩
  · intro H hH x
    exact div_nonneg (rawWeights_nonneg (fun S => (hg.1 S).1) H x) (hm H hH).le
  · intro H hH
    simp only [subsetWeights, ← Finset.sum_div, rawWeights_sum]
    exact div_self (ne_of_gt (hm H hH))
  · intro H hH x hx
    simp [subsetWeights, rawWeights_support g H hx]

theorem subsetWeights_statistic (g : Finset X → ℝ) (H : Finset X) (f : X → ℝ) (hm : subsetMass g H ≠ 0) :
    (∑ x, subsetWeights g H x * f x) * subsetMass g H =
      ∑ S ∈ nonemptySubsets H, g S * (∑ x ∈ S, f x) / S.card := by
  simp only [subsetWeights, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [mul_div_cancel_right₀ _ hm, rawWeights_statistic]

end
end TalagrandIntegral
