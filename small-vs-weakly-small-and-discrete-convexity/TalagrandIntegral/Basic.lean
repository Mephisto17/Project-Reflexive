import TalagrandIntegral.Imports

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def coverCost (p : ℝ) (G : Finset (Finset X)) : ℝ := ∑ S ∈ G, p^S.card
def Covers (G F : Finset (Finset X)) : Prop := ∀ H ∈ F, ∃ S ∈ G, S ⊆ H
def Small (p : ℝ) (F : Finset (Finset X)) : Prop :=
  ∃ G, Covers G F ∧ coverCost p G ≤ 1/2
def FractionalCover (r : ℝ) (F : Finset (Finset X)) (g : Finset X → ℝ) : Prop :=
  (∀ S, 0 ≤ g S ∧ g S ≤ 1) ∧
    (∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, g S) ∧ (∑ S, g S*r^S.card) ≤ 1/2

theorem Small.mono_family {p : ℝ} {A B : Finset (Finset X)} (h : Small p A) (hBA : B ⊆ A) :
    Small p B := by
  obtain ⟨G, hG, hc⟩ := h
  exact ⟨G, fun H hH => hG H (hBA hH), hc⟩

theorem Small.mono_density {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r)
    {F : Finset (Finset X)} (h : Small r F) : Small p F := by
  obtain ⟨G, hG, hc⟩ := h
  refine ⟨G, hG, le_trans ?_ hc⟩
  apply Finset.sum_le_sum
  intro S _
  exact pow_le_pow_left₀ hp hpr _

theorem small_empty (p : ℝ) : Small p (∅ : Finset (Finset X)) := by
  exact ⟨∅, by simp [Covers], by norm_num [coverCost]⟩

def productMass {C : Type} [Fintype C] (π : C → ℝ) (a : X → C) : ℝ := ∏ x, π (a x)

theorem productMass_nonneg {C : Type} [Fintype C] {π : C → ℝ}
    (hπ : ∀ c, 0 ≤ π c) (a : X → C) : 0 ≤ productMass π a :=
  Finset.prod_nonneg (fun x _ => hπ (a x))

theorem productMass_sum {C : Type} [Fintype C] (π : C → ℝ) (hπ : ∑ c, π c = 1) :
    (∑ a : X → C, productMass π a) = 1 := by
  unfold productMass
  rw [← Fintype.prod_sum (fun (_ : X) c => π c)]
  simp [hπ]

theorem productMass_factor {C : Type} [Fintype C] (π : C → ℝ) (f : X → C → ℝ) :
    (∑ a : X → C, productMass π a * ∏ x, f x (a x)) =
      ∏ x, ∑ c, π c*f x c := by
  simp only [productMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun x c => π c*f x c)).symm

end
end TalagrandIntegral
