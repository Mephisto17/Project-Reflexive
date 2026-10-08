import TalagrandIntegral.Selector

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X] {s : ℕ}

def meanColor (w : X → ℝ) (a : Coloring X s) : ℝ :=
  ∑ x, w x * ((a x).val+1)

theorem color_layers (c : Fin (s+1)) :
    (c.val+1:ℝ) = 1 + ∑ i : Fin s, if i.val<c.val then (1:ℝ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i<c.val then (1:ℝ) else 0) s]
  rw [← Finset.sum_filter]
  have he : (range s).filter (fun i => i<c.val) = range c.val := by
    ext i; simp only [mem_filter, mem_range]; have hc := c.isLt; omega
  rw [he]; simp; ring

theorem meanColor_le_two (w : X → ℝ) (a : Coloring X s)
    (hw : ∑ x, w x = 1)
    (hcap : ∀ i : Fin s, 1-deficit i ≤ ∑ x ∈ initial a i, w x) :
    meanColor w a ≤ 2 := by
  have htail (i : Fin s) : (∑ x, w x*(if i.val<(a x).val then (1:ℝ) else 0)) =
      1-∑ x ∈ initial a i, w x := by
    have hsplit : (∑ x, w x*(if i.val<(a x).val then (1:ℝ) else 0)) +
        (∑ x ∈ initial a i, w x) = 1 := by
      rw [initial, Finset.sum_filter, ← Finset.sum_add_distrib]
      calc
        _ = ∑ x, w x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : i.val<(a x).val
          · simp [h, Nat.not_le.mpr h]
          · simp [h, Nat.le_of_not_gt h]
        _ = 1 := hw
    linarith
  have he : meanColor w a = 1+∑ i : Fin s, (1-∑ x ∈ initial a i, w x) := by
    unfold meanColor
    simp_rw [color_layers, mul_add, mul_one, Finset.mul_sum]
    rw [Finset.sum_add_distrib, hw, Finset.sum_comm]
    simp_rw [htail]
  rw [he]
  have ht : (∑ i : Fin s, (1-∑ x ∈ initial a i, w x)) ≤ ∑ i : Fin s, deficit i :=
    Finset.sum_le_sum (fun i _ => by linarith [hcap i])
  have hd : (∑ i : Fin s, deficit i) ≤ 1 := by
    have h := geom_positive_sum_le (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1) s
    simp only [deficit, ← one_div_pow]
    rw [Fin.sum_univ_eq_sum_range (fun i => (1/2:ℝ)^(i+1)) s]
    norm_num at h ⊢
    exact h
  linarith

/-- The mean-color conclusion of the multiscale selector. -/
theorem mean_selector {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw0 : ∀ H ∈ F, ∀ x, 0 ≤ w H x) (hw1 : ∀ H ∈ F, ∑ x, w H x = 1)
    (hsupp : ∀ H ∈ F, ∀ x ∉ H, w H x = 0)
    {p : ℝ} (hp : 0 < p) (hF : ¬ Small p F)
    (hs : p*(∑ j : Fin s, (256:ℝ)^(j.val+1)) ≤ 1/2) :
    (9:ℝ)/10 ≤ ∑ a : Coloring X s,
      if ∃ H ∈ F, meanColor (w H) a ≤ 2 then productMass (colorProb p s) a else 0 := by
  refine (multiscale_selector hw0 hw1 hsupp hp hF hs).trans ?_
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : ∃ H ∈ F, ∀ i : Fin s, 1-deficit i ≤ ∑ x ∈ initial a i, w H x
  · obtain ⟨H,hH,hcap⟩ := ha
    have hmean : ∃ H ∈ F, meanColor (w H) a ≤ 2 := ⟨H,hH,meanColor_le_two _ _ (hw1 H hH) hcap⟩
    simp [hmean]
    split_ifs <;> first | rfl | exact productMass_nonneg (fun i => (colorProb_pos hp hs i).le) a
  · simp only [if_neg ha]
    split_ifs <;> first | rfl | exact productMass_nonneg (fun i => (colorProb_pos hp hs i).le) a

end
end TalagrandIntegral
