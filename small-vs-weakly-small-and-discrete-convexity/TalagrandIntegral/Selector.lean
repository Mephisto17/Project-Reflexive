import TalagrandIntegral.Probabilities

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X] {s : ℕ}

def badProbability (F : Finset (Finset X)) (w : Finset X → X → ℝ)
    (π : Fin (s+1) → ℝ) : ℝ :=
  ∑ a : Coloring X s, if BadColoring F w a then productMass π a else 0

theorem split_moves_by_card (F : Finset (Finset X)) (w : Finset X → X → ℝ)
    (π : Fin (s+1) → ℝ) (p : ℝ) (z : Coloring X s) :
    (∑ a : Coloring X s, if MinimalMove F w a z ∧ (changed a z).Nonempty
      then productMass π a*p^(changed a z).card else 0) =
    ∑ t ∈ range (Fintype.card X+1), if t=0 then 0 else
      ∑ a : Coloring X s, if MinimalMove F w a z ∧ (changed a z).card=t
        then productMass π a*p^t else 0 := by
  have hpoint (a : Coloring X s) :
      (if MinimalMove F w a z ∧ (changed a z).Nonempty
        then productMass π a*p^(changed a z).card else 0) =
      ∑ t ∈ range (Fintype.card X+1), if t=0 then 0 else
        if MinimalMove F w a z ∧ (changed a z).card=t then productMass π a*p^t else 0 := by
    rw [Finset.sum_eq_single (changed a z).card]
    · by_cases hz : (changed a z).card=0
      · simp [hz, ← Finset.card_pos]
      · have hn : (changed a z).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
        simp [hz, hn]
    · intro t ht hne
      have hne' : (changed a z).card ≠ t := Ne.symm hne
      simp [hne']
    · intro hn
      exfalso
      apply hn
      have hcard : (changed a z).card ≤ Fintype.card X := Finset.card_le_univ _
      simp only [mem_range]; omega
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t=0 <;> simp [ht]

theorem selector_bad_bound {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw0 : ∀ H ∈ F, ∀ x, 0 ≤ w H x) (hw1 : ∀ H ∈ F, ∑ x, w H x = 1)
    (hsupp : ∀ H ∈ F, ∀ x ∉ H, w H x = 0)
    {p : ℝ} (hp : 0 < p) (hF : ¬ Small p F)
    (π : Fin (s+1) → ℝ) (hπ : ∀ i, 0 < π i) (hπsum : ∑ i, π i = 1)
    (hrate : moveRate p π ≤ 1/63) : badProbability F w π ≤ 1/10 := by
  have hP (a : Coloring X s) : 0 ≤ productMass π a := productMass_nonneg (fun i => (hπ i).le) a
  have hpoint (a : Coloring X s) :
      (if BadColoring F w a then productMass π a else 0)/2 ≤
      ∑ z : Coloring X s, if MinimalMove F w a z ∧ (changed a z).Nonempty
        then productMass π a*p^(changed a z).card else 0 := by
    by_cases ha : BadColoring F w a
    · have hcov := not_small_minimal_cover hp.le hF hw0 hsupp a
      have he (z : Coloring X s) :
          (if MinimalMove F w a z ∧ (changed a z).Nonempty then productMass π a*p^(changed a z).card else 0) =
          productMass π a*(if MinimalMove F w a z then p^(changed a z).card else 0) := by
        by_cases hz : MinimalMove F w a z
        · simp [hz, bad_minimal_changed_nonempty hw1 ha hz]
        · simp [hz]
      simp_rw [he, ← Finset.mul_sum]
      have h := mul_le_mul_of_nonneg_left hcov.le (hP a)
      simpa [ha, div_eq_mul_inv] using h
    · simp only [if_neg ha, zero_div]
      apply Finset.sum_nonneg
      intro z _
      split_ifs
      · exact mul_nonneg (hP a) (pow_nonneg hp.le _)
      · exact le_rfl
  have hs := Finset.sum_le_sum (s := (univ : Finset (Coloring X s))) (fun a _ => hpoint a)
  rw [← Finset.sum_div, Finset.sum_comm] at hs
  change badProbability F w π / 2 ≤ _ at hs
  have hr0 : 0 ≤ moveRate p π := by
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity)
      (moveWeight_nonneg hp.le (fun i => (hπ i).le) m))
  have hb : 3*moveRate p π ≤ 1/21 := by linarith
  have hgeom (n : ℕ) : (∑ t ∈ range (n+1), if t=0 then (0:ℝ) else (1/21:ℝ)^t) ≤ 1/20 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, zero_add, add_zero]
    have h := geom_positive_sum_le (by norm_num : (0:ℝ) ≤ 1/21) (by norm_num : (1/21:ℝ)<1) n
    norm_num at h ⊢
    exact h
  have hz (z : Coloring X s) :
      (∑ a : Coloring X s, if MinimalMove F w a z ∧ (changed a z).Nonempty
        then productMass π a*p^(changed a z).card else 0) ≤ productMass π z/20 := by
    rw [split_moves_by_card]
    calc
      _ ≤ ∑ t ∈ range (Fintype.card X+1), productMass π z*(if t=0 then 0 else (1/21:ℝ)^t) := by
        apply Finset.sum_le_sum
        intro t _
        by_cases ht : t=0
        · simp [ht]
        · simp only [if_neg ht]
          exact (fixed_cardinality_count hw0 hw1 hp.le π hπ z t).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (hP z))
      _ = productMass π z * (∑ t ∈ range (Fintype.card X+1), if t=0 then 0 else (1/21:ℝ)^t) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ productMass π z/20 := by
        have h := mul_le_mul_of_nonneg_left (hgeom (Fintype.card X)) (hP z)
        simpa [div_eq_mul_inv] using h
  have hzsum := Finset.sum_le_sum (s := (univ : Finset (Coloring X s))) (fun z _ => hz z)
  rw [← Finset.sum_div, productMass_sum π hπsum] at hzsum
  linarith

/-- The simultaneous-capture conclusion (2.2) of Theorem 2.1 in
small-vs-weakly-small.pdf. The family need not be increasing. -/
theorem multiscale_selector {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw0 : ∀ H ∈ F, ∀ x, 0 ≤ w H x) (hw1 : ∀ H ∈ F, ∑ x, w H x = 1)
    (hsupp : ∀ H ∈ F, ∀ x ∉ H, w H x = 0)
    {p : ℝ} (hp : 0 < p) (hF : ¬ Small p F)
    (hs : p*(∑ j : Fin s, (256:ℝ)^(j.val+1)) ≤ 1/2) :
    (9:ℝ)/10 ≤ ∑ a : Coloring X s,
      if ∃ H ∈ F, ∀ i : Fin s, 1-deficit i ≤ ∑ x ∈ initial a i, w H x
      then productMass (colorProb p s) a else 0 := by
  have hb := selector_bad_bound hw0 hw1 hsupp hp hF (colorProb p s)
    (colorProb_pos hp hs) (colorProb_sum p s) (colorProb_moveRate hp hs)
  have he : (∑ a : Coloring X s, if ∃ H ∈ F, ∀ i : Fin s,
      1-deficit i ≤ ∑ x ∈ initial a i, w H x then productMass (colorProb p s) a else 0) +
      badProbability F w (colorProb p s) = 1 := by
    rw [badProbability, ← Finset.sum_add_distrib]
    have h (a : Coloring X s) :
        (if ∃ H ∈ F, ∀ i : Fin s, 1-deficit i ≤ ∑ x ∈ initial a i, w H x
          then productMass (colorProb p s) a else 0) +
        (if BadColoring F w a then productMass (colorProb p s) a else 0) =
          productMass (colorProb p s) a := by
      unfold BadColoring
      split_ifs <;> simp_all
    simp_rw [h]
    exact productMass_sum _ (colorProb_sum p s)
  linarith

end
end TalagrandIntegral
