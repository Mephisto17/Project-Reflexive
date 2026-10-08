import TalagrandIntegral.Counting

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {s : ℕ}

def colorProb (p : ℝ) (s : ℕ) (i : Fin (s+1)) : ℝ :=
  if i.val < s then (256:ℝ)^(i.val+1)*p else 1-p*∑ j : Fin s, (256:ℝ)^(j.val+1)

theorem colorProb_early (p : ℝ) (i : Fin s) :
    colorProb p s i.castSucc = (256:ℝ)^(i.val+1)*p := by simp [colorProb, i.isLt]
theorem colorProb_last (p : ℝ) (s : ℕ) :
    colorProb p s (Fin.last s) = 1-p*∑ j : Fin s, (256:ℝ)^(j.val+1) := by
  simp [colorProb]

theorem colorProb_pos {p : ℝ} (hp : 0 < p)
    (hs : p*(∑ j : Fin s, (256:ℝ)^(j.val+1)) ≤ 1/2) (i : Fin (s+1)) :
    0 < colorProb p s i := by
  unfold colorProb
  split_ifs
  · positivity
  · linarith

theorem colorProb_sum (p : ℝ) (s : ℕ) : (∑ i, colorProb p s i) = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [colorProb_early, colorProb_last, ← Finset.sum_mul]
  ring

theorem geom_positive_sum_le {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) (n : ℕ) :
    (∑ j ∈ range n, b^(j+1)) ≤ b/(1-b) := by
  have hd : 0 < 1-b := by linarith
  have he : (b/(1-b))*(1-b) = b := div_mul_cancel₀ b (ne_of_gt hd)
  induction n with
  | zero => simp; exact div_nonneg hb hd.le
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hs : (∑ j ∈ range n, b^(j+1+1)) = b*(∑ j ∈ range n, b^(j+1)) := by
      simp [pow_succ, Finset.mul_sum, mul_comm]
    rw [hs]
    simp only [zero_add, pow_one]
    nlinarith [mul_le_mul_of_nonneg_left ih hb]

theorem colorProb_moveRate {p : ℝ} (hp : 0 < p)
    (hs : p*(∑ j : Fin s, (256:ℝ)^(j.val+1)) ≤ 1/2) :
    moveRate p (colorProb p s) ≤ 1/63 := by
  let π := colorProb p s
  have hπ := colorProb_pos hp hs
  have hsum := colorProb_sum p s
  have hrepr : moveRate p π = ∑ i : Fin (s+1),
      ((2:ℝ)^(i.val+1)*p/π i) * ∑ h : Fin (s+1), if i < h then π h else 0 := by
    unfold moveRate
    have he : (∑ m : MoveType s, (2:ℝ)^(m.val.1.val+1)*moveWeight p π m) =
        ∑ m : Fin (s+1) × Fin (s+1), if m.1 < m.2 then
          (2:ℝ)^(m.1.val+1)*p*π m.2/π m.1 else 0 := by
      have hsub : (∑ m : Fin (s+1) × Fin (s+1), if m.1 < m.2 then
          (2:ℝ)^(m.1.val+1)*p*π m.2/π m.1 else 0) =
          ∑ m : MoveType s, (2:ℝ)^(m.val.1.val+1)*p*π m.val.2/π m.val.1 := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
      rw [hsub]
      apply Finset.sum_congr rfl
      intro m _; simp [moveWeight]; ring
    rw [he, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> ring
  rw [hrepr, Fin.sum_univ_castSucc]
  have hlast : (∑ h : Fin (s+1), if Fin.last s < h then π h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    rw [if_neg (not_lt_of_ge (Fin.le_last h))]
  rw [hlast, mul_zero, add_zero]
  have htail (i : Fin (s+1)) : (∑ h : Fin (s+1), if i < h then π h else 0) ≤ 1 := by
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin (s+1))))
      (fun h _ => show (if i < h then π h else 0) ≤ π h from by split_ifs <;> first | rfl | exact (hπ h).le)
    exact h.trans_eq hsum
  have he (i : Fin s) : (2:ℝ)^(i.castSucc.val+1)*p/π i.castSucc = (1/128:ℝ)^(i.val+1) := by
    dsimp [π]
    rw [colorProb_early]
    have hh : (2:ℝ)^(i.val+1)*p / ((256:ℝ)^(i.val+1)*p) =
        (2:ℝ)^(i.val+1)/(256:ℝ)^(i.val+1) := by field_simp
    rw [hh, ← div_pow]
    norm_num
  simp_rw [he]
  have h := Finset.sum_le_sum (s := (univ : Finset (Fin s)))
    (fun i _ => mul_le_of_le_one_right (by positivity : 0 ≤ (1/128:ℝ)^(i.val+1)) (htail i.castSucc))
  have hg := geom_positive_sum_le (by norm_num : (0:ℝ) ≤ 1/128) (by norm_num : (1/128:ℝ) < 1) s
  have hgf : (∑ i : Fin s, (1/128:ℝ)^(i.val+1)) ≤ 1/127 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (1/128:ℝ)^(j+1)) s]
    norm_num at hg ⊢
    exact hg
  exact h.trans (hgf.trans (by norm_num))

end
end TalagrandIntegral
