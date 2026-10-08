import TalagrandIntegral.Imports

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def truncSum (w : X → ℝ) (A : Finset X) (d u : ℝ) : ℝ :=
  ∑ x, min (w x) u * ((if x ∈ A then 1 else 0) - (1-d))

def Admissible (w : X → ℝ) (A : Finset X) (d m u : ℝ) : Prop :=
  0 ≤ u ∧ u ≤ 1 ∧ (∀ x, x ∉ A → w x ≤ u) ∧ m*u ≤ truncSum w A d u

theorem continuous_truncSum (w : X → ℝ) (A : Finset X) (d : ℝ) :
    Continuous (truncSum w A d) := by
  unfold truncSum
  fun_prop

theorem admissible_compact (w : X → ℝ) (A : Finset X) (d m : ℝ) :
    IsCompact {u | Admissible w A d m u} := by
  have hc : IsClosed {u : ℝ | ∀ x, x ∉ A → w x ≤ u} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_Ici
  have ht : IsClosed {u : ℝ | m*u ≤ truncSum w A d u} :=
    isClosed_le (continuous_const.mul continuous_id) (continuous_truncSum w A d)
  convert (isCompact_Icc (a := (0:ℝ)) (b := 1)).inter_right (hc.inter ht) using 1
  ext u
  simp [Admissible, and_assoc]

theorem admissible_zero (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (A : Finset X) (d m : ℝ) (hsupp : ∀ x, x ∉ A → w x = 0) :
    Admissible w A d m 0 := by
  refine ⟨le_rfl, zero_le_one, ?_, ?_⟩
  · intro x hx; simp [hsupp x hx]
  · simp [truncSum, min_eq_right (hw _)]

theorem truncSum_untruncated (w : X → ℝ) (A : Finset X) (d u : ℝ)
    (hw : ∑ x, w x = 1) (hd : 0 ≤ d)
    (hA : ∀ x, x ∉ A → w x ≤ u) :
    truncSum w A d u ≤ (∑ x ∈ A, w x) - (1-d) := by
  have hpoint (x : X) : min (w x) u * ((if x ∈ A then 1 else 0) - (1-d)) ≤
      w x * ((if x ∈ A then 1 else 0) - (1-d)) := by
    by_cases hx : x ∈ A
    · simp only [if_pos hx]
      have h := mul_le_mul_of_nonneg_right (min_le_left (w x) u) hd
      nlinarith
    · simp [hx, min_eq_left (hA x hx)]
  have h := Finset.sum_le_sum (s := (univ : Finset X)) (fun x _ => hpoint x)
  simpa [truncSum, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    mul_ite, hw] using h

/-- Lemma 2.2 of the comparison paper, including existence of a largest cutoff. -/
theorem maximal_truncation (w : X → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (A : Finset X) {d m : ℝ}
    (hd : 0 < d) (hd1 : d < 1) (hm : 0 ≤ m)
    (hne : ∃ u, Admissible w A d m u) :
    ∃ ε, Admissible w A d m ε ∧
      (∀ u, Admissible w A d m u → u ≤ ε) ∧
      ((univ.filter (fun x => ε < w x)).card : ℝ) ≤ m/d := by
  obtain ⟨ε, hε, hmax⟩ := (admissible_compact w A d m).exists_isGreatest hne
  refine ⟨ε, hε, hmax, ?_⟩
  let R : Finset X := univ.filter (fun x => ε < w x)
  change (R.card : ℝ) ≤ m/d
  have hwle (x : X) : w x ≤ 1 := by
    simpa [hw1] using Finset.single_le_sum (fun y _ => hw0 y) (mem_univ x)
  by_cases hR : R.Nonempty
  · let v : ℝ := R.inf' hR w
    have hv : ε < v := (Finset.lt_inf'_iff hR).mpr (fun x hx => (mem_filter.mp hx).2)
    have hvl (x : X) (hx : x ∈ R) : v ≤ w x := Finset.inf'_le w hx
    have hv1 : v ≤ 1 := by
      obtain ⟨x, hx⟩ := hR
      exact (hvl x hx).trans (hwle x)
    have hdiff : truncSum w A d v = truncSum w A d ε + d*(R.card : ℝ)*(v-ε) := by
      have he (x : X) :
          min (w x) v * ((if x ∈ A then 1 else 0) - (1-d)) =
          min (w x) ε * ((if x ∈ A then 1 else 0) - (1-d)) +
            (if x ∈ R then d*(v-ε) else 0) := by
        by_cases hx : x ∈ R
        · have hεx := (mem_filter.mp hx).2
          have hxA : x ∈ A := by
            by_contra h; exact (not_le_of_gt hεx) (hε.2.2.1 x h)
          rw [min_eq_right (hvl x hx), min_eq_right hεx.le, if_pos hxA, if_pos hx]
          ring
        · have hεx : w x ≤ ε := le_of_not_gt (by simpa [R] using hx)
          rw [min_eq_left (hεx.trans hv.le), min_eq_left hεx, if_neg hx, add_zero]
      unfold truncSum
      simp_rw [he, Finset.sum_add_distrib]
      simp [mul_comm, mul_left_comm, mul_assoc]
    rw [le_div_iff₀ hd]
    by_contra hn
    have hmR : m < (R.card : ℝ)*d := lt_of_not_ge hn
    have hvadm : Admissible w A d m v := by
      refine ⟨hε.1.trans hv.le, hv1, ?_, ?_⟩
      · intro x hx; exact (hε.2.2.1 x hx).trans hv.le
      · rw [hdiff]
        nlinarith [hε.2.2.2, mul_pos (sub_pos.mpr hmR) (sub_pos.mpr hv)]
    exact (not_le_of_gt hv) (hmax hvadm)
  · have hz : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    simp [hz, div_nonneg hm hd.le]

end
end TalagrandIntegral
