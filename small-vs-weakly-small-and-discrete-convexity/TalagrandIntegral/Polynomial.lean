import TalagrandIntegral.Weights

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X] {s : ℕ}

def avgColor (a : Coloring X s) (S : Finset X) : ℝ :=
  (∑ x ∈ S, ((a x).val+1:ℝ)) / S.card

def coverPolynomial (g : Finset X → ℝ) (y : X → ℝ) : ℝ :=
  ∑ S ∈ nonemptySubsets (univ : Finset X), g S * ∏ x ∈ S, y x

theorem coverPolynomial_nonneg {g : Finset X → ℝ} {y : X → ℝ}
    (hg : ∀ S, 0 ≤ g S) (hy : ∀ x, 0 ≤ y x) : 0 ≤ coverPolynomial g y :=
  Finset.sum_nonneg (fun S _ => mul_nonneg (hg S) (Finset.prod_nonneg (fun x _ => hy x)))

theorem prod_colorY_ge_one (a : Coloring X s) {S : Finset X} (hS : S.Nonempty)
    (havg : avgColor a S ≤ 4) : 1 ≤ ∏ x ∈ S, colorY (a x) := by
  have hc : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hsum : (∑ x ∈ S, ((a x).val+1:ℝ)) ≤ 4*S.card := (div_le_iff₀ hc).mp havg
  have hn : (∑ x ∈ S, ((a x).val+1)) ≤ 4*S.card := by exact_mod_cast hsum
  have he : (∏ x ∈ S, colorY (a x)) =
      (512:ℝ)^(4*S.card) / (512:ℝ)^(∑ x ∈ S, ((a x).val+1)) := by
    simp only [colorY, Finset.prod_div_distrib, Finset.prod_const, ← pow_mul,
      Finset.prod_pow_eq_pow_sum]
  rw [he]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤512) hn)

theorem good_mass_half {I : Type} [DecidableEq I] (E : Finset I) (g f : I → ℝ)
    (hg : ∀ i ∈ E, 0 ≤ g i) (hf : ∀ i ∈ E, 0 ≤ f i)
    (hm : (∑ i ∈ E, g i*f i) ≤ 2*∑ i ∈ E, g i) :
    (∑ i ∈ E, g i)/2 ≤ ∑ i ∈ E, if f i≤4 then g i else 0 := by
  have hpoint (i) (hi : i∈E) : 4*g i ≤ g i*f i + 4*(if f i≤4 then g i else 0) := by
    by_cases h : f i≤4
    · simp only [if_pos h]
      nlinarith [mul_nonneg (hg i hi) (hf i hi)]
    · simp only [if_neg h, mul_zero, add_zero]
      simpa only [mul_comm (g i) 4] using mul_le_mul_of_nonneg_left (le_of_not_ge h) (hg i hi)
  have h := Finset.sum_le_sum (fun i hi => hpoint i hi)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  linarith

theorem coverPolynomial_large {r : ℝ} (hr : 0≤r) {F : Finset (Finset X)} {g : Finset X → ℝ}
    (hg : FractionalCover r F g) (a : Coloring X s) {H : Finset X} (hH : H∈F)
    (hmean : meanColor (subsetWeights g H) a ≤ 2) :
    1/4 ≤ coverPolynomial g (fun x => colorY (a x)) := by
  have hm : 1/2 ≤ subsetMass g H := fractional_mass hr hg hH
  have hm0 : 0 < subsetMass g H := by linarith
  have hstat : (∑ S ∈ nonemptySubsets H, g S*avgColor a S) ≤ 2*subsetMass g H := by
    have he := subsetWeights_statistic g H (fun x => ((a x).val+1:ℝ)) (ne_of_gt hm0)
    have hmul := mul_le_mul_of_nonneg_right hmean hm0.le
    change meanColor (subsetWeights g H) a * subsetMass g H = _ at he
    rw [he] at hmul
    simpa only [avgColor, mul_div_assoc] using hmul
  have hgood := good_mass_half (nonemptySubsets H) g (avgColor a)
    (fun S _ => (hg.1 S).1) (fun S _ => div_nonneg (Finset.sum_nonneg (fun x _ => by positivity)) (Nat.cast_nonneg _)) hstat
  have hsub : nonemptySubsets H ⊆ nonemptySubsets (univ : Finset X) := by
    intro S hS
    exact mem_nonemptySubsets.mpr ⟨(mem_nonemptySubsets.mp hS).1, Finset.subset_univ _⟩
  have hpoly : (∑ S ∈ nonemptySubsets H, if avgColor a S≤4 then g S else 0) ≤
      coverPolynomial g (fun x => colorY (a x)) := by
    calc
      _ ≤ ∑ S ∈ nonemptySubsets H, g S*∏x∈S,colorY (a x) := by
        apply Finset.sum_le_sum
        intro S hS
        by_cases h : avgColor a S≤4
        · simp only [if_pos h]
          exact le_mul_of_one_le_right (hg.1 S).1 (prod_colorY_ge_one a (mem_nonemptySubsets.mp hS).1 h)
        · simp only [if_neg h]
          exact mul_nonneg (hg.1 S).1 (Finset.prod_nonneg (fun x _ => (colorY_pos _).le))
      _ ≤ coverPolynomial g (fun x => colorY (a x)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun S _ _ => mul_nonneg (hg.1 S).1 (Finset.prod_nonneg (fun x _ => (colorY_pos _).le)))
  change subsetMass g H / 2 ≤ _ at hgood
  linarith

end
end TalagrandIntegral
