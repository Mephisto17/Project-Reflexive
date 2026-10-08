import TalagrandIntegral.Polynomial

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X C : Type} [Fintype X] [DecidableEq X] [Fintype C]

theorem productMass_subset (π Y : C → ℝ) (hπ : ∑ c,π c=1) (S : Finset X) :
    (∑ a : X→C, productMass π a * ∏x∈S,Y (a x)) = (∑c,π c*Y c)^S.card := by
  have he (a : X→C) : (∏x, if x∈S then Y (a x) else 1) = ∏x∈S,Y (a x) := by
    rw [← Finset.prod_filter]; simp
  have h := productMass_factor π (fun x c => if x∈S then Y c else 1)
  simp_rw [he] at h
  rw [h]
  have hf (x : X) : (∑c,π c*(if x∈S then Y c else 1)) = if x∈S then (∑c,π c*Y c) else 1 := by
    by_cases hx : x∈S <;> simp [hx,hπ]
  simp_rw [hf]
  rw [← Finset.prod_filter]
  simp

theorem expectation_polynomial (π Y : C → ℝ) (hπ : ∑ c,π c=1) (g : Finset X → ℝ) :
    (∑a : X→C,productMass π a * coverPolynomial g (fun x=>Y (a x))) =
      ∑S∈nonemptySubsets (univ : Finset X),g S*(∑c,π c*Y c)^S.card := by
  unfold coverPolynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  calc
    _ = g S * ∑a : X→C,productMass π a*∏x∈S,Y (a x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ = _ := by rw [productMass_subset π Y hπ S]

theorem expectation_polynomial_upper {r : ℝ} (hr : 0≤r) {F : Finset (Finset X)}
    {g : Finset X → ℝ} (hg : FractionalCover r F g) (π Y : C → ℝ)
    (hπ : ∑c,π c=1) (hπ0 : ∀c,0≤π c) (hY0 : ∀c,0≤Y c)
    (hmean : (∑c,π c*Y c) ≤ r/5) :
    (∑a : X→C,productMass π a*coverPolynomial g (fun x=>Y (a x))) ≤ 1/10 := by
  rw [expectation_polynomial π Y hπ]
  have hm0 : 0≤∑c,π c*Y c := Finset.sum_nonneg (fun c _ => mul_nonneg (hπ0 c) (hY0 c))
  have hp (S : Finset X) (hS : S∈nonemptySubsets (univ : Finset X)) :
      (∑c,π c*Y c)^S.card ≤ (1/5:ℝ)*r^S.card := by
    have hc : 0<S.card := Finset.card_pos.mpr (mem_nonemptySubsets.mp hS).1
    calc
      _ ≤ (r/5)^S.card := pow_le_pow_left₀ hm0 hmean _
      _ = r^S.card*(1/5:ℝ)^S.card := by rw [← mul_pow]; congr 1; ring
      _ ≤ r^S.card*(1/5:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr _)
        calc
          (1/5:ℝ)^S.card ≤ (1/5:ℝ)^1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
          _ = _ := pow_one _
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∑S∈nonemptySubsets (univ : Finset X),(1/5:ℝ)*(g S*r^S.card) := by
      apply Finset.sum_le_sum
      intro S hS
      have h := mul_le_mul_of_nonneg_left (hp S hS) (hg.1 S).1
      nlinarith
    _ = (1/5:ℝ)*∑S∈nonemptySubsets (univ : Finset X),g S*r^S.card := (Finset.mul_sum _ _ _).symm
    _ ≤ (1/5:ℝ)*∑S : Finset X,g S*r^S.card := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun S _ _ => mul_nonneg (hg.1 S).1 (pow_nonneg hr _))
    _ ≤ (1/5:ℝ)*(1/2) := mul_le_mul_of_nonneg_left hg.2.2 (by norm_num)
    _ = _ := by norm_num

theorem expectation_polynomial_lower {r : ℝ} (hr : 0≤r) {F : Finset (Finset X)}
    {g : Finset X → ℝ} (hg : FractionalCover r F g) {p : ℝ} (hp : 0<p)
    (hF : ¬Small p F) {s : ℕ} (hs : p*scaleSum s≤1/2) :
    (9:ℝ)/40 ≤ ∑a : Coloring X s,productMass (colorProb p s) a*
      coverPolynomial g (fun x=>colorY (a x)) := by
  obtain ⟨hw0,hw1,hsupp⟩ := fractional_weights hr hg
  have hevent := mean_selector hw0 hw1 hsupp hp hF hs
  have hP (a : Coloring X s) : 0≤productMass (colorProb p s) a :=
    productMass_nonneg (fun c => (colorProb_pos hp hs c).le) a
  have hpoint (a : Coloring X s) :
      (1/4:ℝ)*(if ∃H∈F,meanColor (subsetWeights g H) a≤2 then productMass (colorProb p s) a else 0) ≤
        productMass (colorProb p s) a*coverPolynomial g (fun x=>colorY (a x)) := by
    by_cases h : ∃H∈F,meanColor (subsetWeights g H) a≤2
    · simp only [if_pos h]
      obtain ⟨H,hH,hmean⟩ := h
      have hl := mul_le_mul_of_nonneg_left (coverPolynomial_large hr hg a hH hmean) (hP a)
      simpa only [mul_comm (1/4:ℝ)] using hl
    · simp only [if_neg h,mul_zero]
      exact mul_nonneg (hP a) (coverPolynomial_nonneg (fun S => (hg.1 S).1) (fun x=>(colorY_pos _).le))
  have h := Finset.sum_le_sum (s := (univ : Finset (Coloring X s))) (fun a _ => hpoint a)
  rw [← Finset.mul_sum] at h
  linarith

end
end TalagrandIntegral
