import TalagrandIntegral.Reconstruction
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X] {s t : ℕ}

theorem sum_comp_le {A B : Type} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (g : B → ℝ) (hg : ∀ b, 0 ≤ g b) :
    (∑ a, g (f a)) ≤ ∑ b, g b := by
  rw [← Finset.sum_image (fun a _ b _ h => hf h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun b _ _ => hg b)

def moveWeight (p : ℝ) (π : Fin (s+1) → ℝ) (m : MoveType s) : ℝ :=
  p * π m.val.2 / π m.val.1
def moveRate (p : ℝ) (π : Fin (s+1) → ℝ) : ℝ :=
  ∑ m : MoveType s, (2:ℝ)^(m.val.1.val+1)*moveWeight p π m

theorem moveWeight_nonneg {p : ℝ} (hp : 0 ≤ p) {π : Fin (s+1) → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (m : MoveType s) : 0 ≤ moveWeight p π m := by
  exact div_nonneg (mul_nonneg hp (hπ m.val.2)) (hπ m.val.1)

theorem mass_moveWord {p : ℝ} (π : Fin (s+1) → ℝ) (hπ : ∀ i, 0 < π i)
    {a z : Coloring X s} (hza : z ≤ a) (e : Fin t ≃ ↥(changed a z)) :
    productMass π a * p^t = productMass π z * ∏ j, moveWeight p π (moveWord e j) := by
  have hpoint (x : X) : π (a x) = π (z x) *
      (if z x < a x then π (a x)/π (z x) else 1) := by
    by_cases hx : z x < a x
    · rw [if_pos hx]; field_simp [ne_of_gt (hπ (z x))]
    · have he : a x = z x := le_antisymm (le_of_not_gt hx) (hza x)
      simp [hx, he]
  have he : (∏ j : Fin t, π (a (e j))/π (z (e j))) =
      ∏ x ∈ changed a z, π (a x)/π (z x) := by
    rw [e.prod_comp (fun x : ↥(changed a z) => π (a x)/π (z x))]
    exact Finset.prod_coe_sort (changed a z) (fun x : X => π (a x)/π (z x))
  have hm : productMass π a = productMass π z *
      ∏ x ∈ changed a z, π (a x)/π (z x) := by
    unfold productMass
    conv_lhs => arg 2; ext x; rw [hpoint x]
    rw [Finset.prod_mul_distrib]
    congr 1
    simp only [changed, Finset.prod_filter]
  rw [hm, ← he]
  simp only [moveWeight, moveWord, mul_div_assoc, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_fin]
  ring

/-- The factorial bound needed for ordered encodings, obtained from one
nonnegative term of the exponential series. -/
theorem factorial_bound (t : ℕ) : (t:ℝ)^t / (t.factorial:ℝ) ≤ (3:ℝ)^t := by
  have h := Real.pow_div_factorial_le_exp (t:ℝ) (show (0:ℝ) ≤ t by positivity) t
  have he : Real.exp (t:ℝ) = (Real.exp 1)^t := by
    simpa using Real.exp_nat_mul 1 t
  rw [he] at h
  exact h.trans (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _)

/-- The cost of all minimal moves into a fixed final coloring, at fixed
nonzero cardinality. This is the grouped estimate underlying (2.13)--(2.14). -/
theorem fixed_cardinality_count {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw0 : ∀ H ∈ F, ∀ x, 0 ≤ w H x) (hw1 : ∀ H ∈ F, ∑ x, w H x = 1)
    {p : ℝ} (hp : 0 ≤ p) (π : Fin (s+1) → ℝ) (hπ : ∀ i, 0 < π i)
    (z : Coloring X s) (t : ℕ) :
    (∑ a : Coloring X s, if MinimalMove F w a z ∧ (changed a z).card = t
      then productMass π a*p^t else 0) ≤
        productMass π z * (3*moveRate p π)^t := by
  let A := {a : Coloring X s // MinimalMove F w a z ∧ (changed a z).card = t}
  let E := (a : A) × (Fin t ≃ ↥(changed a.val z))
  let U := Fin t → MoveType s
  have hsets (u : U) := common_candidate_sets hw0 hw1 z u
  choose R hR hc using hsets
  let B := (u : U) × ((j : Fin t) → ↥(R u j))
  let code : E → B := fun ⟨a, e⟩ => ⟨moveWord e, fun j =>
    ⟨(e j).val, hc (moveWord e) a.val a.property.1 e rfl j⟩⟩
  have hcode : Function.Injective code := by
    rintro ⟨a,e⟩ ⟨b,f⟩ he
    have hword : moveWord e = moveWord f := congrArg Sigma.fst he
    have hpos (j : Fin t) : (e j).val = (f j).val :=
      congrArg (fun q : B => (q.2 j).val) he
    have hab : a = b := Subtype.ext (word_reconstructs a.property.1.1 b.property.1.1 e f hword hpos)
    subst b
    have hef : e = f := by ext j; exact hpos j
    subst f
    rfl
  let W : U → ℝ := fun u => productMass π z * ∏ j, moveWeight p π (u j)
  have hW (u : U) : 0 ≤ W u := by
    apply mul_nonneg (productMass_nonneg (fun i => (hπ i).le) z)
    exact Finset.prod_nonneg (fun j _ => moveWeight_nonneg hp (fun i => (hπ i).le) (u j))
  have hsum := sum_comp_le code hcode (fun q : B => W q.1) (fun q => hW q.1)
  have hcard (a : A) : Fintype.card (Fin t ≃ ↥(changed a.val z)) = t.factorial := by
    have heq : Fintype.card (Fin t) = Fintype.card ↥(changed a.val z) := by
      simpa using a.property.2.symm
    simpa using Fintype.card_equiv (Fintype.equivOfCardEq heq)
  have hleft : (∑ e : E, W (code e).1) =
      (t.factorial:ℝ) * ∑ a : A, productMass π a.val*p^t := by
    rw [Fintype.sum_sigma]
    simp only [code, W]
    have hh (a : A) (e : Fin t ≃ ↥(changed a.val z)) := mass_moveWord (p := p) π hπ a.property.1.1 e
    simp_rw [← hh]
    simp [hcard, nsmul_eq_mul, Finset.mul_sum]
  have hright : (∑ b : B, W b.1) ≤
      productMass π z * (t:ℝ)^t * (moveRate p π)^t := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hprod (u : U) : (Fintype.card ((j : Fin t) → ↥(R u j)) : ℝ) ≤
        ∏ j, (t:ℝ)*(2:ℝ)^((u j).val.1.val+1) := by
      simp only [Fintype.card_pi, Fintype.card_coe, Nat.cast_prod]
      exact Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hR u j)
    calc
      _ ≤ ∑ u : U, (∏ j, (t:ℝ)*(2:ℝ)^((u j).val.1.val+1)) * W u :=
        Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (hprod u) (hW u))
      _ = _ := by
        simp only [W, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
        have hword : (∑ u : U, (∏ j, (2:ℝ)^((u j).val.1.val+1)) *
            ∏ j, moveWeight p π (u j)) = (moveRate p π)^t := by
          simp only [← Finset.prod_mul_distrib]
          rw [← Fintype.prod_sum (fun (_ : Fin t) m => (2:ℝ)^(m.val.1.val+1)*moveWeight p π m)]
          simp [moveRate]
        calc
          _ = productMass π z * (t:ℝ)^t *
              (∑ u : U, (∏ j, (2:ℝ)^((u j).val.1.val+1)) * ∏ j, moveWeight p π (u j)) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _; ring
          _ = _ := by rw [hword]
  rw [hleft] at hsum
  have hbound := hsum.trans hright
  have hf : (0:ℝ) < t.factorial := by positivity
  have hdiv : (∑ a : A, productMass π a.val*p^t) ≤
      productMass π z*(t:ℝ)^t*(moveRate p π)^t/(t.factorial:ℝ) := by
    apply (le_div_iff₀ hf).mpr
    nlinarith [hbound]
  have hn : 0 ≤ productMass π z * (moveRate p π)^t := by
    apply mul_nonneg (productMass_nonneg (fun i => (hπ i).le) z)
    apply pow_nonneg
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (moveWeight_nonneg hp (fun i => (hπ i).le) m))
  have hfac := mul_le_mul_of_nonneg_left (factorial_bound t) hn
  have hfinal : (∑ a : A, productMass π a.val*p^t) ≤ productMass π z*(3*moveRate p π)^t := by
    calc
      _ ≤ productMass π z*(t:ℝ)^t*(moveRate p π)^t/(t.factorial:ℝ) := hdiv
      _ = (productMass π z*(moveRate p π)^t)*((t:ℝ)^t/(t.factorial:ℝ)) := by ring
      _ ≤ (productMass π z*(moveRate p π)^t)*(3:ℝ)^t := hfac
      _ = _ := by rw [mul_pow]; ring
  have he : (∑ a : Coloring X s, if MinimalMove F w a z ∧ (changed a z).card = t
      then productMass π a*p^t else 0) = ∑ a : A, productMass π a.val*p^t := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [he]
  exact hfinal

end
end TalagrandIntegral
