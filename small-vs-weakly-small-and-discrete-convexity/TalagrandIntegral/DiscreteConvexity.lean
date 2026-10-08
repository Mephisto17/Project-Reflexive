import TalagrandIntegral.Grouping

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
open TalagrandConjectures
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The same-density conclusion from a general two-union rounding constant.
The sparse and dense couplings are constructed in `Couplings.lean`. -/
theorem discrete_convexity_general {L k : ℕ} (hL : 1<L) (hLk : 2*L≤k)
    (hconstant : 50*(512:ℝ)^4 ≤ L) {p : ℝ} (hp : 0<p) (hp1 : p<1)
    (D : Set (Cube X)) (hD : 1-1/(k:ℝ) ≤ measure p D) :
    IntegralSmall p (badUnions k D) := by
  have hL0 : 0<L := by omega
  have hk0 : 0<k := by omega
  have hLr : (0:ℝ)<L := by exact_mod_cast hL0
  have hkr : (0:ℝ)<k := by exact_mod_cast hk0
  have hratio : (L:ℝ)*(1/(k:ℝ)) ≤ 1/2 := by
    rw [mul_one_div,div_le_iff₀ hkr]
    have hcast : (2:ℝ)*L≤k := by exact_mod_cast hLk
    linarith
  by_cases hLp : (L:ℝ)*p<1
  · have hdens := sparse_density_boost hp.le hLp.le D hD
    have hhalf : (1:ℝ)/2 ≤ measure ((L:ℝ)*p) (unionFamily L D) := by linarith
    have hsmall := integral_two_unions (mul_pos hLr hp) hLp (unionFamily L D) hhalf
    have hpbound : p ≤ ((L:ℝ)*p)/(50*(512:ℝ)^4) := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<50*(512:ℝ)^4)).mpr
      nlinarith
    exact (hsmall.mono_density hp.le hpbound).mono (badUnions_subset_badTwo_unionFamily hL0 hLk D)
  · have hfull := dense_full_union hL hp1.le (le_of_not_gt hLp)
      (by linarith : (L:ℝ)*(1/(k:ℝ))<1) D hD
    rw [badUnions_empty_of_full_tuple hL0 (by omega : L≤k) hfull]
    exact integralSmall_empty p

/-- Theorem 1.1 of Talagrand-discrete-convexity-conjecture.pdf, with exactly
k = 2^75 and covering cost at most 1/2 at the original density p. The proof
uses the companion comparison theorem followed by the density-boosting
argument; it does not assume the paper's hypergraph-covering lemma. -/
theorem discrete_convexity_theorem_1_1 {p : ℝ} (hp : 0<p) (hp1 : p<1)
    (D : Set (Cube X)) (hD : 1-1/((2:ℝ)^75) ≤ measure p D) :
    IntegralSmall p (badUnions (2^75) D) := by
  apply discrete_convexity_general (L:=2^70) (k:=2^75)
    (by norm_num) (by norm_num) (by norm_num) hp hp1 D
  norm_num at hD ⊢
  exact hD

/-- Proposition 3.1, obtained using the proved comparison theorem and the
fractional two-union certificate. -/
theorem discrete_convexity_proposition_3_1 {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (F : Set (Cube X)) (hF : (1:ℝ)/2≤measure q F) :
    IntegralSmall (q/((2:ℝ)^70)) (badUnions 32 F) := by
  have htwo := integral_two_unions hq hq1 F hF
  have hsub : badUnions 32 F ⊆ badTwo F := by
    intro J hJ
    rintro ⟨Y,hY,Z,hZ,hcov⟩
    let f : Fin 2→Cube X := fun j=>if j.val=0 then Y else Z
    have hf : ∀j,f j∈F := by intro j; dsimp [f]; split_ifs <;> assumption
    obtain ⟨g,hg,hgcover⟩ := pad_tuple (by norm_num : 0<2) (by norm_num : 2≤32) f hf
    apply hJ
    refine ⟨g,hg,?_⟩
    intro x
    apply (hcov x).trans
    change Y x ⊔ Z x ≤ unionOf g x
    apply sup_le
    · have h := Finset.le_sup (f := fun j : Fin 2=>f j x) (Finset.mem_univ (0:Fin 2))
      have hh : Y x ≤ unionOf f x := by simpa [f,unionOf] using h
      exact hh.trans (hgcover x)
    · have h := Finset.le_sup (f := fun j : Fin 2=>f j x) (Finset.mem_univ (1:Fin 2))
      have hh : Z x ≤ unionOf f x := by simpa [f,unionOf] using h
      exact hh.trans (hgcover x)
  have hrad : q/((2:ℝ)^70) ≤ q/(50*(512:ℝ)^4) := by
    exact div_le_div_of_nonneg_left hq.le (by norm_num) (by norm_num)
  exact (htwo.mono_density (by positivity) hrad).mono hsub

end
end TalagrandIntegral
