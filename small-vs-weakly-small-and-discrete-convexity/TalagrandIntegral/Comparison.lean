import TalagrandIntegral.Expectation

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The constant in Theorem 1.1 of small-vs-weakly-small.pdf. -/
def comparisonConstant : ℝ := 25*(512:ℝ)^4

theorem comparisonConstant_pos : 0 < comparisonConstant := by norm_num [comparisonConstant]
theorem comparisonConstant_ge_one : 1 ≤ comparisonConstant := by norm_num [comparisonConstant]

theorem small_zero_of_empty_not_mem {F : Finset (Finset X)} (hF : ∅ ∉ F) : Small 0 F := by
  refine ⟨F, fun H hH => ⟨H,hH,Finset.Subset.refl H⟩, ?_⟩
  have he : coverCost 0 F = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    exact zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr (fun h => hF (h ▸ hS))))
  rw [he]; norm_num

theorem FractionalCover.empty_not_mem {r : ℝ} (hr : 0≤r) {F : Finset (Finset X)} {g : Finset X → ℝ}
    (hg : FractionalCover r F g) : ∅ ∉ F := by
  intro he
  have hm := fractional_mass hr hg he
  norm_num [subsetMass, nonemptySubsets] at hm

/-- Budget-preserving integral rounding, the explicit stronger form of
Theorem 1.1 in small-vs-weakly-small.pdf. All proof dependencies are checked. -/
theorem fractional_to_integral {r : ℝ} (hr : 0≤r) {F : Finset (Finset X)} {g : Finset X → ℝ}
    (hg : FractionalCover r F g) : Small (r/comparisonConstant) F := by
  by_cases hr0 : r=0
  · simpa [hr0] using small_zero_of_empty_not_mem (hg.empty_not_mem hr)
  have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
  let p := r/comparisonConstant
  have hp : 0<p := div_pos hrp comparisonConstant_pos
  by_contra hF
  obtain ⟨s,hs,hnext⟩ := exists_scale hp
  have hl := expectation_polynomial_lower hr hg hp hF hs
  have hm := colorY_mean hp hs hnext
  have hm' : (∑c : Fin (s+1),colorProb p s c*colorY c) ≤ r/5 := by
    have he : 5*(512:ℝ)^4*p = r/5 := by dsimp [p,comparisonConstant]; ring
    rwa [he] at hm
  have hu := expectation_polynomial_upper hr hg (colorProb p s) colorY (colorProb_sum p s)
    (fun c=>(colorProb_pos hp hs c).le) (fun c=>(colorY_pos c).le) hm'
  linarith

/-- Supremum formulation of the integral expectation threshold. -/
def integralThreshold (F : Finset (Finset X)) : ℝ :=
  sSup {p : ℝ | p∈Set.Icc 0 1 ∧ Small p F}

/-- Supremum formulation of the fractional expectation threshold. -/
def fractionalThreshold (F : Finset (Finset X)) : ℝ :=
  sSup {r : ℝ | r∈Set.Icc 0 1 ∧ ∃g, FractionalCover r F g}

theorem integralThreshold_nonneg {F : Finset (Finset X)} (hF : ∅ ∉ F) :
    0 ≤ integralThreshold F := by
  apply le_csSup (show BddAbove {p : ℝ | p∈Set.Icc 0 1 ∧ Small p F} from ⟨1,fun p hp=>hp.1.2⟩)
  exact ⟨⟨le_rfl,by norm_num⟩,small_zero_of_empty_not_mem hF⟩

/-- The threshold inequality in Theorem 1.1. No monotonicity of the family is
needed for this stronger form; exclusion of the empty set suffices. -/
theorem comparison_theorem_1_1 {F : Finset (Finset X)} (hF : ∅ ∉ F) :
    fractionalThreshold F ≤ comparisonConstant*integralThreshold F := by
  have hq0 := integralThreshold_nonneg hF
  by_cases he : {r : ℝ | r∈Set.Icc 0 1 ∧ ∃g, FractionalCover r F g}.Nonempty
  · apply csSup_le he
    intro r hr
    obtain ⟨hr, g,hg⟩ := hr
    have hsmall := fractional_to_integral hr.1 hg
    have hq : r/comparisonConstant ≤ integralThreshold F := by
      apply le_csSup (show BddAbove {p : ℝ | p∈Set.Icc 0 1 ∧ Small p F} from ⟨1,fun p hp=>hp.1.2⟩)
      refine ⟨⟨div_nonneg hr.1 comparisonConstant_pos.le,?_⟩,hsmall⟩
      exact (div_le_one comparisonConstant_pos).mpr (hr.2.trans comparisonConstant_ge_one)
    have hmul := (div_le_iff₀ comparisonConstant_pos).mp hq
    simpa only [mul_comm] using hmul
  · have hempty : {r : ℝ | r∈Set.Icc 0 1 ∧ ∃g, FractionalCover r F g} = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    rw [fractionalThreshold,hempty,Real.sSup_empty]
    exact mul_nonneg comparisonConstant_pos.le hq0

end
end TalagrandIntegral
