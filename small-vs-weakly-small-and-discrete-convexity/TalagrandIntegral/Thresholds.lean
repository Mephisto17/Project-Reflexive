import TalagrandIntegral.Comparison

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

theorem Small.fractional {p : ℝ} {F : Finset (Finset X)} (h : Small p F) :
    ∃g, FractionalCover p F g := by
  obtain ⟨G,hG,hcost⟩ := h
  let g : Finset X→ℝ := fun S=>if S∈G then 1 else 0
  refine ⟨g,?_,?_,?_⟩
  · intro S; dsimp [g]; split_ifs <;> norm_num
  · intro H hH
    obtain ⟨S,hS,hSH⟩ := hG H hH
    have h := Finset.single_le_sum (f:=g) (s:=H.powerset)
      (fun S _=>by dsimp [g]; split_ifs <;> norm_num) (Finset.mem_powerset.mpr hSH)
    simpa [g,hS] using h
  · have he : (∑S,g S*p^S.card)=coverCost p G := by
      simp only [g,ite_mul,one_mul,zero_mul,coverCost]
      rw [← Finset.sum_filter]
      simp
    rw [he]; exact hcost

theorem integral_parameters_compact (F : Finset (Finset X)) :
    IsCompact {p : ℝ | p∈Set.Icc 0 1 ∧ Small p F} := by
  have hc : IsClosed {p : ℝ | Small p F} := by
    have he : {p : ℝ | Small p F} = ⋃G : Finset (Finset X), {p : ℝ | Covers G F ∧ coverCost p G≤1/2} := by
      ext p; simp [Small]
    rw [he]
    apply isClosed_iUnion_of_finite
    intro G
    by_cases hG : Covers G F
    · simp only [hG,true_and]
      apply isClosed_le _ continuous_const
      unfold coverCost; fun_prop
    · simp only [hG,false_and,Set.setOf_false]
      exact isClosed_empty
  exact isCompact_Icc.inter_right hc

theorem fractional_parameters_compact (F : Finset (Finset X)) :
    IsCompact {p : ℝ | p∈Set.Icc 0 1 ∧ ∃g,FractionalCover p F g} := by
  let K : Set (ℝ × (Finset X→ℝ)) := {z | z.1∈Set.Icc 0 1 ∧ FractionalCover z.1 F z.2}
  have hcov : IsClosed {z : ℝ × (Finset X→ℝ) | ∀H∈F,1≤∑S∈H.powerset,z.2 S} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter; intro H
    apply isClosed_iInter; intro _
    apply isClosed_le continuous_const
    fun_prop
  have hcost : IsClosed {z : ℝ × (Finset X→ℝ) | (∑S,z.2 S*z.1^S.card)≤1/2} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hK : IsCompact K := by
    have hb := (isCompact_Icc (a:=((0:ℝ),(0:Finset X→ℝ))) (b:=((1:ℝ),(1:Finset X→ℝ)))).inter_right (hcov.inter hcost)
    convert hb using 1
    ext z
    simp only [K,FractionalCover,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_Icc,
      Prod.le_def,Pi.le_def,Pi.zero_apply,Pi.one_apply,forall_and]
    tauto
  have he : Prod.fst '' K = {p : ℝ | p∈Set.Icc 0 1 ∧ ∃g,FractionalCover p F g} := by
    ext p
    constructor
    · rintro ⟨⟨r,g⟩,h,rfl⟩
      exact ⟨h.1,g,h.2⟩
    · rintro ⟨hp,g,hg⟩
      exact ⟨(p,g),⟨hp,hg⟩,rfl⟩
  rw [← he]
  exact hK.image continuous_fst

/-- The supremum definition is a maximum, as in the paper. -/
theorem integralThreshold_isGreatest {F : Finset (Finset X)} (hF : ∅∉F) :
    IsGreatest {p : ℝ | p∈Set.Icc 0 1 ∧ Small p F} (integralThreshold F) := by
  have hb : BddAbove {p : ℝ | p∈Set.Icc 0 1 ∧ Small p F} := ⟨1,fun p hp=>hp.1.2⟩
  have hn : {p : ℝ | p∈Set.Icc 0 1 ∧ Small p F}.Nonempty :=
    ⟨0,⟨⟨le_rfl,by norm_num⟩,small_zero_of_empty_not_mem hF⟩⟩
  exact ⟨(integral_parameters_compact F).isClosed.csSup_mem hn hb,fun p hp=>le_csSup hb hp⟩

/-- The fractional threshold is also attained; its definition matches the maximum in the paper. -/
theorem fractionalThreshold_isGreatest {F : Finset (Finset X)} (hF : ∅∉F) :
    IsGreatest {p : ℝ | p∈Set.Icc 0 1 ∧ ∃g,FractionalCover p F g} (fractionalThreshold F) := by
  have hb : BddAbove {p : ℝ | p∈Set.Icc 0 1 ∧ ∃g,FractionalCover p F g} := ⟨1,fun p hp=>hp.1.2⟩
  have hn : {p : ℝ | p∈Set.Icc 0 1 ∧ ∃g,FractionalCover p F g}.Nonempty :=
    ⟨0,⟨⟨le_rfl,by norm_num⟩,(small_zero_of_empty_not_mem hF).fractional⟩⟩
  exact ⟨(fractional_parameters_compact F).isClosed.csSup_mem hn hb,fun p hp=>le_csSup hb hp⟩

theorem integralThreshold_le_fractionalThreshold {F : Finset (Finset X)} (hF : ∅∉F) :
    integralThreshold F ≤ fractionalThreshold F := by
  obtain ⟨hp,hsmall⟩ := (integralThreshold_isGreatest hF).1
  exact (fractionalThreshold_isGreatest hF).2 ⟨hp,hsmall.fractional⟩

end
end TalagrandIntegral
