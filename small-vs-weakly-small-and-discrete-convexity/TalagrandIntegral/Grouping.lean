import TalagrandIntegral.Couplings

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
open TalagrandConjectures
variable {X : Type} [Fintype X] [DecidableEq X]

theorem pad_tuple {n k : ℕ} (hn : 0<n) (hnk : n≤k) (f : Fin n→Cube X)
    {D : Set (Cube X)} (hf : ∀j,f j∈D) :
    ∃g : Fin k→Cube X,(∀j,g j∈D) ∧ unionOf f ≤ unionOf g := by
  let g : Fin k→Cube X := fun j=>f ⟨j.val%n,Nat.mod_lt _ hn⟩
  refine ⟨g,(fun j=>hf _),?_⟩
  intro x
  apply Finset.sup_le
  intro j _
  let j' : Fin k := ⟨j.val,lt_of_lt_of_le j.isLt hnk⟩
  have h := Finset.le_sup (f := fun j : Fin k=>g j x) (Finset.mem_univ j')
  simpa [g,j',Nat.mod_eq_of_lt j.isLt,unionOf] using h

theorem union_concat_left {L : ℕ} (f g : Fin L→Cube X) :
    unionOf f ≤ unionOf (Fin.addCases f g) := by
  intro x
  apply Finset.sup_le
  intro j _
  have h := Finset.le_sup (f := fun j : Fin (L+L)=>(Fin.addCases f g j : Cube X) x) (Finset.mem_univ (Fin.castAdd L j))
  simpa only [Fin.addCases_left, Fin.addCases_right, unionOf] using h

theorem union_concat_right {L : ℕ} (f g : Fin L→Cube X) :
    unionOf g ≤ unionOf (Fin.addCases f g) := by
  intro x
  apply Finset.sup_le
  intro j _
  have h := Finset.le_sup (f := fun j : Fin (L+L)=>(Fin.addCases f g j : Cube X) x) (Finset.mem_univ (Fin.natAdd L j))
  simpa only [Fin.addCases_left, Fin.addCases_right, unionOf] using h

theorem badUnions_subset_badTwo_unionFamily {L k : ℕ} (hL : 0<L) (hLk : 2*L≤k)
    (D : Set (Cube X)) : badUnions k D ⊆ badTwo (unionFamily L D) := by
  intro J hJ
  rintro ⟨Y,hY,Z,hZ,hcov⟩
  obtain ⟨f,hf,rfl⟩ := hY
  obtain ⟨g,hg,rfl⟩ := hZ
  have hfg : ∀j : Fin (L+L), Fin.addCases f g j∈D := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i; simpa only [Fin.addCases_left] using hf i
    · intro i; simpa only [Fin.addCases_right] using hg i
  obtain ⟨t,ht,htcov⟩ := pad_tuple (by omega : 0<L+L) (by omega : L+L≤k) (Fin.addCases f g) hfg
  apply hJ
  refine ⟨t,ht,?_⟩
  intro x
  apply (hcov x).trans
  change unionOf f x ⊔ unionOf g x ≤ unionOf t x
  exact sup_le ((union_concat_left f g x).trans (htcov x)) ((union_concat_right f g x).trans (htcov x))

theorem badUnions_empty_of_full_tuple {L k : ℕ} (hL : 0<L) (hLk : L≤k)
    {D : Set (Cube X)} (hfull : ∃f : Fin L→Cube X,(∀j,f j∈D) ∧ unionOf f=⊤) :
    badUnions k D = ∅ := by
  obtain ⟨f,hf,hfull⟩ := hfull
  obtain ⟨g,hg,hgfull⟩ := pad_tuple hL hLk f hf
  rw [hfull] at hgfull
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro J hJ
  exact hJ ⟨g,hg,le_top.trans hgfull⟩

theorem integralSmall_empty (p : ℝ) : IntegralSmall p (∅ : Set (Cube X)) := by
  simpa [IntegralSmall,cubeFamily] using small_empty (X:=X) p

end
end TalagrandIntegral
