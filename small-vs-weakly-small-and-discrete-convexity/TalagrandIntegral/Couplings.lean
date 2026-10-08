import TalagrandIntegral.FiniteProbability

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
open TalagrandConjectures
variable {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}

def labelProb (L : ℕ) (u v : ℝ) (c : Fin (L+1)) : ℝ := if c=0 then u else v

theorem labelProb_sum (L : ℕ) (u v : ℝ) : (∑c,labelProb L u v c) = u+L*v := by
  rw [Fin.sum_univ_succ]
  simp [labelProb]

theorem labelProb_nonneg (L : ℕ) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) (c : Fin (L+1)) :
    0≤labelProb L u v c := by unfold labelProb; split_ifs <;> assumption

def sparseRow (j : Fin L) (c : Fin (L+1)) : Bool := decide (c=j.succ)
def denseRow (j : Fin L) (c : Fin (L+1)) : Bool := decide (c=0 ∨ c=j.succ)
def sparseUnion (c : Fin (L+1)) : Bool := decide (c≠0)

theorem sparseRow_prob (u v : ℝ) (j : Fin L) :
    (∑c,if sparseRow j c=true then labelProb L u v c else 0) = v := by
  simp [sparseRow,labelProb]

theorem denseRow_prob (u v : ℝ) (j : Fin L) :
    (∑c,if denseRow j c=true then labelProb L u v c else 0) = u+v := by
  have he (c : Fin (L+1)) : (if denseRow j c=true then labelProb L u v c else 0) =
      (if c=0 then u else 0)+(if c=j.succ then v else 0) := by
    by_cases hc : c=0
    · subst c; simp [denseRow,labelProb, Ne.symm j.succ_ne_zero]
    · simp [denseRow,labelProb,hc]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

theorem sparseUnion_prob (u v : ℝ) :
    (∑c : Fin (L+1),if sparseUnion c=true then labelProb L u v c else 0) = L*v := by
  rw [Fin.sum_univ_succ]
  simp [sparseUnion,labelProb]

theorem sparse_union (a : X→Fin (L+1)) :
    unionOf (fun j x=>sparseRow j (a x)) = fun x=>sparseUnion (a x) := by
  funext x
  by_cases hx : a x=0
  · simp only [unionOf,sparseRow,sparseUnion,hx,fun j : Fin L=>Ne.symm j.succ_ne_zero,
      ne_eq,not_true_eq_false,decide_false]
    apply le_antisymm
    · apply Finset.sup_le
      intro j _
      exact le_rfl
    · exact bot_le
  · obtain ⟨j,hj⟩ := Fin.exists_succ_eq.mpr hx
    have ht : (true:Bool) ≤ unionOf (fun j x=>sparseRow j (a x)) x := by
      have h := Finset.le_sup (f := fun j : Fin L=>sparseRow j (a x)) (Finset.mem_univ j)
      simpa [sparseRow,hj,unionOf] using h
    have he : unionOf (fun j x=>sparseRow j (a x)) x = true := top_unique ht
    simp only [sparseUnion,ne_eq,hx,not_false_eq_true,decide_true]
    exact he

theorem dense_union (hL : 0<L) (a : X→Fin (L+1)) :
    unionOf (fun j x=>denseRow j (a x)) = ⊤ := by
  funext x
  have hrow : ∃j : Fin L,denseRow j (a x)=true := by
    by_cases hx : a x=0
    · exact ⟨⟨0,hL⟩,by simp [denseRow,hx]⟩
    · obtain ⟨j,hj⟩ := Fin.exists_succ_eq.mpr hx
      exact ⟨j,by simp [denseRow,hj]⟩
  obtain ⟨j,hj⟩ := hrow
  have ht : (true:Bool) ≤ unionOf (fun j x=>denseRow j (a x)) x := by
    have h := Finset.le_sup (f := fun j : Fin L=>denseRow j (a x)) (Finset.mem_univ j)
    simpa only [unionOf,hj] using h
  have he : unionOf (fun j x=>denseRow j (a x)) x = true := top_unique ht
  exact he

def unionFamily (L : ℕ) (D : Set (Cube X)) : Set (Cube X) :=
  {J | ∃f : Fin L→Cube X,(∀j,f j∈D) ∧ J=unionOf f}

theorem sparse_density_boost {p δ : ℝ} (hp : 0≤p) (hLp : (L:ℝ)*p≤1)
    (D : Set (Cube X)) (hD : 1-δ≤measure p D) :
    1-(L:ℝ)*δ ≤ measure ((L:ℝ)*p) (unionFamily L D) := by
  let π := labelProb L (1-(L:ℝ)*p) p
  have hπ0 (c) : 0≤π c := labelProb_nonneg L (by linarith) hp c
  have hπ1 : (∑c,π c)=1 := by rw [labelProb_sum]; ring
  have hrow (j : Fin L) : (∑a : X→Fin (L+1),if (fun x=>sparseRow j (a x))∈D then productMass π a else 0) = measure p D :=
    productMass_bernoulli hπ1 (sparseRow j) (sparseRow_prob _ _ j) D
  have hall := finite_union_bound (fun a : X→Fin (L+1)=>productMass π a)
    (productMass_nonneg hπ0) (productMass_sum π hπ1)
    (fun j : Fin L=>fun a=>(fun x=>sparseRow j (a x))∈D) δ (fun j=>by rw [hrow]; exact hD)
  simp only [Fintype.card_fin] at hall
  have hu := productMass_bernoulli (X:=X) hπ1 sparseUnion (sparseUnion_prob (1-(L:ℝ)*p) p) (unionFamily L D)
  rw [← hu]
  refine hall.trans (Finset.sum_le_sum ?_)
  intro a _
  by_cases ha : ∀j : Fin L,(fun x=>sparseRow j (a x))∈D
  · have hf : (fun x=>sparseUnion (a x))∈unionFamily L D :=
      ⟨(fun j x=>sparseRow j (a x)),ha,(sparse_union a).symm⟩
    simp [ha,hf]
  · simp only [if_neg ha]
    split_ifs <;> first | rfl | exact productMass_nonneg hπ0 a

theorem dense_full_union {p δ : ℝ} (hL : 1<L) (hp1 : p≤1) (hLp : 1≤(L:ℝ)*p)
    (hδ : (L:ℝ)*δ<1) (D : Set (Cube X)) (hD : 1-δ≤measure p D) :
    ∃f : Fin L→Cube X,(∀j,f j∈D) ∧ unionOf f=⊤ := by
  let u := ((L:ℝ)*p-1)/((L:ℝ)-1)
  let v := (1-p)/((L:ℝ)-1)
  have hLr : (1:ℝ)<L := by exact_mod_cast hL
  have hd : (L:ℝ)-1≠0 := by linarith
  have hu : 0≤u := div_nonneg (by linarith) (by linarith)
  have hv : 0≤v := div_nonneg (by linarith) (by linarith)
  let π := labelProb L u v
  have hπ0 (c) : 0≤π c := labelProb_nonneg L hu hv c
  have hπ1 : (∑c,π c)=1 := by rw [labelProb_sum]; dsimp [u,v]; field_simp [hd]; ring
  have hp : u+v=p := by dsimp [u,v]; field_simp [hd]; ring
  have hrow (j : Fin L) : (∑a : X→Fin (L+1),if (fun x=>denseRow j (a x))∈D then productMass π a else 0) = measure p D := by
    apply productMass_bernoulli hπ1 (denseRow j)
    rw [denseRow_prob,hp]
  have hall := finite_union_bound (fun a : X→Fin (L+1)=>productMass π a)
    (productMass_nonneg hπ0) (productMass_sum π hπ1)
    (fun j : Fin L=>fun a=>(fun x=>denseRow j (a x))∈D) δ (fun j=>by rw [hrow]; exact hD)
  simp only [Fintype.card_fin] at hall
  have hex : ∃a : X→Fin (L+1),∀j : Fin L,(fun x=>denseRow j (a x))∈D := by
    by_contra hn
    have hzero : 1-(L:ℝ)*δ ≤ 0 := hall.trans (by
      apply Finset.sum_nonpos
      intro a _
      split_ifs with h
      · exact (hn ⟨a,h⟩).elim
      · exact le_rfl)
    linarith
  obtain ⟨a,ha⟩ := hex
  exact ⟨(fun j x=>denseRow j (a x)),ha,dense_union (by omega) a⟩

end
end TalagrandIntegral
