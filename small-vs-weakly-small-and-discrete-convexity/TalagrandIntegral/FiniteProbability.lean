import TalagrandIntegral.CubeBridge

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X C B : Type} [Fintype X] [DecidableEq X] [Fintype C] [Fintype B] [DecidableEq B]

def pushProb (π : C→ℝ) (φ : C→B) (b : B) : ℝ := ∑c,if φ c=b then π c else 0

theorem productMass_fiber (π : C→ℝ) (φ : C→B) (b : X→B) :
    (∑a : X→C, if (fun x=>φ (a x))=b then productMass π a else 0) =
      productMass (pushProb π φ) b := by
  have hd (a : X→C) : (∏x, if φ (a x)=b x then (1:ℝ) else 0) =
      if (fun x=>φ (a x))=b then 1 else 0 := by
    by_cases h : (fun x=>φ (a x))=b
    · have hx (x) : φ (a x)=b x := congrFun h x
      simp [h,hx]
    · rw [if_neg h]
      obtain ⟨x,hx⟩ : ∃x,φ (a x)≠b x := by simpa only [not_forall, funext_iff] using h
      exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)
  have hf (x : X) : (∑c,π c*(if φ c=b x then (1:ℝ) else 0)) = pushProb π φ (b x) := by
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp
  have h := productMass_factor π (fun x c=>if φ c=b x then 1 else 0)
  simp_rw [hd,hf,mul_ite,mul_one,mul_zero] at h
  exact h

theorem productMass_pushforward (π : C→ℝ) (φ : C→B) (f : (X→B)→ℝ) :
    (∑a : X→C,productMass π a*f (fun x=>φ (a x))) =
      ∑b : X→B,productMass (pushProb π φ) b*f b := by
  have he (a : X→C) : productMass π a*f (fun x=>φ (a x)) =
      ∑b : X→B,(if (fun x=>φ (a x))=b then productMass π a else 0)*f b := by
    simp [ite_mul]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul, productMass_fiber]

theorem pushProb_bool {π : C→ℝ} (hπ : ∑c,π c=1) (φ : C→Bool) {p : ℝ}
    (hp : (∑c,if φ c=true then π c else 0)=p) : pushProb π φ = TalagrandConjectures.bit p := by
  funext b
  cases b with
  | true => simpa [pushProb,TalagrandConjectures.bit] using hp
  | false =>
    have he : pushProb π φ false + pushProb π φ true = 1 := by
      rw [pushProb,pushProb,← Finset.sum_add_distrib]
      calc
        _ = ∑c,π c := by
          apply Finset.sum_congr rfl
          intro c _; cases φ c <;> simp
        _ = 1 := hπ
    change pushProb π φ false = 1-p
    change pushProb π φ true = p at hp
    linarith

theorem productMass_bernoulli {π : C→ℝ} (hπ : ∑c,π c=1) (φ : C→Bool) {p : ℝ}
    (hp : (∑c,if φ c=true then π c else 0)=p) (A : Set (TalagrandConjectures.Cube X)) :
    (∑a : X→C, if (fun x=>φ (a x))∈A then productMass π a else 0) = TalagrandConjectures.measure p A := by
  have h := productMass_pushforward π φ (TalagrandConjectures.ind A)
  rw [pushProb_bool hπ φ hp] at h
  simpa [TalagrandConjectures.measure,TalagrandConjectures.avg,TalagrandConjectures.ind,
    TalagrandConjectures.mass,productMass,mul_ite] using h

theorem finite_union_bound {Ω J : Type} [Fintype Ω] [Fintype J]
    (w : Ω→ℝ) (hw0 : ∀a,0≤w a) (hw1 : ∑a,w a=1) (P : J→Ω→Prop)
    (δ : ℝ) (hP : ∀j,(∑a,if P j a then w a else 0)≥1-δ) :
    (1:ℝ)-(Fintype.card J)*δ ≤ ∑a,if ∀j,P j a then w a else 0 := by
  have hp (a : Ω) : (if ∀j,P j a then (0:ℝ) else 1) ≤ ∑j,if P j a then (0:ℝ) else 1 := by
    by_cases ha : ∀j,P j a
    · simp [ha]
    · rw [if_neg ha]
      obtain ⟨j,hj⟩ := not_forall.mp ha
      have h := Finset.single_le_sum (s := (univ : Finset J)) (f := fun j=>if P j a then (0:ℝ) else 1)
        (fun j _=>by split_ifs <;> norm_num) (Finset.mem_univ j)
      simpa [hj] using h
  have hmul (a : Ω) := mul_le_mul_of_nonneg_left (hp a) (hw0 a)
  have h := Finset.sum_le_sum (s := (univ : Finset Ω)) (fun a _=>hmul a)
  simp_rw [Finset.mul_sum,mul_ite,mul_zero,mul_one] at h
  rw [Finset.sum_comm] at h
  have hc (Q : Ω→Prop) : (∑a,if Q a then 0 else w a) = 1-(∑a,if Q a then w a else 0) := by
    have he : (∑a,if Q a then 0 else w a)+(∑a,if Q a then w a else 0)=1 := by
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑a,w a := by apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
        _ = 1 := hw1
    linarith
  have hsum : (∑j : J, ∑a : Ω,if P j a then 0 else w a) ≤ (Fintype.card J)*δ := by
    calc
      _ ≤ ∑_ : J,δ := Finset.sum_le_sum (fun j _=>by linarith [hP j, hc (P j)])
      _ = _ := by simp
  have hall : (∑a : Ω,if ∀j,P j a then 0 else w a) +
      (∑a : Ω,if ∀j,P j a then w a else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑a,w a := by apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
      _ = 1 := hw1
  linarith only [h,hsum,hall]

end
end TalagrandIntegral
