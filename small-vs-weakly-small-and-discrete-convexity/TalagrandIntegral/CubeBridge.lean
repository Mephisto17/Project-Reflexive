import TalagrandIntegral.Comparison
import TalagrandConjectures.Li

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- Explicit equivalence between finite subsets and the Boolean cube. -/
def finsetCube : Finset X ≃ TalagrandConjectures.Cube X where
  toFun S x := decide (x∈S)
  invFun J := univ.filter (fun x=>J x=true)
  left_inv S := by ext x; simp
  right_inv J := by funext x; simp

theorem finsetCube_le {S T : Finset X} : finsetCube S ≤ finsetCube T ↔ S⊆T := by
  constructor
  · intro h x hx
    have hh := h x
    by_cases ht : x∈T
    · exact ht
    · simp only [finsetCube, Equiv.coe_fn_mk, hx, ht, decide_true, decide_false] at hh
      exact ((by decide : ¬ (true:Bool) ≤ false) hh).elim
  · intro h x
    by_cases hx : x∈S
    · simp [finsetCube,hx,h hx]
    · simp [finsetCube,hx]

theorem monoWeight_finsetCube (r : ℝ) (S : Finset X) :
    TalagrandConjectures.monoWeight r (finsetCube S) = r^S.card := by
  simp only [TalagrandConjectures.monoWeight, finsetCube, Equiv.coe_fn_mk, decide_eq_true_eq]
  rw [← Finset.prod_filter]
  simp

def cubeFamily (A : Set (TalagrandConjectures.Cube X)) : Finset (Finset X) :=
  univ.filter (fun S=>finsetCube S ∈ A)

def IntegralSmall (r : ℝ) (A : Set (TalagrandConjectures.Cube X)) : Prop := Small r (cubeFamily A)

theorem cap_sum_ge_one {I : Type} [DecidableEq I] (E : Finset I) (f : I→ℝ)
    (hf : ∀ i∈E, 0≤f i) (hs : 1≤∑i∈E,f i) : 1≤∑i∈E,min 1 (f i) := by
  by_cases he : ∃i∈E,1≤f i
  · obtain ⟨i,hi,hi1⟩ := he
    have h := Finset.single_le_sum (f := fun i=>min 1 (f i))
      (fun i hi=>le_min (by norm_num) (hf i hi)) hi
    simpa [min_eq_left hi1] using h
  · have hpoint (i) (hi : i∈E) : min 1 (f i) = f i := by
      apply min_eq_right
      by_contra h
      exact he ⟨i,hi,le_of_not_ge h⟩
    simpa only [Finset.sum_congr rfl hpoint] using hs

theorem weaklySmall_fractional {r : ℝ} (hr : 0≤r)
    {A : Set (TalagrandConjectures.Cube X)} (h : TalagrandConjectures.WeaklySmall r A) :
    ∃g, FractionalCover r (cubeFamily A) g := by
  obtain ⟨c,hc,hcost,hcover⟩ := h
  let g : Finset X → ℝ := fun S=>min 1 (c (finsetCube S))
  refine ⟨g, (fun S=>⟨le_min (by norm_num) (hc _),min_le_left _ _⟩), ?_, ?_⟩
  · intro H hH
    have hJ : finsetCube H∈A := (Finset.mem_filter.mp hH).2
    have he : (∑ S∈H.powerset,c (finsetCube S)) =
        ∑I : TalagrandConjectures.Cube X,if I≤finsetCube H then c I else 0 := by
      rw [← Equiv.sum_comp finsetCube (fun I=>if I≤finsetCube H then c I else 0)]
      simp_rw [finsetCube_le]
      rw [← Finset.sum_filter]
      congr 1
      ext S; simp
    exact cap_sum_ge_one H.powerset (fun S=>c (finsetCube S)) (fun S _=>hc _) (he ▸ hcover _ hJ)
  · calc
      (∑S,g S*r^S.card) ≤ ∑S,c (finsetCube S)*TalagrandConjectures.monoWeight r (finsetCube S) := by
        apply Finset.sum_le_sum
        intro S _
        rw [monoWeight_finsetCube]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hr _)
      _ = ∑I,c I*TalagrandConjectures.monoWeight r I := Equiv.sum_comp (finsetCube (X:=X)) (fun I=>c I*TalagrandConjectures.monoWeight r I)
      _ ≤ 1/2 := hcost

theorem weaklySmall_integral {r : ℝ} (hr : 0≤r)
    {A : Set (TalagrandConjectures.Cube X)} (h : TalagrandConjectures.WeaklySmall r A) :
    IntegralSmall (r/comparisonConstant) A := by
  obtain ⟨g,hg⟩ := weaklySmall_fractional hr h
  exact fractional_to_integral hr hg

theorem IntegralSmall.mono {r : ℝ} {A B : Set (TalagrandConjectures.Cube X)}
    (h : IntegralSmall r A) (hBA : B⊆A) : IntegralSmall r B := by
  apply h.mono_family
  intro S hS
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBA (Finset.mem_filter.mp hS).2⟩

theorem IntegralSmall.mono_density {p r : ℝ} (hp : 0≤p) (hpr : p≤r)
    {A : Set (TalagrandConjectures.Cube X)} (h : IntegralSmall r A) : IntegralSmall p A :=
  Small.mono_density hp hpr h

/-- Corollary 4.1 in small-vs-weakly-small.pdf, equivalently Corollary 1.2
in Talagrand-discrete-convexity-conjecture.pdf. The weak inequality at density
one half is included. -/
theorem integral_two_unions {p : ℝ} (hp : 0<p) (hp1 : p<1)
    (A : Set (TalagrandConjectures.Cube X)) (hm : (1:ℝ)/2 ≤ TalagrandConjectures.measure p A) :
    IntegralSmall (p/(50*(512:ℝ)^4)) (TalagrandConjectures.badTwo A) := by
  have h := weaklySmall_integral (show 0≤p/2 by positivity)
    (TalagrandConjectures.li_weaklySmall_badTwo_half hp hp1 A hm)
  have he : p/(50*(512:ℝ)^4) = p/2/comparisonConstant := by norm_num [comparisonConstant]; ring
  rw [he]; exact h

end
end TalagrandIntegral
