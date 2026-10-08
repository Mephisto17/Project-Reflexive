import TalagrandIntegral.Truncation
import TalagrandIntegral.Basic

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X] {s : ℕ}

abbrev Coloring (X : Type) (s : ℕ) := X → Fin (s+1)
def initial (z : Coloring X s) (i : Fin s) : Finset X :=
  univ.filter (fun x => (z x).val ≤ i.val)
def changed (a z : Coloring X s) : Finset X := univ.filter (fun x => z x < a x)
def crossings (a z : Coloring X s) (i : Fin s) : Finset X :=
  univ.filter (fun x => (z x).val ≤ i.val ∧ i.val < (a x).val)
def moveLength (a z : Coloring X s) : ℕ := ∑ x, ((a x).val - (z x).val)
def deficit (i : Fin s) : ℝ := 1/(2:ℝ)^(i.val+1)

def Feasible (F : Finset (Finset X)) (w : Finset X → X → ℝ)
    (a z : Coloring X s) : Prop :=
  ∃ H ∈ F, ∀ i : Fin s, ∃ ε,
    Admissible (w H) (initial z i) (deficit i) (crossings a z i).card ε

def MinimalMove (F : Finset (Finset X)) (w : Finset X → X → ℝ)
    (a z : Coloring X s) : Prop :=
  z ≤ a ∧ Feasible F w a z ∧ ∃ H₀ ∈ F, changed a z ⊆ H₀ ∧
    ∀ z', z' ≤ a → Feasible F w a z' → changed a z' ⊆ H₀ →
      moveLength a z ≤ moveLength a z'

theorem deficit_pos (i : Fin s) : 0 < deficit i := by unfold deficit; positivity
theorem deficit_lt_one (i : Fin s) : deficit i < 1 := by
  unfold deficit
  rw [div_lt_one (by positivity)]
  exact one_lt_pow₀ (by norm_num) (by omega)

def delay (z : Coloring X s) (x : X) (hx : (z x).val < s) : Coloring X s :=
  Function.update z x ⟨(z x).val+1, by omega⟩

theorem delay_le {a z : Coloring X s} (hza : z ≤ a) {x : X} (hx : z x < a x)
    (hxs : (z x).val < s) : delay z x hxs ≤ a := by
  intro y
  by_cases hy : y = x
  · subst y; simp only [delay, Function.update_self]
    change (z x).val+1 ≤ (a x).val
    have h : (z x).val < (a x).val := hx
    omega
  · simpa [delay, hy] using hza y

theorem changed_delay_subset {a z : Coloring X s} {x : X} (hxs : (z x).val < s) :
    changed a (delay z x hxs) ⊆ changed a z := by
  intro y hy
  simp only [changed, mem_filter, mem_univ, true_and] at hy ⊢
  by_cases h : y = x
  · subst y; simp only [delay, Function.update_self] at hy
    exact lt_trans (by exact_mod_cast Nat.lt_succ_self _) hy
  · simpa [delay, h] using hy

theorem initial_delay (z : Coloring X s) (x : X) (hxs : (z x).val < s) (i : Fin s) :
    initial (delay z x hxs) i = if i.val = (z x).val then (initial z i).erase x else initial z i := by
  ext y
  by_cases hy : y = x
  · subst y
    simp only [initial, mem_filter, mem_univ, true_and, delay, Function.update_self]
    split_ifs with h <;> simp_all [Finset.mem_erase] <;> omega
  · split_ifs <;> simp [initial, delay, hy, Finset.mem_erase]

theorem crossings_delay {a z : Coloring X s} (x : X) (hxs : (z x).val < s) (i : Fin s) :
    crossings a (delay z x hxs) i =
      if i.val = (z x).val then (crossings a z i).erase x else crossings a z i := by
  ext y
  by_cases hy : y = x
  · subst y
    simp only [crossings, mem_filter, mem_univ, true_and, delay, Function.update_self]
    split_ifs with h <;> simp_all [Finset.mem_erase] <;> omega
  · split_ifs <;> simp [crossings, delay, hy, Finset.mem_erase]

theorem moveLength_delay {a z : Coloring X s} (hza : z ≤ a) (x : X)
    (hx : z x < a x) (hxs : (z x).val < s) :
    moveLength a (delay z x hxs) + 1 = moveLength a z := by
  unfold moveLength
  rw [← Finset.sum_erase_add _ _ (mem_univ x),
      ← Finset.sum_erase_add _ _ (mem_univ x)]
  have he : (∑ y ∈ univ.erase x, ((a y).val-(delay z x hxs y).val)) =
      ∑ y ∈ univ.erase x, ((a y).val-(z y).val) := by
    apply Finset.sum_congr rfl
    intro y hy
    simp [delay, (mem_erase.mp hy).1]
  rw [he]
  simp only [delay, Function.update_self]
  have hx' : (z x).val < (a x).val := hx
  omega

/-- Deleting a low-weight moved vertex preserves the charged truncation test. -/
theorem admissible_erase (w : X → ℝ) (A : Finset X) {d ε : ℝ} {m : ℕ}
    (h : Admissible w A d m ε) {x : X} (hx : x ∈ A) (hwx : w x ≤ ε) (hm : 0 < m) :
    Admissible w (A.erase x) d (m-1) ε := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro y hy
    by_cases he : y = x
    · simpa [he] using hwx
    · exact h.2.2.1 y (by simpa [mem_erase, he] using hy)
  · have he : truncSum w (A.erase x) d ε = truncSum w A d ε - min (w x) ε := by
      have hp (y : X) : min (w y) ε * ((if y ∈ A.erase x then 1 else 0)-(1-d)) =
          min (w y) ε * ((if y ∈ A then 1 else 0)-(1-d)) -
            (if y = x then min (w x) ε else 0) := by
        by_cases hy : y = x
        · subst y; simp [hx]; ring
        · simp [mem_erase, hy]
      simp_rw [truncSum, hp, Finset.sum_sub_distrib]
      simp
    rw [he]
    have hm' : ((m-1:ℕ):ℝ) = (m:ℝ)-1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hmin : min (w x) ε ≤ ε := min_le_right _ _
    nlinarith [h.2.2.2]

/-- The reconstruction inclusion (2.9), for any common feasible witness.
Minimality concerns total color displacement, not just the number of vertices. -/
theorem minimal_move_reconstruction {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    {a z : Coloring X s} (hz : MinimalMove F w a z)
    {H : Finset X} (hH : H ∈ F) (ε : Fin s → ℝ)
    (hε : ∀ i, Admissible (w H) (initial z i) (deficit i) (crossings a z i).card (ε i))
    (x : X) (hx : z x < a x) :
    ε ⟨(z x).val, by have h := (a x).isLt; exact lt_of_lt_of_le hx (Nat.le_of_lt_succ h)⟩ < w H x := by
  have hxs : (z x).val < s := by have h := (a x).isLt; omega
  let i : Fin s := ⟨(z x).val, hxs⟩
  change ε i < w H x
  by_contra hn
  have hwx : w H x ≤ ε i := le_of_not_gt hn
  let z' := delay z x hxs
  have hfeas : Feasible F w a z' := by
    refine ⟨H, hH, ?_⟩
    intro j
    refine ⟨ε j, ?_⟩
    dsimp [z']
    rw [initial_delay, crossings_delay]
    by_cases hj : j.val = (z x).val
    · have hji : j = i := Fin.ext hj
      subst j
      simp only [i, if_true]
      have hmem : x ∈ crossings a z i := by simp [crossings, i, hx]
      rw [Finset.card_erase_of_mem hmem]
      simpa only [Nat.cast_sub (show 1 ≤ (crossings a z i).card from Finset.card_pos.mpr ⟨x, hmem⟩), Nat.cast_one] using admissible_erase (w H) (initial z i) (hε i)
        (by simp [initial, i]) hwx (Finset.card_pos.mpr ⟨x, hmem⟩)
    · simp only [if_neg hj]; exact hε j
  obtain ⟨H₀, hH₀, hsub, hmin⟩ := hz.2.2
  have hm := hmin z' (delay_le hz.1 hx hxs) hfeas ((changed_delay_subset hxs).trans hsub)
  have he := moveLength_delay hz.1 x hx hxs
  change moveLength a z' + 1 = moveLength a z at he
  omega

theorem exists_minimal_move {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw : ∀ H ∈ F, ∀ x, 0 ≤ w H x)
    (hsupp : ∀ H ∈ F, ∀ x ∉ H, w H x = 0)
    (a : Coloring X s) {H₀ : Finset X} (hH₀ : H₀ ∈ F) :
    ∃ z, MinimalMove F w a z ∧ changed a z ⊆ H₀ := by
  let z₀ : Coloring X s := fun x => if x ∈ H₀ then 0 else a x
  have hle : z₀ ≤ a := by intro x; dsimp [z₀]; split_ifs <;> simp
  have hsub : changed a z₀ ⊆ H₀ := by
    intro x hx
    by_contra hn
    simpa [changed, z₀, hn] using hx
  have hf : Feasible F w a z₀ := by
    refine ⟨H₀, hH₀, ?_⟩
    intro i
    refine ⟨0, admissible_zero (w H₀) (hw H₀ hH₀) _ _ _ ?_⟩
    intro x hx
    apply hsupp H₀ hH₀ x
    intro hxH
    exact hx (by simp [initial, z₀, hxH])
  let Z := univ.filter (fun z => z ≤ a ∧ Feasible F w a z ∧ changed a z ⊆ H₀)
  have hZ : Z.Nonempty := ⟨z₀, by simp [Z, hle, hf, hsub]⟩
  obtain ⟨z, hz, hmin⟩ := Z.exists_min_image (moveLength a) hZ
  have hz' := (mem_filter.mp hz).2
  refine ⟨z, ⟨hz'.1, hz'.2.1, H₀, hH₀, hz'.2.2, ?_⟩, hz'.2.2⟩
  intro z' hz' hf' hs'
  exact hmin z' (by simp [Z, hz', hf', hs'])

def BadColoring (F : Finset (Finset X)) (w : Finset X → X → ℝ) (a : Coloring X s) : Prop :=
  ¬ ∃ H ∈ F, ∀ i : Fin s, 1-deficit i ≤ ∑ x ∈ initial a i, w H x

theorem feasible_unchanged_not_bad {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw : ∀ H ∈ F, ∑ x, w H x = 1) (a : Coloring X s) (h : Feasible F w a a) :
    ¬ BadColoring F w a := by
  intro hb
  apply hb
  obtain ⟨H, hH, he⟩ := h
  refine ⟨H, hH, ?_⟩
  intro i
  obtain ⟨ε, hε⟩ := he i
  have hc : crossings a a i = ∅ := by ext x; simp [crossings]
  have ht := truncSum_untruncated (w H) (initial a i) (deficit i) ε
    (hw H hH) (deficit_pos i).le hε.2.2.1
  have h0 := hε.2.2.2
  rw [hc] at h0
  simp only [card_empty, Nat.cast_zero, zero_mul] at h0
  linarith

theorem bad_minimal_changed_nonempty {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw : ∀ H ∈ F, ∑ x, w H x = 1) {a z : Coloring X s}
    (ha : BadColoring F w a) (hz : MinimalMove F w a z) : (changed a z).Nonempty := by
  by_contra hn
  have he : z = a := by
    funext x
    apply le_antisymm (hz.1 x)
    by_contra h
    exact hn ⟨x, by simp [changed, lt_of_not_ge h]⟩
  subst z
  exact feasible_unchanged_not_bad hw a hz.2.1 ha

theorem not_small_minimal_cover {p : ℝ} (hp : 0 ≤ p)
    {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hF : ¬ Small p F) (hw : ∀ H ∈ F, ∀ x, 0 ≤ w H x)
    (hsupp : ∀ H ∈ F, ∀ x ∉ H, w H x = 0) (a : Coloring X s) :
    (1:ℝ)/2 < ∑ z : Coloring X s, if MinimalMove F w a z then p^(changed a z).card else 0 := by
  let Z := univ.filter (MinimalMove F w a)
  let G := Z.image (changed a)
  have hcover : Covers G F := by
    intro H hH
    obtain ⟨z, hz, hsub⟩ := exists_minimal_move hw hsupp a hH
    exact ⟨changed a z, mem_image.mpr ⟨z, by simp [Z, hz], rfl⟩, hsub⟩
  have hcost : coverCost p G ≤
      ∑ z : Coloring X s, if MinimalMove F w a z then p^(changed a z).card else 0 := by
    have h := Finset.sum_image_le_of_nonneg (s := Z) (g := changed a)
      (f := fun S : Finset X => p^S.card) (fun S _ => pow_nonneg hp _)
    simpa [coverCost, G, Z, Finset.sum_filter] using h
  by_contra hn
  exact hF ⟨G, hcover, hcost.trans (le_of_not_gt hn)⟩

end
end TalagrandIntegral
