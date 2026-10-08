import TalagrandIntegral.Colorings

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X] {s t : ℕ}

abbrev MoveType (s : ℕ) := {ij : Fin (s+1) × Fin (s+1) // ij.1 < ij.2}
def moveCut (m : MoveType s) : Fin s :=
  ⟨m.val.1.val, by have h := m.property; have h' := m.val.2.isLt; omega⟩

def moveWord {a z : Coloring X s} (e : Fin t ≃ ↥(changed a z)) : Fin t → MoveType s :=
  fun j => ⟨(z (e j), a (e j)), (mem_filter.mp (e j).property).2⟩

def wordCrossings (u : Fin t → MoveType s) (i : Fin s) : Finset (Fin t) :=
  univ.filter (fun j => (u j).val.1.val ≤ i.val ∧ i.val < (u j).val.2.val)

theorem crossings_card_word {a z : Coloring X s} (e : Fin t ≃ ↥(changed a z)) (i : Fin s) :
    (crossings a z i).card = (wordCrossings (moveWord e) i).card := by
  symm
  apply Finset.card_bij (fun j _ => (e j).val)
  · intro j hj
    simpa [wordCrossings, moveWord, crossings] using hj
  · intro j hj k hk he
    exact e.injective (Subtype.ext he)
  · intro x hx
    have hc : x ∈ changed a z := by
      simp only [crossings, mem_filter, mem_univ, true_and] at hx
      exact mem_filter.mpr ⟨mem_univ x, (show (z x).val < (a x).val from lt_of_le_of_lt hx.1 hx.2)⟩
    refine ⟨e.symm ⟨x, hc⟩, ?_, ?_⟩
    · simpa [wordCrossings, moveWord, crossings] using hx
    · simp

theorem word_reconstructs {a b z : Coloring X s} (ha : z ≤ a) (hb : z ≤ b)
    (e : Fin t ≃ ↥(changed a z)) (f : Fin t ≃ ↥(changed b z))
    (hword : moveWord e = moveWord f)
    (hpos : ∀ j, (e j).val = (f j).val) : a = b := by
  funext x
  by_cases hx : x ∈ changed a z
  · let j := e.symm ⟨x, hx⟩
    have hex : (e j).val = x := by simp [j]
    have hfx : (f j).val = x := (hpos j).symm.trans hex
    have h := congrArg (fun u => (u j).val.2) hword
    simpa [moveWord, hex, hfx] using h
  · have hbx : x ∉ changed b z := by
      intro hbx
      let j := f.symm ⟨x, hbx⟩
      have he : (e j).val = x := (hpos j).trans (by simp [j])
      exact hx (he ▸ (e j).property)
    have ha' : ¬ z x < a x := by simpa [changed] using hx
    have hb' : ¬ z x < b x := by simpa [changed] using hbx
    exact (le_antisymm (le_of_not_gt ha') (ha x)).trans
      (le_antisymm (le_of_not_gt hb') (hb x)).symm

/-- A complete sequence of move types determines common candidate sets.
Using ordered encodings avoids a separate multinomial/AM--GM calculation. -/
theorem common_candidate_sets {F : Finset (Finset X)} {w : Finset X → X → ℝ}
    (hw0 : ∀ H ∈ F, ∀ x, 0 ≤ w H x) (hw1 : ∀ H ∈ F, ∑ x, w H x = 1)
    (z : Coloring X s) (u : Fin t → MoveType s) :
    ∃ R : Fin t → Finset X,
      (∀ j, ((R j).card : ℝ) ≤ (t:ℝ)*(2:ℝ)^((u j).val.1.val+1)) ∧
      ∀ a : Coloring X s, MinimalMove F w a z →
        ∀ e : Fin t ≃ ↥(changed a z), moveWord e = u → ∀ j, (e j).val ∈ R j := by
  by_cases hne : ∃ a : Coloring X s, MinimalMove F w a z ∧
      ∃ e : Fin t ≃ ↥(changed a z), moveWord e = u
  · obtain ⟨a₀, ha₀, e₀, he₀⟩ := hne
    obtain ⟨H, hH, hfeas⟩ := ha₀.2.1
    have hcut (i : Fin s) : ∃ ε, Admissible (w H) (initial z i) (deficit i)
        (wordCrossings u i).card ε ∧
        ((univ.filter (fun x => ε < w H x)).card : ℝ) ≤
          (wordCrossings u i).card / deficit i := by
      have hh := hfeas i
      rw [crossings_card_word e₀ i, he₀] at hh
      obtain ⟨ε, hε, _, hcard⟩ := maximal_truncation (w H) (hw0 H hH) (hw1 H hH)
        (initial z i) (deficit_pos i) (deficit_lt_one i) (by positivity) hh
      exact ⟨ε, hε, hcard⟩
    choose ε hε hcard using hcut
    let R : Fin t → Finset X := fun j => univ.filter (fun x => ε (moveCut (u j)) < w H x)
    refine ⟨R, ?_, ?_⟩
    · intro j
      have h := hcard (moveCut (u j))
      have hc : ((wordCrossings u (moveCut (u j))).card : ℝ) ≤ (t:ℝ) := by
        exact_mod_cast (Finset.card_filter_le univ _).trans_eq (Finset.card_fin t)
      have hh := div_le_div_of_nonneg_right hc (deficit_pos (moveCut (u j))).le
      refine h.trans (hh.trans_eq ?_)
      simp [deficit, moveCut, div_div]
    · intro a ha e he j
      have hm : ∀ i, Admissible (w H) (initial z i) (deficit i) (crossings a z i).card (ε i) := by
        intro i
        rw [crossings_card_word e i, he]
        exact hε i
      have hx : z (e j) < a (e j) := (mem_filter.mp (e j).property).2
      have h := minimal_move_reconstruction ha hH ε hm (e j) hx
      have hi : moveCut (u j) = ⟨(z (e j)).val, by have h := (a (e j)).isLt; omega⟩ := by
        apply Fin.ext
        have hh := congrArg (fun v => (v j).val.1.val) he
        exact hh.symm
      simpa [R, hi] using h
  · refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro j; simp
    · intro a ha e he
      exact False.elim (hne ⟨a, ha, e, he⟩)

end
end TalagrandIntegral
