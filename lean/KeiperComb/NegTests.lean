import KeiperComb.Statement

/-!
# Negative tests (S6): each is a PROVED fact, so the build stays green.

They show that the guards are not vacuous: a wrong window, a moved zero interval.
(Negative tests of the L2 checker, `check bad_data = false`, belong to B6.)
-/

open Finset

namespace KeiperComb

/-- Toy comb, one zero, `θ = π/5`, `P = 10`: the window bound `M P ≤ L` fails for `L = 2` ... -/
example : ¬ ((1 : ℝ) * (2 * Real.pi / (Real.pi / 5)) ≤ (2 : ℕ)) := by
  have hπ := Real.pi_pos
  have : (1 : ℝ) * (2 * Real.pi / (Real.pi / 5)) = 10 := by field_simp; ring
  rw [this]; norm_num

/-- ... and so does the conclusion: `c n = cos (n π/5)` has no negative term in `[1, 3)`. -/
example : ¬ ∃ n : ℕ, 1 ≤ n ∧ n < 1 + 2 ∧ Real.cos ((n : ℝ) * (Real.pi / 5)) < 0 := by
  rintro ⟨n, h1, h2, h3⟩
  have hπ := Real.pi_pos
  have hn : n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl <;> (apply absurd h3; apply not_lt.mpr; apply (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).le <;> push_cast <;> linarith)

/-- Overlapping intervals are refused by `IntervalsOrdered` (a moved zero interval). -/
example : ¬ IntervalsOrdered 2 (fun k => if k = 0 then 1 else 2) (fun k => if k = 0 then 2 else 3) := by
  intro h
  have := h.2.2 0 (by norm_num)
  norm_num at this

/-- A non-positive first interval is refused. -/
example : ¬ IntervalsOrdered 1 (fun _ => 0) (fun _ => 1) := by
  intro h
  have := h.1
  norm_num at this

/-- The good case, to show the refusals are not a trivial `False`. -/
example : IntervalsOrdered 2 (fun k => if k = 0 then 1 else 3) (fun k => if k = 0 then 2 else 4) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro k hk; interval_cases k <;> norm_num
  · intro k hk
    have : k = 0 := by omega
    subst this; norm_num

end KeiperComb
