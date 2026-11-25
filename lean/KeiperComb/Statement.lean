import KeiperComb.Comb
import KeiperComb.Tail

/-!
# Theorem A' (runs of Keiper-Li signs at most 621 under RH), L1 statement

The analytic and numeric inputs are named hypotheses (Props in the signature, never `axiom`):

* `RiemannHypothesis` (Mathlib);
* `LiSecondDiff c`, `LiWeightSum` (Li's formula, literature-shaped, `HasSum`);
* `ZeroIntervals K lo hi` (one zero in each certified interval, nothing more), with the decidable
  facts `IntervalsOrdered K lo hi`;
* `CombNumerics K M L a V lo hi` (the finite numeric inequalities, for every choice of zeros in
  the intervals), to be discharged in L2.

The name says what it is: Theorem A' follows from these hypotheses, it is not proved from RH alone.
-/

open Finset

namespace KeiperComb

/-- Window form, generic in the data. -/
theorem theoremA'_of_LiFormula {c : ℕ → ℝ} {K M L : ℕ} {lo hi : ℕ → ℚ} {a : ℕ → ℝ}
    {V : Set (ℕ → ℤ)}
    (hK : 1 ≤ K) (hord : IntervalsOrdered K lo hi)
    (ha : ∀ j, j < M → 0 ≤ a j) (hS : 0 < ∑ j ∈ range M, a j)
    (hRH : RiemannHypothesis) (hLi2 : LiSecondDiff c) (hLiW : LiWeightSum)
    (hZ : ZeroIntervals K lo hi) (hnum : CombNumerics K M L a V lo hi) :
    ∀ n0, 1 ≤ n0 →
      (∃ n, n0 ≤ n ∧ n < n0 + L ∧ 0 < c n) ∧ (∃ n, n0 ≤ n ∧ n < n0 + L ∧ c n < 0) := by
  intro n0 hn0
  choose! γ hγ1 hγ2 hγ3 using hZ
  have hγ : ∀ k, k < K → (lo k : ℝ) ≤ γ k ∧ γ k ≤ (hi k : ℝ) := fun k hk => ⟨hγ1 k hk, hγ2 k hk⟩
  obtain ⟨e, hc, he⟩ := tail_decomp hRH hLi2 hLiW hord hγ (fun k hk => by simpa [zpt] using hγ3 k hk)
  obtain ⟨hθ0, hθ1, hML, hV, hN⟩ := hnum γ hγ
  have hw : ∀ k, 0 < wOf (γ k) := fun k => by unfold wOf; positivity
  exact comb_both (w := fun k => wOf (γ k)) (θ := fun k => thetaOf (γ k)) (e := e) (a := a)
    (W := Wtail K γ) (V := V) hK (fun k _ => (hw k).le) (hw 0) hc he ha hS hθ0 hθ1 hML hV hN n0 hn0

/-- Run form: no window of `L` consecutive `n ≥ 1` has `c n ≥ 0` throughout, and none has
`c n ≤ 0` throughout; so every run of one sign has length at most `L - 1`. -/
theorem theoremA'_of_LiFormula_runs {c : ℕ → ℝ} {K M L : ℕ} {lo hi : ℕ → ℚ} {a : ℕ → ℝ}
    {V : Set (ℕ → ℤ)}
    (hK : 1 ≤ K) (hord : IntervalsOrdered K lo hi)
    (ha : ∀ j, j < M → 0 ≤ a j) (hS : 0 < ∑ j ∈ range M, a j)
    (hRH : RiemannHypothesis) (hLi2 : LiSecondDiff c) (hLiW : LiWeightSum)
    (hZ : ZeroIntervals K lo hi) (hnum : CombNumerics K M L a V lo hi) :
    ∀ n0, 1 ≤ n0 →
      ¬ (∀ n, n0 ≤ n → n < n0 + L → 0 ≤ c n) ∧ ¬ (∀ n, n0 ≤ n → n < n0 + L → c n ≤ 0) := by
  intro n0 hn0
  obtain ⟨⟨n, h1, h2, h3⟩, ⟨n', h1', h2', h3'⟩⟩ :=
    theoremA'_of_LiFormula hK hord ha hS hRH hLi2 hLiW hZ hnum n0 hn0
  exact ⟨fun h => absurd (h n' h1' h2') (not_le.mpr h3'),
    fun h => absurd (h n h1 h2) (not_le.mpr h3)⟩

/-- Tier 2: windows of 622 (`M = 7` troughs or crests), 2000 intervals. -/
theorem theoremA'_622 {c : ℕ → ℝ} {lo hi : ℕ → ℚ} {a : ℕ → ℝ} {V : Set (ℕ → ℤ)}
    (hord : IntervalsOrdered 2000 lo hi)
    (ha : ∀ j, j < 7 → 0 ≤ a j) (hS : 0 < ∑ j ∈ range 7, a j)
    (hRH : RiemannHypothesis) (hLi2 : LiSecondDiff c) (hLiW : LiWeightSum)
    (hZ : ZeroIntervals 2000 lo hi) (hnum : CombNumerics 2000 7 622 a V lo hi) :
    ∀ n0, 1 ≤ n0 →
      (∃ n, n0 ≤ n ∧ n < n0 + 622 ∧ 0 < c n) ∧ (∃ n, n0 ≤ n ∧ n < n0 + 622 ∧ c n < 0) :=
  theoremA'_of_LiFormula (by norm_num) hord ha hS hRH hLi2 hLiW hZ hnum

theorem theoremA'_622_runs {c : ℕ → ℝ} {lo hi : ℕ → ℚ} {a : ℕ → ℝ} {V : Set (ℕ → ℤ)}
    (hord : IntervalsOrdered 2000 lo hi)
    (ha : ∀ j, j < 7 → 0 ≤ a j) (hS : 0 < ∑ j ∈ range 7, a j)
    (hRH : RiemannHypothesis) (hLi2 : LiSecondDiff c) (hLiW : LiWeightSum)
    (hZ : ZeroIntervals 2000 lo hi) (hnum : CombNumerics 2000 7 622 a V lo hi) :
    ∀ n0, 1 ≤ n0 →
      ¬ (∀ n, n0 ≤ n → n < n0 + 622 → 0 ≤ c n) ∧ ¬ (∀ n, n0 ≤ n → n < n0 + 622 → c n ≤ 0) :=
  theoremA'_of_LiFormula_runs (by norm_num) hord ha hS hRH hLi2 hLiW hZ hnum

/-- Tier 1: windows of 711 (`M = 8`), closed-form slack, same checker. -/
theorem theoremA'_711 {c : ℕ → ℝ} {lo hi : ℕ → ℚ} {a : ℕ → ℝ} {V : Set (ℕ → ℤ)}
    (hord : IntervalsOrdered 2000 lo hi)
    (ha : ∀ j, j < 8 → 0 ≤ a j) (hS : 0 < ∑ j ∈ range 8, a j)
    (hRH : RiemannHypothesis) (hLi2 : LiSecondDiff c) (hLiW : LiWeightSum)
    (hZ : ZeroIntervals 2000 lo hi) (hnum : CombNumerics 2000 8 711 a V lo hi) :
    ∀ n0, 1 ≤ n0 →
      (∃ n, n0 ≤ n ∧ n < n0 + 711 ∧ 0 < c n) ∧ (∃ n, n0 ≤ n ∧ n < n0 + 711 ∧ c n < 0) :=
  theoremA'_of_LiFormula (by norm_num) hord ha hS hRH hLi2 hLiW hZ hnum

end KeiperComb
