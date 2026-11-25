import KeiperComb.Numerics711Zero1
import KeiperComb.Numerics711Cert

/-! B2, zero 1, the chain: `P = 2 pi / theta_1` lies in `[Plo, Phi]` and `cvec P u` is a chain vector. -/

open Complex Finset

set_option maxHeartbeats 800000

namespace KeiperComb.N711

lemma cv_eq (P u : ℝ) (j : ℕ) (n : ℤ) (h1 : (n : ℝ) ≤ u + j * P + 1 / 2)
    (h2 : u + j * P + 1 / 2 < n + 1) : cvec P u j = n :=
  Int.floor_eq_iff.mpr ⟨h1, h2⟩

macro "leafc" : tactic =>
  `(tactic| (intro j hj; interval_cases j <;> (apply cv_eq <;> norm_num <;> linarith)))

lemma gw_tight (γ : ℝ) (hl : (15177044530 : ℝ) / 1073741824 ≤ γ) (hh : γ ≤ (15177046580 : ℝ) / 1073741824) :
    (7065932839 : ℝ) / 100000000000 ≤ γ * wOf γ ∧ γ * wOf γ ≤ (220810431 : ℝ) / 3125000000 := by
  have hq : (0 : ℝ) < 1 / 4 + γ ^ 2 := by positivity
  have hp : 0 ≤ (γ - 15177044530 / 1073741824) * (15177046580 / 1073741824 - γ) :=
    mul_nonneg (by linarith) (by linarith)
  unfold wOf
  rw [mul_one_div]
  constructor
  · rw [le_div_iff₀ hq]; nlinarith
  · rw [div_le_iff₀ hq]; nlinarith

theorem P_bounds (γ : ℝ) (hl : (15177044530 : ℝ) / 1073741824 ≤ γ) (hh : γ ≤ (15177046580 : ℝ) / 1073741824) :
    (1110601 : ℝ) / 12500 ≤ 2 * Real.pi / thetaOf γ ∧ 2 * Real.pi / thetaOf γ ≤ (88848139 : ℝ) / 1000000 := by
  have hγ : (1 : ℝ) ≤ γ := by linarith
  obtain ⟨hg1, hg2⟩ := gw_tight γ hl hh
  have hlo : (14143651 : ℝ) / 200000000 ≤ thetaOf γ :=
    theta_ge γ _ hγ (by norm_num) (by norm_num) (by norm_num; linarith)
  have hup : thetaOf γ ≤ (70718301 : ℝ) / 1000000000 :=
    theta_le γ _ hγ (by norm_num) (by norm_num) (by norm_num; linarith)
  have h0 : 0 < thetaOf γ := by linarith
  have pl := Real.pi_gt_d20
  have pu := Real.pi_lt_d20
  constructor
  · rw [le_div_iff₀ h0]; nlinarith
  · rw [div_le_iff₀ h0]; nlinarith

lemma leaf0 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (c : u < (711:ℝ)/2 - 4*P) :
    ∀ j, j < 8 → cvec P u j = (([0, 89, 178, 267, 355, 444, 533, 622] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf1 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (c : u < (889:ℝ)/2 - 5*P) :
    ∀ j, j < 8 → cvec P u j = (([0, 89, 178, 267, 356, 444, 533, 622] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf2 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (n1 : ¬ (u < (889:ℝ)/2 - 5*P)) (c : u < (1067:ℝ)/2 - 6*P) :
    ∀ j, j < 8 → cvec P u j = (([0, 89, 178, 267, 356, 445, 533, 622] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf3 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (n1 : ¬ (u < (889:ℝ)/2 - 5*P)) (n2 : ¬ (u < (1067:ℝ)/2 - 6*P)) (c : u < (1:ℝ)/2) :
    ∀ j, j < 8 → cvec P u j = (([0, 89, 178, 267, 356, 445, 534, 622] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf4 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (n1 : ¬ (u < (889:ℝ)/2 - 5*P)) (n2 : ¬ (u < (1067:ℝ)/2 - 6*P)) (n3 : ¬ (u < (1:ℝ)/2)) (c : u < (1245:ℝ)/2 - 7*P) :
    ∀ j, j < 8 → cvec P u j = (([1, 89, 178, 267, 356, 445, 534, 622] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf5 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (n1 : ¬ (u < (889:ℝ)/2 - 5*P)) (n2 : ¬ (u < (1067:ℝ)/2 - 6*P)) (n3 : ¬ (u < (1:ℝ)/2)) (n4 : ¬ (u < (1245:ℝ)/2 - 7*P)) (c : u < (179:ℝ)/2 - P) :
    ∀ j, j < 8 → cvec P u j = (([1, 89, 178, 267, 356, 445, 534, 623] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf6 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (n1 : ¬ (u < (889:ℝ)/2 - 5*P)) (n2 : ¬ (u < (1067:ℝ)/2 - 6*P)) (n3 : ¬ (u < (1:ℝ)/2)) (n4 : ¬ (u < (1245:ℝ)/2 - 7*P)) (n5 : ¬ (u < (179:ℝ)/2 - P)) (c : u < (357:ℝ)/2 - 2*P) :
    ∀ j, j < 8 → cvec P u j = (([1, 90, 178, 267, 356, 445, 534, 623] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf7 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (n1 : ¬ (u < (889:ℝ)/2 - 5*P)) (n2 : ¬ (u < (1067:ℝ)/2 - 6*P)) (n3 : ¬ (u < (1:ℝ)/2)) (n4 : ¬ (u < (1245:ℝ)/2 - 7*P)) (n5 : ¬ (u < (179:ℝ)/2 - P)) (n6 : ¬ (u < (357:ℝ)/2 - 2*P)) (c : u < (535:ℝ)/2 - 3*P) :
    ∀ j, j < 8 → cvec P u j = (([1, 90, 179, 267, 356, 445, 534, 623] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

lemma leaf8 (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (n0 : ¬ (u < (711:ℝ)/2 - 4*P)) (n1 : ¬ (u < (889:ℝ)/2 - 5*P)) (n2 : ¬ (u < (1067:ℝ)/2 - 6*P)) (n3 : ¬ (u < (1:ℝ)/2)) (n4 : ¬ (u < (1245:ℝ)/2 - 7*P)) (n5 : ¬ (u < (179:ℝ)/2 - P)) (n6 : ¬ (u < (357:ℝ)/2 - 2*P)) (n7 : ¬ (u < (535:ℝ)/2 - 3*P)) :
    ∀ j, j < 8 → cvec P u j = (([1, 90, 179, 268, 356, 445, 534, 623] : List Nat).getD j 0 : ℤ) := by
  try push Not at *
  leafc

theorem chain_mem (P u : ℝ) (hP1 : (1110601 : ℝ) / 12500 ≤ P) (hP2 : P ≤ (88848139 : ℝ) / 1000000)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ r ∈ chainVecs, ∀ j, j < 8 → cvec P u j = (r.getD j 0 : ℤ) := by
  by_cases c0 : u < (711:ℝ)/2 - 4*P
  · exact ⟨[0, 89, 178, 267, 355, 444, 533, 622], by decide, leaf0 P u hP1 hP2 hu0 hu1 c0⟩
  have n0 := c0
  by_cases c1 : u < (889:ℝ)/2 - 5*P
  · exact ⟨[0, 89, 178, 267, 356, 444, 533, 622], by decide, leaf1 P u hP1 hP2 hu0 hu1 n0 c1⟩
  have n1 := c1
  by_cases c2 : u < (1067:ℝ)/2 - 6*P
  · exact ⟨[0, 89, 178, 267, 356, 445, 533, 622], by decide, leaf2 P u hP1 hP2 hu0 hu1 n0 n1 c2⟩
  have n2 := c2
  by_cases c3 : u < (1:ℝ)/2
  · exact ⟨[0, 89, 178, 267, 356, 445, 534, 622], by decide, leaf3 P u hP1 hP2 hu0 hu1 n0 n1 n2 c3⟩
  have n3 := c3
  by_cases c4 : u < (1245:ℝ)/2 - 7*P
  · exact ⟨[1, 89, 178, 267, 356, 445, 534, 622], by decide, leaf4 P u hP1 hP2 hu0 hu1 n0 n1 n2 n3 c4⟩
  have n4 := c4
  by_cases c5 : u < (179:ℝ)/2 - P
  · exact ⟨[1, 89, 178, 267, 356, 445, 534, 623], by decide, leaf5 P u hP1 hP2 hu0 hu1 n0 n1 n2 n3 n4 c5⟩
  have n5 := c5
  by_cases c6 : u < (357:ℝ)/2 - 2*P
  · exact ⟨[1, 90, 178, 267, 356, 445, 534, 623], by decide, leaf6 P u hP1 hP2 hu0 hu1 n0 n1 n2 n3 n4 n5 c6⟩
  have n6 := c6
  by_cases c7 : u < (535:ℝ)/2 - 3*P
  · exact ⟨[1, 90, 179, 267, 356, 445, 534, 623], by decide, leaf7 P u hP1 hP2 hu0 hu1 n0 n1 n2 n3 n4 n5 n6 c7⟩
  have n7 := c7
  exact ⟨[1, 90, 179, 268, 356, 445, 534, 623], by decide, leaf8 P u hP1 hP2 hu0 hu1 n0 n1 n2 n3 n4 n5 n6 n7⟩

end KeiperComb.N711
