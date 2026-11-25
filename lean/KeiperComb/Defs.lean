import Mathlib

/-!
# Definitions for the comb argument (Theorem A', runs at most 621 under RH)

Everything the statement needs, no proofs.  Index conventions:

* `c : ℕ → ℝ` is the Li second-difference sequence, `c n = λ_{n+1} - 2 λ_n + λ_{n-1}` with
  `λ_0 = 0`, for `n ≥ 1`.  It is a parameter pinned by `LiSecondDiff c`, not defined here.
* zero number 1 of the paper is index `0` here; the data of zero `k` is `γ k`.
* `zetaMult ρ` is the multiplicity of `ρ` as a nontrivial zero and is `0` off the nontrivial
  zeros, so a sum over all of `ℂ` is a sum over the nontrivial zeros with multiplicity.
-/

open Complex Finset

namespace KeiperComb

noncomputable section

/-- Nontrivial zeros of `riemannZeta`, exactly the side conditions of Mathlib's
`RiemannHypothesis`. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

open Classical in
/-- Multiplicity of a nontrivial zero (order of vanishing), `0` elsewhere. -/
def zetaMult (ρ : ℂ) : ℕ :=
  if IsNontrivialZero ρ then analyticOrderNatAt riemannZeta ρ else 0

/-- Li's formula, second-difference form (literature-shaped, unconditional): for `n ≥ 1`,
`-c_n = ∑_ρ m_ρ (1 - 1/ρ)^(n-1) / ρ^2`, an unconditionally (hence absolutely) summable family. -/
def LiSecondDiff (c : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    HasSum (fun ρ : ℂ => (zetaMult ρ : ℂ) * (1 - 1 / ρ) ^ (n - 1) / ρ ^ 2) (-(c n : ℂ))

/-- Li's weight sum: `∑_ρ m_ρ / (ρ (1 - ρ)) = 2 + γ_E - log (4 π)` (twice `λ_1`). -/
def LiWeightSum : Prop :=
  HasSum (fun ρ : ℂ => (zetaMult ρ : ℂ) / (ρ * (1 - ρ)))
    ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) : ℝ) : ℂ)

/-- The 2000 (here `K`) certified zero intervals, as a Prop: each rational interval contains the
ordinate `γ` of a zero `1/2 + iγ` of `riemannZeta`.  Nothing more (not "exactly one"). -/
def ZeroIntervals (K : ℕ) (lo hi : ℕ → ℚ) : Prop :=
  ∀ k, k < K → ∃ γ : ℝ, (lo k : ℝ) ≤ γ ∧ γ ≤ (hi k : ℝ) ∧
    riemannZeta (1 / 2 + (γ : ℂ) * I) = 0

/-- Decidable facts about the interval data: positive, ordered, disjoint. -/
def IntervalsOrdered (K : ℕ) (lo hi : ℕ → ℚ) : Prop :=
  0 < lo 0 ∧ (∀ k, k < K → lo k ≤ hi k) ∧ (∀ k, k + 1 < K → hi k < lo (k + 1))

/-- The zero `1/2 + iγ`. -/
def zpt (γ : ℝ) : ℂ := 1 / 2 + (γ : ℂ) * I

/-- `q = 1 - 1/ρ`, of modulus one on the critical line. -/
def qOf (γ : ℝ) : ℂ := 1 - 1 / zpt γ

/-- `θ = arg q`, so that `q = e^{iθ}`. -/
def thetaOf (γ : ℝ) : ℝ := (qOf γ).arg

/-- The weight `w = 1 / (1/4 + γ²) = 1/|ρ|²`. -/
def wOf (γ : ℝ) : ℝ := 1 / (1 / 4 + γ ^ 2)

/-- `C = 2 + γ_E - log (4π)`, the total weight. -/
def Cconst : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- Unlisted weight `W = C - 2 ∑_{k<K} w_k`. -/
def Wtail (K : ℕ) (γ : ℕ → ℝ) : ℝ := Cconst - 2 * ∑ k ∈ range K, wOf (γ k)

/-- The integer vector `c(u)_j = ⌊u + j P + 1/2⌋`. -/
def cvec (P u : ℝ) (j : ℕ) : ℤ := ⌊u + j * P + 1 / 2⌋

/-- `B(v) = ∑_{j<M} a_j e^{i v_j θ}`. -/
def Bk (a : ℕ → ℝ) (M : ℕ) (θ : ℝ) (v : ℕ → ℤ) : ℂ :=
  ∑ j ∈ range M, (a j : ℂ) * Complex.exp (((v j : ℝ) * θ : ℝ) * I)

/-- `N(v) = W S + ∑_{k ≥ 1} 2 w_k |B_k(v)|`. -/
def Nbound (K M : ℕ) (w θ a : ℕ → ℝ) (W : ℝ) (v : ℕ → ℤ) : ℝ :=
  W * ∑ j ∈ range M, a j + ∑ k ∈ Ico 1 K, 2 * w k * ‖Bk a M (θ k) v‖

/-- The numeric facts, as one Prop, stated for EVERY choice of zeros in the intervals (the true
zeros, not the midpoints): `0 < θ_1 < π/2`, `M P_1 ≤ L`, the chain `V` contains `c(u)` for all
`u ∈ [0,1)`, and `N(v) < 2 w_1 S cos(θ_1/2)` for every `v ∈ V`. -/
def CombNumerics (K M L : ℕ) (a : ℕ → ℝ) (V : Set (ℕ → ℤ)) (lo hi : ℕ → ℚ) : Prop :=
  ∀ γ : ℕ → ℝ, (∀ k, k < K → (lo k : ℝ) ≤ γ k ∧ γ k ≤ (hi k : ℝ)) →
    0 < thetaOf (γ 0) ∧ thetaOf (γ 0) < Real.pi / 2 ∧
    (M : ℝ) * (2 * Real.pi / thetaOf (γ 0)) ≤ L ∧
    (∀ u ∈ Set.Ico (0 : ℝ) 1, cvec (2 * Real.pi / thetaOf (γ 0)) u ∈ V) ∧
    ∀ v ∈ V, Nbound K M (fun k => wOf (γ k)) (fun k => thetaOf (γ k)) a (Wtail K γ) v <
      2 * wOf (γ 0) * (∑ j ∈ range M, a j) * Real.cos (thetaOf (γ 0) / 2)

end
end KeiperComb
