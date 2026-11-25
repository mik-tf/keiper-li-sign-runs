import KeiperComb.Numerics711Core
import KeiperComb.Numerics711Real

/-!
# B2 glue: soundness of the integer checker `checkZeroAll` against the real per-zero bound

`checkZeroAll_sound`: if the kernel check succeeds on the data of one zero (`N`, the grid midpoint
`N / 2^30`, and for each chain vector the witnesses `rho`, `U`), then for EVERY real `γ` in
`[(N - Hw)/2^30, (N + Hw)/2^30]` and every chain vector `v`,
`2 w(γ) ‖∑_j (A_j/2^50) q(γ)^{v_j}‖ ≤ U / 2^40`.
-/

open Complex Finset

namespace KeiperComb.N711

def gc (z : Int × Int) : ℂ := ⟨z.1, z.2⟩

lemma gc_mul (a b : Int × Int) : gc (gmul a b) = gc a * gc b := by
  apply Complex.ext <;> simp [gc, gmul] <;> ring

lemma gc_one : gc (1, 0) = 1 := by apply Complex.ext <;> simp [gc]

lemma gpowBin_sound (z : Int × Int) : ∀ (f n : Nat), n < 2 ^ f → gc (gpowBin z f n) = (gc z) ^ n := by
  intro f
  induction f with
  | zero => intro n hn; have : n = 0 := by simpa using hn
            subst this; simp [gpowBin, gc_one]
  | succ f ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [gpowBin, gc_one]
    · have hlt : n / 2 < 2 ^ f := by rw [pow_succ] at hn; omega
      have e : (gc z) ^ n = (gc z) ^ (n / 2) * (gc z) ^ (n / 2) * (gc z) ^ (n % 2) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      simp only [gpowBin, h0, if_false]
      by_cases h1 : n % 2 = 1
      · simp only [h1, if_true, gc_mul, ih _ hlt]; rw [e, h1]; ring
      · have : n % 2 = 0 := by omega
        simp only [h1, if_false, gc_mul, ih _ hlt]; rw [e, this]; ring

lemma dedupAux_mem : ∀ (f : Nat) (l : List Nat), l.length ≤ f → ∀ x ∈ l, x ∈ dedupAux f l := by
  intro f
  induction f with
  | zero => intro l hl x hx; have : l = [] := List.length_eq_zero_iff.mp (by omega)
            subst this; simp at hx
  | succ f ih =>
    intro l hl x hx
    cases l with
    | nil => simp at hx
    | cons y ys =>
      simp only [dedupAux]
      by_cases hxy : x = y
      · subst hxy; simp
      · have hx' : x ∈ ys := by simpa [hxy] using hx
        have : x ∈ ys.filter (· != y) := by simp [List.mem_filter, hxy, hx']
        exact List.mem_cons_of_mem _ (ih _ (le_trans (List.length_filter_le _ _) (by simp at hl; omega)) x this)

lemma mem_dedup {l : List Nat} {x : Nat} (h : x ∈ l) : x ∈ dedup l := dedupAux_mem _ _ le_rfl x h

lemma mem_flat (vs : List (List Nat)) (e : Nat) (v : List Nat) (hv : v ∈ vs) (he : e ∈ v) :
    e ∈ vs.foldl (· ++ ·) [] := by
  have : ∀ (vs : List (List Nat)) (init : List Nat), (e ∈ init ∨ ∃ v ∈ vs, e ∈ v) →
      e ∈ vs.foldl (· ++ ·) init := by
    intro vs
    induction vs with
    | nil => intro init h; rcases h with h | ⟨v, hv, _⟩ <;> simp_all
    | cons w ws ih =>
      intro init h
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | ⟨v, hv, he⟩
      · left; simp [h]
      · rcases List.mem_cons.mp hv with rfl | hv
        · left; simp [he]
        · right; exact ⟨v, hv, he⟩
  exact this vs [] (Or.inr ⟨v, hv, he⟩)

lemma lookupPow_map (keys : List Nat) (f : Nat → Int × Int) (e : Nat) (he : e ∈ keys) :
    lookupPow (keys.map fun e => (e, f e)) e = f e := by
  unfold lookupPow
  cases h : (keys.map fun e => (e, f e)).find? (fun p => p.1 == e) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simp) (h (e, f e) (by simp [he]))
  | some p =>
    have h1 := List.find?_some h
    have hm := List.mem_of_find?_eq_some h
    simp only [List.mem_map] at hm
    obtain ⟨a, _, rfl⟩ := hm
    simp at h1; subst h1; rfl

lemma le_foldl_max : ∀ (l : List Nat) (init e : Nat), e ∈ l → e ≤ l.foldl max init := by
  intro l
  induction l with
  | nil => intro init e h; simp at h
  | cons x xs ih =>
    intro init e h
    simp only [List.foldl_cons]
    have hmono : ∀ (l : List Nat) (a b : Nat), a ≤ b → a ≤ l.foldl max b := by
      intro l; induction l with
      | nil => intro a b h; simpa using h
      | cons y ys ih2 => intro a b h; simp only [List.foldl_cons]; exact ih2 _ _ (le_trans h (le_max_left _ _))
    rcases List.mem_cons.mp h with rfl | h
    · exact hmono _ _ _ (le_max_right _ _)
    · exact ih _ _ h

/-- mirror of the code of `checkZeroAll`, with named helpers -/
def stepF (tab : List (Nat × (Int × Int))) (D vm : Nat) (acc : Int × Int) (p : Nat × Nat) : Int × Int :=
  let pw := lookupPow tab p.2
  let f : Int := ((p.1 * D ^ (vm - p.2) : Nat) : Int)
  (acc.1 + f * pw.1, acc.2 + f * pw.2)

def chkOne (A : List Nat) (tab : List (Nat × (Int × Int))) (D : Nat) (Elo : Int) (SA : Nat)
    (v : List Nat) (rho U : Nat) : Bool :=
  let vm : Nat := v.foldl max 0
  let X : Int := ((A.zip v).foldl (stepF tab D vm) (0, 0)).1
  let Y : Int := ((A.zip v).foldl (stepF tab D vm) (0, 0)).2
  let den : Int := ((2 ^ 50 * D ^ vm : Nat) : Int)
  decide (2 ^ 80 * (X * X + Y * Y) ≤ ((rho : Int) * den) ^ 2) &&
  decide (2 ^ 61 * (rho : Int) * Elo + 2 ^ 81 * (SA : Int) * vm * Hw ≤ (U : Int) * Elo ^ 2)

def tabOf (vs : List (List Nat)) (N : Nat) : List (Nat × (Int × Int)) :=
  (dedup (vs.foldl (· ++ ·) [])).map fun e =>
    (e, gpowBin (((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)) 11 e)

def checkZeroAll' (A : List Nat) (vs : List (List Nat)) (col : List (Nat × Nat × Nat)) : Bool :=
  match col with
  | [] => true
  | c0 :: _ =>
    (vs.zip col).all fun q =>
      chkOne A (tabOf vs c0.1) (c0.1 * c0.1 + 2 ^ 58) (((c0.1 : Int) - Hw) ^ 2 + 2 ^ 58)
        (A.foldl (· + ·) 0) q.1 q.2.2.1 q.2.2.2

theorem checkZeroAll_eq (A vs col) : checkZeroAll A vs col = checkZeroAll' A vs col := by
  unfold checkZeroAll checkZeroAll' chkOne stepF tabOf; rfl

end KeiperComb.N711
