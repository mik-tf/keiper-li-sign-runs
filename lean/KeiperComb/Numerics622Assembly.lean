import KeiperComb.Numerics622AsmGen
import KeiperComb.Numerics622Cert

import KeiperComb.Numerics622C00
import KeiperComb.Numerics622C01
import KeiperComb.Numerics622C02
import KeiperComb.Numerics622C03
import KeiperComb.Numerics622C04
import KeiperComb.Numerics622C05
import KeiperComb.Numerics622C06
import KeiperComb.Numerics622C07
import KeiperComb.Numerics622C08
import KeiperComb.Numerics622C09
import KeiperComb.Numerics622C10
import KeiperComb.Numerics622C11
import KeiperComb.Numerics622C12
import KeiperComb.Numerics622C13
import KeiperComb.Numerics622C14
import KeiperComb.Numerics622C15
import KeiperComb.Numerics622C16
import KeiperComb.Numerics622C17
import KeiperComb.Numerics622C18
import KeiperComb.Numerics622Chain
import KeiperComb.Numerics711Tail
import KeiperComb.Numerics711Zero1
import KeiperComb.Statement

/-! B3, final assembly (L = 622, runs at most 621). Indices: the paper counts zeros 1..2000, Lean 0..1999
(Lean index k is paper zero k+1; the chunk table lists Lean indices 1..1999).

* `NSall`/`USall i`: the 1999 grid ordinates (zeros 2 to 2000) and the per-zero bounds `U` for chain
  vector `i`, concatenated from the chunk modules C00 to C18.
* `good_all`: every chunk bound, for every zero interval, in one `Good` statement.
* `combNumerics_622`: `CombNumerics 2000 7 622` for the concrete data, no hypotheses.
* `theoremA'_622_numerics`: `theoremA'_622` with `CombNumerics` discharged. -/

open Complex Finset

set_option Elab.async false

namespace KeiperComb.N622

open KeiperComb.N711 (sum_range_getD_map sum_range_getD getD_mem foldl_add_sum Hw w_ge Wtail_le zero1_facts P_bounds)

def Ul (zs : List (List (Nat × Nat × Nat))) (i : ℕ) : List ℕ := (zs.getD i []).map (fun t => t.2.2)


theorem g_C00 (i : ℕ) (hi : i < 8) : Good i C00.nsC (Ul C00.zsAll i) :=
  chunk_good C00.zsAll C00.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C00.sound (by decide +kernel) i hi

theorem l_C00 : ∀ i, i < 8 → (Ul C00.zsAll i).length = C00.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C01 (i : ℕ) (hi : i < 8) : Good i C01.nsC (Ul C01.zsAll i) :=
  chunk_good C01.zsAll C01.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C01.sound (by decide +kernel) i hi

theorem l_C01 : ∀ i, i < 8 → (Ul C01.zsAll i).length = C01.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C02 (i : ℕ) (hi : i < 8) : Good i C02.nsC (Ul C02.zsAll i) :=
  chunk_good C02.zsAll C02.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C02.sound (by decide +kernel) i hi

theorem l_C02 : ∀ i, i < 8 → (Ul C02.zsAll i).length = C02.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C03 (i : ℕ) (hi : i < 8) : Good i C03.nsC (Ul C03.zsAll i) :=
  chunk_good C03.zsAll C03.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C03.sound (by decide +kernel) i hi

theorem l_C03 : ∀ i, i < 8 → (Ul C03.zsAll i).length = C03.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C04 (i : ℕ) (hi : i < 8) : Good i C04.nsC (Ul C04.zsAll i) :=
  chunk_good C04.zsAll C04.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C04.sound (by decide +kernel) i hi

theorem l_C04 : ∀ i, i < 8 → (Ul C04.zsAll i).length = C04.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C05 (i : ℕ) (hi : i < 8) : Good i C05.nsC (Ul C05.zsAll i) :=
  chunk_good C05.zsAll C05.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C05.sound (by decide +kernel) i hi

theorem l_C05 : ∀ i, i < 8 → (Ul C05.zsAll i).length = C05.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C06 (i : ℕ) (hi : i < 8) : Good i C06.nsC (Ul C06.zsAll i) :=
  chunk_good C06.zsAll C06.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C06.sound (by decide +kernel) i hi

theorem l_C06 : ∀ i, i < 8 → (Ul C06.zsAll i).length = C06.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C07 (i : ℕ) (hi : i < 8) : Good i C07.nsC (Ul C07.zsAll i) :=
  chunk_good C07.zsAll C07.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C07.sound (by decide +kernel) i hi

theorem l_C07 : ∀ i, i < 8 → (Ul C07.zsAll i).length = C07.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C08 (i : ℕ) (hi : i < 8) : Good i C08.nsC (Ul C08.zsAll i) :=
  chunk_good C08.zsAll C08.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C08.sound (by decide +kernel) i hi

theorem l_C08 : ∀ i, i < 8 → (Ul C08.zsAll i).length = C08.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C09 (i : ℕ) (hi : i < 8) : Good i C09.nsC (Ul C09.zsAll i) :=
  chunk_good C09.zsAll C09.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C09.sound (by decide +kernel) i hi

theorem l_C09 : ∀ i, i < 8 → (Ul C09.zsAll i).length = C09.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C10 (i : ℕ) (hi : i < 8) : Good i C10.nsC (Ul C10.zsAll i) :=
  chunk_good C10.zsAll C10.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C10.sound (by decide +kernel) i hi

theorem l_C10 : ∀ i, i < 8 → (Ul C10.zsAll i).length = C10.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C11 (i : ℕ) (hi : i < 8) : Good i C11.nsC (Ul C11.zsAll i) :=
  chunk_good C11.zsAll C11.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C11.sound (by decide +kernel) i hi

theorem l_C11 : ∀ i, i < 8 → (Ul C11.zsAll i).length = C11.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C12 (i : ℕ) (hi : i < 8) : Good i C12.nsC (Ul C12.zsAll i) :=
  chunk_good C12.zsAll C12.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C12.sound (by decide +kernel) i hi

theorem l_C12 : ∀ i, i < 8 → (Ul C12.zsAll i).length = C12.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C13 (i : ℕ) (hi : i < 8) : Good i C13.nsC (Ul C13.zsAll i) :=
  chunk_good C13.zsAll C13.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C13.sound (by decide +kernel) i hi

theorem l_C13 : ∀ i, i < 8 → (Ul C13.zsAll i).length = C13.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C14 (i : ℕ) (hi : i < 8) : Good i C14.nsC (Ul C14.zsAll i) :=
  chunk_good C14.zsAll C14.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C14.sound (by decide +kernel) i hi

theorem l_C14 : ∀ i, i < 8 → (Ul C14.zsAll i).length = C14.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C15 (i : ℕ) (hi : i < 8) : Good i C15.nsC (Ul C15.zsAll i) :=
  chunk_good C15.zsAll C15.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C15.sound (by decide +kernel) i hi

theorem l_C15 : ∀ i, i < 8 → (Ul C15.zsAll i).length = C15.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C16 (i : ℕ) (hi : i < 8) : Good i C16.nsC (Ul C16.zsAll i) :=
  chunk_good C16.zsAll C16.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C16.sound (by decide +kernel) i hi

theorem l_C16 : ∀ i, i < 8 → (Ul C16.zsAll i).length = C16.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C17 (i : ℕ) (hi : i < 8) : Good i C17.nsC (Ul C17.zsAll i) :=
  chunk_good C17.zsAll C17.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C17.sound (by decide +kernel) i hi

theorem l_C17 : ∀ i, i < 8 → (Ul C17.zsAll i).length = C17.nsC.length := by
  unfold Ul; decide +kernel


theorem g_C18 (i : ℕ) (hi : i < 8) : Good i C18.nsC (Ul C18.zsAll i) :=
  chunk_good C18.zsAll C18.nsC (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) C18.sound (by decide +kernel) i hi

theorem l_C18 : ∀ i, i < 8 → (Ul C18.zsAll i).length = C18.nsC.length := by
  unfold Ul; decide +kernel


theorem l_C02t : ∀ i, i < 8 → (Ul C02.zsAll i).tail.length = C02.nsC.tail.length := by
  intro i hi; simp [List.length_tail, l_C02 i hi]

theorem ne_C02 : C02.nsC ≠ [] := by decide +kernel


def NSall : List ℕ := C00.nsC ++ (C01.nsC ++ (C02.nsC ++ (C03.nsC ++ (C04.nsC ++ (C05.nsC ++ (C06.nsC ++ (C07.nsC ++ (C08.nsC ++ (C09.nsC ++ (C10.nsC ++ (C11.nsC ++ (C12.nsC ++ (C13.nsC ++ (C14.nsC ++ (C15.nsC ++ (C16.nsC ++ (C17.nsC ++ (C18.nsC))))))))))))))))))

def USall (i : ℕ) : List ℕ := Ul C00.zsAll i ++ (Ul C01.zsAll i ++ (Ul C02.zsAll i ++ (Ul C03.zsAll i ++ (Ul C04.zsAll i ++ (Ul C05.zsAll i ++ (Ul C06.zsAll i ++ (Ul C07.zsAll i ++ (Ul C08.zsAll i ++ (Ul C09.zsAll i ++ (Ul C10.zsAll i ++ (Ul C11.zsAll i ++ (Ul C12.zsAll i ++ (Ul C13.zsAll i ++ (Ul C14.zsAll i ++ (Ul C15.zsAll i ++ (Ul C16.zsAll i ++ (Ul C17.zsAll i ++ (Ul C18.zsAll i))))))))))))))))))

theorem good_all (i : ℕ) (hi : i < 8) : Good i NSall (USall i) := by
  unfold NSall USall

  refine Good_append i _ _ _ _ (l_C00 i hi) (g_C00 i hi) ?_
  refine Good_append i _ _ _ _ (l_C01 i hi) (g_C01 i hi) ?_
  refine Good_append i _ _ _ _ (l_C02 i hi) (g_C02 i hi) ?_
  refine Good_append i _ _ _ _ (l_C03 i hi) (g_C03 i hi) ?_
  refine Good_append i _ _ _ _ (l_C04 i hi) (g_C04 i hi) ?_
  refine Good_append i _ _ _ _ (l_C05 i hi) (g_C05 i hi) ?_
  refine Good_append i _ _ _ _ (l_C06 i hi) (g_C06 i hi) ?_
  refine Good_append i _ _ _ _ (l_C07 i hi) (g_C07 i hi) ?_
  refine Good_append i _ _ _ _ (l_C08 i hi) (g_C08 i hi) ?_
  refine Good_append i _ _ _ _ (l_C09 i hi) (g_C09 i hi) ?_
  refine Good_append i _ _ _ _ (l_C10 i hi) (g_C10 i hi) ?_
  refine Good_append i _ _ _ _ (l_C11 i hi) (g_C11 i hi) ?_
  refine Good_append i _ _ _ _ (l_C12 i hi) (g_C12 i hi) ?_
  refine Good_append i _ _ _ _ (l_C13 i hi) (g_C13 i hi) ?_
  refine Good_append i _ _ _ _ (l_C14 i hi) (g_C14 i hi) ?_
  refine Good_append i _ _ _ _ (l_C15 i hi) (g_C15 i hi) ?_
  refine Good_append i _ _ _ _ (l_C16 i hi) (g_C16 i hi) ?_
  refine Good_append i _ _ _ _ (l_C17 i hi) (g_C17 i hi) ?_
  exact g_C18 i hi


theorem lenNS : NSall.length = 1999 := by decide +kernel
theorem lenUS : ∀ i, i < 8 → (USall i).length = 1999 := by unfold USall; decide +kernel
theorem geNS : ∀ n ∈ NSall, 1025 ≤ n := by unfold NSall; decide +kernel

def N0 : ℕ := 15177045555
def L0 : List ℕ := N0 :: NSall

theorem lenL0 : L0.length = 2000 := by simp [L0, lenNS]

def loQ (k : ℕ) : ℚ := (((L0.getD k 0 : ℕ) : ℚ) - 1025) / 2 ^ 30
def hiQ (k : ℕ) : ℚ := (((L0.getD k 0 : ℕ) : ℚ) + 1025) / 2 ^ 30
noncomputable def aW (j : ℕ) : ℝ := (weightsA.getD j 0 : ℝ) / 2 ^ 50
def Vset : Set (ℕ → ℤ) := {v | ∃ r ∈ chainVecs, ∀ j, j < 7 → v j = ((r.getD j 0 : ℕ) : ℤ)}

def f160 (n : ℕ) : ℕ := 2 ^ 160 / ((n + 1025) ^ 2 + 2 ^ 58)
def Tsum : ℕ := (L0.map f160).sum
def SA : ℕ := weightsA.foldl (· + ·) 0
def Fl : ℕ := f160 N0
def Ui (i : ℕ) : ℕ := (USall i).sum

/-- The final rational comparison, exact integers, all 8 chain vectors. -/
theorem final_nat : ∀ i, i < 8 →
    461945 * SA * 2 ^ 100 + Ui i * 2 ^ 110 * 10 ^ 7 < 2 * Fl * SA * 99936 * 100 + 2 * Tsum * SA * 10 ^ 7 := by
  unfold Ui Fl Tsum SA f160 N0; unfold USall; decide +kernel

theorem SA_pos : 0 < SA := by unfold SA; decide +kernel
theorem lenW : weightsA.length = 7 := by decide +kernel
theorem lenCV : chainVecs.length = 8 := by decide +kernel

theorem lo_cast (k : ℕ) : (loQ k : ℝ) = (((L0.getD k 0 : ℕ) : ℝ) - 1025) / 2 ^ 30 := by
  unfold loQ; push_cast; ring
theorem hi_cast (k : ℕ) : (hiQ k : ℝ) = (((L0.getD k 0 : ℕ) : ℝ) + 1025) / 2 ^ 30 := by
  unfold hiQ; push_cast; ring
theorem L0_zero : L0.getD 0 0 = 15177045555 := rfl
theorem L0_succ (k : ℕ) : L0.getD (k + 1) 0 = NSall.getD k 0 := rfl

/-- The ordering of the 2000 grid ordinates, a kernel check (`decide +kernel`): consecutive ordinates differ by
more than 2050 grid units, so the radius-1025 intervals are disjoint and increasing. -/
theorem ord_nat : ∀ k, k < 1999 → L0.getD k 0 + 2050 < L0.getD (k + 1) 0 := by
  unfold L0 NSall; decide +kernel

theorem intervalsOrdered : IntervalsOrdered 2000 loQ hiQ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold loQ; rw [L0_zero]; norm_num
  · intro k _
    unfold loQ hiQ
    gcongr
    linarith
  · intro k hk
    have h := ord_nat k (by omega)
    have h' : ((L0.getD k 0 : ℕ) : ℚ) + 2050 < ((L0.getD (k + 1) 0 : ℕ) : ℚ) := by exact_mod_cast h
    unfold loQ hiQ
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith
theorem Hw_cast : (Hw : ℝ) = 1025 := by norm_num [Hw]

theorem S_eq : ∑ j ∈ range 7, aW j = (SA : ℝ) / 2 ^ 50 := by
  have h := foldl_add_sum weightsA 0
  rw [lenW] at h
  unfold SA
  rw [h, Nat.cast_zero, zero_add, Finset.sum_div]
  rfl

theorem Bk_eq (γ : ℝ) (r : List ℕ) (v : ℕ → ℤ) (hv : ∀ j, j < 7 → v j = ((r.getD j 0 : ℕ) : ℤ)) :
    Bk aW 7 (thetaOf γ) v =
      ∑ j ∈ range weightsA.length, (((weightsA.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf γ) ^ (r.getD j 0) := by
  unfold Bk
  rw [lenW]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [hv j hj', qOf_eq_exp, ← Complex.exp_nat_mul]
  unfold aW
  congr 2
  push_cast
  ring

theorem per_zero (i : ℕ) (hi : i < 8) (r : List ℕ) (hr : r = chainVecs.getD i []) (v : ℕ → ℤ)
    (hv : ∀ j, j < 7 → v j = ((r.getD j 0 : ℕ) : ℤ)) (γ : ℕ → ℝ)
    (hγ : ∀ k, k < 2000 → (loQ k : ℝ) ≤ γ k ∧ γ k ≤ (hiQ k : ℝ)) (k : ℕ) (hk : k ∈ Ico 1 2000) :
    2 * wOf (γ k) * ‖Bk aW 7 (thetaOf (γ k)) v‖ ≤ (((USall i).getD (k - 1) 0 : ℕ) : ℝ) / 2 ^ 40 := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : m < NSall.length := by rw [lenNS]; omega
  have h := hγ (m + 1) hk2
  have h1 := h.1
  have h2 := h.2
  rw [lo_cast, L0_succ] at h1
  rw [hi_cast, L0_succ] at h2
  have g := good_all i hi m hm (γ (m + 1)) (by rw [Hw_cast]; exact h1) (by rw [Hw_cast]; exact h2)
  rw [Bk_eq _ r v hv, hr]
  simpa using g

theorem sum_bound (i : ℕ) (hi : i < 8) (r : List ℕ) (hr : r = chainVecs.getD i []) (v : ℕ → ℤ)
    (hv : ∀ j, j < 7 → v j = ((r.getD j 0 : ℕ) : ℤ)) (γ : ℕ → ℝ)
    (hγ : ∀ k, k < 2000 → (loQ k : ℝ) ≤ γ k ∧ γ k ≤ (hiQ k : ℝ)) :
    ∑ k ∈ Ico 1 2000, 2 * wOf (γ k) * ‖Bk aW 7 (thetaOf (γ k)) v‖ ≤ (Ui i : ℝ) / 2 ^ 40 := by
  have h2 : ∑ k ∈ range 1999, (USall i).getD k 0 = Ui i := by
    have := sum_range_getD (USall i); rw [lenUS i hi] at this; exact this
  calc ∑ k ∈ Ico 1 2000, 2 * wOf (γ k) * ‖Bk aW 7 (thetaOf (γ k)) v‖
      ≤ ∑ k ∈ Ico 1 2000, (((USall i).getD (k - 1) 0 : ℕ) : ℝ) / 2 ^ 40 :=
        Finset.sum_le_sum (fun k hk => per_zero i hi r hr v hv γ hγ k hk)
    _ = (Ui i : ℝ) / 2 ^ 40 := by
        rw [Finset.sum_Ico_eq_sum_range]
        have e : ∀ k, 1 + k - 1 = k := fun k => by omega
        simp only [e]
        rw [← Finset.sum_div, ← Nat.cast_sum]
        have e2 : 2000 - 1 = 1999 := rfl
        rw [e2, h2]

theorem aW_nonneg : ∀ j, j < 7 → 0 ≤ aW j := by intro j _; unfold aW; positivity

theorem aW_sum_pos : 0 < ∑ j ∈ range 7, aW j := by
  rw [S_eq]
  have : (0 : ℝ) < SA := by exact_mod_cast SA_pos
  positivity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem combNumerics_622 : CombNumerics 2000 7 622 aW Vset loQ hiQ := by
  intro γ hγ
  have h0 := hγ 0 (by norm_num)
  have h0l : (15177045555 - 1025 : ℝ) / 2 ^ 30 ≤ γ 0 := by
    have := h0.1; rw [lo_cast, L0_zero] at this; simpa using this
  have h0h : γ 0 ≤ (15177045555 + 1025 : ℝ) / 2 ^ 30 := by
    have := h0.2; rw [hi_cast, L0_zero] at this; simpa using this
  have hl1 : (141347241 : ℝ) / 10 ^ 7 ≤ γ 0 := by norm_num at h0l ⊢; linarith
  have hh1 : γ 0 ≤ (141347262 : ℝ) / 10 ^ 7 := by norm_num at h0h ⊢; linarith
  have hl2 : (15177044530 : ℝ) / 1073741824 ≤ γ 0 := by norm_num at h0l ⊢; linarith
  have hh2 : γ 0 ≤ (15177046580 : ℝ) / 1073741824 := by norm_num at h0h ⊢; linarith
  obtain ⟨z1, z2, _, z4⟩ := zero1_facts (γ 0) hl1 hh1
  obtain ⟨hP1, hP2⟩ := P_bounds (γ 0) hl2 hh2
  refine ⟨z1, z2, by push_cast; linarith [hP2], ?_, ?_⟩
  · intro u hu
    obtain ⟨r, hr, hr2⟩ := chain_mem _ u hP1 hP2 hu.1 hu.2
    exact ⟨r, hr, fun j hj => hr2 j hj⟩
  intro v hv
  have hv' : ∃ r ∈ chainVecs, ∀ j, j < 7 → v j = ((r.getD j 0 : ℕ) : ℤ) := hv
  obtain ⟨r, hrr⟩ := hv'
  have hr : r ∈ chainVecs := hrr.1
  have hvr := hrr.2
  clear hrr
  clear hv
  obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
  have hi8 : i < 8 := by rw [lenCV] at hi; exact hi
  have hgi : chainVecs.getD i [] = r := by rw [List.getD_eq_getElem _ _ hi]; exact hri
  have hL : ∀ k, k < 2000 → 1025 ≤ L0.getD k 0 := fun k hk => by
    rcases k with _ | k
    · rw [L0_zero]; norm_num
    · rw [L0_succ]; exact geNS _ (getD_mem NSall k (by rw [lenNS]; omega))
  have hγ0 : ∀ k, k < 2000 → 0 ≤ γ k ∧ γ k ≤ (((L0.getD k 0 : ℕ) : ℝ) + 1025) / 2 ^ 30 := by
    intro k hk
    have h := hγ k hk
    have hLk : (1025 : ℝ) ≤ ((L0.getD k 0 : ℕ) : ℝ) := by exact_mod_cast hL k hk
    refine ⟨?_, ?_⟩
    · have := h.1
      rw [lo_cast] at this
      exact le_trans (div_nonneg (by linarith) (by positivity)) this
    · have := h.2
      rwa [hi_cast] at this
  have hW : Wtail 2000 γ ≤ (461945 : ℝ) / 10 ^ 7 - 2 * (Tsum : ℝ) / 2 ^ 100 := by
    have h1 := Wtail_le 2000 γ (fun k => L0.getD k 0) hγ0
    have hT : (∑ k ∈ range 2000, (2 ^ 160 / ((L0.getD k 0 + 1025) ^ 2 + 2 ^ 58) : ℕ)) = Tsum := by
      have := sum_range_getD_map f160 L0
      rw [lenL0] at this
      exact this
    rw [hT] at h1
    exact h1
  have hN0 : ((N0 : ℕ) : ℝ) = 15177045555 := by unfold N0; norm_num
  have hw0 : (Fl : ℝ) / 2 ^ 100 ≤ wOf (γ 0) := by
    unfold Fl f160
    apply w_ge N0 (γ 0)
    · have := h0.1; rw [lo_cast, L0_zero] at this
      exact le_trans (by norm_num) this
    · rw [hN0]; exact h0h
  have hsum := sum_bound i hi8 r hgi.symm v hvr γ hγ
  have hfin : ((461945 * SA * 2 ^ 100 + Ui i * 2 ^ 110 * 10 ^ 7 : ℕ) : ℝ) <
      ((2 * Fl * SA * 99936 * 100 + 2 * Tsum * SA * 10 ^ 7 : ℕ) : ℝ) := by
    exact_mod_cast final_nat i hi8
  have hSA : (0 : ℝ) < SA := by exact_mod_cast SA_pos
  have hwpos : 0 < wOf (γ 0) := by unfold wOf; positivity
  unfold Nbound
  rw [S_eq]
  push_cast at hfin
  have hWS : Wtail 2000 γ * ((SA : ℝ) / 2 ^ 50) ≤
      ((461945 : ℝ) / 10 ^ 7 - 2 * (Tsum : ℝ) / 2 ^ 100) * ((SA : ℝ) / 2 ^ 50) :=
    mul_le_mul_of_nonneg_right hW (by positivity)
  have hm := mul_le_mul hw0 z4 (by norm_num) hwpos.le
  have hm2 := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * ((SA : ℝ) / 2 ^ 50))
  generalize (Ui i : ℝ) = U at *
  generalize (Fl : ℝ) = F at *
  generalize (Tsum : ℝ) = T at *
  generalize (SA : ℝ) = A at *
  generalize wOf (γ 0) = w0 at *
  generalize Real.cos (thetaOf (γ 0) / 2) = cs at *
  generalize Wtail 2000 γ = Wt at *
  nlinarith [hWS, hsum, hm2, hfin]

/-- Windows of 622 (runs of one sign at most 621): `theoremA'_622` with `CombNumerics` discharged for the
concrete data. The remaining hypotheses are RH, Li's formula identities, the certified zero
intervals (the ordering of the intervals is proved by `intervalsOrdered`). -/
theorem theoremA'_622_numerics {c : ℕ → ℝ}
    (hRH : RiemannHypothesis) (hLi2 : LiSecondDiff c) (hLiW : LiWeightSum)
    (hZ : ZeroIntervals 2000 loQ hiQ) :
    ∀ n0, 1 ≤ n0 →
      (∃ n, n0 ≤ n ∧ n < n0 + 622 ∧ 0 < c n) ∧ (∃ n, n0 ≤ n ∧ n < n0 + 622 ∧ c n < 0) :=
  theoremA'_622 intervalsOrdered aW_nonneg aW_sum_pos hRH hLi2 hLiW hZ combNumerics_622

theorem theoremA'_622_runs_numerics {c : ℕ → ℝ}
    (hRH : RiemannHypothesis) (hLi2 : LiSecondDiff c) (hLiW : LiWeightSum)
    (hZ : ZeroIntervals 2000 loQ hiQ) :
    ∀ n0, 1 ≤ n0 →
      ¬ (∀ n, n0 ≤ n → n < n0 + 622 → 0 ≤ c n) ∧ ¬ (∀ n, n0 ≤ n → n < n0 + 622 → c n ≤ 0) :=
  theoremA'_622_runs intervalsOrdered aW_nonneg aW_sum_pos hRH hLi2 hLiW hZ combNumerics_622

#print axioms theoremA'_622_numerics
#print axioms theoremA'_622_runs_numerics

end KeiperComb.N622
