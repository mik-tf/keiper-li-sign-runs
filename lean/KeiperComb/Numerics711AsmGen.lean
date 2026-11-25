import KeiperComb.Numerics711Sound3
import KeiperComb.Numerics711Cert

/-! B2, assembly, generic part: abstract list lemmas (no big literals) that turn the per-chunk
soundness theorems into per-zero bounds, and concatenate chunks. -/

open Complex Finset

namespace KeiperComb.N711

/-- Column `m` of the transposed table is the list of the `m`-th entries of the rows. -/
theorem transp_get {α : Type} (d : α) : ∀ (m n : ℕ) (zs : List (List α)), m < n →
    (∀ r ∈ zs, m < r.length) → (transpAux n zs)[m]? = some (zs.map (fun r => r.getD m d)) := by
  intro m
  induction m with
  | zero =>
    intro n zs hn hr
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [transpAux, List.getElem?_cons_zero, Option.some.injEq]
    induction zs with
    | nil => rfl
    | cons r rs ih =>
      have hr0 : r ≠ [] := by
        intro h; have := hr r (by simp); simp [h] at this
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hr0
      simp only [List.filterMap_cons, List.head?_cons, List.map_cons, List.getD_cons_zero]
      rw [ih (fun r' hr' => hr r' (by simp [hr']))]
  | succ m ih =>
    intro n zs hn hr
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [transpAux, List.getElem?_cons_succ]
    rw [ih n' (zs.map List.tail) (by omega)]
    · congr 1
      rw [List.map_map]
      refine List.map_congr_left fun r hr' => ?_
      cases r with
      | nil => have := hr _ hr'; simp at this
      | cons x xs => simp
    · intro r hr'
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr'
      have := hr r0 hr0
      simp only [List.length_tail]; omega

lemma getD_mem (l : List ℕ) (k : ℕ) (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-- One vector `i`, a list of `Nat` zero ordinates and a list of bounds `U`. -/
def Good (i : ℕ) (ns us : List ℕ) : Prop :=
  ∀ m, m < ns.length → ∀ γ : ℝ, ((ns.getD m 0 : ℕ) - (Hw : ℝ)) / 2 ^ 30 ≤ γ →
    γ ≤ ((ns.getD m 0 : ℕ) + (Hw : ℝ)) / 2 ^ 30 →
    2 * wOf γ * ‖∑ j ∈ range weightsA.length, (((weightsA.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) *
        (qOf γ) ^ ((chainVecs.getD i []).getD j 0)‖ ≤ ((us.getD m 0 : ℕ) : ℝ) / 2 ^ 40

theorem Good_append (i : ℕ) (ns1 us1 ns2 us2 : List ℕ) (hl : us1.length = ns1.length)
    (g1 : Good i ns1 us1) (g2 : Good i ns2 us2) : Good i (ns1 ++ ns2) (us1 ++ us2) := by
  intro m hm
  rw [List.length_append] at hm
  by_cases h : m < ns1.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by omega)]
    exact g1 m h
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    rw [hl]
    exact g2 (m - ns1.length) (by omega)

theorem Good_tail (i : ℕ) (ns us : List ℕ) (hl : us.length = ns.length) (hne : ns ≠ [])
    (g : Good i ns us) : Good i ns.tail us.tail := by
  cases ns with
  | nil => exact absurd rfl hne
  | cons a ns =>
    cases us with
    | nil => simp at hl
    | cons b us =>
      intro m hm
      have := g (m + 1) (by simpa using hm)
      simpa using this

/-- From a chunk soundness theorem to `Good`. -/
theorem chunk_good (zs : List (List (Nat × Nat × Nat))) (ns : List Nat)
    (hzl : zs.length = 9) (hrect : ∀ r ∈ zs, r.length = ns.length)
    (hns : (zs.headD []).map (fun t => t.1) = ns) (hH : ∀ n ∈ ns, Hw ≤ n)
    (hs : ∀ col ∈ transpAux (zs.headD []).length zs, ∀ c0 rest, col = c0 :: rest → Hw ≤ c0.1 →
      ∀ q ∈ chainVecs.zip col, ∀ γ : ℝ, ((c0.1 : ℝ) - Hw) / 2 ^ 30 ≤ γ → γ ≤ ((c0.1 : ℝ) + Hw) / 2 ^ 30 →
        2 * wOf γ * ‖∑ j ∈ range weightsA.length, (((weightsA.getD j 0 : ℝ) / 2 ^ 50 : ℝ) : ℂ) *
          (qOf γ) ^ (q.1.getD j 0)‖ ≤ (q.2.2.2 : ℝ) / 2 ^ 40)
    (hcv : chainVecs.length = 9) (i : ℕ) (hi : i < 9) :
    Good i ns ((zs.getD i []).map (fun t => t.2.2)) := by
  intro m hm γ h1 h2
  obtain ⟨z0, zs', rfl⟩ : ∃ z0 zs', zs = z0 :: zs' := by
    cases zs with
    | nil => simp at hzl
    | cons a b => exact ⟨a, b, rfl⟩
  simp only [List.headD_cons] at hns hs
  have hn0 : z0.length = ns.length := hrect z0 (by simp)
  have hrow : ∀ r ∈ z0 :: zs', m < r.length := fun r hr => by rw [hrect r hr]; exact hm
  have hget := transp_get ((0, 0, 0) : Nat × Nat × Nat) m z0.length (z0 :: zs') (by omega) hrow
  have hcolmem := List.mem_of_getElem? hget
  set col := (z0 :: zs').map (fun r => r.getD m (0, 0, 0)) with hcol
  obtain ⟨c0, rest, hc⟩ : ∃ c0 rest, col = c0 :: rest := ⟨z0.getD m (0, 0, 0), zs'.map (fun r => r.getD m (0, 0, 0)), by rw [hcol]; rfl⟩
  have hc0 : c0 = z0.getD m (0, 0, 0) := by
    have := hc; simp [hcol] at this; exact this.1.symm
  have hmz : m < z0.length := by omega
  have hN : c0.1 = ns.getD m 0 := by
    rw [hc0, ← hns, List.getD_eq_getElem _ _ hmz, List.getD_eq_getElem _ _ (by simpa using hmz)]
    simp
  have hHw : Hw ≤ c0.1 := by
    rw [hN]; exact hH _ (getD_mem ns m hm)
  have hcl : col.length = 9 := by rw [hcol, List.length_map, hzl]
  have hi1 : i < chainVecs.length := by omega
  have hi2 : i < col.length := by omega
  have hq := List.getElem_mem (l := chainVecs.zip col) (n := i) (by simp [hi1, hi2])
  have key := hs col hcolmem c0 rest hc hHw _ hq γ (by rw [hN]; exact h1) (by rw [hN]; exact h2)
  simp only [List.getElem_zip] at key
  rw [List.getD_eq_getElem _ _ hi1]
  have hzi : i < (z0 :: zs').length := by omega
  have hr : (z0 :: zs').getD i [] = (z0 :: zs')[i]'hzi := List.getD_eq_getElem _ _ hzi
  have hrl : ((z0 :: zs')[i]'hzi).length = ns.length := hrect _ (List.getElem_mem hzi)
  have hUe : ((((z0 :: zs').getD i []).map (fun t => t.2.2)).getD m 0)
      = (col[i]'hi2).2.2 := by
    rw [hr]
    have hm' : m < (List.map (fun t => t.2.2) ((z0 :: zs')[i]'hzi)).length := by
      rw [List.length_map, hrl]; exact hm
    rw [List.getD_eq_getElem _ _ hm', List.getElem_map]
    simp only [hcol, List.getElem_map]
    rw [List.getD_eq_getElem _ _ (by omega : m < ((z0 :: zs')[i]'hzi).length)]
  rw [hUe]
  exact key

/-- `∑_{k<n} f (l.getD k 0) = (l.map f).sum` for `n = l.length`. -/
theorem sum_range_getD_map (f : ℕ → ℕ) : ∀ l : List ℕ,
    ∑ k ∈ range l.length, f (l.getD k 0) = (l.map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

theorem sum_range_getD (l : List ℕ) : ∑ k ∈ range l.length, l.getD k 0 = l.sum := by
  simpa using sum_range_getD_map id l

end KeiperComb.N711
