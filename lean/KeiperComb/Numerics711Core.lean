/-! B2 spike core (not in the default target): exact Gaussian-integer arithmetic for the L = 711
chain check.  Plain Lean, no Mathlib, so the kernel cost is measured alone.  Soundness glue to
`CombNumerics` (gcast, qOf_eq_exp, norm Lipschitz) is NOT written in this spike. -/
namespace KeiperComb.N711

def gmul (a b : Int × Int) : Int × Int := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def gpowAux (z : Int × Int) : Nat → Int × Int → Int × Int
  | 0, acc => acc
  | n + 1, acc => gpowAux z n (gmul acc z)

def gpow (z : Int × Int) (n : Nat) : Int × Int := gpowAux z n (1, 0)

def Hw : Nat := 1025   -- half-width in units 2^-30

/-- One zero, one chain vector: `rho >= 2^40 |B|` witness and the bound `U` (units 2^-40). -/
def checkZero (A v : List Nat) (N rho U : Nat) : Bool :=
  let Zc : Int × Int := ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)
  let D : Int := (N : Int) * N + 2 ^ 58
  let vm : Nat := v.foldl max 0
  let SA : Nat := A.foldl (· + ·) 0
  let (X, Y) := (A.zip v).foldl (fun (acc : Int × Int) (p : Nat × Nat) =>
      let pw := gpow Zc p.2
      let f : Int := (p.1 : Int) * D ^ (vm - p.2)
      (acc.1 + f * pw.1, acc.2 + f * pw.2)) (0, 0)
  let den : Int := 2 ^ 50 * D ^ vm
  let Elo : Int := ((N : Int) - Hw) ^ 2 + 2 ^ 58
  decide (2 ^ 80 * (X * X + Y * Y) ≤ ((rho : Int) * den) ^ 2) &&
  decide (2 ^ 61 * (rho : Int) * Elo + 2 ^ 81 * (SA : Int) * vm * Hw ≤ (U : Int) * Elo ^ 2)

def checkVec (A v : List Nat) (zs : List (Nat × Nat × Nat)) : Bool :=
  zs.all fun t => checkZero A v t.1 t.2.1 t.2.2

def checkBatch (A : List Nat) (vs : List (List Nat)) (zsv : List (List (Nat × Nat × Nat))) : Bool :=
  (vs.zip zsv).all fun p => checkVec A p.1 p.2

/-! ### Fast checker (B2 speedup spike)
Same arithmetic as `checkZero`, three changes: (1) `gpowBin` square-and-multiply (about 10 Gaussian
squarings instead of up to 623 multiplications); (2) the powers `Z^e` are built once per zero for the
distinct exponents of all chain vectors and reused across the 9 vectors; (3) `D^e` is `Nat.pow`
(GMP-accelerated in the kernel), not the unary `Int` power.  Still `decide +kernel`, no native_decide. -/

def gpowBin (z : Int × Int) : Nat → Nat → Int × Int
  | 0, _ => (1, 0)
  | f + 1, n =>
    if n = 0 then (1, 0)
    else
      let h := gpowBin z f (n / 2)
      let s := gmul h h
      if n % 2 = 1 then gmul s z else s

def dedupAux : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | f + 1, x :: xs => x :: dedupAux f (xs.filter (· != x))

def dedup (l : List Nat) : List Nat := dedupAux l.length l

def lookupPow (t : List (Nat × (Int × Int))) (e : Nat) : Int × Int :=
  match t.find? (fun p => p.1 == e) with
  | some p => p.2
  | none => (0, 0)

/-- One zero, all chain vectors `vs`; `col` holds `(N, rho, U)` of this zero for each vector. -/
def checkZeroAll (A : List Nat) (vs : List (List Nat)) (col : List (Nat × Nat × Nat)) : Bool :=
  match col with
  | [] => true
  | c0 :: _ =>
    let N : Nat := c0.1
    let Zc : Int × Int := ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)
    let D : Nat := N * N + 2 ^ 58
    let SA : Nat := A.foldl (· + ·) 0
    let Elo : Int := ((N : Int) - Hw) ^ 2 + 2 ^ 58
    let tab : List (Nat × (Int × Int)) := (dedup (vs.foldl (· ++ ·) [])).map fun e => (e, gpowBin Zc 11 e)
    (vs.zip col).all fun q =>
      let v := q.1
      let rho := q.2.2.1
      let U := q.2.2.2
      let vm : Nat := v.foldl max 0
      let (X, Y) := (A.zip v).foldl (fun (acc : Int × Int) (p : Nat × Nat) =>
          let pw := lookupPow tab p.2
          let f : Int := ((p.1 * D ^ (vm - p.2) : Nat) : Int)
          (acc.1 + f * pw.1, acc.2 + f * pw.2)) (0, 0)
      let den : Int := ((2 ^ 50 * D ^ vm : Nat) : Int)
      decide (2 ^ 80 * (X * X + Y * Y) ≤ ((rho : Int) * den) ^ 2) &&
      decide (2 ^ 61 * (rho : Int) * Elo + 2 ^ 81 * (SA : Int) * vm * Hw ≤ (U : Int) * Elo ^ 2)

def transpAux {α : Type} : Nat → List (List α) → List (List α)
  | 0, _ => []
  | n + 1, rows => (rows.filterMap List.head?) :: transpAux n (rows.map List.tail)

/-- `zsv[j][i]` = zero `i` for vector `j`; check zero by zero, reusing the powers across vectors. -/
def checkBatchFast (A : List Nat) (vs : List (List Nat)) (zsv : List (List (Nat × Nat × Nat))) : Bool :=
  (transpAux (zsv.headD []).length zsv).all fun col => checkZeroAll A vs col

end KeiperComb.N711
