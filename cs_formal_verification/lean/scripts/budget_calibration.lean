/- Calibration workload of scripts/module_budget.py: the module budget scales its 30 s limit by this file's CPU time
   here / on the reference machine. Pinned (its sha256 is in the script): any edit needs a new reference time.
   Lean core only (a Mathlib bump does not move it); kernel reduction, `omega`, `simp`, elaboration. -/

def collatz : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => if n ≤ 1 then n else collatz k (if n % 2 = 0 then n / 2 else 3 * n + 1)

theorem kernel_0 : (List.range' 0 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem kernel_1 : (List.range' 120 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem kernel_2 : (List.range' 240 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem kernel_3 : (List.range' 360 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem kernel_4 : (List.range' 480 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem kernel_5 : (List.range' 600 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem kernel_6 : (List.range' 720 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem kernel_7 : (List.range' 840 120).all (fun n => collatz 300 (n + 1) == 1) = true := by
  decide +kernel

theorem omega_0 (x y z w : Nat) (h₁ : 2 * x + y ≤ 3 * z + 1) (h₂ : z ≤ w + 1) (h₃ : w < x + 0) :
    2 * x + y ≤ 3 * (w + 1) + 1 ∧ z < x + 1 := by
  omega

theorem omega_1 (x y z w : Nat) (h₁ : 3 * x + y ≤ 5 * z + 2) (h₂ : z ≤ w + 2) (h₃ : w < x + 1) :
    3 * x + y ≤ 5 * (w + 2) + 2 ∧ z < x + 3 := by
  omega

theorem omega_2 (x y z w : Nat) (h₁ : 4 * x + y ≤ 7 * z + 3) (h₂ : z ≤ w + 3) (h₃ : w < x + 2) :
    4 * x + y ≤ 7 * (w + 3) + 3 ∧ z < x + 5 := by
  omega

theorem omega_3 (x y z w : Nat) (h₁ : 5 * x + y ≤ 9 * z + 4) (h₂ : z ≤ w + 4) (h₃ : w < x + 3) :
    5 * x + y ≤ 9 * (w + 4) + 4 ∧ z < x + 7 := by
  omega

theorem omega_4 (x y z w : Nat) (h₁ : 6 * x + y ≤ 11 * z + 5) (h₂ : z ≤ w + 5) (h₃ : w < x + 4) :
    6 * x + y ≤ 11 * (w + 5) + 5 ∧ z < x + 9 := by
  omega

theorem omega_5 (x y z w : Nat) (h₁ : 7 * x + y ≤ 13 * z + 1) (h₂ : z ≤ w + 1) (h₃ : w < x + 5) :
    7 * x + y ≤ 13 * (w + 1) + 1 ∧ z < x + 6 := by
  omega

theorem omega_6 (x y z w : Nat) (h₁ : 8 * x + y ≤ 15 * z + 2) (h₂ : z ≤ w + 2) (h₃ : w < x + 6) :
    8 * x + y ≤ 15 * (w + 2) + 2 ∧ z < x + 8 := by
  omega

theorem omega_7 (x y z w : Nat) (h₁ : 9 * x + y ≤ 17 * z + 3) (h₂ : z ≤ w + 3) (h₃ : w < x + 7) :
    9 * x + y ≤ 17 * (w + 3) + 3 ∧ z < x + 10 := by
  omega

theorem omega_8 (x y z w : Nat) (h₁ : 10 * x + y ≤ 19 * z + 4) (h₂ : z ≤ w + 4) (h₃ : w < x + 8) :
    10 * x + y ≤ 19 * (w + 4) + 4 ∧ z < x + 12 := by
  omega

theorem omega_9 (x y z w : Nat) (h₁ : 11 * x + y ≤ 21 * z + 5) (h₂ : z ≤ w + 5) (h₃ : w < x + 9) :
    11 * x + y ≤ 21 * (w + 5) + 5 ∧ z < x + 14 := by
  omega

theorem omega_10 (x y z w : Nat) (h₁ : 12 * x + y ≤ 23 * z + 1) (h₂ : z ≤ w + 1) (h₃ : w < x + 10) :
    12 * x + y ≤ 23 * (w + 1) + 1 ∧ z < x + 11 := by
  omega

theorem omega_11 (x y z w : Nat) (h₁ : 13 * x + y ≤ 25 * z + 2) (h₂ : z ≤ w + 2) (h₃ : w < x + 11) :
    13 * x + y ≤ 25 * (w + 2) + 2 ∧ z < x + 13 := by
  omega

theorem omega_12 (x y z w : Nat) (h₁ : 14 * x + y ≤ 27 * z + 3) (h₂ : z ≤ w + 3) (h₃ : w < x + 12) :
    14 * x + y ≤ 27 * (w + 3) + 3 ∧ z < x + 15 := by
  omega

theorem omega_13 (x y z w : Nat) (h₁ : 15 * x + y ≤ 29 * z + 4) (h₂ : z ≤ w + 4) (h₃ : w < x + 13) :
    15 * x + y ≤ 29 * (w + 4) + 4 ∧ z < x + 17 := by
  omega

theorem omega_14 (x y z w : Nat) (h₁ : 16 * x + y ≤ 31 * z + 5) (h₂ : z ≤ w + 5) (h₃ : w < x + 14) :
    16 * x + y ≤ 31 * (w + 5) + 5 ∧ z < x + 19 := by
  omega

theorem omega_15 (x y z w : Nat) (h₁ : 17 * x + y ≤ 33 * z + 1) (h₂ : z ≤ w + 1) (h₃ : w < x + 15) :
    17 * x + y ≤ 33 * (w + 1) + 1 ∧ z < x + 16 := by
  omega

theorem omega_16 (x y z w : Nat) (h₁ : 18 * x + y ≤ 35 * z + 2) (h₂ : z ≤ w + 2) (h₃ : w < x + 16) :
    18 * x + y ≤ 35 * (w + 2) + 2 ∧ z < x + 18 := by
  omega

theorem omega_17 (x y z w : Nat) (h₁ : 19 * x + y ≤ 37 * z + 3) (h₂ : z ≤ w + 3) (h₃ : w < x + 17) :
    19 * x + y ≤ 37 * (w + 3) + 3 ∧ z < x + 20 := by
  omega

theorem omega_18 (x y z w : Nat) (h₁ : 20 * x + y ≤ 39 * z + 4) (h₂ : z ≤ w + 4) (h₃ : w < x + 18) :
    20 * x + y ≤ 39 * (w + 4) + 4 ∧ z < x + 22 := by
  omega

theorem omega_19 (x y z w : Nat) (h₁ : 21 * x + y ≤ 41 * z + 5) (h₂ : z ≤ w + 5) (h₃ : w < x + 19) :
    21 * x + y ≤ 41 * (w + 5) + 5 ∧ z < x + 24 := by
  omega

theorem omega_20 (x y z w : Nat) (h₁ : 22 * x + y ≤ 43 * z + 1) (h₂ : z ≤ w + 1) (h₃ : w < x + 20) :
    22 * x + y ≤ 43 * (w + 1) + 1 ∧ z < x + 21 := by
  omega

theorem omega_21 (x y z w : Nat) (h₁ : 23 * x + y ≤ 45 * z + 2) (h₂ : z ≤ w + 2) (h₃ : w < x + 21) :
    23 * x + y ≤ 45 * (w + 2) + 2 ∧ z < x + 23 := by
  omega

theorem omega_22 (x y z w : Nat) (h₁ : 24 * x + y ≤ 47 * z + 3) (h₂ : z ≤ w + 3) (h₃ : w < x + 22) :
    24 * x + y ≤ 47 * (w + 3) + 3 ∧ z < x + 25 := by
  omega

theorem omega_23 (x y z w : Nat) (h₁ : 25 * x + y ≤ 49 * z + 4) (h₂ : z ≤ w + 4) (h₃ : w < x + 23) :
    25 * x + y ≤ 49 * (w + 4) + 4 ∧ z < x + 27 := by
  omega

theorem simp_0 (xs ys : List Nat) : ((xs ++ ys).map (· + 0)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_1 (xs ys : List Nat) : ((xs ++ ys).map (· + 1)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_2 (xs ys : List Nat) : ((xs ++ ys).map (· + 2)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_3 (xs ys : List Nat) : ((xs ++ ys).map (· + 3)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_4 (xs ys : List Nat) : ((xs ++ ys).map (· + 4)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_5 (xs ys : List Nat) : ((xs ++ ys).map (· + 5)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_6 (xs ys : List Nat) : ((xs ++ ys).map (· + 6)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_7 (xs ys : List Nat) : ((xs ++ ys).map (· + 7)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_8 (xs ys : List Nat) : ((xs ++ ys).map (· + 8)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_9 (xs ys : List Nat) : ((xs ++ ys).map (· + 9)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_10 (xs ys : List Nat) : ((xs ++ ys).map (· + 10)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_11 (xs ys : List Nat) : ((xs ++ ys).map (· + 11)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_12 (xs ys : List Nat) : ((xs ++ ys).map (· + 12)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_13 (xs ys : List Nat) : ((xs ++ ys).map (· + 13)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_14 (xs ys : List Nat) : ((xs ++ ys).map (· + 14)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_15 (xs ys : List Nat) : ((xs ++ ys).map (· + 15)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_16 (xs ys : List Nat) : ((xs ++ ys).map (· + 16)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_17 (xs ys : List Nat) : ((xs ++ ys).map (· + 17)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_18 (xs ys : List Nat) : ((xs ++ ys).map (· + 18)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_19 (xs ys : List Nat) : ((xs ++ ys).map (· + 19)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_20 (xs ys : List Nat) : ((xs ++ ys).map (· + 20)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_21 (xs ys : List Nat) : ((xs ++ ys).map (· + 21)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_22 (xs ys : List Nat) : ((xs ++ ys).map (· + 22)).length + 0 = xs.length + (ys.map id).length := by
  simp

theorem simp_23 (xs ys : List Nat) : ((xs ++ ys).map (· + 23)).length + 0 = xs.length + (ys.map id).length := by
  simp
