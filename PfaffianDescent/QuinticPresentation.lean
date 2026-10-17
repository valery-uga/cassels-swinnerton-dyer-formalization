import PfaffianDescent.Basic

/-! Explicit equations and Pfaffian presentation for a degree-five point on a rational normal cubic. -/
namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- Five quadrics associated to the monic quintic with coefficients `a`. -/
def quinticQuadrics (a : Vec R 5) (x : Vec R 4) : Vec R 5 :=
  ![x 0 * x 2 - x 1^2,
    x 0 * x 3 - x 1 * x 2,
    x 1 * x 3 - x 2^2,
    x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2,
    x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1]

/-- The alternating presentation, augmented by five linear-form values. -/
def quinticMatrix (a : Vec R 5) (x : Vec R 4) (y : Vec R 5) : Mat R 6 :=
  !![0, a 3 * x 3 + a 0 * x 0, a 4 * x 3 + a 1 * x 0, -x 3, x 2, -y 0;
    -(a 3 * x 3 + a 0 * x 0), 0, x 3 + a 2 * x 0, x 2, -x 1, -y 1;
    -(a 4 * x 3 + a 1 * x 0), -(x 3 + a 2 * x 0), 0, -x 1, x 0, -y 2;
    -(-x 3), -(x 2), -(-x 1), 0, 0, -y 3;
    -(x 2), -(-x 1), -(x 0), -(0), 0, -y 4;
    -(-y 0), -(-y 1), -(-y 2), -(-y 3), -(-y 4), 0]

/-- Expansion of the augmented Pfaffian along its last column. -/
theorem quinticMatrix_pfaffian (a : Vec R 5) (x : Vec R 4) (y : Vec R 5) :
    pf6 (quinticMatrix a x y) = ∑ i, y i * quinticQuadrics a x i := by
  simp only [pf6, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (a 3 * x 3 + a 0 * x 0) * ((-x 1) * (-y 4) - (x 0) * (-y 3) + (-y 2) * (0))
  - (a 4 * x 3 + a 1 * x 0) * ((x 2) * (-y 4) - (-x 1) * (-y 3) + (-y 1) * (0))
  + (-x 3) * ((x 3 + a 2 * x 0) * (-y 4) - (-x 1) * (-y 2) + (-y 1) * (x 0))
  - (x 2) * ((x 3 + a 2 * x 0) * (-y 3) - (x 2) * (-y 2) + (-y 1) * (-x 1))
  + (-y 0) * ((x 3 + a 2 * x 0) * (0) - (x 2) * (x 0) + (-x 1) * (-x 1)) = y 0 * (x 0 * x 2 - x 1^2) + (y 1 * (x 0 * x 3 - x 1 * x 2) + (y 2 * (x 1 * x 3 - x 2^2) + (y 3 * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2) + (y 4 * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1)))))
  ring

theorem quinticMatrix_alternating (a : Vec R 5) (x : Vec R 4) (y : Vec R 5) :
    IsAlternating (quinticMatrix a x y) := by
  constructor
  · intro i
    fin_cases i <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j
    · change (0) = -(0)
      ring
    · change (-(a 3 * x 3 + a 0 * x 0)) = -(a 3 * x 3 + a 0 * x 0)
      ring
    · change (-(a 4 * x 3 + a 1 * x 0)) = -(a 4 * x 3 + a 1 * x 0)
      ring
    · change (-(-x 3)) = -(-x 3)
      ring
    · change (-(x 2)) = -(x 2)
      ring
    · change (-(-y 0)) = -(-y 0)
      ring
    · change (a 3 * x 3 + a 0 * x 0) = -(-(a 3 * x 3 + a 0 * x 0))
      ring
    · change (0) = -(0)
      ring
    · change (-(x 3 + a 2 * x 0)) = -(x 3 + a 2 * x 0)
      ring
    · change (-(x 2)) = -(x 2)
      ring
    · change (-(-x 1)) = -(-x 1)
      ring
    · change (-(-y 1)) = -(-y 1)
      ring
    · change (a 4 * x 3 + a 1 * x 0) = -(-(a 4 * x 3 + a 1 * x 0))
      ring
    · change (x 3 + a 2 * x 0) = -(-(x 3 + a 2 * x 0))
      ring
    · change (0) = -(0)
      ring
    · change (-(-x 1)) = -(-x 1)
      ring
    · change (-(x 0)) = -(x 0)
      ring
    · change (-(-y 2)) = -(-y 2)
      ring
    · change (-x 3) = -(-(-x 3))
      ring
    · change (x 2) = -(-(x 2))
      ring
    · change (-x 1) = -(-(-x 1))
      ring
    · change (0) = -(0)
      ring
    · change (-(0)) = -(0)
      ring
    · change (-(-y 3)) = -(-y 3)
      ring
    · change (x 2) = -(-(x 2))
      ring
    · change (-x 1) = -(-(-x 1))
      ring
    · change (x 0) = -(-(x 0))
      ring
    · change (0) = -(-(0))
      ring
    · change (0) = -(0)
      ring
    · change (-(-y 4)) = -(-y 4)
      ring
    · change (-y 0) = -(-(-y 0))
      ring
    · change (-y 1) = -(-(-y 1))
      ring
    · change (-y 2) = -(-(-y 2))
      ring
    · change (-y 3) = -(-(-y 3))
      ring
    · change (-y 4) = -(-(-y 4))
      ring
    · change (0) = -(0)
      ring

/-- The four coefficient matrices of the linear Pfaffian presentation. -/
def quinticPencil (a : Vec R 5) (l : Fin 5 → Vec R 4) : Fin 4 → Mat R 6 :=
  fun i => quinticMatrix a (Pi.single i 1) (fun j => l j i)

def linearValue (l x : Vec R 4) : R := l 0 * x 0 + l 1 * x 1 + l 2 * x 2 + l 3 * x 3

private theorem quinticPencil_entry_0_0 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 0 0 = quinticMatrix a x (fun s => linearValue (l s) x) 0 0 := by
  change (x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (0)) = (0)
  ring

private theorem quinticPencil_entry_0_1 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 0 1 = quinticMatrix a x (fun s => linearValue (l s) x) 0 1 := by
  change (x 0 * (a 3 * (0 : R) + a 0 * (1 : R)) + x 1 * (a 3 * (0 : R) + a 0 * (0 : R)) + x 2 * (a 3 * (0 : R) + a 0 * (0 : R)) + x 3 * (a 3 * (1 : R) + a 0 * (0 : R))) = (a 3 * x 3 + a 0 * x 0)
  ring

private theorem quinticPencil_entry_0_2 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 0 2 = quinticMatrix a x (fun s => linearValue (l s) x) 0 2 := by
  change (x 0 * (a 4 * (0 : R) + a 1 * (1 : R)) + x 1 * (a 4 * (0 : R) + a 1 * (0 : R)) + x 2 * (a 4 * (0 : R) + a 1 * (0 : R)) + x 3 * (a 4 * (1 : R) + a 1 * (0 : R))) = (a 4 * x 3 + a 1 * x 0)
  ring

private theorem quinticPencil_entry_0_3 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 0 3 = quinticMatrix a x (fun s => linearValue (l s) x) 0 3 := by
  change (x 0 * (-(0 : R)) + x 1 * (-(0 : R)) + x 2 * (-(0 : R)) + x 3 * (-(1 : R))) = (-x 3)
  ring

private theorem quinticPencil_entry_0_4 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 0 4 = quinticMatrix a x (fun s => linearValue (l s) x) 0 4 := by
  change (x 0 * ((0 : R)) + x 1 * ((0 : R)) + x 2 * ((1 : R)) + x 3 * ((0 : R))) = (x 2)
  ring

private theorem quinticPencil_entry_0_5 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 0 5 = quinticMatrix a x (fun s => linearValue (l s) x) 0 5 := by
  change (x 0 * (-l 0 0) + x 1 * (-l 0 1) + x 2 * (-l 0 2) + x 3 * (-l 0 3)) = (-(l 0 0 * x 0 + l 0 1 * x 1 + l 0 2 * x 2 + l 0 3 * x 3))
  ring

private theorem quinticPencil_entry_1_0 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 1 0 = quinticMatrix a x (fun s => linearValue (l s) x) 1 0 := by
  change (x 0 * (-(a 3 * (0 : R) + a 0 * (1 : R))) + x 1 * (-(a 3 * (0 : R) + a 0 * (0 : R))) + x 2 * (-(a 3 * (0 : R) + a 0 * (0 : R))) + x 3 * (-(a 3 * (1 : R) + a 0 * (0 : R)))) = (-(a 3 * x 3 + a 0 * x 0))
  ring

private theorem quinticPencil_entry_1_1 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 1 1 = quinticMatrix a x (fun s => linearValue (l s) x) 1 1 := by
  change (x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (0)) = (0)
  ring

private theorem quinticPencil_entry_1_2 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 1 2 = quinticMatrix a x (fun s => linearValue (l s) x) 1 2 := by
  change (x 0 * ((0 : R) + a 2 * (1 : R)) + x 1 * ((0 : R) + a 2 * (0 : R)) + x 2 * ((0 : R) + a 2 * (0 : R)) + x 3 * ((1 : R) + a 2 * (0 : R))) = (x 3 + a 2 * x 0)
  ring

private theorem quinticPencil_entry_1_3 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 1 3 = quinticMatrix a x (fun s => linearValue (l s) x) 1 3 := by
  change (x 0 * ((0 : R)) + x 1 * ((0 : R)) + x 2 * ((1 : R)) + x 3 * ((0 : R))) = (x 2)
  ring

private theorem quinticPencil_entry_1_4 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 1 4 = quinticMatrix a x (fun s => linearValue (l s) x) 1 4 := by
  change (x 0 * (-(0 : R)) + x 1 * (-(1 : R)) + x 2 * (-(0 : R)) + x 3 * (-(0 : R))) = (-x 1)
  ring

private theorem quinticPencil_entry_1_5 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 1 5 = quinticMatrix a x (fun s => linearValue (l s) x) 1 5 := by
  change (x 0 * (-l 1 0) + x 1 * (-l 1 1) + x 2 * (-l 1 2) + x 3 * (-l 1 3)) = (-(l 1 0 * x 0 + l 1 1 * x 1 + l 1 2 * x 2 + l 1 3 * x 3))
  ring

private theorem quinticPencil_entry_2_0 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 2 0 = quinticMatrix a x (fun s => linearValue (l s) x) 2 0 := by
  change (x 0 * (-(a 4 * (0 : R) + a 1 * (1 : R))) + x 1 * (-(a 4 * (0 : R) + a 1 * (0 : R))) + x 2 * (-(a 4 * (0 : R) + a 1 * (0 : R))) + x 3 * (-(a 4 * (1 : R) + a 1 * (0 : R)))) = (-(a 4 * x 3 + a 1 * x 0))
  ring

private theorem quinticPencil_entry_2_1 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 2 1 = quinticMatrix a x (fun s => linearValue (l s) x) 2 1 := by
  change (x 0 * (-((0 : R) + a 2 * (1 : R))) + x 1 * (-((0 : R) + a 2 * (0 : R))) + x 2 * (-((0 : R) + a 2 * (0 : R))) + x 3 * (-((1 : R) + a 2 * (0 : R)))) = (-(x 3 + a 2 * x 0))
  ring

private theorem quinticPencil_entry_2_2 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 2 2 = quinticMatrix a x (fun s => linearValue (l s) x) 2 2 := by
  change (x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (0)) = (0)
  ring

private theorem quinticPencil_entry_2_3 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 2 3 = quinticMatrix a x (fun s => linearValue (l s) x) 2 3 := by
  change (x 0 * (-(0 : R)) + x 1 * (-(1 : R)) + x 2 * (-(0 : R)) + x 3 * (-(0 : R))) = (-x 1)
  ring

private theorem quinticPencil_entry_2_4 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 2 4 = quinticMatrix a x (fun s => linearValue (l s) x) 2 4 := by
  change (x 0 * ((1 : R)) + x 1 * ((0 : R)) + x 2 * ((0 : R)) + x 3 * ((0 : R))) = (x 0)
  ring

private theorem quinticPencil_entry_2_5 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 2 5 = quinticMatrix a x (fun s => linearValue (l s) x) 2 5 := by
  change (x 0 * (-l 2 0) + x 1 * (-l 2 1) + x 2 * (-l 2 2) + x 3 * (-l 2 3)) = (-(l 2 0 * x 0 + l 2 1 * x 1 + l 2 2 * x 2 + l 2 3 * x 3))
  ring

private theorem quinticPencil_entry_3_0 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 3 0 = quinticMatrix a x (fun s => linearValue (l s) x) 3 0 := by
  change (x 0 * (-(-(0 : R))) + x 1 * (-(-(0 : R))) + x 2 * (-(-(0 : R))) + x 3 * (-(-(1 : R)))) = (-(-x 3))
  ring

private theorem quinticPencil_entry_3_1 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 3 1 = quinticMatrix a x (fun s => linearValue (l s) x) 3 1 := by
  change (x 0 * (-((0 : R))) + x 1 * (-((0 : R))) + x 2 * (-((1 : R))) + x 3 * (-((0 : R)))) = (-(x 2))
  ring

private theorem quinticPencil_entry_3_2 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 3 2 = quinticMatrix a x (fun s => linearValue (l s) x) 3 2 := by
  change (x 0 * (-(-(0 : R))) + x 1 * (-(-(1 : R))) + x 2 * (-(-(0 : R))) + x 3 * (-(-(0 : R)))) = (-(-x 1))
  ring

private theorem quinticPencil_entry_3_3 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 3 3 = quinticMatrix a x (fun s => linearValue (l s) x) 3 3 := by
  change (x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (0)) = (0)
  ring

private theorem quinticPencil_entry_3_4 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 3 4 = quinticMatrix a x (fun s => linearValue (l s) x) 3 4 := by
  change (x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (0)) = (0)
  ring

private theorem quinticPencil_entry_3_5 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 3 5 = quinticMatrix a x (fun s => linearValue (l s) x) 3 5 := by
  change (x 0 * (-l 3 0) + x 1 * (-l 3 1) + x 2 * (-l 3 2) + x 3 * (-l 3 3)) = (-(l 3 0 * x 0 + l 3 1 * x 1 + l 3 2 * x 2 + l 3 3 * x 3))
  ring

private theorem quinticPencil_entry_4_0 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 4 0 = quinticMatrix a x (fun s => linearValue (l s) x) 4 0 := by
  change (x 0 * (-((0 : R))) + x 1 * (-((0 : R))) + x 2 * (-((1 : R))) + x 3 * (-((0 : R)))) = (-(x 2))
  ring

private theorem quinticPencil_entry_4_1 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 4 1 = quinticMatrix a x (fun s => linearValue (l s) x) 4 1 := by
  change (x 0 * (-(-(0 : R))) + x 1 * (-(-(1 : R))) + x 2 * (-(-(0 : R))) + x 3 * (-(-(0 : R)))) = (-(-x 1))
  ring

private theorem quinticPencil_entry_4_2 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 4 2 = quinticMatrix a x (fun s => linearValue (l s) x) 4 2 := by
  change (x 0 * (-((1 : R))) + x 1 * (-((0 : R))) + x 2 * (-((0 : R))) + x 3 * (-((0 : R)))) = (-(x 0))
  ring

private theorem quinticPencil_entry_4_3 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 4 3 = quinticMatrix a x (fun s => linearValue (l s) x) 4 3 := by
  change (x 0 * (-(0)) + x 1 * (-(0)) + x 2 * (-(0)) + x 3 * (-(0))) = (-(0))
  ring

private theorem quinticPencil_entry_4_4 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 4 4 = quinticMatrix a x (fun s => linearValue (l s) x) 4 4 := by
  change (x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (0)) = (0)
  ring

private theorem quinticPencil_entry_4_5 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 4 5 = quinticMatrix a x (fun s => linearValue (l s) x) 4 5 := by
  change (x 0 * (-l 4 0) + x 1 * (-l 4 1) + x 2 * (-l 4 2) + x 3 * (-l 4 3)) = (-(l 4 0 * x 0 + l 4 1 * x 1 + l 4 2 * x 2 + l 4 3 * x 3))
  ring

private theorem quinticPencil_entry_5_0 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 5 0 = quinticMatrix a x (fun s => linearValue (l s) x) 5 0 := by
  change (x 0 * (-(-l 0 0)) + x 1 * (-(-l 0 1)) + x 2 * (-(-l 0 2)) + x 3 * (-(-l 0 3))) = (-(-(l 0 0 * x 0 + l 0 1 * x 1 + l 0 2 * x 2 + l 0 3 * x 3)))
  ring

private theorem quinticPencil_entry_5_1 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 5 1 = quinticMatrix a x (fun s => linearValue (l s) x) 5 1 := by
  change (x 0 * (-(-l 1 0)) + x 1 * (-(-l 1 1)) + x 2 * (-(-l 1 2)) + x 3 * (-(-l 1 3))) = (-(-(l 1 0 * x 0 + l 1 1 * x 1 + l 1 2 * x 2 + l 1 3 * x 3)))
  ring

private theorem quinticPencil_entry_5_2 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 5 2 = quinticMatrix a x (fun s => linearValue (l s) x) 5 2 := by
  change (x 0 * (-(-l 2 0)) + x 1 * (-(-l 2 1)) + x 2 * (-(-l 2 2)) + x 3 * (-(-l 2 3))) = (-(-(l 2 0 * x 0 + l 2 1 * x 1 + l 2 2 * x 2 + l 2 3 * x 3)))
  ring

private theorem quinticPencil_entry_5_3 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 5 3 = quinticMatrix a x (fun s => linearValue (l s) x) 5 3 := by
  change (x 0 * (-(-l 3 0)) + x 1 * (-(-l 3 1)) + x 2 * (-(-l 3 2)) + x 3 * (-(-l 3 3))) = (-(-(l 3 0 * x 0 + l 3 1 * x 1 + l 3 2 * x 2 + l 3 3 * x 3)))
  ring

private theorem quinticPencil_entry_5_4 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 5 4 = quinticMatrix a x (fun s => linearValue (l s) x) 5 4 := by
  change (x 0 * (-(-l 4 0)) + x 1 * (-(-l 4 1)) + x 2 * (-(-l 4 2)) + x 3 * (-(-l 4 3))) = (-(-(l 4 0 * x 0 + l 4 1 * x 1 + l 4 2 * x 2 + l 4 3 * x 3)))
  ring

private theorem quinticPencil_entry_5_5 (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x 5 5 = quinticMatrix a x (fun s => linearValue (l s) x) 5 5 := by
  change (x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (0)) = (0)
  ring

theorem quinticPencil_eval (a : Vec R 5) (l : Fin 5 → Vec R 4) (x : Vec R 4) :
    pencil (quinticPencil a l) x = quinticMatrix a x (fun s => linearValue (l s) x) := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact quinticPencil_entry_0_0 a l x
  · exact quinticPencil_entry_0_1 a l x
  · exact quinticPencil_entry_0_2 a l x
  · exact quinticPencil_entry_0_3 a l x
  · exact quinticPencil_entry_0_4 a l x
  · exact quinticPencil_entry_0_5 a l x
  · exact quinticPencil_entry_1_0 a l x
  · exact quinticPencil_entry_1_1 a l x
  · exact quinticPencil_entry_1_2 a l x
  · exact quinticPencil_entry_1_3 a l x
  · exact quinticPencil_entry_1_4 a l x
  · exact quinticPencil_entry_1_5 a l x
  · exact quinticPencil_entry_2_0 a l x
  · exact quinticPencil_entry_2_1 a l x
  · exact quinticPencil_entry_2_2 a l x
  · exact quinticPencil_entry_2_3 a l x
  · exact quinticPencil_entry_2_4 a l x
  · exact quinticPencil_entry_2_5 a l x
  · exact quinticPencil_entry_3_0 a l x
  · exact quinticPencil_entry_3_1 a l x
  · exact quinticPencil_entry_3_2 a l x
  · exact quinticPencil_entry_3_3 a l x
  · exact quinticPencil_entry_3_4 a l x
  · exact quinticPencil_entry_3_5 a l x
  · exact quinticPencil_entry_4_0 a l x
  · exact quinticPencil_entry_4_1 a l x
  · exact quinticPencil_entry_4_2 a l x
  · exact quinticPencil_entry_4_3 a l x
  · exact quinticPencil_entry_4_4 a l x
  · exact quinticPencil_entry_4_5 a l x
  · exact quinticPencil_entry_5_0 a l x
  · exact quinticPencil_entry_5_1 a l x
  · exact quinticPencil_entry_5_2 a l x
  · exact quinticPencil_entry_5_3 a l x
  · exact quinticPencil_entry_5_4 a l x
  · exact quinticPencil_entry_5_5 a l x

theorem quinticPencil_alternating (a : Vec R 5) (l : Fin 5 → Vec R 4) :
    ∀ i, IsAlternating (quinticPencil a l i) :=
  fun i => quinticMatrix_alternating a (Pi.single i 1) (fun j => l j i)

end
end PfaffianDescent
