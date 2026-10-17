import PfaffianDescent.VoisinParameterizedLineSeparability
import PfaffianDescent.VoisinStandardFourLineWitness

/-!
# A universal change of coordinates for the four-line witness

The sixteen entries of a `4 × 4` matrix are used as independent
parameters.  Its first column is the common point of the four lines and
the remaining standard four-line directions are transported by the same
matrix.  The determinant is a nonzero polynomial, so a simultaneous
nonvanishing argument can later choose an invertible specialization.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial

universe u

abbrev FourLineChangeParameters := Fin 4 × Fin 4

abbrev FourLineChangeRing (K : Type u) [CommRing K] :=
  MvPolynomial FourLineChangeParameters K

/-- The generic `4 × 4` coordinate-change matrix. -/
noncomputable def universalFourLineChangeMatrix
    (K : Type u) [CommRing K] :
    Matrix (Fin 4) (Fin 4) (FourLineChangeRing K) :=
  fun i j => X (i, j)

/-- The common point of the four transported lines. -/
noncomputable def universalChangedFourLineBase
    (K : Type u) [CommRing K] : Fin 4 → FourLineChangeRing K :=
  (universalFourLineChangeMatrix K).mulVec
    (fun i => C ((Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) i))

/-- The four standard directions transported by the generic matrix. -/
noncomputable def universalChangedFourLineDirection
    (K : Type u) [Field K] (i j : Fin 2) :
    Fin 4 → FourLineChangeRing K :=
  (universalFourLineChangeMatrix K).mulVec
    (fun k => C (lineDirection (L := K) i j k))

/-- The generic matrix specializes entrywise to the identity matrix. -/
theorem universalFourLineChangeMatrix_map_identity
    (K : Type u) [Field K] :
    (universalFourLineChangeMatrix K).map
      (MvPolynomial.eval₂Hom (RingHom.id K)
        (fun ij : FourLineChangeParameters => if ij.1 = ij.2 then 1 else 0)) = 1 := by
  ext i j
  simp [universalFourLineChangeMatrix, Matrix.one_apply]

/-- The determinant of the generic coordinate-change matrix is a nonzero
polynomial. -/
theorem universalFourLineChangeMatrix_det_ne_zero
    (K : Type u) [Field K] :
    (universalFourLineChangeMatrix K).det ≠ 0 := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id K)
    (fun ij : FourLineChangeParameters => if ij.1 = ij.2 then 1 else 0)
  intro h
  have hmap := congrArg φ h
  have hmatrix : (universalFourLineChangeMatrix K).map φ = 1 := by
    simpa [φ] using universalFourLineChangeMatrix_map_identity K
  rw [map_zero] at hmap
  have hdetmap : ((universalFourLineChangeMatrix K).map φ).det =
      φ (universalFourLineChangeMatrix K).det := by
    change (φ.mapMatrix (universalFourLineChangeMatrix K)).det = _
    exact (RingHom.map_det φ (universalFourLineChangeMatrix K)).symm
  have honezero : (1 : K) = 0 := by
    calc
      1 = (1 : Matrix (Fin 4) (Fin 4) K).det := Matrix.det_one.symm
      _ = ((universalFourLineChangeMatrix K).map φ).det :=
        congrArg Matrix.det hmatrix.symm
      _ = φ (universalFourLineChangeMatrix K).det := hdetmap
      _ = 0 := hmap
  exact one_ne_zero honezero

/-- Specializing the polynomial common point is matrix multiplication by
the specialized coordinate-change matrix. -/
theorem universalChangedFourLineBase_eval
    (K : Type u) [Field K]
    (x : FourLineChangeParameters → K) (i : Fin 4) :
    MvPolynomial.eval x (universalChangedFourLineBase K i) =
      Matrix.mulVec (fun r s : Fin 4 => x (r, s)) (Pi.single 0 1) i := by
  simp [universalChangedFourLineBase, universalFourLineChangeMatrix,
    Matrix.mulVec, dotProduct]

/-- Specializing a polynomial direction transports the corresponding
standard direction by the specialized matrix. -/
theorem universalChangedFourLineDirection_eval
    (K : Type u) [Field K]
    (x : FourLineChangeParameters → K) (a b : Fin 2) (i : Fin 4) :
    MvPolynomial.eval x (universalChangedFourLineDirection K a b i) =
      Matrix.mulVec (fun r s : Fin 4 => x (r, s)) (lineDirection a b) i := by
  simp [universalChangedFourLineDirection, universalFourLineChangeMatrix,
    Matrix.mulVec, dotProduct]

/-- If the cubic is nonzero at some vector, its value at the universal
common point is a nonzero parameter polynomial. -/
theorem universalChangedCubic_baseEvaluation_ne_zero
    (K : Type u) [Field K] (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0) :
    (c.map MvPolynomial.C).eval (universalChangedFourLineBase K) ≠ 0 := by
  obtain ⟨v, hv⟩ := hc
  let x : FourLineChangeParameters → K :=
    fun ij => if ij.2 = 0 then v ij.1 else 0
  intro hzero
  have hspec := congrArg (MvPolynomial.eval x) hzero
  have hspec' : MvPolynomial.eval x
      ((c.map MvPolynomial.C).eval (universalChangedFourLineBase K)) = 0 := by
    simpa using hspec
  let φ := MvPolynomial.eval₂Hom (RingHom.id K) x
  have hval := Cubic.eval_map φ (c.map MvPolynomial.C)
    (universalChangedFourLineBase K)
  have hcmap : (c.map MvPolynomial.C).map φ = c := by
    funext i
    simp [Cubic.map, φ]
  rw [hcmap] at hval
  have hval' : MvPolynomial.eval x
      ((c.map MvPolynomial.C).eval (universalChangedFourLineBase K)) =
      c.eval (fun j => MvPolynomial.eval x
        (universalChangedFourLineBase K j)) := by
    simpa [φ] using hval.symm
  rw [hval'] at hspec'
  apply hv
  rw [← hspec']
  congr 1
  funext i
  rw [universalChangedFourLineBase_eval]
  simp [Matrix.mulVec, dotProduct, x]

/-- A (possibly singular) matrix specialization whose first column is `a`
and whose active standard direction column is `b`. -/
def fourLineChangeSpecialization
    (K : Type u) [Field K] (q : Fin 2 × Fin 2)
    (a b : Fin 4 → K) : FourLineChangeParameters → K :=
  fun ij =>
    if ij.2 = 0 then a ij.1
    else if ij.2 = (if q.1 = 0 then 2 else 1) then b ij.1
    else 0

theorem universalChangedFourLineBase_eval_specialization
    (K : Type u) [Field K] (q : Fin 2 × Fin 2)
    (a b : Fin 4 → K) :
    (fun i => MvPolynomial.eval (fourLineChangeSpecialization K q a b)
      (universalChangedFourLineBase K i)) = a := by
  funext i
  rw [universalChangedFourLineBase_eval]
  simp [Matrix.mulVec, dotProduct, fourLineChangeSpecialization,
    Fin.sum_univ_four, Pi.single]

theorem universalChangedFourLineDirection_eval_specialization
    (K : Type u) [Field K] (q : Fin 2 × Fin 2)
    (a b : Fin 4 → K) :
    (fun i => MvPolynomial.eval (fourLineChangeSpecialization K q a b)
      (universalChangedFourLineDirection K q.1 q.2 i)) = b := by
  funext i
  rw [universalChangedFourLineDirection_eval]
  rcases q with ⟨q₁, q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    simp [Matrix.mulVec, dotProduct, fourLineChangeSpecialization,
      lineDirection, Fin.sum_univ_four, Pi.single]

/-- If the cubic is nonzero somewhere, its value on each universal
transported direction is a nonzero parameter polynomial. -/
theorem universalChangedCubic_directionEvaluation_ne_zero
    (K : Type u) [Field K] (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0) (q : Fin 2 × Fin 2) :
    (c.map MvPolynomial.C).eval
      (universalChangedFourLineDirection K q.1 q.2) ≠ 0 := by
  obtain ⟨v, hv⟩ := hc
  let x := fourLineChangeSpecialization K q (fun _ => 0) v
  intro hzero
  have hspec := congrArg (MvPolynomial.eval x) hzero
  have hzeroeval : c.eval (fun j => MvPolynomial.eval x
      (universalChangedFourLineDirection K q.1 q.2 j)) = 0 := by
    rw [← parameterizedCubic_baseEvaluation_eval c
      (universalChangedFourLineDirection K q.1 q.2) x]
    simpa using hspec
  rw [universalChangedFourLineDirection_eval_specialization] at hzeroeval
  exact hv hzeroeval

def StrongFourLineChangeWitness
    (K : Type u) [Field K] (c : Cubic K 4)
    (x : FourLineChangeParameters → K) : Prop :=
  MvPolynomial.eval x (universalFourLineChangeMatrix K).det ≠ 0 ∧
  c.eval (fun j => MvPolynomial.eval x
    (universalChangedFourLineBase K j)) ≠ 0 ∧
  (∀ q : Fin 2 × Fin 2, c.eval
    (fun j => MvPolynomial.eval x
      (universalChangedFourLineDirection K q.1 q.2 j)) ≠ 0) ∧
  ∀ q : Fin 2 × Fin 2,
    (AllCharacteristics.cubicLinePolynomial c
      (fun j => MvPolynomial.eval x
        (universalChangedFourLineBase K j))
      (fun j => MvPolynomial.eval x
        (universalChangedFourLineDirection K q.1 q.2 j))).Separable

noncomputable def universalChangedCubicDirectionProduct
    (K : Type u) [Field K] (c : Cubic K 4) : FourLineChangeRing K :=
  ∏ q : Fin 2 × Fin 2,
    (c.map MvPolynomial.C).eval
      (universalChangedFourLineDirection K q.1 q.2)

noncomputable def universalStrongFourLineDet
    (K : Type u) [Field K] (c : Cubic K 4) : FourLineChangeRing K :=
  (universalFourLineChangeMatrix K).det *
    universalChangedCubicDirectionProduct K c

theorem universalChangedCubicDirectionProduct_ne_zero
    (K : Type u) [Field K] (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0) :
    universalChangedCubicDirectionProduct K c ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  exact universalChangedCubic_directionEvaluation_ne_zero K c hc q

theorem universalStrongFourLineDet_ne_zero
    (K : Type u) [Field K] (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0) :
    universalStrongFourLineDet K c ≠ 0 := by
  exact mul_ne_zero (universalFourLineChangeMatrix_det_ne_zero K)
    (universalChangedCubicDirectionProduct_ne_zero K c hc)

theorem eval_matrix_det_ne_zero_of_strongFourLineDet
    (K : Type u) [Field K] (c : Cubic K 4)
    (x : FourLineChangeParameters → K)
    (h : MvPolynomial.eval x (universalStrongFourLineDet K c) ≠ 0) :
    MvPolynomial.eval x (universalFourLineChangeMatrix K).det ≠ 0 := by
  intro hzero
  apply h
  simp [universalStrongFourLineDet, hzero]

theorem eval_directions_ne_zero_of_strongFourLineDet
    (K : Type u) [Field K] (c : Cubic K 4)
    (x : FourLineChangeParameters → K)
    (h : MvPolynomial.eval x (universalStrongFourLineDet K c) ≠ 0) :
    ∀ q : Fin 2 × Fin 2, c.eval
      (fun j => MvPolynomial.eval x
        (universalChangedFourLineDirection K q.1 q.2 j)) ≠ 0 := by
  have hproduct : MvPolynomial.eval x
      (universalChangedCubicDirectionProduct K c) ≠ 0 := by
    intro hzero
    apply h
    simp [universalStrongFourLineDet, hzero]
  have hprod : ∏ q : Fin 2 × Fin 2,
      MvPolynomial.eval x ((c.map MvPolynomial.C).eval
        (universalChangedFourLineDirection K q.1 q.2)) ≠ 0 := by
    simpa [universalChangedCubicDirectionProduct] using hproduct
  intro q
  rw [← parameterizedCubic_baseEvaluation_eval c
    (universalChangedFourLineDirection K q.1 q.2) x]
  exact (Finset.prod_ne_zero_iff.mp hprod) q (Finset.mem_univ q)

/-- Strengthened simultaneous selection: the specialized common point and
all four specialized directions are outside the cubic, while every line
restriction is separable and the coordinate change remains invertible. -/
theorem exists_invertible_change_with_four_separable_nonzero_cubic_lines
    (K : Type u) [Field K] [CharZero K] [Infinite K]
    (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0)
    (hdisc : ∀ q : Fin 2 × Fin 2,
      (parameterizedCubicLinePolynomial c
        (universalChangedFourLineBase K)
        (universalChangedFourLineDirection K q.1 q.2)).discr ≠ 0) :
    ∃ x : FourLineChangeParameters → K,
      StrongFourLineChangeWitness K c x := by
  have hdet := universalStrongFourLineDet_ne_zero K c hc
  have hbase := universalChangedCubic_baseEvaluation_ne_zero K c hc
  obtain ⟨x, hxdet, hxbase, hxsep⟩ :=
    exists_parameter_with_det_ne_zero_and_cubicLines_separable
      (σ := FourLineChangeParameters) (ι := Fin 2 × Fin 2)
      c (universalStrongFourLineDet K c) (universalChangedFourLineBase K)
        (fun q => universalChangedFourLineDirection K q.1 q.2)
      hdet hbase hdisc
  exact ⟨x, eval_matrix_det_ne_zero_of_strongFourLineDet K c x hxdet,
    hxbase, eval_directions_ne_zero_of_strongFourLineDet K c x hxdet, hxsep⟩

/-- A single separable line section certifies that any one of the four
universal transported-line discriminants is a nonzero polynomial.  The
matrix used for this individual certification need not be invertible;
invertibility is imposed later, simultaneously with all four
discriminants. -/
theorem universalChangedFourLine_discr_ne_zero_of_separable_line
    (K : Type u) [Field K] [CharZero K]
    (c : Cubic K 4) (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0)
    (q : Fin 2 × Fin 2) (a b : Fin 4 → K)
    (ha : c.eval a ≠ 0)
    (hsep : (AllCharacteristics.cubicLinePolynomial c a b).Separable) :
    (parameterizedCubicLinePolynomial c
      (universalChangedFourLineBase K)
      (universalChangedFourLineDirection K q.1 q.2)).discr ≠ 0 := by
  let f := parameterizedCubicLinePolynomial c
    (universalChangedFourLineBase K)
    (universalChangedFourLineDirection K q.1 q.2)
  let x := fourLineChangeSpecialization K q a b
  let φ := MvPolynomial.eval₂Hom (RingHom.id K) x
  have hbase := universalChangedCubic_baseEvaluation_ne_zero K c hc
  have hf : f.degree = 3 := by
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree
      (c.map MvPolynomial.C) (universalChangedFourLineBase K)
      (universalChangedFourLineDirection K q.1 q.2) hbase
  have hmapEq : f.map φ =
      AllCharacteristics.cubicLinePolynomial c a b := by
    rw [parameterizedCubicLinePolynomial_map_eval]
    rw [universalChangedFourLineBase_eval_specialization,
      universalChangedFourLineDirection_eval_specialization]
  have hmapDegree : (f.map φ).degree = 3 := by
    rw [hmapEq]
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree c a b ha
  have hmapDisc : (f.map φ).discr ≠ 0 := by
    rw [hmapEq]
    exact cubic_discr_ne_zero_of_separable _
      (by rw [← hmapEq]; exact hmapDegree) hsep
  exact cubic_discr_ne_zero_of_specialization φ f hf hmapDegree hmapDisc

/-- Once the four universal discriminants are known to be nonzero, one
invertible change of coordinates makes all four transported line sections
separable at once.  This isolates the remaining geometric input precisely
as the four hypotheses `hdisc`. -/
theorem exists_invertible_change_with_four_separable_cubic_lines
    (K : Type u) [Field K] [CharZero K] [Infinite K]
    (c : Cubic K 4)
    (hc : ∃ v : Fin 4 → K, c.eval v ≠ 0)
    (hdisc : ∀ q : Fin 2 × Fin 2,
      (parameterizedCubicLinePolynomial c
        (universalChangedFourLineBase K)
        (universalChangedFourLineDirection K q.1 q.2)).discr ≠ 0) :
    ∃ x : FourLineChangeParameters → K,
      MvPolynomial.eval x (universalFourLineChangeMatrix K).det ≠ 0 ∧
      c.eval (fun j => MvPolynomial.eval x
        (universalChangedFourLineBase K j)) ≠ 0 ∧
      ∀ q : Fin 2 × Fin 2,
        (AllCharacteristics.cubicLinePolynomial c
          (fun j => MvPolynomial.eval x
            (universalChangedFourLineBase K j))
          (fun j => MvPolynomial.eval x
            (universalChangedFourLineDirection K q.1 q.2 j))).Separable := by
  let det := (universalFourLineChangeMatrix K).det
  let a := universalChangedFourLineBase K
  let b : Fin 2 × Fin 2 → Fin 4 → FourLineChangeRing K :=
    fun q => universalChangedFourLineDirection K q.1 q.2
  have hdet : det ≠ 0 := universalFourLineChangeMatrix_det_ne_zero K
  have hbase : (c.map MvPolynomial.C).eval a ≠ 0 :=
    universalChangedCubic_baseEvaluation_ne_zero K c hc
  have hdisc' : ∀ q, (parameterizedCubicLinePolynomial c a (b q)).discr ≠ 0 :=
    hdisc
  obtain ⟨x, hxdet, hxbase, hxsep⟩ :=
    exists_parameter_with_det_ne_zero_and_cubicLines_separable
      c det a b hdet hbase hdisc'
  exact ⟨x, hxdet, hxbase, hxsep⟩

/-- One transverse affine line is enough to construct an invertible
four-line arrangement whose four cubic restrictions are all separable. -/
theorem exists_invertible_change_with_four_separable_cubic_lines_of_one
    (K : Type u) [Field K] [CharZero K] [Infinite K]
    (c : Cubic K 4)
    (hline : ∃ a b : Fin 4 → K,
      c.eval a ≠ 0 ∧
        (AllCharacteristics.cubicLinePolynomial c a b).Separable) :
    ∃ x : FourLineChangeParameters → K,
      MvPolynomial.eval x (universalFourLineChangeMatrix K).det ≠ 0 ∧
      c.eval (fun j => MvPolynomial.eval x
        (universalChangedFourLineBase K j)) ≠ 0 ∧
      ∀ q : Fin 2 × Fin 2,
        (AllCharacteristics.cubicLinePolynomial c
          (fun j => MvPolynomial.eval x
            (universalChangedFourLineBase K j))
          (fun j => MvPolynomial.eval x
            (universalChangedFourLineDirection K q.1 q.2 j))).Separable := by
  obtain ⟨a, b, ha, hsep⟩ := hline
  have hc : ∃ v : Fin 4 → K, c.eval v ≠ 0 := ⟨a, ha⟩
  apply exists_invertible_change_with_four_separable_cubic_lines K c hc
  intro q
  exact universalChangedFourLine_discr_ne_zero_of_separable_line
    K c hc q a b ha hsep

/-- One transverse line also yields a simultaneous arrangement whose four
direction points avoid the cubic. -/
theorem exists_invertible_change_with_four_separable_nonzero_cubic_lines_of_one
    (K : Type u) [Field K] [CharZero K] [Infinite K]
    (c : Cubic K 4)
    (hline : ∃ a b : Fin 4 → K,
      c.eval a ≠ 0 ∧
        (AllCharacteristics.cubicLinePolynomial c a b).Separable) :
    ∃ x : FourLineChangeParameters → K,
      StrongFourLineChangeWitness K c x := by
  obtain ⟨a, b, ha, hsep⟩ := hline
  have hc : ∃ v : Fin 4 → K, c.eval v ≠ 0 := ⟨a, ha⟩
  apply exists_invertible_change_with_four_separable_nonzero_cubic_lines K c hc
  intro q
  exact universalChangedFourLine_discr_ne_zero_of_separable_line
    K c hc q a b ha hsep

end PfaffianDescent
