import PfaffianDescent.VoisinQuadraticKernelBlockChart
import PfaffianDescent.VoisinGenericQuadraticEvaluation
import PfaffianDescent.VoisinTwelvePointEvaluationFaithful
import AllCharacteristics.HomogeneousSpecialization

/-!
# The quadratic evaluation matrix of eight ordered vectors

The columns are the ten degree-two monomials in four homogeneous
coordinates.  The entries are polynomial functions of the coordinates of
the eight marked vectors.  This is the affine-cone matrix from which a
full-rank eight-column chart of the configuration family can be selected.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u v

/-- The ten-column quadratic evaluation matrix at eight ordered vectors. -/
noncomputable def eightPointQuadraticEvaluationMatrix
    {R : Type u} [CommRing R] (y : Fin 8 → Fin 4 → R) :
    Matrix (Fin 8) (Monomials (Fin 4) 2) R :=
  fun i m => (MvPolynomial.monomial m.1 (1 : R)).eval (y i)

/-- Evaluating the entries of the universal matrix commutes with a change of
coefficient ring. -/
theorem eightPointQuadraticEvaluationMatrix_map
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S]
    (f : R →+* S) (y : Fin 8 → Fin 4 → R) :
    (eightPointQuadraticEvaluationMatrix y).map f =
      eightPointQuadraticEvaluationMatrix (fun i j => f (y i j)) := by
  ext i m
  simp [eightPointQuadraticEvaluationMatrix, MvPolynomial.eval_monomial]

/-- Rescaling each projective representative scales its evaluation row by
the square of that row's scalar. -/
theorem eightPointQuadraticEvaluationMatrix_scale
    {R : Type u} [CommRing R]
    (a : Fin 8 → R) (y : Fin 8 → Fin 4 → R) :
    eightPointQuadraticEvaluationMatrix
        (fun i j => a i * y i j) =
      Matrix.diagonal (fun i => a i ^ 2) *
        eightPointQuadraticEvaluationMatrix y := by
  ext i m
  have hhom :
      (MvPolynomial.monomial m.1 (1 : R)).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_monomial 1 m.2
  have hscale := AllCharacteristics.eval₂_homogeneous_smul
    (MvPolynomial.monomial m.1 (1 : R)) hhom
    (RingHom.id R) (y i) (a i)
  simpa [eightPointQuadraticEvaluationMatrix, Matrix.diagonal_mul,
    MvPolynomial.eval, Pi.smul_apply, smul_eq_mul] using hscale

/-- The ordered affine-cone parameter ring for eight vectors in four-space. -/
abbrev eightVectorCoordinateRing (K : Type u) [CommRing K] :=
  MvPolynomial (Fin 8 × Fin 4) K

/-- The matrix with polynomial entries on the ordered affine-cone parameter
space. -/
noncomputable def universalEightPointQuadraticEvaluationMatrix
    (K : Type u) [CommRing K] :
    Matrix (Fin 8) (Monomials (Fin 4) 2) (eightVectorCoordinateRing K) :=
  eightPointQuadraticEvaluationMatrix
    (fun i j => MvPolynomial.X (i, j))

/-- Every ordered eight-vector configuration is a specialization of the
single polynomial evaluation matrix. -/
theorem universalEightPointQuadraticEvaluationMatrix_specialize
    {K : Type u} [CommRing K]
    {R : Type v} [CommRing R]
    (f : K →+* R) (y : Fin 8 → Fin 4 → R) :
    (universalEightPointQuadraticEvaluationMatrix K).map
      (MvPolynomial.eval₂Hom f (fun ij => y ij.1 ij.2)) =
        eightPointQuadraticEvaluationMatrix y := by
  rw [universalEightPointQuadraticEvaluationMatrix,
    eightPointQuadraticEvaluationMatrix_map]
  congr 1
  funext i j
  simp

/-- The eight-column minor indexed by a chosen set of quadratic monomials. -/
noncomputable def eightPointQuadraticEvaluationMinor
    {R : Type u} [CommRing R]
    (e : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) : Matrix (Fin 8) (Fin 8) R :=
  (eightPointQuadraticEvaluationMatrix y).submatrix id e

/-- The same row scaling law holds for every chosen eight-column minor. -/
theorem eightPointQuadraticEvaluationMinor_scale
    {R : Type u} [CommRing R]
    (e : Fin 8 ↪ Monomials (Fin 4) 2)
    (a : Fin 8 → R) (y : Fin 8 → Fin 4 → R) :
    eightPointQuadraticEvaluationMinor e
        (fun i j => a i * y i j) =
      Matrix.diagonal (fun i => a i ^ 2) *
        eightPointQuadraticEvaluationMinor e y := by
  ext i j
  have h := congrArg
    (fun M : Matrix (Fin 8) (Monomials (Fin 4) 2) R => M i (e j))
    (eightPointQuadraticEvaluationMatrix_scale a y)
  simpa [eightPointQuadraticEvaluationMinor, Matrix.diagonal_mul] using h

/-- Changing the projective representatives by units does not affect
invertibility of a chosen quadratic evaluation minor. -/
theorem eightPointQuadraticEvaluationMinor_isUnit_det_scale_iff
    {R : Type u} [CommRing R]
    (e : Fin 8 ↪ Monomials (Fin 4) 2)
    (a : Fin 8 → Rˣ) (y : Fin 8 → Fin 4 → R) :
    IsUnit (eightPointQuadraticEvaluationMinor e
      (fun i j => (a i : R) * y i j)).det ↔
      IsUnit (eightPointQuadraticEvaluationMinor e y).det := by
  rw [eightPointQuadraticEvaluationMinor_scale, Matrix.det_mul,
    Matrix.det_diagonal]
  have hunit : IsUnit (∏ i : Fin 8, (a i : R) ^ 2) := by
    refine ⟨∏ i : Fin 8, (a i) ^ 2, ?_⟩
    simp
  rw [IsUnit.mul_iff]
  simp [hunit]

/-- Reordering the eight points preserves invertibility of every selected
minor, so the rank condition is invariant under the permutation quotient. -/
theorem eightPointQuadraticEvaluationMinor_isUnit_det_perm_iff
    {R : Type u} [CommRing R]
    (e : Fin 8 ↪ Monomials (Fin 4) 2)
    (σ : Equiv.Perm (Fin 8)) (y : Fin 8 → Fin 4 → R) :
    IsUnit (eightPointQuadraticEvaluationMinor e (fun i => y (σ i))).det ↔
      IsUnit (eightPointQuadraticEvaluationMinor e y).det := by
  have hmatrix :
      eightPointQuadraticEvaluationMinor e (fun i => y (σ i)) =
        (eightPointQuadraticEvaluationMinor e y).submatrix σ id := by
    rfl
  rw [hmatrix, Matrix.det_permute, IsUnit.mul_iff]
  have hs : IsUnit ((Equiv.Perm.sign σ : ℤ) : R) := by
    exact IsUnit.map (Int.castRingHom R).toMonoidHom
      (Units.isUnit (Equiv.Perm.sign σ))
  simp [hs]

/-- Permuting evaluation rows leaves the full quadratic restriction kernel
literally unchanged. -/
theorem eightPointQuadraticEvaluationKernel_relabel
    {R : Type u} [CommRing R]
    (σ : Equiv.Perm (Fin 8)) (y : Fin 8 → Fin 4 → R) :
    LinearMap.ker (Matrix.toLin'
      (eightPointQuadraticEvaluationMatrix (fun i => y (σ i)))) =
    LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)) := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv ⊢
    funext i
    have hi := congrFun hv (σ.symm i)
    simpa [Matrix.toLin'_apply, Matrix.mulVec,
      eightPointQuadraticEvaluationMatrix] using hi
  · intro hv
    rw [LinearMap.mem_ker] at hv ⊢
    funext i
    have hi := congrFun hv (σ i)
    simpa [Matrix.toLin'_apply, Matrix.mulVec,
      eightPointQuadraticEvaluationMatrix] using hi

/-- Changing each homogeneous representative by a unit does not alter the
quadratic evaluation kernel, over any commutative coefficient ring. -/
theorem eightPointQuadraticEvaluationKernel_scale_units
    {R : Type u} [CommRing R]
    (a : Fin 8 → R) (ha : ∀ i, IsUnit (a i))
    (y : Fin 8 → Fin 4 → R) :
    LinearMap.ker (Matrix.toLin'
      (eightPointQuadraticEvaluationMatrix
        (fun i j => a i * y i j))) =
    LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)) := by
  apply Submodule.ext
  intro v
  have hrow (i : Fin 8) :
      (Matrix.toLin' (eightPointQuadraticEvaluationMatrix
        (fun k j => a k * y k j)) v) i =
      (a i)^2 * (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y) v) i := by
    simp only [Matrix.toLin'_apply,
      eightPointQuadraticEvaluationMatrix_scale,
      Matrix.mulVec, Matrix.diagonal_mul]
    simp [dotProduct, Finset.mul_sum, mul_assoc]
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv ⊢
    funext i
    have hi := congrFun hv i
    rw [hrow] at hi
    exact ((ha i).pow 2).mul_left_cancel (by simpa using hi)
  · intro hv
    rw [LinearMap.mem_ker] at hv ⊢
    funext i
    rw [hrow]
    simp [congrFun hv i]

/-- The quadratic restriction kernel is intrinsic to the unordered set of
eight projective points: permutations and unit rescalings of representatives
leave it unchanged. -/
theorem eightPointQuadraticEvaluationKernel_scale_relabel
    {R : Type u} [CommRing R]
    (σ : Equiv.Perm (Fin 8))
    (a : Fin 8 → R) (ha : ∀ i, IsUnit (a i))
    (y : Fin 8 → Fin 4 → R) :
    LinearMap.ker (Matrix.toLin'
      (eightPointQuadraticEvaluationMatrix
        (fun i j => a i * y (σ i) j))) =
    LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)) :=
  (eightPointQuadraticEvaluationKernel_scale_units a ha
    (fun i => y (σ i))).trans
    (eightPointQuadraticEvaluationKernel_relabel σ y)

/-- The same minor specializes entrywise with the ordered points. -/
theorem eightPointQuadraticEvaluationMinor_map
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S]
    (f : R →+* S)
    (e : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) :
    (eightPointQuadraticEvaluationMinor e y).map f =
      eightPointQuadraticEvaluationMinor e (fun i j => f (y i j)) := by
  ext i j
  simpa [eightPointQuadraticEvaluationMinor] using
    congrArg (fun M : Matrix (Fin 8) (Monomials (Fin 4) 2) S => M i (e j))
      (eightPointQuadraticEvaluationMatrix_map f y)

/-- A full-rank specialized minor yields the same full-rank minor over the
generic field of any integral coordinate ring carrying the eight vectors. -/
theorem eightPointQuadraticEvaluationMinor_generic_unit
    {R : Type u} [CommRing R] [IsDomain R]
    {S : Type v} [Field S]
    (f : R →+* S)
    (e : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (hminor : IsUnit
      (eightPointQuadraticEvaluationMinor e (fun i j => f (y i j))).det) :
    IsUnit ((eightPointQuadraticEvaluationMinor e y).map
      (algebraMap R (FractionRing R))).det := by
  apply quadraticMatrixBlock_generic_det_unit_of_specialization_unit
    f (eightPointQuadraticEvaluationMinor e y)
  simpa only [eightPointQuadraticEvaluationMinor_map] using hminor

/-- Surjectivity of the ten-column evaluation map selects a genuinely
invertible eight-column monomial minor at the given field-valued tuple. -/
theorem exists_unit_eightPointQuadraticEvaluationMinor_of_surjective
    {K : Type u} [Field K]
    (y : Fin 8 → Fin 4 → K)
    (hsurj : Function.Surjective
      (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))) :
    ∃ e : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit (eightPointQuadraticEvaluationMinor e y).det := by
  classical
  let M := eightPointQuadraticEvaluationMatrix y
  have hspan : Submodule.span K (Set.range M.col) = ⊤ := by
    rw [← Matrix.range_toLin']
    exact LinearMap.range_eq_top.mpr hsurj
  obtain ⟨κ, a, ha, hspan', hli⟩ :=
    exists_linearIndependent' K M.col
  letI : Fintype κ := Fintype.ofInjective a ha
  have hselected : Submodule.span K (Set.range (M.col ∘ a)) = ⊤ := by
    rw [hspan', hspan]
  have hcard : Fintype.card κ = 8 := by
    have hdim := finrank_span_eq_card hli
    rw [hselected, finrank_top, Module.finrank_pi] at hdim
    simpa using hdim.symm
  let e : Fin 8 ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let b : Fin 8 ↪ Monomials (Fin 4) 2 :=
    ⟨a ∘ e, ha.comp e.injective⟩
  have hli_b : LinearIndependent K (fun j : Fin 8 => M.col (b j)) := by
    exact hli.comp e e.injective
  have hli_minor : LinearIndependent K (M.submatrix id b).col := by
    convert hli_b using 1
    funext j i
    rfl
  have hunit : IsUnit (M.submatrix id b) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli_minor
  exact ⟨b, (Matrix.isUnit_iff_isUnit_det _).mp hunit⟩

/-- Surjectivity of the actual homogeneous quadratic restriction at eight
ordered vectors is exactly strong enough to make the monomial matrix
surjective. -/
theorem eightPointQuadraticEvaluationMatrix_surjective_of_restriction
    {K : Type u} [Field K]
    (y : Fin 8 → Fin 4 → K)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := K)
        (fun j i => y i j) 2)) :
    Function.Surjective
      (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)) := by
  classical
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  let c : Monomials (Fin 4) 2 → K := fun m => q.1.coeff m.1
  refine ⟨c, ?_⟩
  funext i
  have hexp := sum_monomial_coeff_eq q.1 q.2
  have heval := congrArg (fun p : MvPolynomial (Fin 4) K => p.eval (y i)) hexp
  calc
    (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y) c) i =
        ∑ m : Monomials (Fin 4) 2,
          (MvPolynomial.monomial m.1 (q.1.coeff m.1)).eval (y i) := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        eightPointQuadraticEvaluationMatrix, c,
        MvPolynomial.eval_monomial, mul_comm]
    _ = q.1.eval (y i) := by simpa only [MvPolynomial.eval_sum] using heval
    _ = z i := by
      simpa [homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply] using congrFun hq i

/-- One surjective field-valued quadratic restriction makes a monomial
minor invertible over the generic field of the integral family carrying the
same eight vectors. -/
theorem exists_generic_unit_eightPointQuadraticEvaluationMinor_of_specialization
    {R : Type u} [CommRing R] [IsDomain R]
    {S : Type v} [Field S]
    (f : R →+* S) (y : Fin 8 → Fin 4 → R)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := S)
        (fun j i => f (y i j)) 2)) :
    ∃ e : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit ((eightPointQuadraticEvaluationMinor e y).map
        (algebraMap R (FractionRing R))).det := by
  obtain ⟨e, he⟩ :=
    exists_unit_eightPointQuadraticEvaluationMinor_of_surjective
      (fun i j => f (y i j))
      (eightPointQuadraticEvaluationMatrix_surjective_of_restriction
        (fun i j => f (y i j)) hsurj)
  exact ⟨e, eightPointQuadraticEvaluationMinor_generic_unit f e y he⟩

end PfaffianDescent
