import AllCharacteristics.HomogeneousProjective
import Mathlib.RingTheory.FinitePresentation

/-! Actual positive homogeneous charts of the ORIGINAL whole projective
polynomial quotient over its actual Noetherian coefficient ring. The coordinate algebra, original scalar
map and affine comparison are literal; finite type and finite presentation
construct a polynomial surjection with finitely generated whole kernel.
No presentation, reducedness, smoothness or classifier outcome is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
variable (a : CoordinateRing I)

/-- The literal degree-zero homogeneous localization of the full quotient. -/
abbrev OriginalPositiveHomogeneousChartAlgebra001 :=
  HomogeneousLocalization.Away (grading I) a

/-- ORIGINAL R coefficients act through the original degree-zero quotient. -/
def originalPositiveHomogeneousChartBaseMap001 :
    R →+* OriginalPositiveHomogeneousChartAlgebra001 I a :=
  (HomogeneousLocalization.fromZeroRingHom (grading I) (Submonoid.powers a)).comp
    (algebraMap R (grading I 0))

/-- The actual native chart scalar action is the exact original structure hom. -/
def originalPositiveHomogeneousChartNativeAlgebra001 :
    Algebra R (OriginalPositiveHomogeneousChartAlgebra001 I a) :=
  (originalPositiveHomogeneousChartBaseMap001 I a).toAlgebra

/-- No alternative R-algebra structure is inserted in the chart. -/
theorem originalPositiveHomogeneousChart_algebraMap_eq001 :
    letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
    algebraMap R (OriginalPositiveHomogeneousChartAlgebra001 I a) =
      originalPositiveHomogeneousChartBaseMap001 I a := rfl

/-- Finitely many original polynomial variables and actual homogeneous localization
construct finite type over the SAME original R map; no domain hypothesis. -/
theorem originalPositiveHomogeneousChart_finiteType001
    (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d) :
    letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
    Algebra.FiniteType R (OriginalPositiveHomogeneousChartAlgebra001 I a) := by
  letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
  let C := OriginalPositiveHomogeneousChartAlgebra001 I a
  have hZero : (algebraMap R (grading I 0)).FiniteType :=
    RingHom.FiniteType.of_surjective _ (algebraMap_gradeZero_surjective I)
  letI : Algebra.FiniteType (grading I 0) C :=
    HomogeneousLocalization.Away.finiteType a d ha
  have hAway : (HomogeneousLocalization.fromZeroRingHom (grading I)
      (Submonoid.powers a)).FiniteType := by
    change (algebraMap (grading I 0) C).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  change (originalPositiveHomogeneousChartBaseMap001 I a).FiniteType
  exact hAway.comp hZero

/-- The ORIGINAL coefficient ring is Noetherian, so this actual chart algebra is finitely
presented over its retained original scalar map. Nilpotents remain in C. -/
theorem originalPositiveHomogeneousChart_finitePresentation001
    (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d) :
    letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
    Algebra.FinitePresentation R (OriginalPositiveHomogeneousChartAlgebra001 I a) := by
  letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
  exact Algebra.FinitePresentation.of_finiteType.mp
    (originalPositiveHomogeneousChart_finiteType001 I a d hd ha)

/-- Actual finite polynomial presentation of the SAME full chart ring. The
surjective map and FG kernel are constructed, never premise certificates. -/
theorem originalPositiveHomogeneousChart_exists_surjectivePolynomial_fgKernel001
    (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d) :
    letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
    ∃ m : ℕ, ∃ phi : MvPolynomial (Fin m) R →ₐ[R]
        OriginalPositiveHomogeneousChartAlgebra001 I a,
      Function.Surjective phi ∧ (RingHom.ker phi.toRingHom).FG := by
  letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
  letI : Algebra.FinitePresentation R (OriginalPositiveHomogeneousChartAlgebra001 I a) :=
    originalPositiveHomogeneousChart_finitePresentation001 I a d hd ha
  exact Algebra.FinitePresentation.out (R := R)
    (A := OriginalPositiveHomogeneousChartAlgebra001 I a)

/-- Actual D+(a) affine comparison retains the ORIGINAL projective structure map. -/
theorem originalPositiveHomogeneousChartIso_inv_toOriginalBase001
    (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d) :
    (Proj.basicOpenIsoSpec (grading I) a ha hd).inv ≫
        (Proj.basicOpen (grading I) a).ι ≫ toBase I =
      Spec.map (CommRingCat.ofHom (originalPositiveHomogeneousChartBaseMap001 I a)) := by
  change (Proj.basicOpenIsoSpec (grading I) a ha hd).inv ≫
      (Proj.basicOpen (grading I) a).ι ≫
        (Proj.toSpecZero (grading I) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (grading I 0)))) = _
  rw [Proj.basicOpenIsoSpec_inv_ι_assoc, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The opposite comparison orientation also preserves original coefficients,
ready for transport of the literal original affine-chart family. -/
theorem originalPositiveHomogeneousChartIso_hom_toOriginalBase001
    (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d) :
    (Proj.basicOpenIsoSpec (grading I) a ha hd).hom ≫
        Spec.map (CommRingCat.ofHom (originalPositiveHomogeneousChartBaseMap001 I a)) =
      (Proj.basicOpen (grading I) a).ι ≫ toBase I := by
  rw [← originalPositiveHomogeneousChartIso_inv_toOriginalBase001 I a d hd ha]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end PfaffianDescent
