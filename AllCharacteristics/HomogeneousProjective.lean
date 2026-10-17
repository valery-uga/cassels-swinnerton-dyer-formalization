import AllCharacteristics.HomogeneousQuotient
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Projective schemes defined by homogeneous polynomial ideals

This constructs the actual Mathlib `Proj` of a homogeneous polynomial quotient,
with its structure morphism to the coefficient ring. Finitely many variables
make the structure morphism proper over every commutative coefficient ring.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ R

/-- The homogeneous coordinate ring of the projective scheme. -/
abbrev CoordinateRing (I : HomogeneousIdeal 𝒜) := MvPolynomial σ R ⧸ I.toIdeal

/-- The grading inherited by the homogeneous coordinate ring. -/
noncomputable def grading (I : HomogeneousIdeal 𝒜) : ℕ → Submodule R (CoordinateRing I) :=
  quotientGrading 𝒜 I.toIdeal

/-- Homogeneity of the defining ideal proves the required quotient grading. -/
noncomputable instance gradedRing (I : HomogeneousIdeal 𝒜) : GradedRing (grading I) :=
  quotientGradedRing 𝒜 I.toIdeal I.isHomogeneous

/-- The degree-zero part consists of the images of constants. -/
theorem grading_zero (I : HomogeneousIdeal 𝒜) : grading I 0 = 1 := by
  change (𝒜 0).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap = 1
  rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.map_one]

/-- Every degree-zero element of the coordinate ring is the image of a base
coefficient. No assumption about a field or the characteristic is required. -/
theorem algebraMap_gradeZero_surjective (I : HomogeneousIdeal 𝒜) :
    Function.Surjective (algebraMap R (grading I 0)) := by
  intro x
  have hx : (x : CoordinateRing I) ∈ (1 : Submodule R (CoordinateRing I)) :=
    grading_zero I ▸ x.2
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx
  exact ⟨r, Subtype.ext hr⟩

/-- The scheme associated to a homogeneous ideal in a polynomial ring. -/
noncomputable def scheme (I : HomogeneousIdeal 𝒜) : Scheme.{u} := Proj (grading I)

/-- The structure morphism to the coefficient ring, through the degree-zero
part of the homogeneous coordinate ring. -/
noncomputable def toBase (I : HomogeneousIdeal 𝒜) : scheme I ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading I) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (grading I 0)))

/-- With finitely many variables, the quotient algebra is of finite type over
its degree-zero part. -/
instance finiteType_gradeZero [Finite σ] (I : HomogeneousIdeal 𝒜) :
    Algebra.FiniteType (grading I 0) (CoordinateRing I) := by
  have : IsScalarTower R (grading I 0) (CoordinateRing I) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := grading I 0)
      (A := CoordinateRing I) (fun _ ↦ rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (grading I 0) (CoordinateRing I)

/-- A homogeneous polynomial quotient in finitely many variables defines a
proper scheme over the coefficient ring. -/
instance isProper_toBase [Finite σ] (I : HomogeneousIdeal 𝒜) : IsProper (toBase I) := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (grading I 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (algebraMap_gradeZero_surjective I)
  change IsProper (Proj.toSpecZero (grading I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (grading I 0))))
  infer_instance

/-- A homogeneous polynomial generates a homogeneous ideal. -/
noncomputable def equationIdeal (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span {p}, Ideal.homogeneous_span 𝒜 {p} (by
    intro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact ⟨d, hp⟩)⟩

/-- The projective hypersurface cut out by a homogeneous equation. -/
noncomputable def hypersurface (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    Scheme.{u} := scheme (equationIdeal p hp)

/-- The structure morphism of the projective hypersurface. -/
noncomputable def hypersurfaceToBase (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) : hypersurface p hp ⟶ Spec (.of R) :=
  toBase (equationIdeal p hp)

/-- Projective hypersurfaces in finitely many variables are proper over their
coefficient ring, with no characteristic hypothesis. -/
instance isProper_hypersurfaceToBase [Finite σ] (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) : IsProper (hypersurfaceToBase p hp) :=
  isProper_toBase (equationIdeal p hp)

end HomogeneousProjective
end AllCharacteristics
