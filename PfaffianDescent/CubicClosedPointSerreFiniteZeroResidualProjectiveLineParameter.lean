import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineParameter
import PfaffianDescent.LineGrassmannianProjIso
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Native polynomial parameters on the actual projective-line charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

instance cubicClosedPointSerreFiniteZeroResidual_projectiveLine_chart_principal
    (K : Type u) [Field K] (b : Bool) :
    IsPrincipalIdealRing (ChartRing
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b) := by
  letI : Unique (Fin 1 × Fin 1) :=
    { default := (0, 0), uniq := fun _ => Subsingleton.elim _ _ }
  let e := (MvPolynomial.uniqueAlgEquiv K (Fin 1 × Fin 1)).symm.toRingEquiv.trans
    (lineGrassmannianProjChartRingEquiv K b)
  exact IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective

instance cubicClosedPointSerreFiniteZeroResidual_projectiveLine_chart_sections_principal
    (K : Type u) [Field K] (b : (lineProjOpenCover K).I₀) :
    IsPrincipalIdealRing Γ((lineProjOpenCover K).X b, ⊤) := by
  change IsPrincipalIdealRing Γ(Spec (.of (ChartRing
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b)), ⊤)
  letI : IsPrincipalIdealRing (CommRingCat.of (ChartRing
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b)) :=
    cubicClosedPointSerreFiniteZeroResidual_projectiveLine_chart_principal K b
  let e := (Scheme.ΓSpecIso (.of (ChartRing
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b))).commRingCatIsoToRingEquiv
  exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_chart_parameter
    (K : Type u) [Field K] (b : (lineProjOpenCover K).I₀)
    (x : (lineProjOpenCover K).X b) :
    ∃ t : Γ((lineProjOpenCover K).X b, ⊤),
      ((isAffineOpen_top ((lineProjOpenCover K).X b)).primeIdealOf ⟨x, by trivial⟩).asIdeal =
        Ideal.span {t} ∧
      IsLocalRing.maximalIdeal (((lineProjOpenCover K).X b).presheaf.stalk x) =
        Ideal.span ({((lineProjOpenCover K).X b).presheaf.germ ⊤ x (by trivial) t} :
          Set (((lineProjOpenCover K).X b).presheaf.stalk x)) :=
  cubicClosedPointSerreFiniteZeroResidual_affine_parameter_of_principalIdealRing
    ((lineProjOpenCover K).X b) ⟨⊤, isAffineOpen_top _⟩ x (by trivial)

end PfaffianDescent
