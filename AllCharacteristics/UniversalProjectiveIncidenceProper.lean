import AllCharacteristics.UniversalProjectiveAmbient
import AllCharacteristics.UniversalProjectiveFamilyCharts
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Properness of the universal projective incidence morphism

The global universal hypersurface is a proper family over the projective
space of equations.  Its map to the product of the fixed ambient projective
space and the parameter space is therefore proper as well: the target
projection to parameters is separated.  In particular, the universal
vanishing incidence has closed image.  This is the topological input needed
when forming closed bad loci for generic-section arguments.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AllCharacteristics
namespace UniversalHomogeneous

open HomogeneousProjective

universe u

variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The global universal incidence morphism is proper. -/
instance isProper_projectiveUniversalIncidence :
    IsProper (projectiveUniversalIncidence R σ d) := by
  let g :
      Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯ projectiveParameters R σ d ⟶
        projectiveParameters R σ d := prod.snd
  letI : IsSeparated g := by
    dsimp only [g]
    rw [← prodIsoPullback_hom_snd]
    infer_instance
  letI : IsProper (projectiveUniversalIncidence R σ d ≫ g) := by
    change IsProper (projectiveUniversalIncidence R σ d ≫ prod.snd)
    rw [projectiveUniversalIncidence_snd]
    infer_instance
  exact IsProper.of_comp (projectiveUniversalIncidence R σ d) g

/-- The image of the universal projective incidence morphism is closed in
the ambient-projective-space times equation-parameter space. -/
theorem isClosed_range_projectiveUniversalIncidence :
    IsClosed (Set.range (projectiveUniversalIncidence R σ d)) := by
  simpa only [Set.image_univ] using
    (projectiveUniversalIncidence R σ d).isClosedMap Set.univ isClosed_univ

/-- The universal hypersurface incidence pulled back along an arbitrary
parameter map to ambient projective space times equation space.  It is the
scheme-theoretic parameter space of pairs for which the chosen universal
equation vanishes at the chosen ambient point. -/
noncomputable def projectiveUniversalIncidenceBaseChange
    {B : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d) : Scheme.{u} :=
  pullback b (projectiveUniversalIncidence R σ d)

/-- The induced morphism from the universal vanishing locus to its parameter
scheme. -/
noncomputable def projectiveUniversalIncidenceBaseChangeToBase
    {B : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d) :
    projectiveUniversalIncidenceBaseChange R σ d b ⟶ B :=
  pullback.fst b (projectiveUniversalIncidence R σ d)

/-- On underlying points, the pulled-back universal vanishing locus is
exactly the inverse image of the universal incidence locus. -/
theorem range_projectiveUniversalIncidenceBaseChangeToBase
    {B : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d) :
    Set.range (projectiveUniversalIncidenceBaseChangeToBase R σ d b) =
      b ⁻¹' Set.range (projectiveUniversalIncidence R σ d) := by
  change Set.range (pullback.fst b (projectiveUniversalIncidence R σ d)) = _
  exact AlgebraicGeometry.Scheme.Pullback.range_fst b
    (projectiveUniversalIncidence R σ d)

/-- Universal vanishing loci remain proper after any change of parameters. -/
instance isProper_projectiveUniversalIncidenceBaseChangeToBase
    {B : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d) :
    IsProper (projectiveUniversalIncidenceBaseChangeToBase R σ d b) := by
  change IsProper (pullback.fst b (projectiveUniversalIncidence R σ d))
  infer_instance

/-- The parameters admitting a point on the pulled-back universal vanishing
locus form a closed subset. -/
theorem isClosed_range_projectiveUniversalIncidenceBaseChangeToBase
    {B : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d) :
    IsClosed (Set.range (projectiveUniversalIncidenceBaseChangeToBase R σ d b)) := by
  simpa only [Set.image_univ] using
    (projectiveUniversalIncidenceBaseChangeToBase R σ d b).isClosedMap Set.univ isClosed_univ

/-- The universal vanishing locus, after a change of parameters, followed by
any further parameter map. -/
noncomputable def projectiveUniversalIncidenceBaseChangeToTarget
    {B C : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (π : B ⟶ C) :
    projectiveUniversalIncidenceBaseChange R σ d b ⟶ C :=
  projectiveUniversalIncidenceBaseChangeToBase R σ d b ≫ π

/-- The image after a further parameter map is the image of the inverse
image of the universal incidence locus. -/
theorem range_projectiveUniversalIncidenceBaseChangeToTarget
    {B C : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (π : B ⟶ C) :
    Set.range (projectiveUniversalIncidenceBaseChangeToTarget R σ d b π) =
      π '' (b ⁻¹' Set.range (projectiveUniversalIncidence R σ d)) := by
  change Set.range (pullback.fst b (projectiveUniversalIncidence R σ d) ≫ π) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    AlgebraicGeometry.Scheme.Pullback.range_fst]

/-- A universal vanishing locus has proper image after any proper projection
of its parameter space. -/
instance isProper_projectiveUniversalIncidenceBaseChangeToTarget
    {B C : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (π : B ⟶ C) [IsProper π] :
    IsProper (projectiveUniversalIncidenceBaseChangeToTarget R σ d b π) := by
  change IsProper (pullback.fst b (projectiveUniversalIncidence R σ d) ≫ π)
  infer_instance

/-- The parameter values admitting a point on a pulled-back universal
vanishing locus form a closed subset after any proper projection. -/
theorem isClosed_range_projectiveUniversalIncidenceBaseChangeToTarget
    {B C : Scheme.{u}}
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (π : B ⟶ C) [IsProper π] :
    IsClosed (Set.range
      (projectiveUniversalIncidenceBaseChangeToTarget R σ d b π)) := by
  simpa only [Set.image_univ] using
    (projectiveUniversalIncidenceBaseChangeToTarget R σ d b π).isClosedMap
      Set.univ isClosed_univ

end UniversalHomogeneous
end AllCharacteristics
