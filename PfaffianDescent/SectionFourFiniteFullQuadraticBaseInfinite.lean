import PfaffianDescent.FiniteProjectiveFullQuadraticKernel

/-! The existence-of-point proposition from a finite FULL quadratic base
locus, over an infinite field.  The finite triple and its containment are
derived internally from the actual finite subscheme.  Arbitrary-field
descent remains a separate interface, not an extra premise of this theorem. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionFour_section_of_cubic_of_finite_full_quadratic_base_infinite
    {K : Type u} [Field K] [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (j : Z ⟶ hypersurface F hF) [IsClosedImmersion j]
    [IsFinite (j ≫ hypersurfaceToBase F hF)]
    (hZ : AllCharacteristics.finiteSchemeRank (j ≫ hypersurfaceToBase F hF) = 8)
    [IsFinite (toBase (finiteProjectiveFullQuadraticBaseIdeal (equationIdeal F hF) j))] :
    ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  let I := equationIdeal F hF
  letI : IsAffine Z := isAffine_of_isAffineHom (j ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (j ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (j ≫ toBase I)
  let c := finiteProjectiveQuadraticCoordinates I j
  obtain ⟨q, hfinite, l, hl, hambient, hbase⟩ :=
    finiteProjectiveFullQuadraticKernel_exists_triple_iso I j hZ
  letI := hfinite
  letI := hl
  let hf := normalizedQuadraticSystem_homogeneous c.x _ (q 0).property
  let hg := normalizedQuadraticSystem_homogeneous c.x _ (q 1).property
  let hh := normalizedQuadraticSystem_homogeneous c.x _ (q 2).property
  let v := tripleCompleteIntersectionToHypersurface
    (q 0).val (q 1).val (q 2).val hf hg hh
  let i := l ≫ v
  have hbasei : i ≫ hypersurfaceToBase (q 0).val hf = j ≫ hypersurfaceToBase F hF := by
    change (l ≫ v) ≫ hypersurfaceToBase (q 0).val hf = _
    rw [Category.assoc, tripleCompleteIntersectionToHypersurface_toBase]
    exact hbase
  letI : IsClosedImmersion i := inferInstance
  letI : IsFinite (i ≫ hypersurfaceToBase (q 0).val hf) := by
    rw [hbasei]
    infer_instance
  have hZi : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase (q 0).val hf) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbasei,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hZ
  apply AllCharacteristics.sectionFour_section_of_cubic_of_finite_nonempty_net
    F (q 0).val (q 1).val (q 2).val hF hf hg hh i (l.le_ker_comp v) hZi j
  change j ≫ quotientProjMap I = (l ≫ v) ≫ hypersurfaceToAmbient (q 0).val hf
  rw [Category.assoc, tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
  exact hambient.symm

end PfaffianDescent
