import PfaffianDescent.QuarticTwistedCubicGeometricPresentation
import PfaffianDescent.QuarticTwistedCubicPoint
import PfaffianDescent.ProjectiveLinearCoordinateRank
import PfaffianDescent.HomogeneousQuotientMap
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! Source-only, UNVERIFIED.  Intersect the SAME ground embedded twisted
cubic with a cubic equation.  The transformed equation, non-containment,
finiteness and rank are derived from the actual ground presentation. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The scheme-theoretic intersection in the original coordinates. -/
def groundTwistedCubicCubicIntersectionIdeal
    (B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) :=
  B ⊔ equationIdeal F hF

/-- Kernel membership of the actual transformed cubic detects containment;
there is no separately supplied equation comparison. -/
theorem twisted_cubic_mem_iff_transformed_param_zero
    (B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (M : GL (Fin 4) k)
    (hB : B.toIdeal.map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k)).toRingHom =
        standardTwistedCubicIdeal k)
    (F : MvPolynomial (Fin 4) k) :
    F ∈ B.toIdeal ↔ standardTwistedCubicParam k
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F) = 0 := by
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) k).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  let E := linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet
  have hBE : B.toIdeal.map E.toRingHom = standardTwistedCubicIdeal k := hB
  constructor
  · intro hF
    have h := Ideal.mem_map_of_mem E.toRingHom hF
    rw [hBE, standardTwistedCubicIdeal_eq_ker] at h
    exact h
  · intro hF
    have h : E F ∈ B.toIdeal.map E.toRingHom := by
      rw [hBE, standardTwistedCubicIdeal_eq_ker]
      exact hF
    obtain ⟨p, hp, hpF⟩ :=
      (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp h
    have hpEq : p = F := E.injective hpF
    simpa only [hpEq] using hp

/-- Transport the whole summed ideal, preserving nilpotents and the original
cubic, rather than transporting its support. -/
theorem groundTwistedCubicCubicIntersectionIdeal_coordinate_map
    (B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (M : GL (Fin 4) k)
    (hB : B.toIdeal.map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k)).toRingHom =
        standardTwistedCubicIdeal k)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) k).det)) :
    (standardTwistedCubicCubicIntersectionIdeal
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F)
      (linearSubstitution_homogeneous _ hF)).toIdeal =
      (groundTwistedCubicCubicIntersectionIdeal B F hF).toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingHom := by
  change (standardTwistedCubicHomogeneousIdeal ⊔ equationIdeal
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F)
      (linearSubstitution_homogeneous _ hF)).toIdeal =
    (B ⊔ equationIdeal F hF).toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingHom
  rw [HomogeneousIdeal.toIdeal_sup, HomogeneousIdeal.toIdeal_sup, Ideal.map_sup]
  have hBE : B.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingHom =
        standardTwistedCubicIdeal k := hB
  rw [hBE]
  change standardTwistedCubicIdeal k ⊔
      Ideal.span {linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F} =
    standardTwistedCubicIdeal k ⊔ (Ideal.span {F}).map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingHom
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- A non-contained cubic cuts the actual ground twisted cubic in a finite
scheme of rank nine.  Both conclusions come from the transformed polynomial. -/
theorem GroundTwistedCubicPresentation.cubicIntersection_finite_rank_nine
    [Infinite k]
    {B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k)}
    (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnot : F ∉ B.toIdeal) :
    ∃ hfinite : IsFinite (toBase (groundTwistedCubicCubicIntersectionIdeal B F hF)),
      @AllCharacteristics.finiteSchemeRank k _ _
        (toBase (groundTwistedCubicCubicIntersectionIdeal B F hF)) hfinite = 9 := by
  obtain ⟨M, hM⟩ := hB
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) k).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hnonzero : standardTwistedCubicParam k
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F) ≠ 0 := by
    intro hz
    exact hnot ((twisted_cubic_mem_iff_transformed_param_zero B M hM F).mpr hz)
  exact projective_finiteSchemeRank_of_linearCoordinateChange_eventual_hilbert
    (M : Matrix (Fin 4) (Fin 4) k) hdet
    (groundTwistedCubicCubicIntersectionIdeal B F hF)
    (standardTwistedCubicCubicIntersectionIdeal
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k) F)
      (linearSubstitution_homogeneous _ hF))
    (groundTwistedCubicCubicIntersectionIdeal_coordinate_map B M hM F hF hdet)
    3 9 (fun d hd => standardTwistedCubicCubicIntersection_grade_finrank
      _ _ hnonzero d hd)

/-- In the contained branch the actual embedded curve maps to the ORIGINAL
cubic, with both ambient and structural morphisms retained. -/
theorem GroundTwistedCubicPresentation.contained_cubic_section
    {B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k)}
    (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hmem : F ∈ B.toIdeal) :
    ∃ c : scheme B ⟶ hypersurface F hF,
      c ≫ hypersurfaceToAmbient F hF = quotientProjMap B ∧
      c ≫ hypersurfaceToBase F hF = toBase B ∧
      ∃ s : Spec (.of k) ⟶ hypersurface F hF,
        s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  have hFB : (equationIdeal F hF).toIdeal ≤ B.toIdeal := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact hmem
  let c : scheme B ⟶ hypersurface F hF :=
    schemeQuotientMap (equationIdeal F hF) B hFB
  have hc : c ≫ hypersurfaceToBase F hF = toBase B :=
    schemeQuotientMap_toBase _ _ _
  obtain ⟨M, hM⟩ := hB
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) k).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  obtain ⟨s, hs⟩ := splitTwistedCubic_has_rational_section B
    (M : Matrix (Fin 4) (Fin 4) k) hdet hM
  exact ⟨c, schemeQuotientMap_comp_quotientProjMap _ _ _, hc,
    s ≫ c, by rw [Category.assoc, hc, hs]⟩

end PfaffianDescent.QuarticNet
