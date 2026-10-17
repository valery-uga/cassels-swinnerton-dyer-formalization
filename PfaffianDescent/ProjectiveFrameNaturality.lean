import PfaffianDescent.ProjectiveFrameCoordinateMap

/-!
# Coefficient naturality of projective frame changes

The polynomial substitution identity descends to graded homogeneous
coordinate rings and then to actual scheme morphisms via `Proj.map_comp`.
These identities allow the coefficient changes in Grassmannian overlap
maps to commute past their frame changes when proving gluing cocycles.
-/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {m : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

private lemma frameCoefficient_mk (f : R →+* S)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin m) R))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin m) S))
    (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
    (p : MvPolynomial (Fin m) R) :
    gradedCoefficientMap f I J h (Ideal.Quotient.mk I.toIdeal p) =
      Ideal.Quotient.mk J.toIdeal (MvPolynomial.map f p) :=
  coordinateCoefficientMap_mk f I J h p

/-- Frame substitution commutes with coefficient extension on graded quotients. -/
theorem projectiveFrameGradedMap_naturality (f : R →+* S)
    (M : Matrix (Fin m) (Fin m) R) :
    (gradedCoefficientMap f
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) R))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) S)) (by simp)).comp
      (polynomialQuotientGradingMap ⊥ ⊥ (rectangularSubstitution M) bot_le
        (fun _ _ hp => rectangularSubstitution_homogeneous M hp)) =
    (polynomialQuotientGradingMap ⊥ ⊥ (rectangularSubstitution (M.map f)) bot_le
      (fun _ _ hp => rectangularSubstitution_homogeneous (M.map f) hp)).comp
      (gradedCoefficientMap f
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) R))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) S)) (by simp)) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [GradedRingHom.comp_apply, polynomialQuotientGradingMap_mk, frameCoefficient_mk]
  exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun
    (rectangularSubstitution_map_comm f M) p)

/-- Projective frame-coordinate changes commute with every coefficient map. -/
theorem projectiveFrameCoordinateMap_naturality (f : R →+* S)
    (M N : Matrix (Fin m) (Fin m) R) (hNM : N * M = 1)
    (hNM' : N.map f * M.map f = 1) :
    projectiveFrameCoordinateCoefficientMap f ≫ projectiveFrameCoordinateMap M N hNM =
      projectiveFrameCoordinateMap (M.map f) (N.map f) hNM' ≫
        projectiveFrameCoordinateCoefficientMap f := by
  unfold projectiveFrameCoordinateCoefficientMap projectiveCoefficientMap
    projectiveFrameCoordinateMap polynomialProjectiveMap
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  apply projMap_congr
  exact projectiveFrameGradedMap_naturality f M

/-- Successive projective coordinate changes are given by the product matrix. -/
theorem projectiveFrameCoordinateMap_mul
    (A A' B B' : Matrix (Fin m) (Fin m) R)
    (hA : A' * A = 1) (hB : B' * B = 1)
    (hAB : (A' * B') * (B * A) = 1) :
    projectiveFrameCoordinateMap A A' hA ≫ projectiveFrameCoordinateMap B B' hB =
      projectiveFrameCoordinateMap (B * A) (A' * B') hAB := by
  unfold projectiveFrameCoordinateMap polynomialProjectiveMap
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  apply projMap_congr
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [GradedRingHom.comp_apply, polynomialQuotientGradingMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun
    (rectangularSubstitution_comp A B) p)

/-- The projective coordinate map attached to the identity matrix is the
identity scheme morphism. -/
theorem projectiveFrameCoordinateMap_one :
    projectiveFrameCoordinateMap
      (1 : Matrix (Fin m) (Fin m) R) 1 (mul_one 1) = 𝟙 _ := by
  let I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R) := ⊥
  let F := polynomialQuotientGradingMap I I
    (rectangularSubstitution (1 : Matrix (Fin m) (Fin m) R)) bot_le
    (fun _d _p hp => rectangularSubstitution_homogeneous 1 hp)
  let hF := gradedSurjective_irrelevant_le F
    (polynomialQuotientGradingMap_surjective I I (rectangularSubstitution 1) bot_le
      (fun _d _p hp => rectangularSubstitution_homogeneous 1 hp)
      (rectangularSubstitution_surjective 1 1 (mul_one 1)))
  have hFid : F = GradedRingHom.id (grading I) := by
    apply GradedRingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [F, polynomialQuotientGradingMap_mk, GradedRingHom.id_apply]
    exact congrArg (Ideal.Quotient.mk I.toIdeal)
      (AlgHom.congr_fun rectangularSubstitution_one p)
  change Proj.map F hF = 𝟙 _
  exact (projMap_congr I I F (GradedRingHom.id (grading I)) hF _ hFid).trans Proj.map_id

/-- Three frames for the same system satisfy the projective transition
cocycle, as an equality of scheme morphisms. -/
theorem projectiveFrameProjectiveTransition_cocycle
    {V : Type*} [AddCommGroup V] [Module R V]
    (q r s : Fin m → V) (rq rr rs : V →ₗ[R] (Fin m → R))
    (hq : rq.comp (projectiveFrameMap q) = LinearMap.id)
    (hr : rr.comp (projectiveFrameMap r) = LinearMap.id)
    (hs : rs.comp (projectiveFrameMap s) = LinearMap.id)
    (hqr : Submodule.span R (Set.range q) = Submodule.span R (Set.range r))
    (hrs : Submodule.span R (Set.range r) = Submodule.span R (Set.range s)) :
    projectiveFrameProjectiveTransition q r rq rr hq hr hqr ≫
      projectiveFrameProjectiveTransition r s rr rs hr hs hrs =
        projectiveFrameProjectiveTransition q s rq rs hq hs (hqr.trans hrs) := by
  unfold projectiveFrameProjectiveTransition projectiveFrameCoordinateMap polynomialProjectiveMap
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  apply projMap_congr
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [GradedRingHom.comp_apply, polynomialQuotientGradingMap_mk]
  rw [← AlgHom.comp_apply, rectangularSubstitution_comp,
    ← LinearMap.toMatrix'_comp, projectiveFrameTransition_cocycle q r s rr rs hr hqr.le]

end PfaffianDescent
