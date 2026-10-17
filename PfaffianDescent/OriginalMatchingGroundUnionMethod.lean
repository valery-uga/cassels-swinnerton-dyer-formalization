import PfaffianDescent.OriginalMatchingActualQuadraticLineSecantData
import PfaffianDescent.ActualMatchingGroundUnionInOriginalCubic

/-! SOURCE ONLY, UNVERIFIED. Proof-valued OUTPUT of internally derived
matching method. All fields share ONE actual E/P/J extraction. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual matching union, its original ground cubic embedding, derived
quadratic line/P1/point, and Chapter2 secant. This is an OUTPUT interface. -/
def OriginalMatchingGroundUnionMethod
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) : Prop :=
  ∃ B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k),
    ∃ E : IntermediateField k (AlgebraicClosure k), ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧
      E = IntermediateField.adjoin k (Set.range (fun m => B 0 m + B 1 m)) ∧
      ∃ P : Matrix (Fin 4) (Fin 4) E,
        P.map E.val.toRingHom = QuarticNet.matchingEdgeProjectorMatrix B ∧
        ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k),
          J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
            (QuarticNet.matchingProjectorIntersectionIdeal P).toIdeal ∧
          J.toIdeal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) =
            (QuarticNet.coordinateMatchingUnionIdeal (K := AlgebraicClosure k)).toIdeal.map
              (linearSubstitution (QuarticNet.basisCoordinateMatrix B)⁻¹).toRingHom ∧
          ∃ cGround : scheme J ⟶ hypersurface F hF,
            IsClosedImmersion cGround ∧
            cGround ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap J ∧
            ∃ C : Basis (Fin 4) E (Fin 4 → E), QuarticNet.matchingEdgeProjectorMatrix C = P ∧
              ∃ e : scheme (QuarticNet.projectorLineIdeal P) ≅ Proj (homogeneousSubmodule (Fin 2) E),
                e.hom ≫ ambientToBase (R := E) (σ := Fin 2) = toBase (QuarticNet.projectorLineIdeal P) ∧
                ∃ c : scheme (QuarticNet.projectorLineIdeal P) ⟶
                    hypersurface (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)),
                  IsClosedImmersion c ∧
                  c ≫ quotientProjMap (equationIdeal (MvPolynomial.map (algebraMap k E) F)
                    (hF.map (algebraMap k E))) = quotientProjMap (QuarticNet.projectorLineIdeal P) ∧
                  ∃ q : Spec (.of E) ⟶ scheme (QuarticNet.projectorLineIdeal P),
                    q ≫ toBase (QuarticNet.projectorLineIdeal P) = 𝟙 _ ∧
                    (q ≫ c) ≫ hypersurfaceToBase (MvPolynomial.map (algebraMap k E) F)
                      (hF.map (algebraMap k E)) = 𝟙 _ ∧
                    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
                      s ≫ hypersurfaceToBase F hF = 𝟙 _

/-- Preserve the SAME original ambient embedding in the other branch. -/
def OriginalEmbeddedZeroEntryMethodGeometry
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k)) : Prop :=
  OriginalMatchingGroundUnionMethod F hF ∨ IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))

namespace QuarticNet
variable [PerfectField k]
variable {L : Type u} [Field L] [Algebra k L]

theorem originalMatchingBranch_actualGroundMethod
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k)) (p v : Fin 4 → L)
    (hs : Submodule.span (AlgebraicClosure k) (Set.range (fun sigma : L →ₐ[k] AlgebraicClosure k =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : AlgebraicClosure k) (ha : a ≠ 0) (hf : f ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi = skewTangentDirections a 0 0 0 0 f)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r, aeval (tangentDualPoint (skewTangentDirections a 0 0 0 0 f) r)
      (linearSubstitution (basisCoordinateMatrix ((conjugateBasis full p hs).reindex pi.symm))
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) F)) = 0) :
    OriginalMatchingGroundUnionMethod F hF := by
  classical
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel, hOtherKernel,
      J, hJE, hJK, hUnion, hContain, cGround, hcGround, hAmbientGround⟩ :=
    actualMatching_ground_union_in_original_cubic full p v hs l hl pi a f ha hf hU F hF hvan
  letI : FiniteDimensional k E := hFD
  letI : IsGalois k E := hGal
  obtain ⟨C, hC, e, heBase, c, hc, hAmbient, q, hq, hqCubic, s, hsPoint⟩ :=
    originalMatching_groundUnion_actualQuadraticLine_and_secant E hdeg P B hP F hF J hJE hContain
  exact ⟨B, E, hFD, hdeg, hGal, hE, P, hP, J, hJE, hUnion,
    cGround, hcGround, hAmbientGround, C, hC, e, heBase, c, hc, hAmbient, q, hq, hqCubic, s, hsPoint⟩

end QuarticNet
end PfaffianDescent
