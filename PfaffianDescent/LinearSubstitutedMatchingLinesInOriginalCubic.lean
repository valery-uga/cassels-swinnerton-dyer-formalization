import PfaffianDescent.MatchingCoordinateLineSchemes
import PfaffianDescent.ProjectiveLinearCoordinateAmbientSquare

/-! SOURCE ONLY, UNVERIFIED. Transport BOTH matching line immersions back
to the original cubic through the actual coordinate automorphism. Every
line ambient square is retained; no point-existence theorem substitutes for
line containment. The restriction equalities are an internal derived interface. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem linearSubstituted_matching_lines_in_original_cubic
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (h01 : coordinateLineRestriction (linearSubstitution M F) = 0)
    (h23 : coordinateLineRestriction23 (linearSubstitution M F) = 0) :
    ∃ l : ∀ side : Bool, scheme (coordinateMatchingLineIdeal (K := K) side) ⟶ hypersurface F hF,
      (∀ side, IsClosedImmersion (l side)) ∧
      (∀ side, l side ≫ quotientProjMap (equationIdeal F hF) =
        quotientProjMap (coordinateMatchingLineIdeal side) ≫
          (linearCoordinateChangeAmbientIso M hM).inv) := by
  let G := linearSubstitution M F
  let hG := linearSubstitution_homogeneous M hF
  let I := equationIdeal F hF
  let J := equationIdeal G hG
  have hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom := by
    change Ideal.span ({G} : Set (MvPolynomial (Fin 4) K)) =
      (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).map
        (linearSubstitutionEquiv M hM).toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let e := linearCoordinateChangeSchemeIso M hM I J hIJ
  let alpha := linearCoordinateChangeAmbientIso M hM
  have hAmbient : e.hom ≫ quotientProjMap J = quotientProjMap I ≫ alpha.hom :=
    linearCoordinateChangeSchemeIso_hom_toAmbient M hM I J hIJ
  have hInv : e.inv ≫ quotientProjMap I = quotientProjMap J ≫ alpha.inv := by
    apply (cancel_mono alpha.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hAmbient, Iso.inv_hom_id_assoc]
  have hline (side : Bool) : coordinateMatchingLineRestriction side G = 0 := by
    cases side
    · exact h01
    · exact h23
  let l := fun side => coordinateMatchingLineToCubic side G hG (hline side) ≫ e.inv
  refine ⟨l, ?_, ?_⟩
  · intro side
    dsimp only [l]
    infer_instance
  · intro side
    change (coordinateMatchingLineToCubic side G hG (hline side) ≫ e.inv) ≫
      quotientProjMap I = quotientProjMap (coordinateMatchingLineIdeal side) ≫ alpha.inv
    rw [Category.assoc, hInv, ← Category.assoc,
      coordinateMatchingLineToCubic_toAmbient]

end PfaffianDescent.QuarticNet
