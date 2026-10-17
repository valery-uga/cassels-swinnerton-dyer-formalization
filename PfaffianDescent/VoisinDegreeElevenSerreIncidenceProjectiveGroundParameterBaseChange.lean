import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectiveGroundOpen
import AllCharacteristics.ProjectiveBaseChange

/-! # The selected geometric parameter is literally the base change of a ground parameter -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceProjectiveGroundParameter_baseChange
    {K E : Type u} [Field K] [Field E] [Algebra K E] {σ : Type}
    (qK : Spec (.of K) ⟶ scheme (⊥ : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule σ K)))
    (qE : Spec (.of E) ⟶ scheme (⊥ : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule σ E)))
    (hK : qK ≫ toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) = 𝟙 _)
    (hE : qE ≫ toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) = 𝟙 _)
    (h : qE ≫ projectiveCoefficientMap (algebraMap K E)
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) (by simp) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ qK) :
    qE ≫ (projectiveBaseChangeIso (algebraMap K E)
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) (by simp)).hom =
    pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ qK) (𝟙 _)
      (by simp only [Category.assoc, hK, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, projectiveBaseChangeIso_hom_fst, pullback.lift_fst]
    exact h
  · simp only [Category.assoc, projectiveBaseChangeIso_hom_snd, pullback.lift_snd]
    exact hE

end PfaffianDescent
