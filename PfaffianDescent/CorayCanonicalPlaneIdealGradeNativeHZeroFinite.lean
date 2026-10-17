import PfaffianDescent.CorayCanonicalPlaneWholeCutEuler
import PfaffianDescent.CorayOriginalWholePlaneIdealNativeHZeroInjection

/-! Genuine canonical HF9 join eliminating the native H0 finiteness premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem selectedOriginalWholeCurve_canonicalPlane_idealGrade_le_nativeHZero_withoutFinitePremise001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let F := GenericHyperplaneField K
      let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
      let pi := toBase E
      let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
      ∀ d : ℕ, 1 ≤ d →
        let S := PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading E) d)
        Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
          Module.finrank F (wholeIdealGrade (grading E)
            (wholeOriginalPlaneCutCoordinateIdeal C p hp) d) ≤
          Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := by
  obtain ⟨hpC, hData⟩ := selectedOriginalWholeCurve_canonicalPlane_firstIdeal_finite_euler001
    p q hp hp0 n hq hnot C hCmin
  let F := GenericHyperplaneField K
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let pi := toBase E
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d hd
  let S := PfaffianDescent.closedImmersionIdealTwistSequence i
    (positiveSheafOfModules (grading E) d)
  have hFinite : Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := (hData d hd).1
  letI : Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := hFinite
  exact ⟨hFinite, @originalWholePlaneIdealGrade_finrank_le_nativeHZero.{u}
    K inferInstance p hp hp0 inferInstance C hpC d hFinite⟩

end PfaffianDescent.Coray
