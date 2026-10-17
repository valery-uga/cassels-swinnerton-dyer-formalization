import PfaffianDescent.CubicClosedPointSerreQuotientSectionTarget
import PfaffianDescent.AffineFreeModuleBaseChange
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! # Native linear section spaces of the cubic point quotient -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- An actual module-sheaf isomorphism induces a ground-field linear
equivalence on morphism-valued global sections. -/
def cubicClosedPointSerreQuotientSection_globalSectionsIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) {M N : X.Modules} (e : M ≅ N) :
    SchemeModuleGlobalSectionsOver base M ≃ₗ[K]
      SchemeModuleGlobalSectionsOver base N where
  toFun s := s ≫ e.hom
  invFun t := t ≫ e.inv
  left_inv s := by
    dsimp only [SchemeModuleGlobalSectionsOver] at s ⊢
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv t := by
    dsimp only [SchemeModuleGlobalSectionsOver] at t ⊢
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  map_add' s t := Preadditive.add_comp _ _ _ s t e.hom
  map_smul' c s := Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The literal pushforward of a field point has its coefficient field as
its global-section space, with the scalar structure supplied by the actual
map to the base. -/
def cubicClosedPointSerreQuotientSection_pointGlobalSectionsEquiv
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K))
    {L : Type u} [Field L] [Algebra K L]
    (i : Spec (.of L) ⟶ X)
    (hi : i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    SchemeModuleGlobalSectionsOver base
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) ≃ₗ[K] L := by
  let N := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  let e : SchemeModuleOpenSectionsOver base N ⊤ ≃ₗ[K] L :=
    { __ := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
      map_smul' c s := by
        change (Scheme.ΓSpecIso (.of L)).hom.hom
            (i.appTop.hom (schemeOpenBaseRingHom base ⊤ c) *
              (show Γ(Spec (.of L), ⊤) from s)) =
          c • (Scheme.ΓSpecIso (.of L)).hom.hom s
        rw [map_mul, schemeOpenBaseRingHom_top_apply]
        have hc : (Scheme.ΓSpecIso (.of L)).hom.hom
            (i.appTop.hom (affineFunctionHom base c)) = algebraMap K L c := by
          have hcomp := congrArg (fun f : K →+* Γ(Spec (.of L), ⊤) => f c)
            (affineFunctionHom_comp i base)
          dsimp only [RingHom.comp_apply] at hcomp
          rw [← hcomp, hi]
          exact gammaSpec_baseRingHom_apply c
        rw [hc]
        exact (Algebra.smul_def c ((Scheme.ΓSpecIso (.of L)).hom.hom s)).symm }
  exact (schemeModuleGlobalSectionsLinearEquivOpenTop base N).trans e

namespace ProjectiveNegativeTwist
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Global sections of the original positive-three quotient sheaf at an
actual field point are linearly equivalent to its coefficient field. -/
def cubicClosedPointSerreQuotientSection_targetGlobalSectionsEquiv
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L] [Algebra K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ toBase (equationIdeal p hp) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    SchemeModuleGlobalSectionsOver (toBase (equationIdeal p hp))
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₃ ≃ₗ[K] L :=
  (cubicClosedPointSerreQuotientSection_globalSectionsIso
    (toBase (equationIdeal p hp))
    (cubicClosedPointSerreQuotientSection_targetIso K p hp i)).trans
      (cubicClosedPointSerreQuotientSection_pointGlobalSectionsEquiv
        (toBase (equationIdeal p hp)) i hi)

end ProjectiveNegativeTwist
end PfaffianDescent
