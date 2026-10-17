import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationMap

/-! # Actual global section comparison for an affine spectrum presentation -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Pullback along an actual scheme isomorphism is an equivalence of the
actual module-sheaf categories, using the actual pullback composition maps. -/
def cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoEquivalence
    {X Z : Scheme.{u}} (e : Z ≅ X) : X.Modules ≌ Z.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId X).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId Z)

/-- Literal geometric pullback is a bijection on actual global sections
for an actual scheme isomorphism. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationSchemeIso_bijective
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (e : Z ≅ X) (E : X.Modules) :
    Function.Bijective (cubicClosedPointSerreDegreeThreeEvaluationMap base e.hom E) := by
  let P := Scheme.Modules.pullback e.hom
  let q := cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoEquivalence e
  letI : P.IsEquivalence := by
    change q.functor.IsEquivalence
    infer_instance
  letI : IsIso (pullbackUnitComparison e.hom) := isIso_pullbackUnitComparison e.hom
  let u := asIso (pullbackUnitComparison e.hom)
  refine ⟨?_, ?_⟩
  · intro s t h
    apply P.map_injective
    exact (cancel_epi u.inv).mp h
  · intro t
    obtain ⟨s, hs⟩ := P.map_surjective (u.hom ≫ t)
    refine ⟨s, ?_⟩
    change u.inv ≫ P.map s = t
    rw [hs]
    exact u.inv_hom_id_assoc t

/-- The actual geometric spectrum presentation gives a ground-field
linear equivalence on the actual pulled-back global sections. -/
def cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoLinearEquiv
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (e : Z ≅ X) (E : X.Modules) :
    SchemeModuleGlobalSectionsOver base E ≃ₗ[K]
      SchemeModuleGlobalSectionsOver (e.hom ≫ base)
        ((Scheme.Modules.pullback e.hom).obj E) :=
  LinearEquiv.ofBijective (cubicClosedPointSerreDegreeThreeEvaluationMap base e.hom E)
    (cubicClosedPointSerreDegreeThreeEvaluationSchemeIso_bijective base e E)

/-- An actual module-sheaf isomorphism induces the actual linear
isomorphism of global sections by postcomposition. -/
def cubicClosedPointSerreDegreeThreeEvaluationModuleIsoLinearEquiv
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) {M N : X.Modules} (e : M ≅ N) :
    SchemeModuleGlobalSectionsOver base M ≃ₗ[K] SchemeModuleGlobalSectionsOver base N := by
  refine LinearEquiv.ofLinear (schemeModuleGlobalSectionsMap base e.hom)
    (schemeModuleGlobalSectionsMap base e.inv) ?_ ?_
  · ext s
    exact (Category.assoc s e.inv e.hom).trans
      ((congrArg (fun f => s ≫ f) e.inv_hom_id).trans (Category.comp_id s))
  · ext s
    exact (Category.assoc s e.hom e.inv).trans
      ((congrArg (fun f => s ≫ f) e.hom_inv_id).trans (Category.comp_id s))

end PfaffianDescent
