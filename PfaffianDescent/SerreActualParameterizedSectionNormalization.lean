import PfaffianDescent.SerreActualParameterizedBasisComparison

/-! Normalized coefficient changes are actual scalar changes of the whole
parameterized section, including arbitrary regular coefficient functions. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v w
set_option backward.isDefEq.respectTransparency false

theorem serreActualParameterizedSection_commonRegularScale
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι] (f : T ⟶ X) (coeff : ι → Γ(T, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) (a : Γ(T, ⊤)) :
    parameterizedSchemeModuleSection base M f (fun i => a * coeff i) s =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (parameterizedSchemeModuleSection base M f coeff s) := by
  unfold parameterizedSchemeModuleSection
  rw [finiteLinearCombinationSections_commonScale]
  congr 1
  funext i
  exact unitEndomorphismOfRegularFunction_mul a (coeff i)

theorem serreActualParameterizedBasis_normalized
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (b : Basis κ K (SchemeModuleGlobalSectionsOver base M))
    (c : Basis ι K (SchemeModuleGlobalSectionsOver base M))
    (f : T ⟶ X) (coeff : κ → Γ(T, ⊤)) (a : Γ(T, ⊤)) :
    parameterizedSchemeModuleSection base M f
        (fun i => a * (((c.toMatrix b).map
          (affineFunctionHom (f ≫ base))).mulVec coeff) i) c =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (parameterizedSchemeModuleSection base M f coeff b) := by
  rw [serreActualParameterizedSection_commonRegularScale,
    ← serreActualParameterizedSection_basis_change base M b c f coeff]

end PfaffianDescent
