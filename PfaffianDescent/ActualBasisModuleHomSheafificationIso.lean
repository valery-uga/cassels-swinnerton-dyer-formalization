import PfaffianDescent.ModulePresheafHomFromActualBasis
import PfaffianDescent.BasiswiseBijectiveModuleSheafification

/- SOURCE ONLY / UNVERIFIED. Small generic gluing consumer. The eventual
actual affine caller derives its local maps, linearity and bijectivity from
coefficient localization. These are auxiliary inputs here, not final
geometry or genuine differential comparison certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {X : Scheme.{u}} {ι : Type u}

private instance actualBasisConsumerSectionModule (N : X.Modules) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (N.presheaf.obj U) :=
  (N.val.obj U).isModule

/-- The module-linear extension retains its exact given map on each basis
open; this comes from the actual sheaf extension equivalence. -/
lemma modulePresheafHomFromActualBasis_on_basis
    (P : X.PresheafOfModules) (N : X.Modules)
    (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (a : (inducedFunctor B).op ⋙ P.presheaf ⟶
      (inducedFunctor B).op ⋙ N.presheaf)
    (ha : ∀ (i : ι) (r : X.ringCatSheaf.obj.obj (op (B i)))
      (x : P.obj (op (B i))),
      (a.app (op i) (r • x) : N.val.obj (op (B i))) =
        r • (a.app (op i) x : N.val.obj (op (B i))))
    (i : ι) (x : P.obj (op (B i))) :
    (modulePresheafHomFromActualBasis P N B hB a ha).app (op (B i)) x =
      a.app (op i) x := by
  let Ns : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  exact ConcreteCategory.congr_hom
    (TopCat.Sheaf.extend_hom_app P.presheaf Ns hB a i) x

/-- The genuine module sheafification of the glued comparison is an Iso
when its internally chosen basis components are bijections. -/
lemma actualBasisModuleHom_sheafification_isIso
    (P : X.PresheafOfModules) (N : X.Modules)
    (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (a : (inducedFunctor B).op ⋙ P.presheaf ⟶
      (inducedFunctor B).op ⋙ N.presheaf)
    (ha : ∀ (i : ι) (r : X.ringCatSheaf.obj.obj (op (B i)))
      (x : P.obj (op (B i))),
      (a.app (op i) (r • x) : N.val.obj (op (B i))) =
        r • (a.app (op i) x : N.val.obj (op (B i))))
    (hbij : ∀ i, Function.Bijective (a.app (op i))) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (modulePresheafHomFromActualBasis P N B hB a ha)) := by
  apply moduleSheafification_map_isIso_of_basiswise_bijective
    (modulePresheafHomFromActualBasis P N B hB a ha) B hB
  intro i
  constructor
  · intro x y hxy
    apply (hbij i).injective
    exact (modulePresheafHomFromActualBasis_on_basis P N B hB a ha i x).symm.trans
      (hxy.trans (modulePresheafHomFromActualBasis_on_basis P N B hB a ha i y))
  · intro y
    obtain ⟨x, hx⟩ := (hbij i).surjective y
    exact ⟨x, (modulePresheafHomFromActualBasis_on_basis P N B hB a ha i x).trans hx⟩

end PfaffianDescent
