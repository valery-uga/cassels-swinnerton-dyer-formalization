import PfaffianDescent.ClosedImmersionIdealBaseChangeOpenCover
import PfaffianDescent.OpenPullbackMono

/-!
# Invariance of ideal base change under source isomorphism

If the canonical ideal comparison holds after an isomorphic change of its
source, it holds for the original map. The proof transports monicity of the
pulled-back ideal inclusion through the pullback functor of the inverse
isomorphism.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem isIso_closedImmersionIdealBaseChangeHom_of_sourceIso
    {X X' Y Z : Scheme.{u}}
    (e : X' ≅ X) (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [IsIso (closedImmersionIdealBaseChangeHom (e.hom ≫ f) i)] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  let m := IdealSheafDataModule.closedImmersionModuleToUnit i
  have hlocal : Mono ((Scheme.Modules.pullback (e.hom ≫ f)).map m) :=
    closedImmersionIdealPullback_mono_of_baseChangeIso (e.hom ≫ f) i
  haveI : IsOpenImmersion e.inv := inferInstance
  have hcomposed : Mono
      ((Scheme.Modules.pullback e.inv).map
        ((Scheme.Modules.pullback (e.hom ≫ f)).map m)) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.pullback e.inv)
      (openImmersionPullback_preservesMonomorphisms e.inv) _ _ _ hlocal
  have hfinal : Mono
      ((Scheme.Modules.pullback (e.inv ≫ (e.hom ≫ f))).map m) :=
    mono_map_of_natIso (Scheme.Modules.pullbackComp e.inv (e.hom ≫ f))
      m hcomposed
  have heq : e.inv ≫ (e.hom ≫ f) = f := by
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [heq] at hfinal
  letI : Mono ((Scheme.Modules.pullback f).map m) := hfinal
  exact isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono f i

end PfaffianDescent
