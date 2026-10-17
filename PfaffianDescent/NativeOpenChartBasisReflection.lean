import PfaffianDescent.FiniteProjectiveProjectionFormula
import PfaffianDescent.SchemeModuleTensor

/-! SOURCE ONLY. Native Spec-chart invertibility is reflected to its SAME
original image open, using genuine original module stalks and over-site maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual chart detects invertibility on its original image open.
The image equality is geometric chart data, not an Iso/outcome certificate. -/
theorem nativeOpenChart_restrictMap_isIso_of_pullbackMap_isIso
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U)
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.pullback j).map f)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  letI : IsIso ((Scheme.Modules.restrictFunctor j).map f) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j) f).mpr inferInstance
  apply schemeModuleMap_isIso_of_stalk ((Scheme.Modules.restrictFunctor U.ι).map f)
  intro x
  have hx : U.ι x ∈ j.opensRange := by rw [hU]; exact x.property
  obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp hx
  let G := Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z
  have hlocal : IsIso (G.map ((Scheme.Modules.restrictFunctor j).map f)) :=
    Functor.map_isIso G _
  have hglobal : IsIso ((schemeModuleStalkFunctor X (j z)).map f) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso j z) f).mp hlocal
  have hglobal' : IsIso ((schemeModuleStalkFunctor X (U.ι x)).map f) := by
    exact hz ▸ hglobal
  let H := Scheme.Modules.toPresheaf (U : Scheme) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hrestrict : IsIso (H.map ((Scheme.Modules.restrictFunctor U.ι).map f)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι x) f).mpr hglobal'
  let F := forget₂ (ModuleCat ((U : Scheme).presheaf.stalk x)) AddCommGrpCat
  letI : IsIso (F.map ((schemeModuleStalkModuleFunctor (U : Scheme) x).map
      ((Scheme.Modules.restrictFunctor U.ι).map f))) := by
    change IsIso (H.map ((Scheme.Modules.restrictFunctor U.ι).map f))
    exact hrestrict
  exact isIso_of_reflects_iso
    ((schemeModuleStalkModuleFunctor (U : Scheme) x).map
      ((Scheme.Modules.restrictFunctor U.ι).map f)) F

/-- The SAME chart detects invertibility of the SAME actual over-site map. -/
theorem nativeOpenChart_overMap_isIso_of_pullbackMap_isIso
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U)
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.pullback j).map f)] : IsIso (f.over U) := by
  letI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) :=
    nativeOpenChart_restrictMap_isIso_of_pullbackMap_isIso j U hU f
  exact overFunctorMap_isIso_of_restrictMap_isIso U f

end PfaffianDescent
