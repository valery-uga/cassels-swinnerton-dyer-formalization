import PfaffianDescent.FiniteProjectiveProjectionFormula
import PfaffianDescent.ClosedImmersionIdealBaseChange

/-! Isomorphisms of scheme modules can be checked on an open cover. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Restriction to an open cover jointly detects isomorphisms of scheme
modules. This criterion lets affine ideal-module calculations glue without
constructing an inverse morphism on the original scheme. -/
theorem schemeModule_isIso_of_openCover_restrict_isIso
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {M N : X.Modules}
    (φ : M ⟶ N)
    (h : ∀ a : 𝒰.I₀,
      IsIso ((Scheme.Modules.restrictFunctor (𝒰.f a)).map φ)) :
    IsIso φ := by
  apply schemeModuleMap_isIso_of_stalk φ
  intro x
  rcases 𝒰.exists_eq x with ⟨a, y, rfl⟩
  letI : IsIso ((Scheme.Modules.restrictFunctor (𝒰.f a)).map φ) := h a
  let G := Scheme.Modules.toPresheaf (𝒰.X a) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  have hlocal : IsIso
      (G.map ((Scheme.Modules.restrictFunctor (𝒰.f a)).map φ)) :=
    Functor.map_isIso G _
  have hstalk : IsIso
      ((schemeModuleStalkFunctor X ((𝒰.f a) y)).map φ) :=
    (NatIso.isIso_map_iff
      (Scheme.Modules.restrictStalkNatIso (𝒰.f a) y) φ).mp hlocal
  have hforget : IsIso
      ((forget₂ (ModuleCat (X.presheaf.stalk ((𝒰.f a) y))) AddCommGrpCat).map
        ((schemeModuleStalkModuleFunctor X ((𝒰.f a) y)).map φ)) := by
    change IsIso ((schemeModuleStalkFunctor X ((𝒰.f a) y)).map φ)
    exact hstalk
  letI : IsIso
      ((forget₂ (ModuleCat (X.presheaf.stalk ((𝒰.f a) y))) AddCommGrpCat).map
        ((schemeModuleStalkModuleFunctor X ((𝒰.f a) y)).map φ)) := hforget
  exact isIso_of_reflects_iso
    ((schemeModuleStalkModuleFunctor X ((𝒰.f a) y)).map φ)
    (forget₂ (ModuleCat (X.presheaf.stalk ((𝒰.f a) y))) AddCommGrpCat)

/-- The canonical quotient-pushforward base-change map remains an
epimorphism after restriction to an open subscheme of its source. -/
theorem closedImmersionPushforwardBaseChangeHom_restrict_epi
    {X Y Z U : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] (u : U ⟶ X) [IsOpenImmersion u] :
    Epi ((Scheme.Modules.restrictFunctor u).map
      (closedImmersionPushforwardBaseChangeHom f i)) := by
  let R := Scheme.Modules.restrictFunctor u
  let j := pullback.fst f i
  let uf := BundleSectionZeroLocus.pullbackUnitComparison f
  let qj := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence j
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact j
  have hR := ShortComplex.shortExact_map_restrictFunctor u S hS
  have hEpiQj : Epi (R.map qj) := by
    change Epi (S.map R).g
    exact hR.epi_g
  haveI : IsIso uf := BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  have hIsoUf : IsIso (R.map uf) := Functor.map_isIso R uf
  have hEpiUf : Epi (R.map uf) := by
    letI := hIsoUf
    exact IsIso.epi_of_iso (R.map uf)
  have hEpiComp : Epi (R.map uf ≫ R.map qj) :=
    epi_comp' hEpiUf hEpiQj
  have hfac : R.map ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) ≫
      R.map (closedImmersionPushforwardBaseChangeHom f i) =
      R.map uf ≫ R.map qj := by
    calc
      _ = R.map ((Scheme.Modules.pullback f).map
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
          closedImmersionPushforwardBaseChangeHom f i) :=
        (R.map_comp _ _).symm
      _ = R.map (uf ≫ qj) :=
        congrArg R.map (closedImmersionPushforwardBaseChangeHom_quotient f i)
      _ = R.map uf ≫ R.map qj := R.map_comp _ _
  exact epi_of_epi_fac hfac

/-- For a flat morphism, invertibility of the canonical actual ideal map
on an open cover of the source suffices for closed-immersion quotient
pushforward base change. -/
theorem isIso_closedImmersionPushforwardBaseChangeHom_of_ideal_openCover
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i] (𝒰 : X.OpenCover)
    (h : ∀ a : 𝒰.I₀,
      IsIso ((Scheme.Modules.restrictFunctor (𝒰.f a)).map
        (closedImmersionIdealBaseChangeHom f i))) :
    IsIso (closedImmersionPushforwardBaseChangeHom f i) := by
  letI : IsIso (closedImmersionIdealBaseChangeHom f i) :=
    schemeModule_isIso_of_openCover_restrict_isIso 𝒰 _ h
  exact isIso_closedImmersionPushforwardBaseChangeHom_of_ideal f i

end PfaffianDescent
