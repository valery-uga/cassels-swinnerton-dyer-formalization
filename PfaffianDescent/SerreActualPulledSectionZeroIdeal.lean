import PfaffianDescent.VoisinDegreeElevenSerreIncidenceAffineZeroEquations

/-! Actual section compatibility identifies actual pulled zero ideals.
Changing the finite free frame and multiplying by an invertible regular
function preserve the scheme ideal, not just its set of points. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualSectionZeroIdeal_transport
    {T : Scheme.{u}} {M N : T.Modules} {ι : Type u}
    (t : SheafOfModules.free (R := T.ringCatSheaf) ι ≅ M)
    (e : M ≅ N) (s : M.sections) :
    sectionZeroIdealOfFreeIso ι (t ≪≫ e) (SheafOfModules.sectionsMap e.hom s) =
      sectionZeroIdealOfFreeIso ι t s := by
  unfold sectionZeroIdealOfFreeIso
  apply congrArg (freeSectionZeroIdeal ι)
  have h : SheafOfModules.sectionsMap (t ≪≫ e).inv
      (SheafOfModules.sectionsMap e.hom s) = SheafOfModules.sectionsMap t.inv s := by
    rw [← SheafOfModules.sectionsMap_comp]
    simp only [Iso.trans_inv, Iso.hom_inv_id_assoc]
  exact h

theorem serreActualPulledSectionZeroIdeal_eq_of_iso
    {T X Y : Scheme.{u}} [IsAffine T] [IsAffine X] [IsAffine Y]
    (f : T ⟶ X) (g : T ⟶ Y) {M : X.Modules} {N : Y.Modules}
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (t : SheafOfModules.free (R := X.ringCatSheaf) ι ≅ M)
    (r : SheafOfModules.free (R := Y.ringCatSheaf) κ ≅ N)
    (s : M.sections) (v : N.sections)
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj N)
    (hsections : SheafOfModules.sectionsMap e.hom
      (pullbackSection f M (isIso_pullbackUnitComparison f) s) =
      pullbackSection g N (isIso_pullbackUnitComparison g) v) :
    (sectionZeroIdealOfFreeIso ι t s).comap f =
      (sectionZeroIdealOfFreeIso κ r v).comap g := by
  rw [serreIncidenceZeroIdeal_comap_pullback, serreIncidenceZeroIdeal_comap_pullback]
  calc
    _ = sectionZeroIdealOfFreeIso ι ((pullbackFreeIso f ι t) ≪≫ e)
        (SheafOfModules.sectionsMap e.hom
          (pullbackSection f M (isIso_pullbackUnitComparison f) s)) :=
      (serreActualSectionZeroIdeal_transport (pullbackFreeIso f ι t) e _).symm
    _ = sectionZeroIdealOfFreeIso κ (pullbackFreeIso g κ r)
        (SheafOfModules.sectionsMap e.hom
          (pullbackSection f M (isIso_pullbackUnitComparison f) s)) :=
      sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso ι κ _ _ _
    _ = _ := congrArg (sectionZeroIdealOfFreeIso κ (pullbackFreeIso g κ r)) hsections

theorem serreActualPulledSectionZeroIdeal_eq_of_iso_unit_scale
    {T X Y : Scheme.{u}} [IsAffine T] [IsAffine X] [IsAffine Y]
    (f : T ⟶ X) (g : T ⟶ Y) {M : X.Modules} {N : Y.Modules}
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (t : SheafOfModules.free (R := X.ringCatSheaf) ι ≅ M)
    (r : SheafOfModules.free (R := Y.ringCatSheaf) κ ≅ N)
    (s : M.sections) (v : N.sections)
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj N)
    (a : Γ(T, ⊤)) (ha : IsUnit a)
    (hsections : SheafOfModules.sectionsMap e.hom
      (pullbackSection f M (isIso_pullbackUnitComparison f) s) =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (pullbackSection g N (isIso_pullbackUnitComparison g) v)) :
    (sectionZeroIdealOfFreeIso ι t s).comap f =
      (sectionZeroIdealOfFreeIso κ r v).comap g := by
  letI : IsIso (unitEndomorphismOfRegularFunction (X := T) a) :=
    isIso_unitEndomorphismOfRegularFunction_of_isUnit a ha
  rw [serreIncidenceZeroIdeal_comap_pullback, serreIncidenceZeroIdeal_comap_pullback]
  calc
    _ = sectionZeroIdealOfFreeIso ι ((pullbackFreeIso f ι t) ≪≫ e)
        (SheafOfModules.sectionsMap e.hom
          (pullbackSection f M (isIso_pullbackUnitComparison f) s)) :=
      (serreActualSectionZeroIdeal_transport (pullbackFreeIso f ι t) e _).symm
    _ = sectionZeroIdealOfFreeIso κ (pullbackFreeIso g κ r)
        (SheafOfModules.sectionsMap e.hom
          (pullbackSection f M (isIso_pullbackUnitComparison f) s)) :=
      sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso ι κ _ _ _
    _ = sectionZeroIdealOfFreeIso κ (pullbackFreeIso g κ r)
        (scaleSection (unitEndomorphismOfRegularFunction a)
          (pullbackSection g N (isIso_pullbackUnitComparison g) v)) :=
      congrArg (sectionZeroIdealOfFreeIso κ (pullbackFreeIso g κ r)) hsections
    _ = _ := sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso κ _ _ _

end PfaffianDescent
