import PfaffianDescent.CorayAffineOriginalTopSections

/-! Actual quotient projection under actual affine top-section comparison.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mappedIso_conjugate_cancel
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B : C} (e : A ≅ B) {Z : D} (d : G.obj A ≅ Z) :
    d.inv ≫ G.map e.hom ≫ (G.map e.inv ≫ d.hom) = 𝟙 Z := by
  rw [← Functor.map_comp_assoc, e.hom_inv_id, G.map_id,
    Category.id_comp, Iso.inv_hom_id]

/-- The actual affine top-section comparison takes the actual SHEAF
quotient projection to the actual original-module cokernel projection.
Every transport and its projection is the canonical map used in the
constructed affine comparison; no comparison certificate is assumed. -/
theorem affineTargetQuotientSheaf_topCokernelIso_π {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) :
    (schemeTopModuleFunctor X).map
      (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
        (affineTargetQuotientSheaf_topCokernelIso f).hom =
      cokernel.π ((schemeTopModuleFunctor X).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  let e := X.isoSpec.hom
  let F := Scheme.Modules.pushforward e
  let G := moduleSpecΓFunctor (R := Γ(X, ⊤))
  let T := schemeTopModuleFunctor X
  let E := affineTargetPushforwardTopSectionsNatIso X
  let OX := SheafOfModules.unit X.ringCatSheaf
  let OY := SheafOfModules.unit Y.ringCatSheaf
  let N := (Scheme.Modules.pushforward f).obj OY
  let qf := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qe := SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom
  let qfe := SheafOfModules.unitToPushforwardObjUnit (f ≫ e).toRingCatSheafHom
  letI : IsIso qe := affineSource_unit_isIso_of_isIso e
  let C := (Scheme.Modules.pushforwardComp f e).app OY
  let eA := G.mapIso (asIso qe) ≪≫ E.app OX
  let eB := G.mapIso C.symm ≪≫ E.app N
  have hcomp : qfe ≫ C.inv = qe ≫ F.map qf := by
    exact C.comp_inv_eq.mpr
      ((affineSource_unit_comp f e).trans (Category.assoc qe (F.map qf) C.hom).symm)
  have hc : G.map qfe ≫ eB.hom = eA.hom ≫ T.map qf := by
    change G.map qfe ≫ (G.map C.inv ≫ E.hom.app N) =
      (G.map qe ≫ E.hom.app OX) ≫ T.map qf
    rw [← Category.assoc, ← G.map_comp, hcomp, G.map_comp, Category.assoc]
    have hn : G.map (F.map qf) ≫ E.hom.app N = E.hom.app OX ≫ T.map qf :=
      E.hom.naturality qf
    rw [hn, Category.assoc]
  let eC := cokernel.mapIso (G.map qfe) (T.map qf) eA eB hc
  let eSpec := affineTargetQuotientSheaf_specSectionsIso f
  have hdef : (affineTargetQuotientSheaf_topCokernelIso f).hom =
      ((E.app (cokernel qf)).inv ≫ eSpec.hom) ≫ eC.hom := by
    rfl
  have hnat : T.map (cokernel.π qf) ≫ (E.app (cokernel qf)).inv =
      (E.app N).inv ≫ G.map (F.map (cokernel.π qf)) := by
    exact E.inv.naturality (cokernel.π qf)
  have hspec : G.map (F.map (cokernel.π qf)) ≫ eSpec.hom =
      G.map C.hom ≫ cokernel.π (G.map qfe) :=
    affineTargetQuotientSheaf_specSectionsIso_π f
  have hmap : cokernel.π (G.map qfe) ≫ eC.hom =
      eB.hom ≫ cokernel.π (T.map qf) := cokernel.π_desc _ _ _
  have hcancel : (E.app N).inv ≫ G.map C.hom ≫ eB.hom = 𝟙 (T.obj N) := by
    change (E.app N).inv ≫ G.map C.hom ≫ (G.map C.inv ≫ (E.app N).hom) = _
    exact mappedIso_conjugate_cancel G C (E.app N)
  change T.map (cokernel.π qf) ≫
    (affineTargetQuotientSheaf_topCokernelIso f).hom = cokernel.π (T.map qf)
  calc
    T.map (cokernel.π qf) ≫ (affineTargetQuotientSheaf_topCokernelIso f).hom =
        (T.map (cokernel.π qf) ≫ (E.app (cokernel qf)).inv) ≫ eSpec.hom ≫ eC.hom := by
          rw [hdef]
          simp only [Category.assoc]
    _ = ((E.app N).inv ≫ G.map (F.map (cokernel.π qf))) ≫ eSpec.hom ≫ eC.hom := by
          rw [hnat]
    _ = (E.app N).inv ≫ (G.map (F.map (cokernel.π qf)) ≫ eSpec.hom) ≫ eC.hom := by
          simp only [Category.assoc]
    _ = (E.app N).inv ≫ (G.map C.hom ≫ cokernel.π (G.map qfe)) ≫ eC.hom := by
          rw [hspec]
    _ = (E.app N).inv ≫ G.map C.hom ≫ (cokernel.π (G.map qfe) ≫ eC.hom) := by
          simp only [Category.assoc]
    _ = (E.app N).inv ≫ G.map C.hom ≫ (eB.hom ≫ cokernel.π (T.map qf)) := by
          rw [hmap]
    _ = ((E.app N).inv ≫ G.map C.hom ≫ eB.hom) ≫ cokernel.π (T.map qf) := by
          simp only [Category.assoc]
    _ = cokernel.π (T.map qf) := by rw [hcancel, Category.id_comp]

end PfaffianDescent.Coray
