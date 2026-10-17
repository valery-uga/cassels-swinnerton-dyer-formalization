import PfaffianDescent.VoisinFixedLinearSystemUniversalZeroSubschemeDescent

/-! Equality of the actual pulled zero ideals gives an isomorphism of the
actual closed pullbacks, retaining their morphisms to the common source. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreActualClosedPullbackZeroIso
    {T X Y Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : T ⟶ X) (g : T ⟶ Y)
    (h : i.ker.comap f = j.ker.comap g) :
    pullback f i ≅ pullback g j :=
  asIso (pullback.fst f i).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme
      ((Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f).trans
        (h.trans (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion j g).symm))) ≪≫
    (asIso (pullback.fst g j).toImage).symm

@[reassoc]
theorem serreActualClosedPullbackZeroIso_hom_fst
    {T X Y Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : T ⟶ X) (g : T ⟶ Y)
    (h : i.ker.comap f = j.ker.comap g) :
    (serreActualClosedPullbackZeroIso i j f g h).hom ≫ pullback.fst g j =
      pullback.fst f i := by
  let p := pullback.fst f i
  let q := pullback.fst g j
  let he : p.ker = q.ker :=
    (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f).trans
      (h.trans (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion j g).symm)
  have hq : (asIso q.toImage).inv ≫ q = q.imageι := by
    calc
      _ = (asIso q.toImage).inv ≫ (q.toImage ≫ q.imageι) :=
        congrArg (fun k => (asIso q.toImage).inv ≫ k) q.toImage_imageι.symm
      _ = q.imageι := (asIso q.toImage).inv_hom_id_assoc q.imageι
  have heι : (eqToIso (congrArg Scheme.IdealSheafData.subscheme he)).hom ≫
      q.imageι = p.imageι :=
    SchemeModuleFiniteFreeAffineCover.universalIdealSheafData_eqToIso_subschemeι p.ker q.ker he
  change ((asIso p.toImage).hom ≫
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme he)).hom ≫
      (asIso q.toImage).inv) ≫ q = p
  calc
    _ = (asIso p.toImage).hom ≫
        (eqToIso (congrArg Scheme.IdealSheafData.subscheme he)).hom ≫
          ((asIso q.toImage).inv ≫ q) := by simp only [Category.assoc]
    _ = (asIso p.toImage).hom ≫
        (eqToIso (congrArg Scheme.IdealSheafData.subscheme he)).hom ≫ q.imageι :=
      congrArg (fun k => (asIso p.toImage).hom ≫
        (eqToIso (congrArg Scheme.IdealSheafData.subscheme he)).hom ≫ k) hq
    _ = (asIso p.toImage).hom ≫ p.imageι :=
      congrArg (fun k => (asIso p.toImage).hom ≫ k) heι
    _ = p := p.toImage_imageι

end PfaffianDescent
