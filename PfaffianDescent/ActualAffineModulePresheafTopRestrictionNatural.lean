import PfaffianDescent.ActualAffineModulePresheafLocalizedBasisEquiv

/- SOURCE ONLY / UNVERIFIED. Actual full-open natural maps from the same
presheaf top module. No localization or derivative comparison input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- True ALL-open tilde restriction natural transformation, checked with
an ABSTRACT bundled ring and module before actual P(top) is substituted. -/
private def actualTildeTopToOpenNatural
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    (Functor.const (Spec R).Opensᵒᵖ).obj M ⟶
      ((modulesSpecToSheaf (R := R)).obj (tilde (R := R) M)).obj where
  app U := tilde.toOpen (R := R) M U.unop
  naturality {U V} i := by
    have h : tilde.toOpen (R := R) M U.unop ≫
        ((modulesSpecToSheaf (R := R)).obj (tilde (R := R) M)).obj.map i =
        tilde.toOpen (R := R) M V.unop :=
      tilde.toOpen_res (R := R) M U.unop V.unop i.unop
    exact (Category.id_comp (tilde.toOpen (R := R) M V.unop)).trans h.symm

/-- The true functorial top restriction, on ALL opens. -/
def actualAffineModulePresheafTopRestriction
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules) :
    (Functor.const (Spec (CommRingCat.of R)).Opensᵒᵖ).obj
        ((actualAffineModulePresheafOverBase P).obj (op ⊤)) ⟶
      actualAffineModulePresheafOverBase P where
  app U := (actualAffineModulePresheafOverBase P).map U.unop.leTop.op
  naturality {U V} i := by
    let F := actualAffineModulePresheafOverBase P
    have h : F.map U.unop.leTop.op ≫ F.map i = F.map V.unop.leTop.op :=
      (F.map_comp U.unop.leTop.op i).symm.trans
        (congrArg (fun a => F.map a) (Subsingleton.elim _ _))
    exact (Category.id_comp (F.map V.unop.leTop.op)).trans h.symm

/-- The true tilde localization maps, naturally on ALL opens. -/
def actualAffineModulePresheafTopToTilde
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules) :
    (Functor.const (Spec (CommRingCat.of R)).Opensᵒᵖ).obj
        ((actualAffineModulePresheafOverBase P).obj (op ⊤)) ⟶
      (modulesSpecToSheaf.obj
        (tilde ((actualAffineModulePresheafOverBase P).obj (op ⊤)))).obj :=
  actualTildeTopToOpenNatural (R := CommRingCat.of R)
    ((actualAffineModulePresheafOverBase P).obj (op ⊤))

end PfaffianDescent
