import PfaffianDescent.ActualAffineLocalizedModulePresheafSheafification

/- SOURCE ONLY / UNVERIFIED. Genuine sheafification/counit consumer.
The actual affine differential specialization will derive hLoc from the
primitive one-open theorem. No native Omega or chart comparison occurs here. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine sheafification of the SAME presheaf is isomorphic to tilde of
its SAME canonically forgotten top module. The counit is an actual sheaf map. -/
noncomputable def actualAffineLocalizedModulePresheafSheafIso
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) :=
  let X := Spec (CommRingCat.of R)
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let N := tilde (R := CommRingCat.of R)
    ((actualAffineModulePresheafOverBase P).obj (op ⊤))
  let b := actualAffineLocalizedModulePresheafToTilde P hLoc
  letI : IsIso (S.map b) :=
    actualAffineLocalizedModulePresheafSheafification_isIso P hLoc
  letI : IsIso adj.counit := inferInstance
  asIso (S.map b) ≪≫ asIso (adj.counit.app N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary purely categorical use of the actual unit. A component of
this unit is bijective whenever a genuine sheafification-Iso comparison
has a bijective component there. These inputs are derived below. -/
private lemma actualModuleSheafificationUnit_bijective_on_open
    {X : Scheme.{u}} (P : X.PresheafOfModules) (N : X.Modules)
    (b : P ⟶ N.val)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map b)]
    (U : X.Opensᵒᵖ) (hb : Function.Bijective (b.app U)) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app U) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := inferInstance
  let j : S.obj P ⟶ N := S.map b ≫ adj.counit.app N
  letI : IsIso j := inferInstance
  let E := PresheafOfModules.evaluation X.ringCatSheaf.obj U
  let t := E.map (G.map j)
  let v := E.map (adj.unit.app P)
  have ht : Function.Bijective t := ConcreteCategory.bijective_of_isIso t
  have hj : j = (adj.homEquiv P N).symm b :=
    (adj.homEquiv_counit P N b).symm
  have hu : adj.unit.app P ≫ G.map j = b :=
    (adj.homEquiv_unit P N j).symm.trans
      ((congrArg (adj.homEquiv P N) hj).trans
        ((adj.homEquiv P N).apply_symm_apply b))
  have he : v ≫ t = E.map b :=
    (E.map_comp (adj.unit.app P) (G.map j)).symm.trans
      (congrArg E.map hu)
  have hev : ∀ x, t (v x) = b.app U x :=
    fun x => ConcreteCategory.congr_hom he x
  constructor
  · intro x y hxy
    exact hb.injective ((hev x).symm.trans
      ((congrArg (fun z => t z) hxy).trans (hev y)))
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (t y)
    exact ⟨x, ht.injective ((hev x).trans hx)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived glued map keeps the actual basis comparison, not merely
some independently chosen module isomorphism. -/
noncomputable def actualAffineLocalizedModulePresheafToTilde_on_basis
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom))
    (f : R) (x : P.obj (op (PrimeSpectrum.basicOpen f))) :=
  let b := actualAffineLocalizedModulePresheafToTilde (R := R) P hLoc
  let e := actualAffineModulePresheafLocalizedBasisIso (R := R) P hLoc
  have h : b.app (op (PrimeSpectrum.basicOpen f)) x =
      e.hom.app (op f) x := by
    dsimp only [b]
    unfold actualAffineLocalizedModulePresheafToTilde
    refine (modulePresheafHomFromActualBasis_on_basis _ _ _ _ _ _ f x).trans ?_
    rfl
  h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual sheafification unit is bijective on each basic open, by its
real composite with the derived sheaf Iso and the derived basis comparison. -/
noncomputable def actualAffineLocalizedModulePresheafUnit_basis_bijective
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) (f : R) := by
  let X := Spec (CommRingCat.of R)
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let N := tilde (R := CommRingCat.of R)
    ((actualAffineModulePresheafOverBase P).obj (op ⊤))
  let b := actualAffineLocalizedModulePresheafToTilde P hLoc
  let e := actualAffineModulePresheafLocalizedBasisIso P hLoc
  letI : IsIso (S.map b) :=
    actualAffineLocalizedModulePresheafSheafification_isIso P hLoc
  have he : (fun x => b.app (op (PrimeSpectrum.basicOpen f)) x) =
      (fun x => e.hom.app (op f) x) :=
    funext (actualAffineLocalizedModulePresheafToTilde_on_basis P hLoc f)
  have hb : Function.Bijective (b.app (op (PrimeSpectrum.basicOpen f))) := by
    change Function.Bijective (fun x => b.app (op (PrimeSpectrum.basicOpen f)) x)
    rw [he]
    exact ConcreteCategory.bijective_of_isIso (e.hom.app (op f))
  exact actualModuleSheafificationUnit_bijective_on_open P N b
    (op (PrimeSpectrum.basicOpen f)) hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- D(1) is literally top; no localization-map comparison input is added. -/
noncomputable def actualAffineLocalizedModulePresheafUnit_top_bijective
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app P).app (op ⊤)) := by
  let X := Spec (CommRingCat.of R)
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  have hU : (PrimeSpectrum.basicOpen (R := R) (1 : R) : X.Opens) = ⊤ :=
    PrimeSpectrum.basicOpen_one
  have h : Function.Bijective (eta.app (op (PrimeSpectrum.basicOpen (R := R) (1 : R)))) :=
    actualAffineLocalizedModulePresheafUnit_basis_bijective P hLoc (1 : R)
  exact (congrArg (fun U : X.Opens => Function.Bijective (eta.app (op U))) hU).mp h

end PfaffianDescent
