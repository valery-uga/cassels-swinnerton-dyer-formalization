import PfaffianDescent.ActualAffineModulePresheafLocalizedBasisIso
import PfaffianDescent.ActualBasisModuleHomSheafificationIso

/- SOURCE ONLY / UNVERIFIED. The basic maps, their coefficient linearity,
naturality and bijectivity are derived from canonical localization.
The actual differential caller supplies hLoc internally via one-open202. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
universe v w

/-- Over-base scalar restriction leaves the original additive presheaf
unchanged. This Iso is the identity on every actual section. -/
private def actualAffineOverBaseForgetIso
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules) :
    actualAffineModulePresheafOverBase P ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅ P.presheaf := by
  refine NatIso.ofComponents (fun U => Iso.refl (P.presheaf.obj U)) ?_
  intro U V i
  apply AddCommGrpCat.ext
  intro x
  rfl

/-- The installed Spec-module forgetful functor preserves the SAME
additive section presheaf; only scalar actions have been restricted. -/
private def actualAffineSheafModuleForgetIso
    {R : Type u} [CommRing R]
    (N : (Spec (CommRingCat.of R)).Modules) :
    ((modulesSpecToSheaf (R := CommRingCat.of R)).obj N).obj ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅ N.presheaf := by
  refine NatIso.ofComponents (fun U => Iso.refl (N.presheaf.obj U)) ?_
  intro U V i
  apply AddCommGrpCat.ext
  intro x
  rfl

/-- Forget one original module-Iso component, with its exact hom and inv.
This abstract precursor has no factored functor endpoint to normalize. -/
private def actualModuleBasisIsoAdditiveComponent
    {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]
    {F G : C ⥤ ModuleCat.{u} R} (e : F ≅ G) (c : C) :
    AddCommGrpCat.of (F.obj c) ≅ AddCommGrpCat.of (G.obj c) where
  hom := AddCommGrpCat.ofHom (e.hom.app c).hom.toAddMonoidHom
  inv := AddCommGrpCat.ofHom (e.inv.app c).hom.toAddMonoidHom
  hom_inv_id := by
    apply AddCommGrpCat.ext
    intro x
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app c) x
  inv_hom_id := by
    apply AddCommGrpCat.ext
    intro x
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app c) x

/-- The underlying value of the abstract additive component is exactly
its original module component; no concrete presheaf dictionaries occur. -/
private theorem actualModuleBasisIsoAdditiveComponent_apply
    {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]
    {F G : C ⥤ ModuleCat.{u} R} (e : F ≅ G) (c : C) (x : F.obj c) :
    (actualModuleBasisIsoAdditiveComponent e c).hom x = e.hom.app c x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The SAME accepted module basis comparison, constructed at the genuine
additive presheaf endpoints one component at a time. Naturality is the
accepted module comparison's naturality on the SAME actual sections. -/
private noncomputable def actualAffineLocalizedBasisAdditiveIso
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙ P.presheaf ≅
      (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        (tilde (R := CommRingCat.of R)
          ((actualAffineModulePresheafOverBase P).obj (op ⊤))).presheaf := by
  let X := Spec (CommRingCat.of R)
  let B : R → X.Opens := PrimeSpectrum.basicOpen
  let H := (inducedFunctor B).op
  let N := tilde (R := CommRingCat.of R)
    ((actualAffineModulePresheafOverBase P).obj (op ⊤))
  let e := actualAffineModulePresheafLocalizedBasisIso (R := R) P hLoc
  let p := actualAffineOverBaseForgetIso (R := R) P
  let q := actualAffineSheafModuleForgetIso (R := R) N
  refine NatIso.ofComponents (fun c =>
    (p.app (H.obj c)).symm ≪≫ actualModuleBasisIsoAdditiveComponent e c ≪≫
      q.app (H.obj c)) ?_
  intro c d i
  apply AddCommGrpCat.ext
  intro x
  exact ConcreteCategory.congr_hom (e.hom.naturality i) x

set_option backward.isDefEq.respectTransparency false in
/-- Actual module-linear extension to tilde of the SAME original top module. -/
noncomputable def actualAffineLocalizedModulePresheafToTilde
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) :
    P ⟶ (tilde (R := CommRingCat.of R)
      ((actualAffineModulePresheafOverBase P).obj (op ⊤))).val :=
  let X := Spec (CommRingCat.of R)
  let B : R → X.Opens := PrimeSpectrum.basicOpen
  let N := tilde (R := CommRingCat.of R)
    ((actualAffineModulePresheafOverBase P).obj (op ⊤))
  let aIso := actualAffineLocalizedBasisAdditiveIso (R := R) P hLoc
  let a := aIso.hom
  have ha : ∀ (i : R) (r : X.ringCatSheaf.obj.obj (op (B i)))
      (x : P.obj (op (B i))),
      (a.app (op i) (r • x) : N.val.obj (op (B i))) =
        @SMul.smul (X.ringCatSheaf.obj.obj (op (B i)))
          (N.val.obj (op (B i))) (N.val.obj (op (B i))).isModule.toSMul
          r (a.app (op i) x) := by
    intro i r x
    let e := actualAffineModulePresheafLocalizedBasisIso (R := R) P hLoc
    let b := actualAffineModulePresheafLocalizedBasisEquiv (R := R) P hLoc i
    have hEval (y : P.obj (op (B i))) :
        (a.app (op i) y : N.val.obj (op (B i))) = b y := by
      have hNative := actualModuleBasisIsoAdditiveComponent_apply (R := R)
        e (op i) y
      exact hNative.trans (by rfl)
    exact (hEval (r • x)).trans
      ((b.map_smul r x).trans
        (congrArg (fun y : N.val.obj (op (B i)) =>
          @SMul.smul (X.ringCatSheaf.obj.obj (op (B i)))
            (N.val.obj (op (B i))) (N.val.obj (op (B i))).isModule.toSMul r y)
          (hEval x).symm))
  modulePresheafHomFromActualBasis P N B PrimeSpectrum.isBasis_basic_opens a ha

set_option backward.isDefEq.respectTransparency false in
/-- Genuine sheafification of the SAME derived module map is an Iso. -/
noncomputable def actualAffineLocalizedModulePresheafSheafification_isIso
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) :=
  let X := Spec (CommRingCat.of R)
  let B : R → X.Opens := PrimeSpectrum.basicOpen
  let N := tilde (R := CommRingCat.of R)
    ((actualAffineModulePresheafOverBase P).obj (op ⊤))
  let aIso := actualAffineLocalizedBasisAdditiveIso (R := R) P hLoc
  let a := aIso.hom
  have ha : ∀ (i : R) (r : X.ringCatSheaf.obj.obj (op (B i)))
      (x : P.obj (op (B i))),
      (a.app (op i) (r • x) : N.val.obj (op (B i))) =
        @SMul.smul (X.ringCatSheaf.obj.obj (op (B i)))
          (N.val.obj (op (B i))) (N.val.obj (op (B i))).isModule.toSMul
          r (a.app (op i) x) := by
    intro i r x
    let e := actualAffineModulePresheafLocalizedBasisIso (R := R) P hLoc
    let b := actualAffineModulePresheafLocalizedBasisEquiv (R := R) P hLoc i
    have hEval (y : P.obj (op (B i))) :
        (a.app (op i) y : N.val.obj (op (B i))) = b y := by
      have hNative := actualModuleBasisIsoAdditiveComponent_apply (R := R)
        e (op i) y
      exact hNative.trans (by rfl)
    exact (hEval (r • x)).trans
      ((b.map_smul r x).trans
        (congrArg (fun y : N.val.obj (op (B i)) =>
          @SMul.smul (X.ringCatSheaf.obj.obj (op (B i)))
            (N.val.obj (op (B i))) (N.val.obj (op (B i))).isModule.toSMul r y)
          (hEval x).symm))
  have hbij : ∀ i : R, Function.Bijective (a.app (op i)) := by
    intro i
    exact ConcreteCategory.bijective_of_isIso (aIso.hom.app (op i))
  let b := actualAffineLocalizedModulePresheafToTilde (R := R) P hLoc
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hIso : IsIso (S.map b) := by
    exact actualBasisModuleHom_sheafification_isIso P N B
      PrimeSpectrum.isBasis_basic_opens a ha hbij
  hIso

end PfaffianDescent
