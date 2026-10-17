import PfaffianDescent.CorayActualBasicOpenSpecUnitMatrix

/-! Whole generator comparison for the OWN native ambient chart pullback.
All frames and map equalities are derived. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The actual pullback-composition/restriction comparison, before any
positive-twist or finite-coproduct frame is applied. -/
def actualPositiveNativeChartRestrictionIso (j : Fin 4) :
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))) ≅
    (Scheme.Modules.restrictFunctor (Proj.basicOpen PS (X j)).ι ⋙
      Scheme.Modules.pullback
        (Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j)
          (by decide : 0 < 1)).inv) := by
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  change Scheme.Modules.pullback (e.inv ≫ U.ι) ≅ _
  exact (Scheme.Modules.pullbackComp e.inv U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm P

private lemma mappedComp_with_outerMaps
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N L : C} {A B : D}
    (a : A ⟶ F.obj M) (f : M ⟶ N) (g : N ⟶ L) (b : F.obj L ⟶ B) :
    a ≫ F.map (f ≫ g) ≫ b = (a ≫ F.map f) ≫ F.map g ≫ b := by
  have hm : a ≫ F.map (f ≫ g) ≫ b = a ≫ (F.map f ≫ F.map g) ≫ b :=
    congrArg (fun z => a ≫ z ≫ b) (F.map_comp f g)
  have ha : a ≫ (F.map f ≫ F.map g) ≫ b = (a ≫ F.map f) ≫ F.map g ≫ b := by
    simp only [Category.assoc]
  exact hm.trans ha

private theorem canonicalPullbackUnit_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (actualCanonicalPullbackUnitIso f).hom = pullbackUnitComparison f := rfl

private theorem restrictionIsoFactory_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : D ⥤ E) {Q : C ⥤ E} {R S : C ⥤ D}
    (a : S ⋙ P ≅ Q) (b : R ≅ S) (M : C) :
    (a.symm ≪≫ Functor.isoWhiskerRight b.symm P).hom.app M =
      a.inv.app M ≫ P.map (b.inv.app M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]

private theorem positiveIsoFactory_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : D ⥤ E) {Q : C ⥤ E} {R S : C ⥤ D}
    (a : S ⋙ P ≅ Q) (b : R ≅ S) (M : C)
    {N : D} {W : E} (c : R.obj M ≅ N) (v : P.obj N ⟶ W) [IsIso v] :
    (a.symm.app M ≪≫ P.mapIso (b.symm.app M ≪≫ c) ≪≫ asIso v).hom =
      a.inv.app M ≫ P.map (b.inv.app M ≫ c.hom) ≫ v := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.app_hom, Iso.symm_hom]

private def nativeRestrictionHomFactoryResult (j : Fin 4) (m : ℕ) :=
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  restrictionIsoFactory_hom (C := (Proj PS).Modules) (D := U.toScheme.Modules)
    (E := (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules) P
    (Scheme.Modules.pullbackComp e.inv U.ι)
    (Scheme.Modules.restrictFunctorIsoPullback U.ι) (positiveSheafOfModules PS m)

private theorem nativeRestrictionIso_formula (j : Fin 4) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    actualPositiveNativeChartRestrictionIso (K := K) j =
      (Scheme.Modules.pullbackComp e.inv U.ι).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
          (Scheme.Modules.pullback e.inv) := rfl

private theorem nativeRestrictionUnit_hom (j : Fin 4) (m : ℕ) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let M := positiveSheafOfModules PS m
    (actualPositiveNativeChartRestrictionIso (K := K) j).hom.app M =
      (Scheme.Modules.pullbackComp e.inv U.ι).inv.app M ≫
        (Scheme.Modules.pullback e.inv).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M) := by
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  let M := positiveSheafOfModules PS m
  let Q := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let R := Scheme.Modules.restrictFunctor U.ι
  have hf := nativeRestrictionHomFactoryResult (K := K) j m
  have hi := nativeRestrictionIso_formula (K := K) j
  have hh : (actualPositiveNativeChartRestrictionIso (K := K) j).hom.app M =
      ((Scheme.Modules.pullbackComp e.inv U.ι).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm P).hom.app M :=
    congrArg (fun E : Q ≅ R ⋙ P => E.hom.app M) hi
  exact hh.trans hf

private theorem originalNativePositiveUnit_hom (j : Fin 4) (m : ℕ) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let M := positiveSheafOfModules PS m
    (actualAmbientPositiveNativeChartUnitIso (K := K) j m).hom =
      (Scheme.Modules.pullbackComp e.inv U.ι).inv.app M ≫
        (Scheme.Modules.pullback e.inv).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M ≫
            (p3PositiveTwistOpenIsoUnit K U j le_rfl m).hom) ≫
        pullbackUnitComparison e.inv := by
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  let M := positiveSheafOfModules PS m
  let v := pullbackUnitComparison e.inv
  letI : IsIso v := isIso_pullbackUnitComparison e.inv
  have h := positiveIsoFactory_hom (C := (Proj PS).Modules)
    (D := U.toScheme.Modules)
    (E := (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules) P
    (Scheme.Modules.pullbackComp e.inv U.ι)
    (Scheme.Modules.restrictFunctorIsoPullback U.ι) M
    (p3PositiveTwistOpenIsoUnit K U j le_rfl m) v
  exact h

private theorem nativePositiveUnit_mappedComposition (j : Fin 4) (m : ℕ) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let P := Scheme.Modules.pullback e.inv
    let M := positiveSheafOfModules PS m
    (Scheme.Modules.pullbackComp e.inv U.ι).inv.app M ≫
      P.map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M ≫
        (p3PositiveTwistOpenIsoUnit K U j le_rfl m).hom) ≫
      pullbackUnitComparison e.inv =
    ((Scheme.Modules.pullbackComp e.inv U.ι).inv.app M ≫
      P.map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M)) ≫
      P.map (p3PositiveTwistOpenIsoUnit K U j le_rfl m).hom ≫
      pullbackUnitComparison e.inv := by
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  let M := positiveSheafOfModules PS m
  have h := mappedComp_with_outerMaps (C := U.toScheme.Modules)
    (D := (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules) P
    ((Scheme.Modules.pullbackComp e.inv U.ι).inv.app M)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M)
    (p3PositiveTwistOpenIsoUnit K U j le_rfl m).hom (pullbackUnitComparison e.inv)
  exact h

/-- The positive native unit frame is the SAME canonical composite.
This is an equality of its actual maps, not a supplied frame certificate. -/
theorem actualAmbientPositiveNativeChartUnitIso_restriction_hom
    (j : Fin 4) (m : ℕ) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    (actualAmbientPositiveNativeChartUnitIso (K := K) j m).hom =
      (actualPositiveNativeChartRestrictionIso (K := K) j).hom.app
        (positiveSheafOfModules PS m) ≫
      (Scheme.Modules.pullback e.inv).map
        (p3PositiveTwistOpenIsoUnit K U j le_rfl m).hom ≫
      (actualCanonicalPullbackUnitIso e.inv).hom := by
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  let M := positiveSheafOfModules PS m
  let n := (actualPositiveNativeChartRestrictionIso (K := K) j).hom.app M
  let a := (Scheme.Modules.pullbackComp e.inv U.ι).inv.app M
  let f := (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M
  let b := (p3PositiveTwistOpenIsoUnit K U j le_rfl m).hom
  let c := (actualCanonicalPullbackUnitIso e.inv).hom
  let u := pullbackUnitComparison e.inv
  have hframe := originalNativePositiveUnit_hom (K := K) j m
  have hcomposition := nativePositiveUnit_mappedComposition (K := K) j m
  have hn : n = a ≫ P.map f := nativeRestrictionUnit_hom (K := K) j m
  have hc : c = u := canonicalPullbackUnit_hom e.inv
  have hright : (a ≫ P.map f) ≫ P.map b ≫ u = n ≫ P.map b ≫ c :=
    (congrArg (fun z => z ≫ P.map b ≫ u) hn.symm).trans
      (congrArg (fun z => n ≫ P.map b ≫ z) hc.symm)
  exact hframe.trans (hcomposition.trans hright)

/-- A canonical native frame of the original finite positive coproduct.
It uses the actual restriction and pullback comparisons; no carrier or
scalar action is transported. -/
def actualPositiveNativeWholeGeneratorFrame
    {ι : Type u} [Fintype ι] (j : Fin 4) (d : ι → ℕ) (m : ℕ) :
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
        (∐ fun i => positiveSheafOfModules PS (m - d i)) ≅
    (∐ fun _ : ι => SheafOfModules.unit
      (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) := by
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  exact (actualPositiveNativeChartRestrictionIso (K := K) j).app _ ≪≫
    (Scheme.Modules.pullback e.inv).mapIso
      (actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl d m) ≪≫
    actualCanonicalPullbackUnitCoproductIso e.inv ι

private theorem naturalFrame_conjugation
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ E) (R : C ⥤ D) (P : D ⥤ E) (n : Q ≅ R ⋙ P)
    {M N : C} {M' N' : D} {M'' N'' : E}
    (a : R.obj M ≅ M') (b : R.obj N ≅ N')
    (u : P.obj M' ≅ M'') (v : P.obj N' ≅ N'')
    (f : M ⟶ N) (g : M' ⟶ N')
    (h : a.inv ≫ R.map f ≫ b.hom = g) :
    (n.app M ≪≫ P.mapIso a ≪≫ u).inv ≫ Q.map f ≫
      (n.app N ≪≫ P.mapIso b ≪≫ v).hom = u.inv ≫ P.map g ≫ v.hom := by
  have hn : (n.app M).inv ≫ Q.map f ≫ (n.app N).hom = P.map (R.map f) := by
    calc
      _ = (n.app M).inv ≫ (Q.map f ≫ (n.app N).hom) := rfl
      _ = (n.app M).inv ≫ ((n.app M).hom ≫ P.map (R.map f)) :=
        congrArg (fun k => (n.app M).inv ≫ k) (n.hom.naturality f)
      _ = _ := (n.app M).inv_hom_id_assoc _
  calc
    _ = u.inv ≫ P.map a.inv ≫
        ((n.app M).inv ≫ Q.map f ≫ (n.app N).hom) ≫ P.map b.hom ≫ v.hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Category.assoc]
    _ = u.inv ≫ P.map a.inv ≫ P.map (R.map f) ≫ P.map b.hom ≫ v.hom :=
      congrArg (fun k => u.inv ≫ P.map a.inv ≫ k ≫ P.map b.hom ≫ v.hom) hn
    _ = u.inv ≫ P.map (a.inv ≫ R.map f ≫ b.hom) ≫ v.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := congrArg (fun k => u.inv ≫ P.map k ≫ v.hom) h

/-- The whole OWN native chart generator has the literal normalized matrix.
The source is the original coproduct and the target is its existing positive
native unit frame, including the original positive-degree casts. -/
theorem actualPositiveFiniteGeneratorMap_nativeWholeMatrix
    {ι : Type u} [Fintype ι] (g : ι → PolyA) (d : ι → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (hm : ∀ i, d i ≤ m) (j : Fin 4) :
    (actualPositiveNativeWholeGeneratorFrame (K := K) j d m).inv ≫
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
          (actualPositiveFiniteGeneratorMap g d hg m hm) ≫
      (actualAmbientPositiveNativeChartUnitIso (K := K) j m).hom =
      actualNormalizedSpecUnitGeneratorMatrix j g := by
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let Q := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let R := Scheme.Modules.restrictFunctor U.ι
  let P := Scheme.Modules.pullback e.inv
  let n := actualPositiveNativeChartRestrictionIso (K := K) j
  let a := actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl d m
  let b := p3PositiveTwistOpenIsoUnit K U j le_rfl m
  let u := actualCanonicalPullbackUnitCoproductIso e.inv ι
  let v := actualCanonicalPullbackUnitIso e.inv
  let G := actualPositiveFiniteGeneratorMap g d hg m hm
  have h := naturalFrame_conjugation Q R P n a b u v G
    (actualRestrictedPositiveUnitGeneratorMatrix j U le_rfl g)
    (actualPositiveFiniteGeneratorMap_restrictedWholeMatrix g d hg m hm j U le_rfl)
  have ht : (actualAmbientPositiveNativeChartUnitIso (K := K) j m).hom =
      (n.app (positiveSheafOfModules PS m) ≪≫ P.mapIso b ≪≫ v).hom :=
    actualAmbientPositiveNativeChartUnitIso_restriction_hom j m
  have h₁ : (actualPositiveNativeWholeGeneratorFrame (K := K) j d m).inv ≫
      Q.map G ≫ (actualAmbientPositiveNativeChartUnitIso (K := K) j m).hom =
      (n.app _ ≪≫ P.mapIso a ≪≫ u).inv ≫ Q.map G ≫
        (n.app _ ≪≫ P.mapIso b ≪≫ v).hom :=
    congrArg (fun k => (actualPositiveNativeWholeGeneratorFrame (K := K) j d m).inv ≫
      Q.map G ≫ k) ht
  exact h₁.trans (h.trans (actualRestrictedPositiveUnitGeneratorMatrix_basicOpenPullback j g))

end PfaffianDescent.Coray
