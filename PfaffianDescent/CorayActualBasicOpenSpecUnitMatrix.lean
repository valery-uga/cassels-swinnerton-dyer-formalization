import PfaffianDescent.CorayActualNormalizedSpecUnitMatrixExact

/-! The canonical actual basic-open/Spec pullback of the WHOLE unit matrices.
No comparison or exactness premise is supplied. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Canonical unit comparison, with its actual inverse derived internally. -/
def actualCanonicalPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : IsIso (pullbackUnitComparison f) := isIso_pullbackUnitComparison f
  exact asIso (pullbackUnitComparison f)

/-- Canonical pullback comparison on the OWN finite coproduct of units. -/
def actualCanonicalPullbackUnitCoproductIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ι : Type u) [Fintype ι] :
    (Scheme.Modules.pullback f).obj (∐ fun _ : ι => SheafOfModules.unit Y.ringCatSheaf) ≅
      (∐ fun _ : ι => SheafOfModules.unit X.ringCatSheaf) :=
  PreservesCoproduct.iso (Scheme.Modules.pullback f)
    (fun _ : ι => SheafOfModules.unit Y.ringCatSheaf) ≪≫
      Sigma.mapIso (fun _ => actualCanonicalPullbackUnitIso f)

private theorem canonicalUnitInverse_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (actualCanonicalPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (actualCanonicalPullbackUnitIso f).hom =
    pullbackUnitEndomorphism f (isIso_pullbackUnitComparison f) a := by
  let h := isIso_pullbackUnitComparison f
  letI : IsIso (pullbackUnitComparison f) := h
  have hc : Classical.choose h.out = inv (pullbackUnitComparison f) := by congr 1
  change inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map a ≫
    pullbackUnitComparison f =
    Classical.choose h.out ≫ (Scheme.Modules.pullback f).map a ≫ pullbackUnitComparison f
  exact congrArg (fun k => k ≫ (Scheme.Modules.pullback f).map a ≫
    pullbackUnitComparison f) hc.symm

private theorem actualBasicOpenCanonicalUnit_scalar
    (j : Fin 4) (p : A) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    (actualCanonicalPullbackUnitIso e.inv).inv ≫
      (Scheme.Modules.pullback e.inv).map (unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl p))) ≫
      (actualCanonicalPullbackUnitIso e.inv).hom =
    unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).inv.hom
        (ambientChartEvaluation j p)) := by
  dsimp only
  exact (canonicalUnitInverse_scalar _ _).trans
    (actualBasicOpenIsoSpec_pullback_normalizedUnitEndomorphism j p)

@[reassoc]
private lemma coproductFrame_inv_component
    {C D : Type*} [Category C] [Category D] {ι : Type u}
    (F : C ⥤ D) (f : ι → C) (g : ι → D)
    [HasCoproduct f] [HasCoproductsOfShape ι D]
    [PreservesColimit (Discrete.functor f) F]
    (e : ∀ i, F.obj (f i) ≅ g i) (i : ι) :
    Sigma.ι g i ≫ (PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e).inv =
      (e i).inv ≫ F.map (Sigma.ι f i) := by
  change Sigma.ι g i ≫ (Sigma.mapIso e).inv ≫ (PreservesCoproduct.iso F f).inv = _
  rw [PreservesCoproduct.inv_hom]
  calc
    _ = (Sigma.ι g i ≫ (Sigma.mapIso e).inv) ≫ sigmaComparison F f :=
      (Category.assoc _ _ _).symm
    _ = ((e i).inv ≫ Sigma.ι (fun i => F.obj (f i)) i) ≫ sigmaComparison F f :=
      congrArg (fun k => k ≫ sigmaComparison F f) (Sigma.ι_mapIso_inv e i)
    _ = (e i).inv ≫ (Sigma.ι (fun i => F.obj (f i)) i ≫ sigmaComparison F f) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun k => (e i).inv ≫ k) (ι_comp_sigmaComparison F f i)

private lemma coproductFrame_hom_component
    {C D : Type*} [Category C] [Category D] {ι : Type u}
    (F : C ⥤ D) (f : ι → C) (g : ι → D)
    [HasCoproduct f] [HasCoproductsOfShape ι D]
    [PreservesColimit (Discrete.functor f) F]
    (e : ∀ i, F.obj (f i) ≅ g i) (i : ι) :
    F.map (Sigma.ι f i) ≫ (PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e).hom =
      (e i).hom ≫ Sigma.ι g i := by
  let E := PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e
  have h := coproductFrame_inv_component F f g e i
  have hi : ((e i).hom ≫ Sigma.ι g i) ≫ E.inv = F.map (Sigma.ι f i) := by
    calc
      _ = (e i).hom ≫ (Sigma.ι g i ≫ E.inv) := Category.assoc _ _ _
      _ = (e i).hom ≫ (e i).inv ≫ F.map (Sigma.ι f i) :=
        congrArg (fun k => (e i).hom ≫ k) h
      _ = _ := (e i).hom_inv_id_assoc _
  exact ((Iso.comp_inv_eq E).mp hi).symm

private lemma coproductFrame_column
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {ι : Type u} [Fintype ι]
    (F : C ⥤ D) [F.Additive] (f : ι → C) (g : ι → D)
    [HasCoproduct f] [HasCoproductsOfShape ι D]
    [PreservesColimit (Discrete.functor f) F]
    (e : ∀ i, F.obj (f i) ≅ g i) {M : C} {N : D}
    (ea : F.obj M ≅ N) (r : ∀ i, M ⟶ f i) :
    ea.inv ≫ F.map (∑ i, r i ≫ Sigma.ι f i) ≫
        (PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e).hom =
      ∑ i, (ea.inv ≫ F.map (r i) ≫ (e i).hom) ≫ Sigma.ι g i := by
  simp only [Functor.map_sum, Functor.map_comp, Preadditive.sum_comp,
    Preadditive.comp_sum, Category.assoc]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coproductFrame_hom_component F f g e i]

private lemma mappedFrame_component
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {V W T : C} {M₀ M₁ M₂ : D}
    (a : M₀ ⟶ M₁) (e : M₁ ⟶ F.obj V)
    (t : M₀ ⟶ F.obj W) (v : F.obj T ⟶ M₂)
    (f : W ⟶ V) (g : V ⟶ T) (k : W ⟶ T)
    (hframe : a ≫ e = t ≫ F.map f) (hfg : f ≫ g = k) :
    a ≫ e ≫ F.map g ≫ v = t ≫ F.map k ≫ v := by
  calc
    _ = (a ≫ e) ≫ F.map g ≫ v := (Category.assoc a e (F.map g ≫ v)).symm
    _ = (t ≫ F.map f) ≫ F.map g ≫ v :=
      congrArg (fun z => z ≫ F.map g ≫ v) hframe
    _ = t ≫ F.map (f ≫ g) ≫ v := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := congrArg (fun z => t ≫ F.map z ≫ v) hfg

/-- Canonical actual basic-open pullback of the whole generator matrix is
EXACTLY the native Spec-unit generator matrix with the SAME coefficients. -/
theorem actualRestrictedPositiveUnitGeneratorMatrix_basicOpenPullback
    {ι : Type u} [Fintype ι] (j : Fin 4) (g : ι → A) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    (actualCanonicalPullbackUnitCoproductIso e.inv ι).inv ≫
      (Scheme.Modules.pullback e.inv).map
        (actualRestrictedPositiveUnitGeneratorMatrix j U le_rfl g) ≫
      (actualCanonicalPullbackUnitIso e.inv).hom =
      actualNormalizedSpecUnitGeneratorMatrix j g := by
  classical
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let R := CommRingCat.of (HomogeneousLocalization.Away PS (X j))
  let P := Scheme.Modules.pullback e.inv
  let O : U.toScheme.Modules := SheafOfModules.unit U.toScheme.ringCatSheaf
  let O' : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let family : ι → U.toScheme.Modules := fun _ => O
  let family' : ι → (Spec R).Modules := fun _ => O'
  let u := actualCanonicalPullbackUnitIso e.inv
  let E := actualCanonicalPullbackUnitCoproductIso e.inv ι
  let c : ι → (O ⟶ O) := fun i => unitEndomorphismOfRegularFunction
    (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl (g i)))
  let c' : ι → (O' ⟶ O') := fun i => unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso R).inv.hom (ambientChartEvaluation j (g i)))
  let G := actualRestrictedPositiveUnitGeneratorMatrix j U le_rfl g
  apply Sigma.hom_ext
  intro i
  have hframe : Sigma.ι family' i ≫ E.inv = u.inv ≫ P.map (Sigma.ι family i) :=
    coproductFrame_inv_component (C := U.toScheme.Modules) (D := (Spec R).Modules)
      P family family' (fun _ => u) i
  have hdesc : Sigma.ι family i ≫ G = c i := Sigma.ι_desc c i
  have hcomponent := mappedFrame_component
    (C := U.toScheme.Modules) (D := (Spec R).Modules) P
    (Sigma.ι family' i) E.inv u.inv u.hom (Sigma.ι family i) G (c i) hframe hdesc
  have hscalar : u.inv ≫ P.map (c i) ≫ u.hom = c' i :=
    actualBasicOpenCanonicalUnit_scalar j (g i)
  have htarget : Sigma.ι family' i ≫ actualNormalizedSpecUnitGeneratorMatrix j g = c' i :=
    Sigma.ι_desc c' i
  exact hcomponent.trans (hscalar.trans htarget.symm)

private theorem canonicalUnitColumn
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} [Fintype ι]
    (a : ι → (SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)) :
    letI : Preadditive Y.Modules :=
      inferInstanceAs (Preadditive (SheafOfModules.{u} Y.ringCatSheaf))
    letI : Preadditive X.Modules :=
      inferInstanceAs (Preadditive (SheafOfModules.{u} X.ringCatSheaf))
    let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let familyY : ι → Y.Modules := fun _ => OY
    let familyX : ι → X.Modules := fun _ => OX
    letI : AddCommGroup (OY ⟶ ∐ familyY) :=
      @Preadditive.homGroup Y.Modules (inferInstance : Category Y.Modules)
        (inferInstance : Preadditive Y.Modules) OY (∐ familyY)
    letI : AddCommGroup (OX ⟶ ∐ familyX) :=
      @Preadditive.homGroup X.Modules (inferInstance : Category X.Modules)
        (inferInstance : Preadditive X.Modules) OX (∐ familyX)
    (actualCanonicalPullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (∑ i,
        (show OY ⟶ ∐ familyY from a i ≫ Sigma.ι familyY i)) ≫
      (actualCanonicalPullbackUnitCoproductIso f ι).hom =
    ∑ i, (show OX ⟶ ∐ familyX from ((actualCanonicalPullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (a i) ≫ (actualCanonicalPullbackUnitIso f).hom) ≫
      Sigma.ι familyX i) := by
  dsimp only
  let P := Scheme.Modules.pullback f
  letI : Preadditive Y.Modules :=
    inferInstanceAs (Preadditive (SheafOfModules.{u} Y.ringCatSheaf))
  letI : Preadditive X.Modules :=
    inferInstanceAs (Preadditive (SheafOfModules.{u} X.ringCatSheaf))
  letI : P.IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction f).isLeftAdjoint
  letI : PreservesBinaryBiproducts P :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts P
  letI : P.Additive := CategoryTheory.Functor.additive_of_preservesBinaryBiproducts P
  exact coproductFrame_column (C := Y.Modules) (D := X.Modules) P
    (fun _ : ι => SheafOfModules.unit Y.ringCatSheaf)
    (fun _ : ι => SheafOfModules.unit X.ringCatSheaf)
    (fun _ => actualCanonicalPullbackUnitIso f) (actualCanonicalPullbackUnitIso f) a

private theorem basicOpenUnitInverse_component
    {κ : Type u} [Fintype κ] (j : Fin 4) (a : κ) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    Sigma.ι (fun _ : κ => SheafOfModules.unit
      (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) a ≫
        (actualCanonicalPullbackUnitCoproductIso e.inv κ).inv =
    (actualCanonicalPullbackUnitIso e.inv).inv ≫
      (Scheme.Modules.pullback e.inv).map
        (Sigma.ι (fun _ : κ => SheafOfModules.unit U.toScheme.ringCatSheaf) a) := by
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  exact coproductFrame_inv_component (C := U.toScheme.Modules)
    (D := (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules)
    (Scheme.Modules.pullback e.inv)
    (fun _ : κ => SheafOfModules.unit U.toScheme.ringCatSheaf)
    (fun _ : κ => SheafOfModules.unit
      (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)
    (fun _ => actualCanonicalPullbackUnitIso e.inv) a

private theorem basicOpenUnitColumn
    {ι : Type u} [Fintype ι] (j : Fin 4) (r : ι → A) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let R := CommRingCat.of (HomogeneousLocalization.Away PS (X j))
    letI : Preadditive U.toScheme.Modules :=
      inferInstanceAs (Preadditive (SheafOfModules.{u} U.toScheme.ringCatSheaf))
    letI : Preadditive (Spec R).Modules :=
      inferInstanceAs (Preadditive (SheafOfModules.{u} (Spec R).ringCatSheaf))
    let O : U.toScheme.Modules := SheafOfModules.unit U.toScheme.ringCatSheaf
    let O' : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
    let family : ι → U.toScheme.Modules := fun _ => O
    let family' : ι → (Spec R).Modules := fun _ => O'
    letI : AddCommGroup (O ⟶ ∐ family) :=
      @Preadditive.homGroup U.toScheme.Modules (inferInstance : Category U.toScheme.Modules)
        (inferInstance : Preadditive U.toScheme.Modules) O (∐ family)
    letI : AddCommGroup (O' ⟶ ∐ family') :=
      @Preadditive.homGroup (Spec R).Modules (inferInstance : Category (Spec R).Modules)
        (inferInstance : Preadditive (Spec R).Modules) O' (∐ family')
    (actualCanonicalPullbackUnitIso e.inv).inv ≫
      (Scheme.Modules.pullback e.inv).map (∑ i, (show O ⟶ ∐ family from
        unitEndomorphismOfRegularFunction
          (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl (r i))) ≫
          Sigma.ι family i)) ≫
      (actualCanonicalPullbackUnitCoproductIso e.inv ι).hom =
    ∑ i, (show O' ⟶ ∐ family' from unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso R).inv.hom (ambientChartEvaluation j (r i))) ≫
      Sigma.ι family' i) := by
  classical
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let R := CommRingCat.of (HomogeneousLocalization.Away PS (X j))
  let O : U.toScheme.Modules := SheafOfModules.unit U.toScheme.ringCatSheaf
  let O' : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let family' : ι → (Spec R).Modules := fun _ => O'
  let c : ι → (O ⟶ O) := fun i => unitEndomorphismOfRegularFunction
    (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl (r i)))
  have h := canonicalUnitColumn e.inv c
  letI : Preadditive (Spec R).Modules :=
    inferInstanceAs (Preadditive (SheafOfModules.{u} (Spec R).ringCatSheaf))
  letI : AddCommGroup (O' ⟶ ∐ family') :=
    @Preadditive.homGroup (Spec R).Modules (inferInstance : Category (Spec R).Modules)
      (inferInstance : Preadditive (Spec R).Modules) O' (∐ family')
  have hs : (∑ i, (show O' ⟶ ∐ family' from
      ((actualCanonicalPullbackUnitIso e.inv).inv ≫
      (Scheme.Modules.pullback e.inv).map (c i) ≫
      (actualCanonicalPullbackUnitIso e.inv).hom) ≫ Sigma.ι family' i)) =
      ∑ i, (show O' ⟶ ∐ family' from unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso R).inv.hom (ambientChartEvaluation j (r i))) ≫ Sigma.ι family' i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z : O' ⟶ O' => z ≫ Sigma.ι family' i)
      (actualBasicOpenCanonicalUnit_scalar j (r i))
  exact h.trans hs

private lemma coproductDesc_conjugation
    {C D : Type*} [Category C] [Category D] {κ : Type u}
    (F : C ⥤ D) (f : κ → C) (g : κ → D) [HasCoproduct f] [HasCoproduct g]
    {V : C} {W : D} (E : F.obj (∐ f) ≅ ∐ g) (u : F.obj V ⟶ W)
    (ei : ∀ a, g a ⟶ F.obj (f a)) (c : ∀ a, f a ⟶ V) (d : ∀ a, g a ⟶ W)
    (hframe : ∀ a, Sigma.ι g a ≫ E.inv = ei a ≫ F.map (Sigma.ι f a))
    (hcolumn : ∀ a, ei a ≫ F.map (c a) ≫ u = d a) :
    E.inv ≫ F.map (Sigma.desc c) ≫ u = Sigma.desc d := by
  apply Sigma.hom_ext
  intro a
  have hc := mappedFrame_component F (Sigma.ι g a) E.inv (ei a) u
    (Sigma.ι f a) (Sigma.desc c) (c a) (hframe a) (Sigma.ι_desc c a)
  exact hc.trans ((hcolumn a).trans (Sigma.ι_desc d a).symm)

/-- Canonical actual basic-open pullback of the WHOLE relation matrix is
EXACTLY the native Spec-unit matrix, entry by entry and column by column. -/
theorem actualRestrictedPositiveUnitRelationMatrix_basicOpenPullback
    {ι κ : Type u} [Fintype ι] [Fintype κ] (j : Fin 4) (r : κ → ι → A) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    (actualCanonicalPullbackUnitCoproductIso e.inv κ).inv ≫
      (Scheme.Modules.pullback e.inv).map
        (actualRestrictedPositiveUnitRelationMatrix j U le_rfl r) ≫
      (actualCanonicalPullbackUnitCoproductIso e.inv ι).hom =
      actualNormalizedSpecUnitRelationMatrix j r := by
  classical
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let R := CommRingCat.of (HomogeneousLocalization.Away PS (X j))
  let P := Scheme.Modules.pullback e.inv
  letI : Preadditive U.toScheme.Modules :=
    inferInstanceAs (Preadditive (SheafOfModules.{u} U.toScheme.ringCatSheaf))
  letI : Preadditive (Spec R).Modules :=
    inferInstanceAs (Preadditive (SheafOfModules.{u} (Spec R).ringCatSheaf))
  let O : U.toScheme.Modules := SheafOfModules.unit U.toScheme.ringCatSheaf
  let O' : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let sourceFamily : κ → U.toScheme.Modules := fun _ => O
  let sourceFamily' : κ → (Spec R).Modules := fun _ => O'
  let family : ι → U.toScheme.Modules := fun _ => O
  let family' : ι → (Spec R).Modules := fun _ => O'
  let c : κ → (O ⟶ ∐ family) := fun a => ∑ i, unitEndomorphismOfRegularFunction
    (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl (r a i))) ≫
    Sigma.ι family i
  let c' : κ → (O' ⟶ ∐ family') := fun a => ∑ i, unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso R).inv.hom (ambientChartEvaluation j (r a i))) ≫ Sigma.ι family' i
  exact coproductDesc_conjugation (C := U.toScheme.Modules) (D := (Spec R).Modules)
    P sourceFamily sourceFamily' (actualCanonicalPullbackUnitCoproductIso e.inv κ)
    (actualCanonicalPullbackUnitCoproductIso e.inv ι).hom
    (fun _ => (actualCanonicalPullbackUnitIso e.inv).inv) c c'
    (fun a => basicOpenUnitInverse_component j a)
    (fun a => basicOpenUnitColumn j (r a))

end PfaffianDescent.Coray
