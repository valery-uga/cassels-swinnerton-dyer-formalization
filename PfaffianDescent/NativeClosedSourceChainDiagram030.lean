import PfaffianDescent.NativeCanonicalIdealInclusionFactory013

/- The whole ORIGINAL three-arrow diagram is formed at an abstract Scheme.
There is no ring, quotient ring, Spec, tilde or surjective-map substitution here. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u

/-- Rebuild only the native Scheme.Modules Iso dictionary at abstract sheaf
objects. All map fields are the ORIGINAL raw Iso fields. No image objects yet. -/
def nativeRawModuleIsoToOwn031
    {X : Scheme.{u}} {M N : SheafOfModules X.ringCatSheaf} (q : M ≅ N) :
    @Iso X.Modules (inferInstance : Category X.Modules) M N where
  hom := q.hom
  inv := q.inv
  hom_inv_id := q.hom_inv_id
  inv_hom_id := q.inv_hom_id

/-- WHOLE Iso identity, proved before any original SourceIso or ideal image is inserted. -/
theorem nativeRawModuleIsoToOwn_original031
    {X : Scheme.{u}} {M N : SheafOfModules X.ringCatSheaf} (q : M ≅ N) :
    nativeRawModuleIsoToOwn031 q = q := rfl

/-- Coherent native Iso+inverse-law data at ABSTRACT objects. The raw inverse law
is converted together with the map, before a closed-immersion image is substituted. -/
def nativeRawModuleIsoInverseData031
    {X : Scheme.{u}} {M N U : SheafOfModules X.ringCatSheaf}
    (q : M ≅ N) (v : M ⟶ U) (w : N ⟶ U) (h : q.inv ≫ v = w) :
    {r : @Iso X.Modules (inferInstance : Category X.Modules) M N //
      @CategoryStruct.comp X.Modules
        (inferInstance : Category X.Modules).toCategoryStruct N M U r.inv v = w} :=
  ⟨nativeRawModuleIsoToOwn031 q, h⟩

/-- Capture the ORIGINAL source Iso and its ACCEPTED RAW inverse law in ONE
native dictionary producer, with kernel-image object arguments fixed together. -/
def nativeOriginalSourceOwnInverseData031
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :=
  nativeRawModuleIsoInverseData031 (X := X)
    (M := idealModule (e.hom ≫ i).ker) (N := idealModule i.ker)
    (U := SheafOfModules.unit X.ringCatSheaf)
    (closedImmersionModuleSourceIso e i)
    (closedImmersionModuleToUnit (e.hom ≫ i))
    (closedImmersionModuleToUnit i)
    (nativeClosedImmersionSourceInverseRawSquare013 e i)

/-- The source producer inherits the VERIFIED generic WHOLE Iso identity.
Inferred output avoids duplicating an independently elaborated concrete target. -/
def nativeOriginalSourceOwnInverseData_original031
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :=
  @nativeRawModuleIsoToOwn_original031 X
    (idealModule (e.hom ≫ i).ker) (idealModule i.ker)
    (closedImmersionModuleSourceIso e i)

/-- Equality Iso and its inclusion law created together at abstract category/index data. -/
def nativeEqualityIsoInclusionData033
    {C : Type*} [Category C] {D : Type*} {U : C}
    (F : D → C) (v : ∀ d, F d ⟶ U) {d e : D} (h : d = e) :
    {c : F d ≅ F e // c.hom ≫ v e = v d} := by
  cases h
  exact ⟨eqToIso (congrArg F rfl), Category.id_comp (v d)⟩

theorem nativeEqualityIsoInclusionData_original033
    {C : Type*} [Category C] {D : Type*} {U : C}
    (F : D → C) (v : ∀ d, F d ⟶ U) {d e : D} (h : d = e) :
    (nativeEqualityIsoInclusionData033 F v h).val = eqToIso (congrArg F h) := by
  cases h
  rfl

/-- Original equality Scheme maps give the SAME native equality Iso and its own law. -/
def nativeOriginalEqualityIsoInclusionData033
    {X Z : Scheme.{u}} (f g : Z ⟶ X) (h : f = g) :=
  nativeEqualityIsoInclusionData033 (C := X.Modules)
    (D := Z ⟶ X) (U := SheafOfModules.unit X.ringCatSheaf)
    closedImmersionModule closedImmersionModuleToUnit h

def nativeOriginalEqualityIsoInclusionData_original033
    {X Z : Scheme.{u}} (f g : Z ⟶ X) (h : f = g) :=
  nativeEqualityIsoInclusionData_original033 (C := X.Modules)
    (D := Z ⟶ X) (U := SheafOfModules.unit X.ringCatSheaf)
    closedImmersionModule closedImmersionModuleToUnit h

/-- View the VARIABLE first Iso at its literal ideal-image target before any
original source data or Spec quotient is substituted. Its maps are unchanged. -/
def nativeFirstInputIdealView035
    {X Z' : Scheme.{u}} {M : X.Modules} (i : Z' ⟶ X)
    (a : M ≅ closedImmersionModule i) :
    @Iso X.Modules (inferInstance : Category X.Modules) M (idealModule i.ker) := a

/-- The target annotation changes no original Iso value. -/
theorem nativeFirstInputIdealView_original035
    {X Z' : Scheme.{u}} {M : X.Modules} (i : Z' ⟶ X)
    (a : M ≅ closedImmersionModule i) :
    nativeFirstInputIdealView035 i a = a := rfl

/-- DIAGNOSTIC first factory argument: no source/equality Iso or inclusion law supplied. -/
private def nativeFirstIsoFactorySlot033
    {X Z' : Scheme.{u}} {M D E U : X.Modules} (i : Z' ⟶ X)
    (a : @Iso X.Modules (inferInstance : Category X.Modules) M (idealModule i.ker)) :=
  canonicalIsoChainInclusionData013 (C := X.Modules) (A := M) (B := idealModule i.ker) (D := D) (E := E) (U := U) a

/-- DIAGNOSTIC source Iso slot: only the checked coherent native value is added. -/
private def nativeSourceIsoFactorySlot033
    {X Z Z' : Scheme.{u}} {M E U : X.Modules} (e : Z ≅ Z') (i : Z' ⟶ X)
    (a : @Iso X.Modules (inferInstance : Category X.Modules) M (idealModule i.ker)) :=
  nativeFirstIsoFactorySlot033 (D := idealModule (e.hom ≫ i).ker) (E := E) (U := U)
    i a (nativeOriginalSourceOwnInverseData031 e i).val

/-- DIAGNOSTIC equality Iso slot: the paired native equality value is added. -/
private def nativeEqualityIsoFactorySlot033
    {X Z Z' : Scheme.{u}} {M U : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : @Iso X.Modules (inferInstance : Category X.Modules) M (idealModule i.ker)) :=
  nativeSourceIsoFactorySlot033 (E := closedImmersionModule f) (U := U) e i a
    (nativeOriginalEqualityIsoInclusionData033 (e.hom ≫ i) f he).val

/-- DIAGNOSTIC inclusion-map slots: no law argument is supplied yet. -/
private def nativeInclusionMapsFactorySlot033
    {X Z Z' : Scheme.{u}} {M : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : @Iso X.Modules (inferInstance : Category X.Modules) M (idealModule i.ker))
    (w : M ⟶ SheafOfModules.unit X.ringCatSheaf) :=
  nativeEqualityIsoFactorySlot033 (U := SheafOfModules.unit X.ringCatSheaf) e i f he a
    (closedImmersionModuleToUnit i)
    (closedImmersionModuleToUnit (e.hom ≫ i))
    (closedImmersionModuleToUnit f) w

/-- DIAGNOSTIC first inclusion-law slot; source/equality laws remain curried. -/
private def nativeFirstLawFactorySlot033
    {X Z Z' : Scheme.{u}} {M : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : @Iso X.Modules (inferInstance : Category X.Modules) M (idealModule i.ker))
    (w : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ha : a.hom ≫ closedImmersionModuleToUnit i = w) :=
  nativeInclusionMapsFactorySlot033 e i f he a w ha

/-- DIAGNOSTIC source-law slot, supplied by the SAME coherent native source data. -/
private def nativeSourceLawFactorySlot033
    {X Z Z' : Scheme.{u}} {M : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : @Iso X.Modules (inferInstance : Category X.Modules) M (idealModule i.ker))
    (w : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ha : a.hom ≫ closedImmersionModuleToUnit i = w) :=
  nativeFirstLawFactorySlot033 e i f he a w ha
    (nativeOriginalSourceOwnInverseData031 e i).property

/-- The checked categorical factory has the literal original chain as its value.
This identity is proved at arbitrary category objects, before ideal images. -/
theorem nativeCanonicalIsoChainFactoryValue036
    {C : Type*} [Category C] {A B D E U : C}
    (a : A ≅ B) (b : D ≅ B) (c : D ≅ E)
    (vB : B ⟶ U) (vD : D ⟶ U) (vE : E ⟶ U) (w : A ⟶ U)
    (ha : a.hom ≫ vB = w) (hb : b.inv ≫ vD = vB)
    (hc : c.hom ≫ vE = vD) :
    (canonicalIsoChainInclusionData013 a b c vB vD vE w ha hb hc).val =
      a ≪≫ b.symm ≪≫ c := rfl

/-- Replace three equal original Iso values at FIXED category objects.
There is no original Scheme dictionary or ideal image in this proof. -/
theorem nativeIsoChainOriginalValue036
    {C : Type*} [Category C] {A B D E : C}
    (a a' : A ≅ B) (b b' : D ≅ B) (c c' : D ≅ E)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    a ≪≫ b.symm ≪≫ c = a' ≪≫ b'.symm ≪≫ c' := by
  cases ha
  cases hb
  cases hc
  rfl

/-- Infer the original-chain equality ONLY after every object and original
value substitution is explicit. No diagram-law proof is inspected here. -/
private def nativeOriginalChainValueIdentity036
    {X Z Z' : Scheme.{u}} {M : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : M ≅ closedImmersionModule i) :=
  @nativeIsoChainOriginalValue036 X.Modules (inferInstance : Category X.Modules)
    M (idealModule i.ker) (idealModule (e.hom ≫ i).ker) (closedImmersionModule f)
    (nativeFirstInputIdealView035 i a) a
    (nativeOriginalSourceOwnInverseData031 e i).val (closedImmersionModuleSourceIso e i)
    (nativeOriginalEqualityIsoInclusionData033 (e.hom ≫ i) f he).val
      (eqToIso (congrArg closedImmersionModule he))
    (nativeFirstInputIdealView_original035 i a)
    (nativeOriginalSourceOwnInverseData_original031 e i)
    (nativeOriginalEqualityIsoInclusionData_original033 (e.hom ≫ i) f he)

/-- Original chain and diagram at an abstract Scheme, with a proved first-leg law.
The other two laws come from the accepted original source/equality producers. -/
def nativeClosedSourceChainDiagramData030
    {X Z Z' : Scheme.{u}} {M : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : M ≅ closedImmersionModule i)
    (w : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ha : a.hom ≫ closedImmersionModuleToUnit i = w) :=
  nativeSourceLawFactorySlot033 e i f he (nativeFirstInputIdealView035 i a) w ha
    (nativeOriginalEqualityIsoInclusionData033 (e.hom ≫ i) f he).property

/-- Infer the categorical factory value identity at the SAME normalized object
arguments used by the passed constructor. The chain equality is a separate cut. -/
private def nativeClosedSourceChainFactoryValue036
    {X Z Z' : Scheme.{u}} {M : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : M ≅ closedImmersionModule i)
    (w : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ha : a.hom ≫ closedImmersionModuleToUnit i = w) :=
  @nativeCanonicalIsoChainFactoryValue036 X.Modules (inferInstance : Category X.Modules)
    M (idealModule i.ker) (idealModule (e.hom ≫ i).ker) (closedImmersionModule f)
      (SheafOfModules.unit X.ringCatSheaf)
    (nativeFirstInputIdealView035 i a)
    (nativeOriginalSourceOwnInverseData031 e i).val
    (nativeOriginalEqualityIsoInclusionData033 (e.hom ≫ i) f he).val
    (closedImmersionModuleToUnit i)
    (closedImmersionModuleToUnit (e.hom ≫ i)) (closedImmersionModuleToUnit f) w
    ha (nativeOriginalSourceOwnInverseData031 e i).property
    (nativeOriginalEqualityIsoInclusionData033 (e.hom ≫ i) f he).property

/-- The value is the SAME original right-associated chain, including original
SourceIso and native equality transport; no alternate morphism is substituted. -/
theorem nativeClosedSourceChainDiagramData_original030
    {X Z Z' : Scheme.{u}} {M : X.Modules}
    (e : Z ≅ Z') (i : Z' ⟶ X) (f : Z ⟶ X) (he : e.hom ≫ i = f)
    (a : M ≅ closedImmersionModule i)
    (w : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ha : a.hom ≫ closedImmersionModuleToUnit i = w) :
    (nativeClosedSourceChainDiagramData030 e i f he a w ha).val =
      a ≪≫ (closedImmersionModuleSourceIso e i).symm ≪≫
        eqToIso (congrArg closedImmersionModule he) := by
  exact @Eq.trans
    (@Iso X.Modules (inferInstance : Category X.Modules) M (closedImmersionModule f))
    (nativeClosedSourceChainDiagramData030 e i f he a w ha).val
    ((nativeFirstInputIdealView035 i a) ≪≫
      (nativeOriginalSourceOwnInverseData031 e i).val.symm ≪≫
      (nativeOriginalEqualityIsoInclusionData033 (e.hom ≫ i) f he).val)
    (a ≪≫ (closedImmersionModuleSourceIso e i).symm ≪≫
      eqToIso (congrArg closedImmersionModule he))
    (nativeClosedSourceChainFactoryValue036 e i f he a w ha)
    (nativeOriginalChainValueIdentity036 e i f he a)

end PfaffianDescent
