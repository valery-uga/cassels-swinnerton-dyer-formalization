import PfaffianDescent.AffineGammaPushforward

/- Source-only indexed transport and map/law factory. The actual image objects
are inserted only after the category dictionary and reflexive law are fixed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u

private lemma inclusionFamily_inverse_raw013
    {C : Type*} [Category C] {D : Type*} {U : C}
    (F : D → C) (v : ∀ d, F d ⟶ U)
    (t : ∀ {d e : D}, d = e → (F d ≅ F e))
    (ht : ∀ d, t (Eq.refl d) = Iso.refl (F d))
    {d e : D} (h : d = e) : (t h).inv ≫ v d = v e := by
  cases h
  rw [ht d]
  exact Category.id_comp (v d)

private lemma inclusionFamily_inverse_own013
    {S : Scheme.{u}} {D : Type*}
    (F : D → SheafOfModules S.ringCatSheaf)
    (v : ∀ d, F d ⟶ SheafOfModules.unit S.ringCatSheaf)
    (t : ∀ {d e : D}, d = e → (F d ≅ F e))
    (ht : ∀ d, t (Eq.refl d) = Iso.refl (F d))
    {d e : D} (h : d = e) :
    @CategoryStruct.comp S.Modules
      (inferInstance : Category S.Modules).toCategoryStruct
      (F e) (F d) (SheafOfModules.unit S.ringCatSheaf)
      (t h).inv (v d) = v e := by
  cases h
  rw [ht d]
  exact @Category.id_comp S.Modules (inferInstance : Category S.Modules)
    (F d) (SheafOfModules.unit S.ringCatSheaf) (v d)

/-- Pin the exact native raw sheaf category before inserting any image objects.
This is an ordinary dictionary definition, not a new registered instance. -/
private def nativeRawSheafModuleCategory016 (X : Scheme.{u}) :
    Category (SheafOfModules X.ringCatSheaf) :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

/-- The exact native Scheme.Modules dictionary: its Hom wrapper and raw category fields.
No category structure or original module map is replaced. -/
private def nativeOwnSheafModuleCategory016 (X : Scheme.{u}) : Category X.Modules where
  Hom := fun M N => Scheme.Modules.Hom (X := X) M N
  __ := nativeRawSheafModuleCategory016 X

private lemma inclusionFamily_eqToIso_inverse_raw016
    {C : Type*} [Category C] {D : Type*} {U : C}
    (F : D → C) (v : ∀ d, F d ⟶ U)
    {d e : D} (h : d = e) :
    (eqToIso (congrArg F h)).inv ≫ v d = v e := by
  cases h
  exact Category.id_comp (v d)

private lemma inclusionFamily_eqToIso_inverse_own016
    {S : Scheme.{u}} {D : Type*}
    (F : D → SheafOfModules S.ringCatSheaf)
    (v : ∀ d, F d ⟶ SheafOfModules.unit S.ringCatSheaf)
    {d e : D} (h : d = e) :
    @CategoryStruct.comp S.Modules
      (nativeOwnSheafModuleCategory016 S).toCategoryStruct
      (F e) (F d) (SheafOfModules.unit S.ringCatSheaf)
      (@eqToIso (SheafOfModules S.ringCatSheaf) (nativeRawSheafModuleCategory016 S)
        (F d) (F e) (congrArg F h)).inv (v d) = v e := by
  cases h
  exact @Category.id_comp S.Modules (nativeOwnSheafModuleCategory016 S)
    (F d) (SheafOfModules.unit S.ringCatSheaf) (v d)

/-- Infer the actual ideal-index raw proof before specializing to source-isomorphism kernels. -/
private def nativeIdealTransportInverseRawProof016
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :=
  @inclusionFamily_eqToIso_inverse_raw016
    (SheafOfModules X.ringCatSheaf) (nativeRawSheafModuleCategory016 X)
    X.IdealSheafData (SheafOfModules.unit X.ringCatSheaf)
    idealModule idealModuleToUnit I J h

/-- Infer the actual ideal-index own proof before specializing to source-isomorphism kernels. -/
private def nativeIdealTransportInverseOwnProof016
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :=
  inclusionFamily_eqToIso_inverse_own016 (S := X) (D := X.IdealSheafData)
    idealModule idealModuleToUnit (d := I) (e := J) h

/-- Convert the original raw composition law at abstract objects, before inserting ideal images. -/
private lemma nativeRawCompositionLaw_toOwn017
    {X : Scheme.{u}} {M N U : SheafOfModules X.ringCatSheaf}
    (f : M ⟶ N) (v : N ⟶ U) (w : M ⟶ U) (h : f ≫ v = w) :
    @CategoryStruct.comp X.Modules
      (inferInstance : Category X.Modules).toCategoryStruct M N U f v = w := h

/-- Convert the folded ORIGINAL ideal transport law at abstract ideal indices,
before any source-isomorphism aliases or kernel expressions are inserted. -/
private def nativeFoldedIdealTransportInverseOwnProof018
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :=
  nativeRawCompositionLaw_toOwn017 (X := X)
    (M := idealModule J) (N := idealModule I) (U := SheafOfModules.unit X.ringCatSheaf)
    (idealModuleTransport h).inv (idealModuleToUnit I) (idealModuleToUnit J)
    (idealModuleTransport_inv_toUnit h)

/-- Use the ACCEPTED original transport inverse law in its original raw dictionary;
keep idealModuleTransport folded until the actual source specialization is captured. -/
private def nativeActualSourceInverseRawProof017
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :=
  @idealModuleTransport_inv_toUnit X (e.hom ≫ i).ker i.ker
    (Scheme.Hom.ker_comp_of_isIso e.hom i)

/-- Capture the own composition law at the exact original SourceIso/inclusion expressions. -/
private def nativeActualSourceInverseOwnProof017
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :=
  nativeFoldedIdealTransportInverseOwnProof018 (X := X)
    (I := (e.hom ≫ i).ker) (J := i.ker) (Scheme.Hom.ker_comp_of_isIso e.hom i)

/-- Whole-Iso identity witness for the unchanged original source transport, not only its Hom. -/
theorem nativeClosedImmersionSourceIso_original017
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :
    closedImmersionModuleSourceIso e i =
      idealModuleTransport (Scheme.Hom.ker_comp_of_isIso e.hom i) := rfl

/-- Transport a proved diagram predicate using three independent equalities.
This cut has no category, ideal-module or source-kernel specialization. -/
private lemma nativeDiagramAliasTransport019
    {A V W : Type*} (P : A → V → W → Prop)
    {a a' : A} {v v' : V} {w w' : W}
    (ha : a = a') (hv : v = v') (hw : w = w')
    (h : P a' v' w') : P a v w := by
  cases ha
  cases hv
  cases hw
  exact h

/-- The literal inclusion alias is compared separately at an arbitrary immersion.
Neither the ideal image nor its sheafification is expanded. -/
private theorem nativeClosedImmersionInclusion_original019
    {X Z : Scheme.{u}} (i : Z ⟶ X) :
    closedImmersionModuleToUnit i = idealModuleToUnit i.ker := rfl

/-- Infer the original raw diagram AFTER explicit equality transport of all aliases.
The already checked folded source law is an input, not re-proved by conversion. -/
private def nativeActualSourceAliasRawProof019
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :=
  nativeDiagramAliasTransport019
    (fun (a : idealModule (e.hom ≫ i).ker ≅ idealModule i.ker)
      (v : idealModule (e.hom ≫ i).ker ⟶ SheafOfModules.unit X.ringCatSheaf)
      (w : idealModule i.ker ⟶ SheafOfModules.unit X.ringCatSheaf) =>
      a.inv ≫ v = w)
    (nativeClosedImmersionSourceIso_original017 e i)
    (nativeClosedImmersionInclusion_original019 (e.hom ≫ i))
    (nativeClosedImmersionInclusion_original019 i)
    (nativeActualSourceInverseRawProof017 e i)

/-- The same alias predicate transport in the original Scheme.Modules dictionary. -/
private def nativeActualSourceAliasOwnProof019
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :=
  nativeDiagramAliasTransport019
    (fun (a : idealModule (e.hom ≫ i).ker ≅ idealModule i.ker)
      (v : idealModule (e.hom ≫ i).ker ⟶ SheafOfModules.unit X.ringCatSheaf)
      (w : idealModule i.ker ⟶ SheafOfModules.unit X.ringCatSheaf) =>
      @CategoryStruct.comp X.Modules
        (inferInstance : Category X.Modules).toCategoryStruct
        (idealModule i.ker) (idealModule (e.hom ≫ i).ker)
        (SheafOfModules.unit X.ringCatSheaf) a.inv v = w)
    (nativeClosedImmersionSourceIso_original017 e i)
    (nativeClosedImmersionInclusion_original019 (e.hom ≫ i))
    (nativeClosedImmersionInclusion_original019 i)
    (nativeActualSourceInverseOwnProof017 e i)

/-- The exact original source-isomorphism square in its raw public category.
Only the original transport's reflexive identity enters the indexed factory. -/
def nativeClosedImmersionSourceInverseRawSquare013 :=
  @nativeActualSourceAliasRawProof019

/-- The same canonical maps with the Scheme.Modules dictionary fixed upstream. -/
def nativeClosedImmersionSourceInverseOwnSquare013 :=
  @nativeActualSourceAliasOwnProof019

private lemma inclusionFamily_eqToIso_own013
    {S : Scheme.{u}} {D : Type*}
    (F : D → SheafOfModules S.ringCatSheaf)
    (v : ∀ d, F d ⟶ SheafOfModules.unit S.ringCatSheaf)
    {d e : D} (h : d = e) :
    @CategoryStruct.comp S.Modules
      (inferInstance : Category S.Modules).toCategoryStruct
      (F d) (F e) (SheafOfModules.unit S.ringCatSheaf)
      (@eqToIso S.Modules (inferInstance : Category S.Modules)
        (F d) (F e) (congrArg F h)).hom (v e) = v d := by
  cases h
  exact @Category.id_comp S.Modules (inferInstance : Category S.Modules)
    (F d) (SheafOfModules.unit S.ringCatSheaf) (v d)

/-- Equality transport is constructed directly in the original own dictionary. -/
theorem nativeClosedImmersionEqualityOwnSquare013
    {X Z : Scheme.{u}} (f g : Z ⟶ X) (h : f = g) :
    @CategoryStruct.comp X.Modules
      (inferInstance : Category X.Modules).toCategoryStruct
      (closedImmersionModule f) (closedImmersionModule g)
      (SheafOfModules.unit X.ringCatSheaf)
      (@eqToIso X.Modules (inferInstance : Category X.Modules)
        (closedImmersionModule f) (closedImmersionModule g)
        (congrArg closedImmersionModule h)).hom (closedImmersionModuleToUnit g) =
      closedImmersionModuleToUnit f :=
  inclusionFamily_eqToIso_own013 (S := X)
    closedImmersionModule closedImmersionModuleToUnit h

private lemma canonicalIsoChain_inclusion013
    {C : Type*} [Category C] {A B D E U : C}
    (a : A ≅ B) (b : D ≅ B) (c : D ≅ E)
    (vB : B ⟶ U) (vD : D ⟶ U) (vE : E ⟶ U) (w : A ⟶ U)
    (ha : a.hom ≫ vB = w) (hb : b.inv ≫ vD = vB)
    (hc : c.hom ≫ vE = vD) :
    (a ≪≫ b.symm ≪≫ c).hom ≫ vE = w := by
  change (a.hom ≫ b.inv ≫ c.hom) ≫ vE = w
  calc
    _ = a.hom ≫ b.inv ≫ (c.hom ≫ vE) :=
      (Category.assoc a.hom (b.inv ≫ c.hom) vE).trans
        (congrArg (fun z => a.hom ≫ z) (Category.assoc b.inv c.hom vE))
    _ = a.hom ≫ b.inv ≫ vD := congrArg (fun z => a.hom ≫ b.inv ≫ z) hc
    _ = a.hom ≫ vB := congrArg (fun z => a.hom ≫ z) hb
    _ = w := ha

/-- Return the original right-associated chain together with its law BEFORE
specialization to an actual affine image or first-isomorphism context. -/
def canonicalIsoChainInclusionData013
    {C : Type*} [Category C] {A B D E U : C}
    (a : A ≅ B) (b : D ≅ B) (c : D ≅ E)
    (vB : B ⟶ U) (vD : D ⟶ U) (vE : E ⟶ U) (w : A ⟶ U)
    (ha : a.hom ≫ vB = w) (hb : b.inv ≫ vD = vB)
    (hc : c.hom ≫ vE = vD) :
    { q : A ≅ E // q.hom ≫ vE = w } :=
  ⟨a ≪≫ b.symm ≪≫ c,
    canonicalIsoChain_inclusion013 a b c vB vD vE w ha hb hc⟩

end PfaffianDescent
