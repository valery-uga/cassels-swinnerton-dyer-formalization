import PfaffianDescent.AffineFreeModuleBaseChange
import PfaffianDescent.BundleSectionZeroLocusNaturality
import PfaffianDescent.SchemeModuleGlobalSectionsTop
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Field base change restricted to an open subscheme

The inverse image of an open under a field-base-change projection is the
field base change of that open.  These canonical isomorphisms transport the
affine local calculations to the actual opens used by the global Cech cover.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

noncomputable section

/-- The inverse-image open square, pasted with the field-base-change square,
is itself a pullback square over the restricted structure morphism. -/
theorem isPullback_schemeFieldBaseChangeOpen
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens) :
    IsPullback
      (schemeFieldBaseChangeToOriginal (L := L) base ∣_ U)
      ((schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U).ι ≫
        schemeFieldBaseChangeToField (L := L) base)
      (U.ι ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  exact (isPullback_morphismRestrict
    (schemeFieldBaseChangeToOriginal (L := L) base) U).paste_vert
      (IsPullback.of_hasPullback base
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))

/-- Canonical identification of the field base change of an open subscheme
with the inverse-image open inside the field base change of the whole
scheme. -/
noncomputable def schemeFieldBaseChangeOpenIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens) :
    schemeFieldBaseChange (L := L) (U.ι ≫ base) ≅
      (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U : Scheme.{u}) :=
  (IsPullback.of_hasPullback (U.ι ≫ base)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))).isoIsPullback
      (U : Scheme.{u}) (Spec (.of L))
      (isPullback_schemeFieldBaseChangeOpen base U)

@[reassoc (attr := simp)]
theorem schemeFieldBaseChangeOpenIso_hom_toOriginal
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens) :
    (schemeFieldBaseChangeOpenIso (L := L) base U).hom ≫
        (schemeFieldBaseChangeToOriginal (L := L) base ∣_ U) =
      schemeFieldBaseChangeToOriginal (L := L) (U.ι ≫ base) :=
  (IsPullback.of_hasPullback (U.ι ≫ base)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))).isoIsPullback_hom_fst
      (U : Scheme.{u}) (Spec (.of L))
      (isPullback_schemeFieldBaseChangeOpen base U)

@[reassoc (attr := simp)]
theorem schemeFieldBaseChangeOpenIso_hom_toField
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens) :
    (schemeFieldBaseChangeOpenIso (L := L) base U).hom ≫
        ((schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U).ι ≫
          schemeFieldBaseChangeToField (L := L) base) =
      schemeFieldBaseChangeToField (L := L) (U.ι ≫ base) :=
  (IsPullback.of_hasPullback (U.ι ≫ base)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))).isoIsPullback_hom_snd
      (U : Scheme.{u}) (Spec (.of L))
      (isPullback_schemeFieldBaseChangeOpen base U)

/-- Pulling the restricted module back along the inverse-image open map is
canonically the restriction of the globally pulled-back module. -/
noncomputable def schemeFieldBaseChangeOpenModuleIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let p := g ∣_ U
    (Scheme.Modules.pullback p).obj (M.restrict U.ι) ≅
      ((Scheme.Modules.pullback g).obj M).restrict V.ι := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let p := g ∣_ U
  exact
    (Scheme.Modules.pullback p).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) ≪≫
      (Scheme.Modules.pullbackComp p U.ι).app M ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι g U)).app M ≪≫
      ((Scheme.Modules.pullbackComp V.ι g).app M).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        ((Scheme.Modules.pullback g).obj M)).symm

/-- A finite-free trivialization on an open of the original scheme pulls
back to a finite-free trivialization on its actual inverse-image open in the
field base change.  The target is kept in pullback form for later comparison
with restriction of the globally pulled-back module. -/
noncomputable def schemeFieldBaseChangeOpenPulledBackFreeIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    SheafOfModules.free (R := (V : Scheme.{u}).ringCatSheaf) I ≅
      ((Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pullback g).obj M)) := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let p := g ∣_ U
  let eU :=
    (BundleSectionZeroLocus.localFreeIsoOfOver U I t) ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
  exact
    BundleSectionZeroLocus.pullbackFreeIso p I eU ≪≫
      (Scheme.Modules.pullback p).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) ≪≫
      (Scheme.Modules.pullbackComp p U.ι).app M ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι g U)).app M ≪≫
      ((Scheme.Modules.pullbackComp V.ι g).app M).symm

/-- The same pulled-back finite-free presentation, expressed as a
trivialization of the restriction of the globally pulled-back module. -/
noncomputable def schemeFieldBaseChangeOpenRestrictedFreeIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    SheafOfModules.free (R := (V : Scheme.{u}).ringCatSheaf) I ≅
      ((Scheme.Modules.pullback g).obj M).restrict V.ι := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let p := g ∣_ U
  let eU :=
    (BundleSectionZeroLocus.localFreeIsoOfOver U I t) ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
  exact BundleSectionZeroLocus.pullbackFreeIso p I eU ≪≫
    schemeFieldBaseChangeOpenModuleIso base M U

/-- The inverse image of an affine open under the field-base-change
projection is affine. -/
theorem isAffine_schemeFieldBaseChangeOpen
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens)
    [IsAffine (U : Scheme.{u})] :
    IsAffine
      (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U : Scheme.{u}) := by
  let h : IsAffine (schemeFieldBaseChange (L := L) (U.ι ≫ base)) := by
    infer_instance
  exact @IsAffine.of_isIso _ _
    (schemeFieldBaseChangeOpenIso (L := L) base U).inv _ h

/-- Canonical affine presentation of the field base change of an affine
scheme as the spectrum of the scalar-extended ring of global functions. -/
noncomputable def affineSchemeFieldBaseChangeIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of K)) :
    letI := RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
    schemeFieldBaseChange (L := L) p ≅
      Spec (.of (L ⊗[K] Γ(X, ⊤))) := by
  letI : Algebra K Γ(X, ⊤) :=
    RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
  let pA : Spec (.of Γ(X, ⊤)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))
  have hp : p = X.isoSpec.hom ≫ pA := by
    dsimp [pA]
    rw [show algebraMap K Γ(X, ⊤) = affineFunctionHom p by
      ext c
      exact schemeOpenBaseRingHom_top_apply p c]
    exact (from_affineFunctionHom p).symm
  let e₁ : schemeFieldBaseChange (L := L) p ≅
      pullback pA (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    asIso (pullback.map p
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) pA
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      X.isoSpec.hom (𝟙 _) (𝟙 _) (by simpa using hp) (by simp))
  exact e₁ ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackSpecIso K L Γ(X, ⊤)

/-- The affine tensor-product presentation respects the structure morphism
to the extended ground field. -/
@[reassoc]
theorem affineSchemeFieldBaseChangeIso_hom_toField
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of K)) :
    letI : Algebra K Γ(X, ⊤) :=
      RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
    (affineSchemeFieldBaseChangeIso (L := L) p).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap L (L ⊗[K] Γ(X, ⊤)))) =
      schemeFieldBaseChangeToField (L := L) p := by
  letI : Algebra K Γ(X, ⊤) :=
    RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
  simp only [affineSchemeFieldBaseChangeIso, Iso.trans_hom, Category.assoc,
    pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst,
    asIso_hom, schemeFieldBaseChangeToField, pullback.map]
  exact pullback.lift_snd _ _ _

/-- An isomorphism of schemes over a field induces the contravariant linear
equivalence on their rings of global functions. -/
noncomputable def schemeIsoGlobalFunctionsLinearEquivOver
    {F : Type u} [Field F] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of F)) (pY : Y ⟶ Spec (.of F))
    (e : X ≅ Y) (h : e.hom ≫ pY = pX) :
    letI := Module.compHom Γ(Y, ⊤) (schemeOpenBaseRingHom pY ⊤)
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom pX ⊤)
    Γ(Y, ⊤) ≃ₗ[F] Γ(X, ⊤) := by
  letI iY : Module F Γ(Y, ⊤) :=
    Module.compHom Γ(Y, ⊤) (schemeOpenBaseRingHom pY ⊤)
  letI iX : Module F Γ(X, ⊤) :=
    Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom pX ⊤)
  exact {
    toFun := e.hom.appTop.hom
    invFun := e.inv.appTop.hom
    left_inv s := by
      change (e.hom.appTop ≫ e.inv.appTop).hom s = s
      rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]
      rfl
    right_inv s := by
      change (e.inv.appTop ≫ e.hom.appTop).hom s = s
      rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]
      rfl
    map_add' s t := map_add _ _ _
    map_smul' c s := by
      change e.hom.appTop.hom (schemeOpenBaseRingHom pY ⊤ c * s) =
        schemeOpenBaseRingHom pX ⊤ c * e.hom.appTop.hom s
      rw [map_mul]
      congr 1
      rw [schemeOpenBaseRingHom_top_apply,
        schemeOpenBaseRingHom_top_apply]
      have hc := congrArg (fun q : F →+* Γ(X, ⊤) ↦ q c)
        (affineFunctionHom_comp e.hom pY)
      rw [h] at hc
      exact hc.symm }

/-- Global functions on an affine scheme are linearly identified with its
affine coordinate ring, with the scalar action supplied by the chosen
structure morphism. -/
noncomputable def affineGlobalFunctionsLinearEquiv
    {K : Type u} [Field K] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of K)) :
    letI : Algebra K Γ(X, ⊤) :=
      RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
    Γ(X, ⊤) ≃ₗ[K] Γ(X, ⊤) := by
  letI : Algebra K Γ(X, ⊤) :=
    RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
  let pA : Spec (.of Γ(X, ⊤)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))
  have hp : X.isoSpec.hom ≫ pA = p := by
    dsimp [pA]
    rw [show algebraMap K Γ(X, ⊤) = affineFunctionHom p by
      ext c
      exact schemeOpenBaseRingHom_top_apply p c]
    exact from_affineFunctionHom p
  exact
    (schemeIsoGlobalFunctionsLinearEquivOver p pA X.isoSpec hp).symm ≪≫ₗ
      specGlobalFunctionsLinearEquiv K Γ(X, ⊤)

/-- The affine-coordinate identification above is the identity on the
underlying ring of global functions. -/
@[simp]
theorem affineGlobalFunctionsLinearEquiv_apply
    {K : Type u} [Field K] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of K)) (r : Γ(X, ⊤)) :
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
    affineGlobalFunctionsLinearEquiv p r = r := by
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
  change (X.isoSpec.inv.appTop ≫
      (Scheme.ΓSpecIso (.of Γ(X, ⊤))).hom).hom r = r
  have ht : X.isoSpec.hom.appTop =
      (Scheme.ΓSpecIso (.of Γ(X, ⊤))).hom :=
    Scheme.toSpecΓ_appTop X
  rw [← ht]
  change (X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop).hom r = r
  rw [← Scheme.Hom.comp_appTop, X.isoSpec.hom_inv_id]
  rfl

/-- The affine tensor-product presentation also respects the projection back
to the original affine scheme, after its canonical `Spec Γ` presentation. -/
@[reassoc]
theorem affineSchemeFieldBaseChangeIso_hom_toOriginalSpec
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of K)) :
    letI : Algebra K Γ(X, ⊤) :=
      RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
    (affineSchemeFieldBaseChangeIso (L := L) p).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom :
            Γ(X, ⊤) →+* L ⊗[K] Γ(X, ⊤))) =
      schemeFieldBaseChangeToOriginal (L := L) p ≫ X.isoSpec.hom := by
  letI : Algebra K Γ(X, ⊤) :=
    RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
  simp [affineSchemeFieldBaseChangeIso, Iso.trans_hom, Category.assoc,
    pullbackSpecIso_hom_snd, pullbackSymmetry_hom_comp_snd,
    asIso_hom, schemeFieldBaseChangeToOriginal, pullback.map]
  exact pullback.lift_fst _ _ _

/-- The inverse affine-spectrum identification sends an algebra-map value to
the corresponding constant regular function. -/
theorem gammaSpecIso_inv_algebraMap
    (L B : Type u) [Field L] [CommRing B] [Algebra L B]
    (c : L) :
    (Scheme.ΓSpecIso (.of B)).inv.hom (algebraMap L B c) =
      affineFunctionHom
        (Spec.map (CommRingCat.ofHom (algebraMap L B))) c := by
  apply (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (.of B)).hom.hom
      ((Scheme.ΓSpecIso (.of B)).inv.hom (algebraMap L B c)) =
    (Scheme.ΓSpecIso (.of B)).hom.hom
      (affineFunctionHom
        (Spec.map (CommRingCat.ofHom (algebraMap L B))) c)
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
  rw [CommRingCat.id_apply]
  exact (gammaSpec_baseRingHom_apply c).symm

/-- Naturality of the inverse affine-spectrum identification for the right
inclusion into a tensor product. -/
theorem gammaSpecIso_inv_includeRight
    (K L A : Type u) [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] (r : A) :
    (Scheme.ΓSpecIso (.of (L ⊗[K] A))).inv.hom
        (Algebra.TensorProduct.includeRight r) =
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* L ⊗[K] A))).appTop.hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom r) := by
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom :
        A →+* L ⊗[K] A))
  exact congrArg (fun q ↦ q.hom r) h

/-- Global functions on an arbitrary affine scheme commute with extension
of the ground field. -/
noncomputable def affineGlobalFunctionsBaseChangeLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of K)) :
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
    letI := Module.compHom Γ(schemeFieldBaseChange (L := L) p, ⊤)
      (schemeOpenBaseRingHom
        (schemeFieldBaseChangeToField (L := L) p) ⊤)
    (L ⊗[K] Γ(X, ⊤)) ≃ₗ[L]
      Γ(schemeFieldBaseChange (L := L) p, ⊤) := by
  letI : Algebra K Γ(X, ⊤) :=
    RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
  letI := Module.compHom Γ(schemeFieldBaseChange (L := L) p, ⊤)
    (schemeOpenBaseRingHom
      (schemeFieldBaseChangeToField (L := L) p) ⊤)
  let pB : Spec (.of (L ⊗[K] Γ(X, ⊤))) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap L (L ⊗[K] Γ(X, ⊤))))
  let e := affineSchemeFieldBaseChangeIso (L := L) p
  exact (affineGlobalFunctionsLinearEquiv p).baseChange K L _ _ ≪≫ₗ
    (specGlobalFunctionsLinearEquiv L (L ⊗[K] Γ(X, ⊤))).symm ≪≫ₗ
      schemeIsoGlobalFunctionsLinearEquivOver
        (schemeFieldBaseChangeToField (L := L) p) pB e
        (affineSchemeFieldBaseChangeIso_hom_toField (L := L) p)

/-- On a pure tensor, affine global-function base change is multiplication
of the extended-field constant by pullback of the original function. -/
theorem affineGlobalFunctionsBaseChangeLinearEquiv_tmul
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of K))
    (c : L) (r : Γ(X, ⊤)) :
    letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
    affineGlobalFunctionsBaseChangeLinearEquiv (L := L) p (c ⊗ₜ[K] r) =
      schemeOpenBaseRingHom
          (schemeFieldBaseChangeToField (L := L) p) ⊤ c *
        (schemeFieldBaseChangeToOriginal (L := L) p).appTop.hom r := by
  letI := Module.compHom Γ(X, ⊤) (schemeOpenBaseRingHom p ⊤)
  letI : Algebra K Γ(X, ⊤) :=
    RingHom.toAlgebra (schemeOpenBaseRingHom p ⊤)
  let B := L ⊗[K] Γ(X, ⊤)
  let e := affineSchemeFieldBaseChangeIso (L := L) p
  let pB : Spec (.of B) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L B))
  let fB : Spec (.of B) ⟶ Spec (.of Γ(X, ⊤)) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom : Γ(X, ⊤) →+* B))
  change e.hom.appTop.hom
      ((Scheme.ΓSpecIso (.of B)).inv.hom
        ((affineGlobalFunctionsLinearEquiv p).baseChange K L _ _
          (c ⊗ₜ[K] r))) = _
  rw [LinearEquiv.baseChange_tmul,
    affineGlobalFunctionsLinearEquiv_apply]
  rw [show c ⊗ₜ[K] r =
      algebraMap L B c * Algebra.TensorProduct.includeRight r by
    simp [B, Algebra.TensorProduct.algebraMap_def]]
  rw [map_mul, map_mul]
  rw [gammaSpecIso_inv_algebraMap L B c,
    gammaSpecIso_inv_includeRight K L Γ(X, ⊤) r]
  have hc := congrArg
    (fun q : L →+* Γ(schemeFieldBaseChange (L := L) p, ⊤) ↦ q c)
    (affineFunctionHom_comp e.hom pB)
  have heField : e.hom ≫ pB =
      schemeFieldBaseChangeToField (L := L) p :=
    affineSchemeFieldBaseChangeIso_hom_toField (L := L) p
  rw [heField] at hc
  have hc' : e.hom.appTop.hom (affineFunctionHom pB c) =
      schemeOpenBaseRingHom
        (schemeFieldBaseChangeToField (L := L) p) ⊤ c := by
    rw [schemeOpenBaseRingHom_top_apply]
    exact hc.symm
  rw [hc']
  congr 1
  change (fB.appTop ≫ e.hom.appTop).hom
      ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom r) = _
  rw [← Scheme.Hom.comp_appTop,
    affineSchemeFieldBaseChangeIso_hom_toOriginalSpec (L := L) p,
    Scheme.Hom.comp_appTop]
  change (X.isoSpec.hom.appTop ≫
      (schemeFieldBaseChangeToOriginal (L := L) p).appTop).hom
        ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom r) = _
  have ht : X.isoSpec.hom.appTop =
      (Scheme.ΓSpecIso (.of Γ(X, ⊤))).hom :=
    Scheme.toSpecΓ_appTop X
  rw [ht, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- Ring-level base change on an actual inverse-image affine open, obtained
by transporting the canonical affine calculation through the pullback-open
isomorphism. -/
noncomputable def schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens)
    [IsAffine (U : Scheme.{u})] :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
      (schemeOpenBaseRingHom pU ⊤)
    letI := Module.compHom Γ((V : Scheme.{u}), ⊤)
      (schemeOpenBaseRingHom pV ⊤)
    (L ⊗[K] Γ((U : Scheme.{u}), ⊤)) ≃ₗ[L]
      Γ((V : Scheme.{u}), ⊤) := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let pU := U.ι ≫ base
  let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
  letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
    (schemeOpenBaseRingHom pU ⊤)
  letI := Module.compHom Γ((V : Scheme.{u}), ⊤)
    (schemeOpenBaseRingHom pV ⊤)
  let e := schemeFieldBaseChangeOpenIso (L := L) base U
  exact affineGlobalFunctionsBaseChangeLinearEquiv (L := L) pU ≪≫ₗ
    (schemeIsoGlobalFunctionsLinearEquivOver
      (schemeFieldBaseChangeToField (L := L) pU) pV e
      (schemeFieldBaseChangeOpenIso_hom_toField (L := L) base U)).symm

/-- On a pure tensor, ring base change on an actual inverse-image affine open
is multiplication of the extended-field constant by the restricted original
function. -/
theorem schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv_tmul
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens)
    [IsAffine (U : Scheme.{u})] (c : L) (r : Γ((U : Scheme.{u}), ⊤)) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
      (schemeOpenBaseRingHom pU ⊤)
    schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv base U
        (c ⊗ₜ[K] r) =
      schemeOpenBaseRingHom pV ⊤ c * (g ∣_ U).appTop.hom r := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let pU := U.ι ≫ base
  let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
  letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
    (schemeOpenBaseRingHom pU ⊤)
  let e := schemeFieldBaseChangeOpenIso (L := L) base U
  change e.inv.appTop.hom
      (affineGlobalFunctionsBaseChangeLinearEquiv (L := L) pU
        (c ⊗ₜ[K] r)) = _
  rw [affineGlobalFunctionsBaseChangeLinearEquiv_tmul]
  rw [map_mul]
  have heField : e.inv ≫ schemeFieldBaseChangeToField (L := L) pU = pV := by
    rw [← cancel_epi e.hom, ← Category.assoc,
      schemeFieldBaseChangeOpenIso_hom_toField,
      e.hom_inv_id, Category.id_comp]
  have hc := congrArg (fun q : L →+* Γ((V : Scheme.{u}), ⊤) ↦ q c)
    (affineFunctionHom_comp e.inv
      (schemeFieldBaseChangeToField (L := L) pU))
  rw [heField] at hc
  have hc' : e.inv.appTop.hom
      (schemeOpenBaseRingHom
        (schemeFieldBaseChangeToField (L := L) pU) ⊤ c) =
      schemeOpenBaseRingHom pV ⊤ c := by
    rw [schemeOpenBaseRingHom_top_apply,
      schemeOpenBaseRingHom_top_apply]
    exact hc.symm
  rw [hc']
  congr 1
  have heOriginal : e.inv ≫
      schemeFieldBaseChangeToOriginal (L := L) pU = g ∣_ U := by
    rw [← cancel_epi e.hom, ← Category.assoc,
      schemeFieldBaseChangeOpenIso_hom_toOriginal,
      e.hom_inv_id, Category.id_comp]
  change e.inv.appTop.hom
      ((schemeFieldBaseChangeToOriginal (L := L) pU).appTop.hom r) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, heOriginal]

/-- The top-open coordinate map is the same coordinate map obtained by
turning a top-open section into a categorical module section. -/
theorem moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate
    {X : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    (M : X.Modules)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (s : Γ(M, ⊤)) (i : I) :
    moduleOpenTopLinearEquivOfFreeIso I M e s i =
      BundleSectionZeroLocus.freeSectionCoordinate I
        (SheafOfModules.sectionsMap e.inv
          ((schemeModuleSectionsEquivTop M).symm s)) i := by
  let q := SheafOfModules.sectionsMap e.inv
    ((schemeModuleSectionsEquivTop M).symm s)
  change ((BundleSectionZeroLocus.freeCoordinateMap I i).val.app
      (op ⊤)).hom ((e.inv.val.app (op ⊤)).hom s) =
    ((BundleSectionZeroLocus.freeCoordinateMap I i).val.app
      (op ⊤)).hom
      ((((SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        q).val.app (op ⊤)).hom (show Γ(X, ⊤) from 1))
  congr 1
  have h := congrArg (fun z ↦ z.val (op ⊤))
    ((SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.apply_symm_apply q)
  exact (h.trans (by
    change (e.inv.val.app (op ⊤)).hom
      (((schemeModuleSectionsEquivTop M).symm s).val (op ⊤)) = _
    exact congrArg (fun z ↦ (e.inv.val.app (op ⊤)).hom z)
      ((schemeModuleSectionsEquivTop M).apply_symm_apply s))).symm

/-- Coordinates in a restricted free presentation are the restrictions of
the original coordinates. -/
theorem moduleOpenTopLinearEquivOfRestrictionFreeIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : Y.Modules)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ M)
    (s : Γ(M, ⊤)) (i : I) :
    let sY := (schemeModuleSectionsEquivTop M).symm s
    let MX := (Scheme.Modules.restrictFunctor f).obj M
    let sX := BundleSectionZeroLocus.restrictModuleSection f M sY
    moduleOpenTopLinearEquivOfFreeIso I MX
        (BundleSectionZeroLocus.restrictionFreeIsoOf f I e)
        (schemeModuleSectionsEquivTop MX sX) i =
      f.appTop.hom (moduleOpenTopLinearEquivOfFreeIso I M e s i) := by
  let sY := (schemeModuleSectionsEquivTop M).symm s
  let MX := (Scheme.Modules.restrictFunctor f).obj M
  let sX := BundleSectionZeroLocus.restrictModuleSection f M sY
  dsimp only
  rw [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate,
    moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate]
  rw [(schemeModuleSectionsEquivTop MX).symm_apply_apply]
  rw [BundleSectionZeroLocus.restrictionFreeIsoOf_inv_sections_eq_restrictFreeSection]
  exact BundleSectionZeroLocus.freeSectionCoordinate_restrictFreeSection_eq_appTop
    f I (SheafOfModules.sectionsMap e.inv sY) i

/-- A named three-step linear equivalence.  Keeping the composition opaque
prevents dependent open-section types from being repeatedly normalized in
later cancellation arguments. -/
noncomputable def linearEquivTriple
    {F A B C D : Type u} [Semiring F]
    [AddCommMonoid A] [Module F A] [AddCommMonoid B] [Module F B]
    [AddCommMonoid C] [Module F C] [AddCommMonoid D] [Module F D]
    (pre : A ≃ₗ[F] B) (mid : B ≃ₗ[F] C) (post : C ≃ₗ[F] D) :
    A ≃ₗ[F] D :=
  pre ≪≫ₗ mid ≪≫ₗ post

/-- Cancelling the last transport in a named three-step equivalence. -/
theorem linearEquivTriple_post_symm_apply
    {F A B C D : Type u} [Semiring F]
    [AddCommMonoid A] [Module F A] [AddCommMonoid B] [Module F B]
    [AddCommMonoid C] [Module F C] [AddCommMonoid D] [Module F D]
    (pre : A ≃ₗ[F] B) (mid : B ≃ₗ[F] C) (post : C ≃ₗ[F] D)
    (x : A) :
    post.symm (linearEquivTriple pre mid post x) = mid (pre x) :=
  post.symm_apply_apply _

/-- Finite-free module sections commute with field extension on the top
opens of a trivializing affine chart and its actual inverse-image chart. -/
noncomputable def schemeFieldBaseChangeOpenFreeModuleTopSectionsLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    (L ⊗[K] SchemeModuleOpenSectionsOver pU (M.restrict U.ι) ⊤) ≃ₗ[L]
      SchemeModuleOpenSectionsOver pV
        (((Scheme.Modules.pullback g).obj M).restrict V.ι) ⊤ := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let pU := U.ι ≫ base
  let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
  let eU := BundleSectionZeroLocus.localFreeIsoOfOver U I t ≪≫
    (Scheme.Modules.overFunctorEquiv U).app M
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso
    (K := K) (L := L) base M U I t
  exact freeModuleOpenSectionsBaseChangeLinearEquivOfRing
    pU pV I (M.restrict U.ι)
      (((Scheme.Modules.pullback g).obj M).restrict V.ι)
      eU eV (schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv base U)

/-- Sections of a module on an ambient open are linearly equivalent to top
sections of the restricted module on the corresponding open subscheme. -/
noncomputable def moduleRestrictTopLinearEquivOpenSectionsOver
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) (U : X.Opens) :
    let pU := U.ι ≫ p
    SchemeModuleOpenSectionsOver pU (M.restrict U.ι) ⊤ ≃ₗ[K]
      SchemeModuleOpenSectionsOver p M U := by
  let pU := U.ι ≫ p
  let q : Γ(M.restrict U.ι, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso U.ι ⊤ ≪≫
      M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
  exact {
    toFun := q.hom
    invFun := q.inv
    left_inv s := q.hom_inv_id_apply s
    right_inv s := q.inv_hom_id_apply s
    map_add' s t := map_add _ _ _
    map_smul' c s := by
      let a := (M.restrictAppIso U.ι ⊤).hom
      let b := (M.presheaf.mapIso
        (eqToIso U.ι_image_top.symm).op).hom
      let r := schemeOpenBaseRingHom pU ⊤ c
      let s' : Γ(M.restrict U.ι, ⊤) := s
      change b (a (r • s')) =
        schemeOpenBaseRingHom p U c • b (a s')
      rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
      change M.presheaf.map (eqToHom U.ι_image_top.symm).op
          ((U.ι.appIso ⊤).inv r • a s') = _
      rw [M.map_smul]
      congr 1
      let f : (Opposite.op (⊤ : X.Opens)) ⟶
          Opposite.op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) :=
        (homOfLE le_top).op
      let e : Opposite.op
          (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) ⟶
          Opposite.op U := (eqToHom U.ι_image_top.symm).op
      let h : Opposite.op (⊤ : X.Opens) ⟶ Opposite.op U :=
        (homOfLE le_top).op
      have heq : f ≫ e = h := Subsingleton.elim _ _
      have hr : (U.ι.appIso ⊤).inv r =
          X.presheaf.map f (affineFunctionHom p c) := by
        simp [r, pU, affineFunctionHom_comp, f]
        rfl
      have hu : schemeOpenBaseRingHom p U c =
          X.presheaf.map h (affineFunctionHom p c) := by
        rfl
      rw [hr, hu]
      change X.presheaf.map e
          (X.presheaf.map f (affineFunctionHom p c)) =
        X.presheaf.map h (affineFunctionHom p c)
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, heq] }

/-- Complete local base-change equivalence on an affine trivializing open,
written in the ambient-open section models used by the Cech complex. -/
noncomputable def schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    (L ⊗[K] SchemeModuleOpenSectionsOver base M U) ≃ₗ[L]
      SchemeModuleOpenSectionsOver
        (schemeFieldBaseChangeToField (L := L) base) ML V := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  exact linearEquivTriple
    ((moduleRestrictTopLinearEquivOpenSectionsOver base M U).symm.baseChange
        K L (SchemeModuleOpenSectionsOver base M U)
          (SchemeModuleOpenSectionsOver (U.ι ≫ base) (M.restrict U.ι) ⊤))
    (schemeFieldBaseChangeOpenFreeModuleTopSectionsLinearEquiv
      base M U I t)
    (moduleRestrictTopLinearEquivOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V)

/-- Removing the final ambient-open transport from the local equivalence
recovers the top-open finite-free equivalence. -/
theorem schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_toTop
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (x : L ⊗[K] SchemeModuleOpenSectionsOver base M U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V
    qV.symm (schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
      base M U I t x) =
      schemeFieldBaseChangeOpenFreeModuleTopSectionsLinearEquiv base M U I t
        (qU.symm.baseChange K L
          (SchemeModuleOpenSectionsOver base M U)
          (SchemeModuleOpenSectionsOver (U.ι ≫ base) (M.restrict U.ι) ⊤) x) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pre := (moduleRestrictTopLinearEquivOpenSectionsOver base M U).symm.baseChange
    K L (SchemeModuleOpenSectionsOver base M U)
      (SchemeModuleOpenSectionsOver (U.ι ≫ base) (M.restrict U.ι) ⊤)
  let mid := schemeFieldBaseChangeOpenFreeModuleTopSectionsLinearEquiv
    (K := K) (L := L) base M U I t
  let post := moduleRestrictTopLinearEquivOpenSectionsOver
    (schemeFieldBaseChangeToField (L := L) base) ML V
  have hE : schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
      base M U I t = linearEquivTriple pre mid post := rfl
  rw [hE]
  rw [linearEquivTriple_post_symm_apply]

/-- In free coordinates, the actual-open local equivalence applies the ring
base-change equivalence coordinatewise to every pure tensor. -/
theorem schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_coord
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (c : L) (s : SchemeModuleOpenSectionsOver base M U) (i : I) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    let eU := BundleSectionZeroLocus.localFreeIsoOfOver U I t ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
    let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I t
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V
    letI := Module.compHom Γ((U : Scheme.{u}), ⊤)
      (schemeOpenBaseRingHom pU ⊤)
    moduleOpenTopLinearEquivOfFreeIsoOver pV I (ML.restrict V.ι) eV
        (qV.symm (schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
          base M U I t (c ⊗ₜ[K] s))) i =
      schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv base U
        (c ⊗ₜ[K]
          moduleOpenTopLinearEquivOfFreeIsoOver pU I (M.restrict U.ι) eU
            (qU.symm s) i) := by
  dsimp only
  rw [schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_toTop]
  unfold schemeFieldBaseChangeOpenFreeModuleTopSectionsLinearEquiv
  dsimp only
  rw [LinearEquiv.baseChange_tmul]
  rw [freeModuleOpenSectionsBaseChangeLinearEquivOfRing_tmul_coord]

end

end PfaffianDescent
