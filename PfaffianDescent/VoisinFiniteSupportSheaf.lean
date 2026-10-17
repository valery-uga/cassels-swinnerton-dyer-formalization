import PfaffianDescent.VoisinGaloisBaseChange
import PfaffianDescent.FiniteProductTildeDecomposition
import PfaffianDescent.FiniteSupportExtComponents
import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.LocalExtResidueInjective
import PfaffianDescent.SchemeModuleCohomology

/-!
# Splitting the sheaf of Voisin's finite separable orbit

The scalar extension of a finite separable point has an affine product-ring
model.  On that model its structure sheaf, pushed into the scalar-extended
ambient scheme, is the finite biproduct of the individual point sheaves.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L]

/-- The product-ring model of the scalar-extended finite point, mapped into
the scalar-extended ambient scheme. -/
noncomputable def finiteSeparableProductModelToAmbient
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L] :
    Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L)) ⟶
      schemeBaseChangeToField (L := L) X p :=
  (finiteSeparablePointBaseChangeIsoProduct
    (K := K) (A := A) (L := L)).inv ≫
      finitePointBaseChangeToAmbient p center hcenter

/-- The split product model is a closed subscheme of the scalar-extended
ambient scheme whenever the original finite point is closed. -/
noncomputable instance finiteSeparableProductModelToAmbient_isClosedImmersion
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L] :
    IsClosedImmersion
      (finiteSeparableProductModelToAmbient (L := L) p center hcenter) := by
  unfold finiteSeparableProductModelToAmbient
  infer_instance

/-- The coordinate map selected by an embedding, before mapping the split
finite point into the ambient scalar extension. -/
noncomputable def finiteSeparableEmbeddingToPointBaseChange
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) :
    Spec (.of L) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  productCoordinateSpecMap
      (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
      (finiteSeparableEmbeddingEquivPrimeSpectrum
        (K := K) (A := A) (L := L) phi) ≫
    (finiteSeparablePointBaseChangeIsoProduct
      (K := K) (A := A) (L := L)).inv

set_option linter.style.haveILetI false in
@[reassoc (attr := simp)]
theorem finiteSeparableEmbeddingToPointBaseChange_fst
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) :
    finiteSeparableEmbeddingToPointBaseChange
        (K := K) (A := A) (L := L) phi ≫
      pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
    Spec.map (CommRingCat.ofHom phi.toRingHom) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  simp [finiteSeparableEmbeddingToPointBaseChange,
    finiteSeparablePointBaseChangeIsoProduct,
    Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simpa [baseChangeEmbeddingEval] using
    (finiteSeparableBaseChangeEquivPi_apply_embedding phi
      (Algebra.TensorProduct.includeRight a))

set_option linter.style.haveILetI false in
@[reassoc (attr := simp)]
theorem finiteSeparableEmbeddingToPointBaseChange_snd
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) :
    finiteSeparableEmbeddingToPointBaseChange
        (K := K) (A := A) (L := L) phi ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
    𝟙 (Spec (.of L)) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  simp [finiteSeparableEmbeddingToPointBaseChange,
    finiteSeparablePointBaseChangeIsoProduct,
    Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro l
  simpa [baseChangeEmbeddingEval] using
    (finiteSeparableBaseChangeEquivPi_apply_embedding phi
      (Algebra.TensorProduct.includeLeftRingHom l))

/-- The embedding-indexed coordinate of the product model is exactly the
geometric conjugate point constructed directly by the pullback universal
property. -/
theorem finiteSeparableEmbeddingProductModelToAmbient_eq
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) :
    productCoordinateSpecMap
        (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
        (finiteSeparableEmbeddingEquivPrimeSpectrum
          (K := K) (A := A) (L := L) phi) ≫
      finiteSeparableProductModelToAmbient p center hcenter =
    galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi := by
  apply pullback.hom_ext
  · simp only [finiteSeparableProductModelToAmbient, Category.assoc,
      finitePointBaseChangeToAmbient_fst,
      galoisEmbeddingBaseChangeGeometricPoint_fst]
    change (finiteSeparableEmbeddingToPointBaseChange
        (K := K) (A := A) (L := L) phi ≫
      pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫ center = _
    rw [finiteSeparableEmbeddingToPointBaseChange_fst]
  · simp only [finiteSeparableProductModelToAmbient, Category.assoc,
      finitePointBaseChangeToAmbient_snd,
      galoisEmbeddingBaseChangeGeometricPoint_snd]
    change finiteSeparableEmbeddingToPointBaseChange
        (K := K) (A := A) (L := L) phi ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) = _
    rw [finiteSeparableEmbeddingToPointBaseChange_snd]

/-- Every actual Galois-conjugate geometric point obtained from a closed
finite point is itself a closed immersion into the scalar-extended ambient
scheme. -/
noncomputable instance
    galoisEmbeddingBaseChangeGeometricPoint_isClosedImmersion
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (phi : A →ₐ[K] L) :
    IsClosedImmersion
      (galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi) := by
  rw [← finiteSeparableEmbeddingProductModelToAmbient_eq
    p center hcenter phi]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- On the product-ring model of the split finite point, its pushed-forward
structure sheaf is the finite biproduct of its coordinate point sheaves. -/
noncomputable def finiteSeparableProductModelPushforwardBiproductIso
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))] :
    (⨁ fun i : PrimeSpectrum (L ⊗[K] A) ↦
      productCoordinatePointPushforwardToAmbient
        (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
        (finiteSeparableProductModelToAmbient p center hcenter) i) ≅
      (Scheme.Modules.pushforward
        (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf) :=
  productCoordinatePointPushforwardToAmbientBiproductIso
    (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
    (finiteSeparableProductModelToAmbient p center hcenter)

/-- The point-supported summand indexed by an actual field embedding, via
the canonical equivalence between embeddings and points of the split fibre. -/
noncomputable abbrev finiteSeparableEmbeddingPointPushforwardToAmbient
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) : (schemeBaseChangeToField (L := L) X p).Modules :=
  productCoordinatePointPushforwardToAmbient
    (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
    (finiteSeparableProductModelToAmbient p center hcenter)
    (finiteSeparableEmbeddingEquivPrimeSpectrum
      (K := K) (A := A) (L := L) phi)

/-- Each embedding-indexed summand of the product-model decomposition is the
pushforward from the corresponding actual geometric conjugate point. -/
noncomputable def finiteSeparableEmbeddingPointPushforwardIsoGalois
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) :
    finiteSeparableEmbeddingPointPushforwardToAmbient
        p center hcenter phi ≅
      (Scheme.Modules.pushforward
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter phi)).obj
        (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf) :=
  (Scheme.Modules.pushforwardCongr
    (finiteSeparableEmbeddingProductModelToAmbient_eq
      p center hcenter phi)).app
      (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing by the embedding/prime-spectrum equivalence gives the split
finite-support sheaf decomposition in the actual Galois-orbit indexing. -/
noncomputable def finiteSeparableEmbeddingPushforwardBiproductIso
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))] :
    (⨁ fun phi : A →ₐ[K] L ↦
      finiteSeparableEmbeddingPointPushforwardToAmbient
        p center hcenter phi) ≅
      (Scheme.Modules.pushforward
        (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf) :=
  biproduct.whiskerEquiv
      (finiteSeparableEmbeddingEquivPrimeSpectrum
        (K := K) (A := A) (L := L))
      (fun _ ↦ Iso.refl _) ≪≫
    finiteSeparableProductModelPushforwardBiproductIso p center hcenter

/-- The finite-support decomposition written entirely with the actual
geometric conjugate point morphisms on the scalar-extended ambient scheme. -/
noncomputable def finiteSeparableGaloisPointPushforwardBiproductIso
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))] :
    (⨁ fun phi : A →ₐ[K] L ↦
      (Scheme.Modules.pushforward
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter phi)).obj
        (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf)) ≅
      (Scheme.Modules.pushforward
        (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf) :=
  (biproduct.mapIso (fun phi ↦
    finiteSeparableEmbeddingPointPushforwardIsoGalois
      p center hcenter phi)).symm ≪≫
    finiteSeparableEmbeddingPushforwardBiproductIso p center hcenter

/-- On the split finite-support sheaf, an arbitrary family of local Ext
classes assembles into one class on the pushforward of the full finite
subscheme. This is the existence counterpart to the joint-detection theorem
below; it is stated in the actual geometric Galois-point decomposition. -/
theorem finiteSeparableGaloisPointExt_exists_of_components
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    (Y : (schemeBaseChangeToField (L := L) X p).Modules) (n : ℕ)
    (components : ∀ phi : A →ₐ[K] L,
      CategoryTheory.Abelian.Ext
        ((Scheme.Modules.pushforward
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi)).obj
          (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf))
        Y n) :
    ∃ z : CategoryTheory.Abelian.Ext
        ((Scheme.Modules.pushforward
          (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf))
        Y n,
      ∀ phi : A →ₐ[K] L,
        (CategoryTheory.Abelian.Ext.mk₀
          (biproduct.ι
            (fun phi : A →ₐ[K] L ↦
              (Scheme.Modules.pushforward
                (galoisEmbeddingBaseChangeGeometricPoint
                  p center hcenter phi)).obj
                (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf)) phi ≫
            (finiteSeparableGaloisPointPushforwardBiproductIso
              p center hcenter).hom)).comp z (zero_add n) = components phi := by
  exact ext_iso_biproduct_components_surjective
    (biproduct.isBilimit _)
    (finiteSeparableGaloisPointPushforwardBiproductIso p center hcenter)
    n components

/-- After tensoring by the line-bundle factor in Voisin's construction, the
finite-support sheaf remains the biproduct of the tensorized sheaves of the
actual geometric conjugate points. -/
noncomputable def finiteSeparableGaloisPointPushforwardTwistBiproductIso
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)] :
    (⨁ fun phi : A →ₐ[K] L ↦
      schemeModuleTensor
        ((Scheme.Modules.pushforward
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi)).obj
          (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf)) T) ≅
      schemeModuleTensor
        ((Scheme.Modules.pushforward
          (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf)) T :=
  schemeModuleTensorRightBiproductIso T
      (fun phi : A →ₐ[K] L ↦
        (Scheme.Modules.pushforward
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi)).obj
          (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf)) ≪≫
    (schemeModuleTensorRight T).mapIso
      (finiteSeparableGaloisPointPushforwardBiproductIso
        p center hcenter)

/-- The twisted finite-support decomposition, written directly as the third
objects of the closed-immersion ideal sequences for the individual Galois
points and for their full split union. -/
noncomputable def
    finiteSeparableGaloisPointIdealTwistSequenceBiproductIso
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)] :
    (⨁ fun phi : A →ₐ[K] L ↦
      (closedImmersionIdealTwistSequence
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter phi) T).X₃) ≅
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₃ :=
  finiteSeparableGaloisPointPushforwardTwistBiproductIso
    p center hcenter T

/-- Cover-trivialized form of the twisted finite-support decomposition.  The
finite-limit preservation required by the biproduct comparison is derived
from the supplied local trivializations of the twist. -/
noncomputable def
    finiteSeparableGaloisPointPushforwardTwistBiproductIso_of_coversTop_iso_unit
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    {I : Type u}
    (U : I → (schemeBaseChangeToField (L := L) X p).Opens)
    (hU : (Opens.grothendieckTopology
      (schemeBaseChangeToField (L := L) X p)).CoversTop U)
    (eU : ∀ j,
      (SheafOfModules.overFunctor
        (schemeBaseChangeToField (L := L) X p).ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver
          (schemeBaseChangeToField (L := L) X p).sheaf (U j)))) :
    (⨁ fun phi : A →ₐ[K] L ↦
      schemeModuleTensor
        ((Scheme.Modules.pushforward
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi)).obj
          (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf)) T) ≅
      schemeModuleTensor
        ((Scheme.Modules.pushforward
          (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf)) T := by
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit
      U hU eU
  exact finiteSeparableGaloisPointPushforwardTwistBiproductIso
    p center hcenter T

/-- The preceding cover-trivialized decomposition written as the third
objects of the individual and total closed-immersion ideal sequences. -/
noncomputable def
    finiteSeparableGaloisPointIdealTwistSequenceBiproductIso_of_coversTop_iso_unit
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    {I : Type u}
    (U : I → (schemeBaseChangeToField (L := L) X p).Opens)
    (hU : (Opens.grothendieckTopology
      (schemeBaseChangeToField (L := L) X p)).CoversTop U)
    (eU : ∀ j,
      (SheafOfModules.overFunctor
        (schemeBaseChangeToField (L := L) X p).ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver
          (schemeBaseChangeToField (L := L) X p).sheaf (U j)))) :
    (⨁ fun phi : A →ₐ[K] L ↦
      (closedImmersionIdealTwistSequence
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter phi) T).X₃) ≅
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₃ :=
  finiteSeparableGaloisPointPushforwardTwistBiproductIso_of_coversTop_iso_unit
    p center hcenter T U hU eU

/-- Ext classes supported on the split finite point are jointly detected by
any injective collection of coordinates on the individual point-supported
Ext groups.  This is the global-to-local categorical step in Voisin's
argument, now instantiated on the actual scalar-extended finite point. -/
theorem finiteSeparableProductModelExt_jointly_detect
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    (Y : (schemeBaseChangeToField (L := L) X p).Modules) (n : ℕ)
    {W : PrimeSpectrum (L ⊗[K] A) → Type*}
    [∀ i, AddCommMonoid (W i)]
    (coordinate : ∀ i,
      CategoryTheory.Abelian.Ext
        (productCoordinatePointPushforwardToAmbient
          (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
          (finiteSeparableProductModelToAmbient p center hcenter) i)
        Y n →+ W i)
    (hcoordinate : ∀ i, Function.Injective (coordinate i))
    (z : CategoryTheory.Abelian.Ext
      ((Scheme.Modules.pushforward
        (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf))
      Y n)
    (hz : ∀ i, coordinate i
      ((CategoryTheory.Abelian.Ext.mk₀
        (biproduct.ι
          (fun i : PrimeSpectrum (L ⊗[K] A) ↦
            productCoordinatePointPushforwardToAmbient
              (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
              (finiteSeparableProductModelToAmbient p center hcenter) i) i ≫
          (finiteSeparableProductModelPushforwardBiproductIso
            p center hcenter).hom)).comp z (zero_add n)) = 0) :
    z = 0 := by
  apply ext_iso_biproduct_injective_coordinates_jointly_detect
    (biproduct.isBilimit _)
    (finiteSeparableProductModelPushforwardBiproductIso p center hcenter)
    n coordinate hcoordinate z
  exact hz

/-- Galois-indexed form of finite-support Ext detection.  Its summands are
the actual geometric conjugate point pushforwards on the scalar-extended
ambient scheme. -/
theorem finiteSeparableGaloisPointExt_jointly_detect
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    (Y : (schemeBaseChangeToField (L := L) X p).Modules) (n : ℕ)
    {W : (A →ₐ[K] L) → Type*} [∀ phi, AddCommMonoid (W phi)]
    (coordinate : ∀ phi,
      CategoryTheory.Abelian.Ext
        ((Scheme.Modules.pushforward
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi)).obj
          (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf))
        Y n →+ W phi)
    (hcoordinate : ∀ phi, Function.Injective (coordinate phi))
    (z : CategoryTheory.Abelian.Ext
      ((Scheme.Modules.pushforward
        (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf))
      Y n)
    (hz : ∀ phi, coordinate phi
      ((CategoryTheory.Abelian.Ext.mk₀
        (biproduct.ι
          (fun phi : A →ₐ[K] L ↦
            (Scheme.Modules.pushforward
              (galoisEmbeddingBaseChangeGeometricPoint
                p center hcenter phi)).obj
              (SheafOfModules.unit.{u}
                (Spec (.of L)).ringCatSheaf)) phi ≫
          (finiteSeparableGaloisPointPushforwardBiproductIso
            p center hcenter).hom)).comp z (zero_add n)) = 0) :
    z = 0 := by
  apply ext_iso_biproduct_injective_coordinates_jointly_detect
    (biproduct.isBilimit _)
    (finiteSeparableGaloisPointPushforwardBiproductIso p center hcenter)
    n coordinate hcoordinate z
  exact hz

/-- Twisted Galois-indexed finite-support detection.  This is the form
needed for the quotient term of Voisin's line-bundle-twisted ideal
sequence. -/
theorem finiteSeparableGaloisPointTwistExt_jointly_detect
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    (Y : (schemeBaseChangeToField (L := L) X p).Modules) (n : ℕ)
    {W : (A →ₐ[K] L) → Type*} [∀ phi, AddCommMonoid (W phi)]
    (coordinate : ∀ phi,
      CategoryTheory.Abelian.Ext
        (schemeModuleTensor
          ((Scheme.Modules.pushforward
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter phi)).obj
            (SheafOfModules.unit.{u} (Spec (.of L)).ringCatSheaf)) T)
        Y n →+ W phi)
    (hcoordinate : ∀ phi, Function.Injective (coordinate phi))
    (z : CategoryTheory.Abelian.Ext
      (schemeModuleTensor
        ((Scheme.Modules.pushforward
          (finiteSeparableProductModelToAmbient p center hcenter)).obj
          (SheafOfModules.unit.{u}
            (Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L))).ringCatSheaf)) T)
      Y n)
    (hz : ∀ phi, coordinate phi
      ((CategoryTheory.Abelian.Ext.mk₀
        (biproduct.ι
          (fun phi : A →ₐ[K] L ↦
            schemeModuleTensor
              ((Scheme.Modules.pushforward
                (galoisEmbeddingBaseChangeGeometricPoint
                  p center hcenter phi)).obj
                (SheafOfModules.unit.{u}
                  (Spec (.of L)).ringCatSheaf)) T) phi ≫
          (finiteSeparableGaloisPointPushforwardTwistBiproductIso
            p center hcenter T).hom)).comp z (zero_add n)) = 0) :
    z = 0 := by
  apply ext_iso_biproduct_injective_coordinates_jointly_detect
    (biproduct.isBilimit _)
    (finiteSeparableGaloisPointPushforwardTwistBiproductIso
      p center hcenter T)
    n coordinate hcoordinate z
  exact hz

/-- Closed-immersion-sequence form of twisted finite-support detection.  It
connects the Galois decomposition directly to the quotient objects used by
the Serre Yoneda product. -/
theorem finiteSeparableGaloisPointIdealTwistExt_jointly_detect
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    (Y : (schemeBaseChangeToField (L := L) X p).Modules) (n : ℕ)
    {W : (A →ₐ[K] L) → Type*} [∀ phi, AddCommMonoid (W phi)]
    (coordinate : ∀ phi,
      CategoryTheory.Abelian.Ext
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃ Y n →+ W phi)
    (hcoordinate : ∀ phi, Function.Injective (coordinate phi))
    (z : CategoryTheory.Abelian.Ext
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₃ Y n)
    (hz : ∀ phi, coordinate phi
      ((CategoryTheory.Abelian.Ext.mk₀
        (biproduct.ι
          (fun phi : A →ₐ[K] L ↦
            (closedImmersionIdealTwistSequence
              (galoisEmbeddingBaseChangeGeometricPoint
                p center hcenter phi) T).X₃) phi ≫
          (finiteSeparableGaloisPointIdealTwistSequenceBiproductIso
            p center hcenter T).hom)).comp z (zero_add n)) = 0) :
    z = 0 := by
  apply ext_iso_biproduct_injective_coordinates_jointly_detect
    (biproduct.isBilimit _)
    (finiteSeparableGaloisPointIdealTwistSequenceBiproductIso
      p center hcenter T)
    n coordinate hcoordinate z
  exact hz

/-- Precomposition with the `phi`th summand inclusion, followed by a chosen
point-supported coordinate.  This is the concrete component family consumed
by the Galois bad-locus argument. -/
noncomputable def finiteSeparableGaloisPointIdealTwistExtComponent
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T Y : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    (n : ℕ) {W : (A →ₐ[K] L) → Type*}
    [∀ phi, AddCommMonoid (W phi)]
    (coordinate : ∀ phi,
      CategoryTheory.Abelian.Ext
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃ Y n →+ W phi)
    (phi : A →ₐ[K] L) :
    CategoryTheory.Abelian.Ext
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₃ Y n →+
      W phi :=
  (coordinate phi).comp
    ((CategoryTheory.Abelian.Ext.mk₀
      (biproduct.ι
        (fun psi : A →ₐ[K] L ↦
          (closedImmersionIdealTwistSequence
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter psi) T).X₃) phi ≫
        (finiteSeparableGaloisPointIdealTwistSequenceBiproductIso
          p center hcenter T).hom)).precomp Y (zero_add n))

/-- The preceding actual Galois-point components jointly detect a twisted
finite-support Ext class whenever each point-supported coordinate is
injective. -/
theorem finiteSeparableGaloisPointIdealTwistExtComponents_jointly_detect
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T Y : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    (n : ℕ) {W : (A →ₐ[K] L) → Type*}
    [∀ phi, AddCommMonoid (W phi)]
    (coordinate : ∀ phi,
      CategoryTheory.Abelian.Ext
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃ Y n →+ W phi)
    (hcoordinate : ∀ phi, Function.Injective (coordinate phi))
    (z : CategoryTheory.Abelian.Ext
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₃ Y n)
    (hz : ∀ phi,
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T Y n coordinate phi z = 0) :
    z = 0 := by
  apply finiteSeparableGaloisPointIdealTwistExt_jointly_detect
    p center hcenter T Y n coordinate hcoordinate z
  exact hz

set_option linter.style.haveILetI false in
/-- Minimal local form of residue-component detection.  It only asks for an
identification of each point-supported source stalk with its codimension-two
complete-intersection quotient; in particular, the twisting sheaf need only
be trivial near the relevant point. -/
theorem finiteSeparableGaloisPointLocalResidueExtComponents_jointly_detect
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))]
    (f g : ∀ phi : A →ₐ[K] L,
      (schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi))
    (hf : ∀ phi, IsRegular (f phi))
    (hg : ∀ phi,
      IsRegular (Ideal.Quotient.mk (Ideal.span {f phi}) (g phi)))
    (hfm : ∀ phi, f phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hgm : ∀ phi, g phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hspan : ∀ phi,
      Ideal.span ({f phi, g phi} : Set
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))) =
      IsLocalRing.maximalIdeal
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (qM : ∀ phi,
      (schemeModuleStalkModuleFunctor
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)).obj
          (closedImmersionIdealTwistSequence
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter phi) T).X₃ ≅
      ModuleCat.of
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))
        (((schemeBaseChangeToField (L := L) X p).presheaf.stalk
            (galoisEmbeddingBaseChangePoint p center hcenter phi)) ⧸
          Ideal.span ({f phi, g phi} : Set _)))
    (hstalk : ∀ phi, Function.Injective
      (schemeModuleStalkModuleExtMap
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2))
    (z : CategoryTheory.Abelian.Ext
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₃
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2)
    (hz : ∀ phi,
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
        2
        (fun psi ↦ schemeModuleExtLocalResidueComponentLarge
          (galoisEmbeddingBaseChangePoint p center hcenter psi)
          (closedImmersionIdealTwistSequence
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter psi) T).X₃
          (show (schemeBaseChangeToField (L := L) X p).Modules from
            SheafOfModules.unit
              (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
          (f psi) (g psi)
          (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
          (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
          (hfm psi) (hgm psi) (qM psi)
          (schemeModuleUnitStalkIso _ _)) phi z = 0) :
    z = 0 := by
  apply finiteSeparableGaloisPointIdealTwistExtComponents_jointly_detect
    p center hcenter T
    (show (schemeBaseChangeToField (L := L) X p).Modules from
      SheafOfModules.unit
        (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
    2
    (fun psi ↦ schemeModuleExtLocalResidueComponentLarge
      (galoisEmbeddingBaseChangePoint p center hcenter psi)
      (closedImmersionIdealTwistSequence
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter psi) T).X₃
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
      (f psi) (g psi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
      (hfm psi) (hgm psi) (qM psi)
      (schemeModuleUnitStalkIso _ _))
  · intro phi
    exact schemeModuleExtLocalResidueComponentLarge_injective
      (galoisEmbeddingBaseChangePoint p center hcenter phi)
      (closedImmersionIdealTwistSequence
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter phi) T).X₃
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
      (f phi) (g phi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf phi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg phi))
      (hfm phi) (hgm phi) (qM phi)
      (schemeModuleUnitStalkIso _ _) (hspan phi) (hstalk phi)
  exact hz

set_option linter.style.haveILetI false in
/-- The actual local complete-intersection residue maps jointly detect a
degree-two Ext class supported on a split finite separable orbit.  This
specializes the abstract point-coordinate theorem to the literal stalk and
residue maps used in Voisin's local calculation. -/
theorem finiteSeparableGaloisPointResidueExtComponents_jointly_detect
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))]
    (eT : T ≅ SheafOfModules.unit
      (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
    (f g : ∀ phi : A →ₐ[K] L,
      (schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi))
    (hkernel : ∀ phi,
      let i := galoisEmbeddingBaseChangeGeometricPoint
        p center hcenter phi
      let x := galoisEmbeddingBaseChangePoint p center hcenter phi
      letI : Module
          ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x)
          ((show (schemeBaseChangeToField (L := L) X p).Modules from
            (Scheme.Modules.pushforward i).obj
              (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk x) :=
        schemeModuleStalkModule _ x
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f phi, g phi} : Set _))
    (hf : ∀ phi, IsRegular (f phi))
    (hg : ∀ phi,
      IsRegular (Ideal.Quotient.mk (Ideal.span {f phi}) (g phi)))
    (hfm : ∀ phi, f phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hgm : ∀ phi, g phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hspan : ∀ phi,
      Ideal.span ({f phi, g phi} : Set
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))) =
      IsLocalRing.maximalIdeal
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hstalk : ∀ phi, Function.Injective
      (schemeModuleStalkModuleExtMap
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2))
    (z : CategoryTheory.Abelian.Ext
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₃
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2)
    (hz : ∀ phi,
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
        2
        (fun psi ↦ serreYonedaResidueComponent
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter psi) eT
          (galoisEmbeddingBaseChangePoint p center hcenter psi)
          (f psi) (g psi) (hkernel psi)
          (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
          (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
          (hfm psi) (hgm psi)) phi z = 0) :
    z = 0 := by
  apply finiteSeparableGaloisPointIdealTwistExtComponents_jointly_detect
    p center hcenter T
    (show (schemeBaseChangeToField (L := L) X p).Modules from
      SheafOfModules.unit
        (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
    2
    (fun psi ↦ serreYonedaResidueComponent
      (galoisEmbeddingBaseChangeGeometricPoint
        p center hcenter psi) eT
      (galoisEmbeddingBaseChangePoint p center hcenter psi)
      (f psi) (g psi) (hkernel psi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
      (hfm psi) (hgm psi))
  · intro phi
    exact serreYonedaResidueComponent_injective
      (galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi) eT
      (galoisEmbeddingBaseChangePoint p center hcenter phi)
      (f phi) (g phi) (hkernel phi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf phi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg phi))
      (hfm phi) (hgm phi) (hspan phi) (hstalk phi)
  exact hz

/-- Voisin's Galois bad-locus conclusion when exactness of the actual
twisted ideal sequence is supplied directly.  Finite-limit preservation is
still used for the finite-support biproduct decomposition, but no global
right-exactness hypothesis on every tensor sequence is needed. -/
theorem finiteSeparableGaloisPoint_badLocus_eq_empty_of_shortExact_of_pointwise_vanishing
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Normal K L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T Y : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    (hS : (closedImmersionIdealTwistSequence
      (finiteSeparableProductModelToAmbient p center hcenter) T).ShortExact)
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₂ Y 1)]
    {W : (A →ₐ[K] L) → Type*} [∀ phi, AddCommMonoid (W phi)]
    (coordinate : ∀ phi,
      CategoryTheory.Abelian.Ext
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃ Y 2 →+ W phi)
    (hcoordinate : ∀ phi, Function.Injective (coordinate phi))
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (sigma : L ≃ₐ[K] L) (phi : A →ₐ[K] L), phi ∈ B →
      sigma.toAlgHom.comp phi ∈ B)
    (e : CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwist
        (finiteSeparableProductModelToAmbient p center hcenter) T) Y 1)
    (hne : e ≠ 0)
    (hbad : ∀ phi, phi ∈ B →
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T Y 2 coordinate phi
        (hS.extClass.comp e (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  exact
    galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt_of_shortExact_of_pointwise_vanishing
    (K := K) (A := A) (L := L)
    (finiteSeparableProductModelToAmbient p center hcenter) T Y hS
    B hstable e hne
    (finiteSeparableGaloisPointIdealTwistExtComponent
      p center hcenter T Y 2 coordinate)
    (fun z hz ↦
      finiteSeparableGaloisPointIdealTwistExtComponents_jointly_detect
        p center hcenter T Y 2 coordinate hcoordinate z hz)
    hbad

/-- Voisin's Galois bad-locus conclusion with the global component-detection
hypothesis discharged by the actual split finite-support decomposition.  The
remaining inputs are point-supported injective coordinates and their
vanishing at bad conjugate points. -/
theorem finiteSeparableGaloisPoint_badLocus_eq_empty_of_pointwise_vanishing
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Normal K L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T Y : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₂ Y 1)]
    {W : (A →ₐ[K] L) → Type*} [∀ phi, AddCommMonoid (W phi)]
    (coordinate : ∀ phi,
      CategoryTheory.Abelian.Ext
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃ Y 2 →+ W phi)
    (hcoordinate : ∀ phi, Function.Injective (coordinate phi))
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (sigma : L ≃ₐ[K] L) (phi : A →ₐ[K] L), phi ∈ B →
      sigma.toAlgHom.comp phi ∈ B)
    (e : CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwist
        (finiteSeparableProductModelToAmbient p center hcenter) T) Y 1)
    (hne : e ≠ 0)
    (hbad : ∀ phi, phi ∈ B →
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T Y 2 coordinate phi
        ((closedImmersionIdealTwistSequence_shortExact
          (finiteSeparableProductModelToAmbient p center hcenter) T).extClass.comp
            e (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  exact
    finiteSeparableGaloisPoint_badLocus_eq_empty_of_shortExact_of_pointwise_vanishing
      p center hcenter T Y
      (closedImmersionIdealTwistSequence_shortExact
        (finiteSeparableProductModelToAmbient p center hcenter) T)
      coordinate hcoordinate B hstable e hne hbad

set_option linter.style.haveILetI false in
/-- Local-trivialization form of Voisin's bad-locus conclusion.  The source
stalk is identified directly with its complete-intersection quotient, so no
global trivialization of the projective twisting sheaf is required. -/
theorem finiteSeparableGaloisPoint_badLocus_eq_empty_of_localResidue_vanishing
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Normal K L] [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    (hS : (closedImmersionIdealTwistSequence
      (finiteSeparableProductModelToAmbient p center hcenter) T).ShortExact)
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))]
    [Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₂
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 1)]
    (f g : ∀ phi : A →ₐ[K] L,
      (schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi))
    (hf : ∀ phi, IsRegular (f phi))
    (hg : ∀ phi,
      IsRegular (Ideal.Quotient.mk (Ideal.span {f phi}) (g phi)))
    (hfm : ∀ phi, f phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hgm : ∀ phi, g phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hspan : ∀ phi,
      Ideal.span ({f phi, g phi} : Set
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))) =
      IsLocalRing.maximalIdeal
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (qM : ∀ phi,
      (schemeModuleStalkModuleFunctor
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)).obj
          (closedImmersionIdealTwistSequence
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter phi) T).X₃ ≅
      ModuleCat.of
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))
        (((schemeBaseChangeToField (L := L) X p).presheaf.stalk
            (galoisEmbeddingBaseChangePoint p center hcenter phi)) ⧸
          Ideal.span ({f phi, g phi} : Set _)))
    (hstalk : ∀ phi, Function.Injective
      (schemeModuleStalkModuleExtMap
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2))
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (sigma : L ≃ₐ[K] L) (phi : A →ₐ[K] L), phi ∈ B →
      sigma.toAlgHom.comp phi ∈ B)
    (e : CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwist
        (finiteSeparableProductModelToAmbient p center hcenter) T)
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 1)
    (hne : e ≠ 0)
    (hbad : ∀ phi, phi ∈ B →
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
        2
        (fun psi ↦ schemeModuleExtLocalResidueComponentLarge
          (galoisEmbeddingBaseChangePoint p center hcenter psi)
          (closedImmersionIdealTwistSequence
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter psi) T).X₃
          (show (schemeBaseChangeToField (L := L) X p).Modules from
            SheafOfModules.unit
              (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
          (f psi) (g psi)
          (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
          (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
          (hfm psi) (hgm psi) (qM psi)
          (schemeModuleUnitStalkIso _ _)) phi
        (hS.extClass.comp e (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  apply
    finiteSeparableGaloisPoint_badLocus_eq_empty_of_shortExact_of_pointwise_vanishing
    p center hcenter T
    (show (schemeBaseChangeToField (L := L) X p).Modules from
      SheafOfModules.unit
        (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
    hS
    (fun psi ↦ schemeModuleExtLocalResidueComponentLarge
      (galoisEmbeddingBaseChangePoint p center hcenter psi)
      (closedImmersionIdealTwistSequence
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter psi) T).X₃
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
      (f psi) (g psi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
      (hfm psi) (hgm psi) (qM psi)
      (schemeModuleUnitStalkIso _ _))
  · intro phi
    exact schemeModuleExtLocalResidueComponentLarge_injective
      (galoisEmbeddingBaseChangePoint p center hcenter phi)
      (closedImmersionIdealTwistSequence
        (galoisEmbeddingBaseChangeGeometricPoint
          p center hcenter phi) T).X₃
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
      (f phi) (g phi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf phi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg phi))
      (hfm phi) (hgm phi) (qM phi)
      (schemeModuleUnitStalkIso _ _) (hspan phi) (hstalk phi)
  · exact hstable
  · exact hne
  exact hbad

set_option linter.style.haveILetI false in
/-- The degree-two stalk injectivity needed by the residue criterion follows
from the exact kernel-image-zero condition at each geometric conjugate point.
Unlike vanishing of the whole kernel Ext group, this asks only that its map
into Ext against the ambient structure sheaf be zero. -/
theorem finiteSeparableGaloisPoint_stalkExtTwo_injective_of_kernel_image_zero
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))]
    (hkernelImage : ∀ phi : A →ₐ[K] L,
      let Y := schemeBaseChangeToField (L := L) X p
      let x := galoisEmbeddingBaseChangePoint p center hcenter phi
      let i := galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi
      let M := (closedImmersionIdealTwistSequence i T).X₃
      let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
      let f := schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor Y x).obj N))
      ∀ k : CategoryTheory.Abelian.Ext M (kernel f) 2,
        k.comp (CategoryTheory.Abelian.Ext.mk₀ (kernel.ι f))
          (add_zero 2) = 0) :
    ∀ phi : A →ₐ[K] L, Function.Injective
      (schemeModuleStalkModuleExtMap
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2) := by
  intro phi
  let i := galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi
  let x := galoisEmbeddingBaseChangePoint p center hcenter phi
  let Y := schemeBaseChangeToField (L := L) X p
  let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let M := (closedImmersionIdealTwistSequence i T).X₃
  have hix : i default = x := by
    change i default = i (specClosedPoint L)
    exact congrArg i (Subsingleton.elim _ _)
  have hxclosed : IsClosed ({x} : Set Y) := by
    rw [← hix]
    exact fieldPoint_image_isClosed i
  apply schemeModuleStalkModuleExtMap_injective_of_kernel_image_zero
    x hxclosed M N 2
  exact hkernelImage phi

set_option linter.style.haveILetI false in
/-- On every point of the split finite separable orbit, the degree-two
global-to-stalk map is injective exactly when the kernel of the canonical map
to the stalk skyscraper has zero image in ambient Ext. -/
theorem finiteSeparableGaloisPoint_stalkExtTwo_injective_iff_kernel_image_zero
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))] :
    (∀ phi : A →ₐ[K] L, Function.Injective
      (schemeModuleStalkModuleExtMap
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2)) ↔
      (∀ phi : A →ₐ[K] L,
        let Y := schemeBaseChangeToField (L := L) X p
        let x := galoisEmbeddingBaseChangePoint p center hcenter phi
        let i := galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi
        let M := (closedImmersionIdealTwistSequence i T).X₃
        let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
        let f := schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor Y x).obj N))
        ∀ k : CategoryTheory.Abelian.Ext M (kernel f) 2,
          k.comp (CategoryTheory.Abelian.Ext.mk₀ (kernel.ι f))
            (add_zero 2) = 0) := by
  constructor
  · intro hstalk phi
    let i := galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi
    let x := galoisEmbeddingBaseChangePoint p center hcenter phi
    let Y := schemeBaseChangeToField (L := L) X p
    let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let M := (closedImmersionIdealTwistSequence i T).X₃
    have hix : i default = x := by
      change i default = i (specClosedPoint L)
      exact congrArg i (Subsingleton.elim _ _)
    have hxclosed : IsClosed ({x} : Set Y) := by
      rw [← hix]
      exact fieldPoint_image_isClosed i
    exact (schemeModuleStalkModuleExtMap_injective_iff_kernel_image_zero
      x hxclosed M N 2).mp (hstalk phi)
  · exact finiteSeparableGaloisPoint_stalkExtTwo_injective_of_kernel_image_zero
      p center hcenter T

set_option linter.style.haveILetI false in
attribute [local instance] CategoryTheory.Abelian.Ext.subsingleton_of_injective in
/-- Vanishing of the kernel Ext group at every conjugate point supplies the
weaker kernel-image-zero premise. -/
theorem finiteSeparableGaloisPoint_stalkExtTwo_injective_of_kernel_ext_subsingleton
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))]
    (hkernelExt : ∀ phi : A →ₐ[K] L,
      Subsingleton (CategoryTheory.Abelian.Ext
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃
        (kernel (schemeModuleToSkyscraper
          (galoisEmbeddingBaseChangePoint p center hcenter phi)
          (𝟙 ((schemeModuleStalkModuleFunctor
            (schemeBaseChangeToField (L := L) X p)
            (galoisEmbeddingBaseChangePoint p center hcenter phi)).obj
              (show (schemeBaseChangeToField (L := L) X p).Modules from
                SheafOfModules.unit
                  (schemeBaseChangeToField (L := L) X p).ringCatSheaf))))) 2)) :
    ∀ phi : A →ₐ[K] L, Function.Injective
      (schemeModuleStalkModuleExtMap
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)
        (closedImmersionIdealTwistSequence
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter phi) T).X₃
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 2) := by
  apply finiteSeparableGaloisPoint_stalkExtTwo_injective_of_kernel_image_zero
    p center hcenter T
  intro phi
  dsimp only
  intro k
  rw [@Subsingleton.elim _ (hkernelExt phi) k 0]
  exact CategoryTheory.Abelian.Ext.zero_comp _ _ _ _ _

set_option linter.style.haveILetI false in
/-- Voisin's bad-locus conclusion in the form used for a projective twist.
The twist is trivialized only at each conjugate point, its global
cohomological input is the inverse-twist vanishing `Ext¹(O_Y, Tinv) = 0`,
and the degree-two global-to-local comparison is supplied by the exact
kernel-image-zero condition. -/
theorem finiteSeparableGaloisPoint_badLocus_eq_empty_of_localResidue_kernel_image_zero
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Normal K L] [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    (Tinv : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))]
    (tensorUnitIso : 𝟭 (schemeBaseChangeToField (L := L) X p).Modules ≅
      schemeModuleTensorRight Tinv ⋙ schemeModuleTensorRight T)
    (tensorCounitIso : schemeModuleTensorRight T ⋙
      schemeModuleTensorRight Tinv ≅
        𝟭 (schemeBaseChangeToField (L := L) X p).Modules)
    (tensorInverseIso : schemeModuleTensor T Tinv ≅
      SheafOfModules.unit
        (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
    [Subsingleton (schemeModuleCohomology
      (schemeBaseChangeToField (L := L) X p) Tinv 1)]
    (f g : ∀ phi : A →ₐ[K] L,
      (schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi))
    (hf : ∀ phi, IsRegular (f phi))
    (hg : ∀ phi,
      IsRegular (Ideal.Quotient.mk (Ideal.span {f phi}) (g phi)))
    (hfm : ∀ phi, f phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hgm : ∀ phi, g phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hspan : ∀ phi,
      Ideal.span ({f phi, g phi} : Set
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))) =
      IsLocalRing.maximalIdeal
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (qM : ∀ phi,
      (schemeModuleStalkModuleFunctor
        (schemeBaseChangeToField (L := L) X p)
        (galoisEmbeddingBaseChangePoint p center hcenter phi)).obj
          (closedImmersionIdealTwistSequence
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter phi) T).X₃ ≅
      ModuleCat.of
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))
        (((schemeBaseChangeToField (L := L) X p).presheaf.stalk
            (galoisEmbeddingBaseChangePoint p center hcenter phi)) ⧸
          Ideal.span ({f phi, g phi} : Set _)))
    (hkernelImage : ∀ phi : A →ₐ[K] L,
      let Y := schemeBaseChangeToField (L := L) X p
      let x := galoisEmbeddingBaseChangePoint p center hcenter phi
      let i := galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi
      let M := (closedImmersionIdealTwistSequence i T).X₃
      let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
      let f₀ := schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor Y x).obj N))
      ∀ k : CategoryTheory.Abelian.Ext M (kernel f₀) 2,
        k.comp (CategoryTheory.Abelian.Ext.mk₀ (kernel.ι f₀))
          (add_zero 2) = 0)
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (sigma : L ≃ₐ[K] L) (phi : A →ₐ[K] L), phi ∈ B →
      sigma.toAlgHom.comp phi ∈ B)
    (e : CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwist
        (finiteSeparableProductModelToAmbient p center hcenter) T)
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 1)
    (hne : e ≠ 0)
    (hbad : ∀ phi, phi ∈ B →
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
        2
        (fun psi ↦ schemeModuleExtLocalResidueComponentLarge
          (galoisEmbeddingBaseChangePoint p center hcenter psi)
          (closedImmersionIdealTwistSequence
            (galoisEmbeddingBaseChangeGeometricPoint
              p center hcenter psi) T).X₃
          (show (schemeBaseChangeToField (L := L) X p).Modules from
            SheafOfModules.unit
              (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
          (f psi) (g psi)
          (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
          (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
          (hfm psi) (hgm psi) (qM psi)
          (schemeModuleUnitStalkIso _ _)) phi
        ((closedImmersionIdealTwistSequence_shortExact
          (finiteSeparableProductModelToAmbient p center hcenter) T).extClass.comp
            e (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  let Y := schemeBaseChangeToField (L := L) X p
  let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  letI : Subsingleton (CategoryTheory.Abelian.Ext
      (show Y.Modules from T) N 1) :=
    schemeModule_twist_ext_subsingleton_of_tensor_inverse T Tinv
      tensorUnitIso tensorCounitIso tensorInverseIso 1
  letI : Subsingleton (CategoryTheory.Abelian.Ext
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₂ N 1) :=
    closedImmersionIdealTwistSequence_middle_ext_subsingleton_of_iso
      (finiteSeparableProductModelToAmbient p center hcenter) T T N
      (Iso.refl T) 1
  have hstalk :=
    finiteSeparableGaloisPoint_stalkExtTwo_injective_of_kernel_image_zero
      p center hcenter T hkernelImage
  apply finiteSeparableGaloisPoint_badLocus_eq_empty_of_localResidue_vanishing
    p center hcenter T
    (closedImmersionIdealTwistSequence_shortExact
      (finiteSeparableProductModelToAmbient p center hcenter) T)
    f g hf hg hfm hgm hspan qM hstalk B hstable e hne
  exact hbad

set_option linter.style.haveILetI false in
/-- Specialization of the bad-locus conclusion to a globally trivial twist.
The support-theoretic input is the exact kernel-image-zero condition, and the
cohomological premise reduces to `Ext¹(O_Y, O_Y) = 0`.  The projective-twist
form used in Voisin's argument is
`finiteSeparableGaloisPoint_badLocus_eq_empty_of_localResidue_kernel_image_zero`
above. -/
theorem finiteSeparableGaloisPoint_badLocus_eq_empty_of_residue_vanishing
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    [Normal K L] [Fintype (PrimeSpectrum (L ⊗[K] A))]
    (T : (schemeBaseChangeToField (L := L) X p).Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    [CategoryTheory.HasExt.{u}
      ((schemeBaseChangeToField (L := L) X p).Modules)]
    [∀ phi : A →ₐ[K] L, CategoryTheory.HasExt.{u + 1}
      (ModuleCat ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))]
    [Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 1)]
    (eT : T ≅ SheafOfModules.unit
      (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
    (f g : ∀ phi : A →ₐ[K] L,
      (schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi))
    (hkernel : ∀ phi,
      let i := galoisEmbeddingBaseChangeGeometricPoint
        p center hcenter phi
      let x := galoisEmbeddingBaseChangePoint p center hcenter phi
      letI : Module
          ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x)
          ((show (schemeBaseChangeToField (L := L) X p).Modules from
            (Scheme.Modules.pushforward i).obj
              (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk x) :=
        schemeModuleStalkModule _ x
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f phi, g phi} : Set _))
    (hf : ∀ phi, IsRegular (f phi))
    (hg : ∀ phi,
      IsRegular (Ideal.Quotient.mk (Ideal.span {f phi}) (g phi)))
    (hfm : ∀ phi, f phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hgm : ∀ phi, g phi ∈ IsLocalRing.maximalIdeal
      ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
        (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hspan : ∀ phi,
      Ideal.span ({f phi, g phi} : Set
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi))) =
      IsLocalRing.maximalIdeal
        ((schemeBaseChangeToField (L := L) X p).presheaf.stalk
          (galoisEmbeddingBaseChangePoint p center hcenter phi)))
    (hkernelImage : ∀ phi : A →ₐ[K] L,
      let Y := schemeBaseChangeToField (L := L) X p
      let x := galoisEmbeddingBaseChangePoint p center hcenter phi
      let i := galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi
      let M := (closedImmersionIdealTwistSequence i T).X₃
      let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
      let f₀ := schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor Y x).obj N))
      ∀ k : CategoryTheory.Abelian.Ext M (kernel f₀) 2,
        k.comp (CategoryTheory.Abelian.Ext.mk₀ (kernel.ι f₀))
          (add_zero 2) = 0)
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (sigma : L ≃ₐ[K] L) (phi : A →ₐ[K] L), phi ∈ B →
      sigma.toAlgHom.comp phi ∈ B)
    (e : CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwist
        (finiteSeparableProductModelToAmbient p center hcenter) T)
      (show (schemeBaseChangeToField (L := L) X p).Modules from
        SheafOfModules.unit
          (schemeBaseChangeToField (L := L) X p).ringCatSheaf) 1)
    (hne : e ≠ 0)
    (hbad : ∀ phi, phi ∈ B →
      finiteSeparableGaloisPointIdealTwistExtComponent
        p center hcenter T
        (show (schemeBaseChangeToField (L := L) X p).Modules from
          SheafOfModules.unit
            (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
        2
        (fun psi ↦ serreYonedaResidueComponent
          (galoisEmbeddingBaseChangeGeometricPoint
            p center hcenter psi) eT
          (galoisEmbeddingBaseChangePoint p center hcenter psi)
          (f psi) (g psi) (hkernel psi)
          (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
          (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
          (hfm psi) (hgm psi)) phi
        ((closedImmersionIdealTwistSequence_shortExact
          (finiteSeparableProductModelToAmbient p center hcenter) T).extClass.comp
            e (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  let Y := schemeBaseChangeToField (L := L) X p
  let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  letI : Subsingleton (CategoryTheory.Abelian.Ext
      (closedImmersionIdealTwistSequence
        (finiteSeparableProductModelToAmbient p center hcenter) T).X₂ N 1) :=
    closedImmersionIdealTwistSequence_middle_ext_subsingleton_of_iso
      (finiteSeparableProductModelToAmbient p center hcenter) T N N eT 1
  have hstalk :=
    finiteSeparableGaloisPoint_stalkExtTwo_injective_of_kernel_image_zero
      p center hcenter T hkernelImage
  apply finiteSeparableGaloisPoint_badLocus_eq_empty_of_pointwise_vanishing
    p center hcenter T
    (show (schemeBaseChangeToField (L := L) X p).Modules from
      SheafOfModules.unit
        (schemeBaseChangeToField (L := L) X p).ringCatSheaf)
    (fun psi ↦ serreYonedaResidueComponent
      (galoisEmbeddingBaseChangeGeometricPoint
        p center hcenter psi) eT
      (galoisEmbeddingBaseChangePoint p center hcenter psi)
      (f psi) (g psi) (hkernel psi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf psi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg psi))
      (hfm psi) (hgm psi))
  · intro phi
    exact serreYonedaResidueComponent_injective
      (galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi) eT
      (galoisEmbeddingBaseChangePoint p center hcenter phi)
      (f phi) (g phi) (hkernel phi)
      (isRegular_iff_mem_nonZeroDivisors.mp (hf phi))
      (isRegular_iff_mem_nonZeroDivisors.mp (hg phi))
      (hfm phi) (hgm phi) (hspan phi) (hstalk phi)
  · exact hstable
  · exact hne
  exact hbad

end PfaffianDescent
