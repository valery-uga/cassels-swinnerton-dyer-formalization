import PfaffianDescent.AffineBaseChangeQuotientPresentation
import PfaffianDescent.AffineQuotientPushforwardTilde
import PfaffianDescent.TargetAffineQuotientSheaf
import PfaffianDescent.AffineGammaPushforward

/-! The affine base-changed quotient as a module over the source ring. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-- The categorical cokernel of an ideal inclusion is its ordinary
quotient module. -/
noncomputable def idealInclusionCokernelIsoQuotient
    {A : Type u} [CommRing A] (I : Ideal A) :
    cokernel (ModuleCat.ofHom I.subtype) ≅ ModuleCat.of A (A ⧸ I) := by
  let f := ModuleCat.ofHom I.subtype
  have h : LinearMap.range I.subtype = I :=
    Submodule.range_subtype (I : Submodule A A)
  exact ModuleCat.cokernelIsoRangeQuotient f ≪≫
    (Submodule.quotEquivOfEq _ _ h).toModuleIso

/-- The categorical cokernel projection becomes the usual quotient map. -/
theorem idealInclusionCokernelIsoQuotient_π
    {A : Type u} [CommRing A] (I : Ideal A) :
    cokernel.π (ModuleCat.ofHom I.subtype) ≫
      (idealInclusionCokernelIsoQuotient I).hom =
    ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I)) := by
  let f := ModuleCat.ofHom I.subtype
  have h : LinearMap.range I.subtype = I :=
    Submodule.range_subtype (I : Submodule A A)
  change cokernel.π f ≫
    (ModuleCat.cokernelIsoRangeQuotient f ≪≫
      (Submodule.quotEquivOfEq _ _ h).toModuleIso).hom = _
  rw [Iso.trans_hom, ← Category.assoc,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Submodule.quotEquivOfEq_mk _ _ h a

/-- After affine sheafification, the cokernel of the `tilde` ideal
inclusion is the `tilde` sheaf of the quotient module. -/
noncomputable def tildeIdealInclusionCokernelIsoQuotient
    {A : Type u} [CommRing A] (I : Ideal A) :
    cokernel ((tilde.functor (CommRingCat.of A)).map
      (ModuleCat.ofHom I.subtype)) ≅
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (A ⧸ I)) := by
  letI : (tilde.functor (CommRingCat.of A)).IsLeftAdjoint :=
    tilde.adjunction.isLeftAdjoint
  letI : (tilde.functor (CommRingCat.of A)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact (PreservesCokernel.iso (tilde.functor (CommRingCat.of A))
      (ModuleCat.ofHom I.subtype)).symm ≪≫
    (tilde.functor (CommRingCat.of A)).mapIso
      (idealInclusionCokernelIsoQuotient I)

/-- The affine sheaf cokernel projection is the sheafified quotient map. -/
theorem tildeIdealInclusionCokernelIsoQuotient_π
    {A : Type u} [CommRing A] (I : Ideal A) :
    cokernel.π ((tilde.functor (CommRingCat.of A)).map
        (ModuleCat.ofHom I.subtype)) ≫
      (tildeIdealInclusionCokernelIsoQuotient I).hom =
    (tilde.functor (CommRingCat.of A)).map
      (ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I))) := by
  let F := tilde.functor (CommRingCat.of A)
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  let f := ModuleCat.ofHom I.subtype
  let e := idealInclusionCokernelIsoQuotient I
  change cokernel.π (F.map f) ≫
    ((PreservesCokernel.iso F f).symm ≪≫ F.mapIso e).hom = _
  rw [Iso.trans_hom, ← Category.assoc]
  have h : cokernel.π (F.map f) ≫ (PreservesCokernel.iso F f).inv =
      F.map (cokernel.π f) := by
    apply (cancel_mono (PreservesCokernel.iso F f).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (PreservesCokernel.π_iso_hom F f).symm
  change (cokernel.π (F.map f) ≫ (PreservesCokernel.iso F f).inv) ≫
    F.map e.hom = _
  rw [h, ← F.map_comp, idealInclusionCokernelIsoQuotient_π]

/-- The sheaf cokernel presentation is the actual pushforward structure
sheaf for the affine quotient closed immersion. -/
noncomputable def affineQuotientTildePushforwardIso
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (A ⧸ I)) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf) := by
  dsimp only
  let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  letI : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  let F := tilde.functor (CommRingCat.of A)
  let eI := affineQuotientIdealTildeClosedImmersionModuleIso I
  let eU := affineGlobalSectionsUnitTildeIso (A := A)
  let c := F.map (ModuleCat.ofHom I.subtype)
  let d := IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)
  have h : c ≫ eU.hom = eI.hom ≫ d :=
    (affineQuotientIdealTildeClosedImmersionModuleIso_hom_toUnit I).symm
  exact (tildeIdealInclusionCokernelIsoQuotient I).symm ≪≫
    cokernel.mapIso c d eI eU h ≪≫
    closedImmersionPushforwardCokernelIso (Spec.map φ)

/-- The affine quotient sheaf comparison carries the sheafified quotient
map to the actual unit-to-pushforward map. -/
theorem affineQuotientTildePushforwardIso_quotient
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    (tilde.functor (CommRingCat.of A)).map
        (ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I))) ≫
      (affineQuotientTildePushforwardIso I).hom =
    (affineGlobalSectionsUnitTildeIso (A := A)).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ) := by
  dsimp only
  let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  letI : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  let F := tilde.functor (CommRingCat.of A)
  let c := F.map (ModuleCat.ofHom I.subtype)
  let d := IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)
  let eQ := tildeIdealInclusionCokernelIsoQuotient I
  let eI := affineQuotientIdealTildeClosedImmersionModuleIso I
  let eU := affineGlobalSectionsUnitTildeIso (A := A)
  let eC := cokernel.mapIso c d eI eU
    (affineQuotientIdealTildeClosedImmersionModuleIso_hom_toUnit I).symm
  let eP := closedImmersionPushforwardCokernelIso (Spec.map φ)
  have hQ : cokernel.π c ≫ eQ.hom =
      F.map (ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I))) :=
    tildeIdealInclusionCokernelIsoQuotient_π I
  have hC : cokernel.π c ≫ eC.hom =
      eU.hom ≫ cokernel.π d := cokernel.π_desc _ _ _
  have hP : cokernel.π d ≫ eP.hom =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ) :=
    closedImmersionPushforwardCokernelIso_π (Spec.map φ)
  change F.map (ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I))) ≫
    (eQ.symm ≪≫ eC ≪≫ eP).hom = _
  rw [← hQ]
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change (cokernel.π c ≫ eC.hom) ≫ eP.hom =
    eU.hom ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
  rw [hC]
  exact (Category.assoc eU.hom (cokernel.π d) eP.hom).trans
    (congrArg (fun q => eU.hom ≫ q) hP)

/-- The quotient coordinate ring and the tensor-product coordinate ring
agree as algebras over `B`, compatibly with the quotient map from `B`. -/
noncomputable def affineBaseChangeQuotientAlgEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (B ⧸ K) ≃ₐ[B] B ⊗[A] (A ⧸ I) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  apply AlgEquiv.ofRingEquiv (f := affineBaseChangeQuotientRingEquiv g I)
  intro b
  change affineBaseChangeQuotientRingEquiv g I (Ideal.Quotient.mk K b) =
    (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)) b
  exact affineBaseChangeQuotientRingEquiv_mk g I b

/-- The same comparison as an isomorphism of `B`-modules, ready for the
affine `tilde` functor. -/
noncomputable def affineBaseChangeQuotientModuleIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    ModuleCat.of B (B ⧸ K) ≅ ModuleCat.of B (B ⊗[A] (A ⧸ I)) := by
  letI : Algebra A B := g.toAlgebra
  exact (affineBaseChangeQuotientAlgEquiv g I).toLinearEquiv.toModuleIso

/-- On the quotient of `B`, the module isomorphism is the canonical
tensor-product quotient map. -/
theorem affineBaseChangeQuotientModuleIso_mk
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) (b : B) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (affineBaseChangeQuotientModuleIso g I).hom.hom (Ideal.Quotient.mk K b) =
      (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := A ⧸ I)) b := by
  letI : Algebra A B := g.toAlgebra
  change affineBaseChangeQuotientAlgEquiv g I (Ideal.Quotient.mk _ b) = _
  exact affineBaseChangeQuotientRingEquiv_mk g I b

/-- The module isomorphism carries the `B`-linear quotient map to the
`B`-linear tensor-product map. This is the square used after applying
the affine `tilde` functor. -/
theorem affineBaseChangeQuotientModuleIso_quotient
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    ModuleCat.ofHom (Algebra.linearMap B (B ⧸ K)) ≫
      (affineBaseChangeQuotientModuleIso g I).hom =
    ModuleCat.ofHom (Algebra.linearMap B (B ⊗[A] (A ⧸ I))) := by
  letI : Algebra A B := g.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact affineBaseChangeQuotientModuleIso_mk g I b

/-- Pulling back the affine quotient sheaf is the tilde sheaf of the
actual base-changed quotient ring. -/
noncomputable def affineQuotientTildePullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (A ⧸ I))) ≅
    (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (B ⧸ K)) := by
  letI : Algebra A B := g.toAlgebra
  exact (affineTildePullbackNatIso (CommRingCat.ofHom g)).app
      (ModuleCat.of A (A ⧸ I)) ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (affineBaseChangeQuotientModuleIso g I).symm

/-- On affine spectra, pulling back the quotient pushforward agrees with
the pushforward from the actual quotient presentation of the fibre product. -/
noncomputable def affineQuotientPushforwardPullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let ψ : CommRingCat.of B ⟶ CommRingCat.of (B ⧸ K) :=
      CommRingCat.ofHom (Ideal.Quotient.mk K)
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (Spec.map ψ)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ K))).ringCatSheaf) := by
  letI : Algebra A B := g.toAlgebra
  exact (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso
      (affineQuotientTildePushforwardIso I).symm ≪≫
    affineQuotientTildePullbackIso g I ≪≫
    affineQuotientTildePushforwardIso
      (RingHom.ker (Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom)

/-- For flat affine base change, the exact-sequence presentation gives a
quotient pushforward isomorphism compatible with the actual ideal maps. -/
noncomputable def flatAffineQuotientPushforwardPullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let ψ : CommRingCat.of B ⟶ CommRingCat.of (B ⧸ K) :=
      CommRingCat.ofHom (Ideal.Quotient.mk K)
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (Spec.map ψ)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ K))).ringCatSheaf) := by
  letI : Algebra A B := g.toAlgebra
  letI : Flat (Spec.map (CommRingCat.ofHom g)) :=
    Flat.SpecMap_iff.mpr hg
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let ψ := CommRingCat.ofHom (Ideal.Quotient.mk K)
  letI : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  letI : IsClosedImmersion (Spec.map ψ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of B) K
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))
  let c := P.map (IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ))
  let d := IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map ψ)
  let eI := flatAffineClosedImmersionIdealModulePullbackIso g hg I
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (Spec.map (CommRingCat.ofHom g))) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison _
  let eU := asIso (BundleSectionZeroLocus.pullbackUnitComparison
    (Spec.map (CommRingCat.ofHom g)))
  have h : c ≫ eU.hom = eI.hom ≫ d :=
    (flatAffineClosedImmersionIdealModulePullbackIso_hom_toCanonicalUnit g hg I).symm
  exact (flatClosedImmersionPullbackQuotientIsoCokernel
      (Spec.map (CommRingCat.ofHom g)) (Spec.map φ)).symm ≪≫
    cokernel.mapIso c d eI eU h ≪≫
    closedImmersionPushforwardCokernelIso (Spec.map ψ)

/-- The exact-sequence affine comparison is characterized by the canonical
quotient-map square. -/
theorem flatAffineQuotientPushforwardPullbackIso_quotient
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let ψ : CommRingCat.of B ⟶ CommRingCat.of (B ⧸ K) :=
      CommRingCat.ofHom (Ideal.Quotient.mk K)
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)) ≫
      (flatAffineQuotientPushforwardPullbackIso g hg I).hom =
    BundleSectionZeroLocus.pullbackUnitComparison
      (Spec.map (CommRingCat.ofHom g)) ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map ψ) := by
  letI : Algebra A B := g.toAlgebra
  letI : Flat (Spec.map (CommRingCat.ofHom g)) :=
    Flat.SpecMap_iff.mpr hg
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let ψ := CommRingCat.ofHom (Ideal.Quotient.mk K)
  letI : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  letI : IsClosedImmersion (Spec.map ψ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of B) K
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))
  let c := P.map (IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ))
  let d := IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map ψ)
  let eI := flatAffineClosedImmersionIdealModulePullbackIso g hg I
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (Spec.map (CommRingCat.ofHom g))) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison _
  let eU := asIso (BundleSectionZeroLocus.pullbackUnitComparison
    (Spec.map (CommRingCat.ofHom g)))
  let eC := cokernel.mapIso c d eI eU
    (flatAffineClosedImmersionIdealModulePullbackIso_hom_toCanonicalUnit g hg I).symm
  let eS := flatClosedImmersionPullbackQuotientIsoCokernel
    (Spec.map (CommRingCat.ofHom g)) (Spec.map φ)
  let eT := closedImmersionPushforwardCokernelIso (Spec.map ψ)
  have hS : cokernel.π c ≫ eS.hom =
      P.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)) :=
    flatClosedImmersionPullbackQuotientIsoCokernel_π _ _
  have hC : cokernel.π c ≫ eC.hom =
      eU.hom ≫ cokernel.π d := cokernel.π_desc _ _ _
  have hT : cokernel.π d ≫ eT.hom =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map ψ) :=
    closedImmersionPushforwardCokernelIso_π _
  change P.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)) ≫
    (eS.symm ≪≫ eC ≪≫ eT).hom = _
  rw [← hS]
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change (cokernel.π c ≫ eC.hom) ≫ eT.hom = eU.hom ≫
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map ψ)
  rw [hC]
  exact (Category.assoc eU.hom (cokernel.π d) eT.hom).trans
    (congrArg (fun q => eU.hom ≫ q) hT)

/-- Transporting ideal data across an equality preserves the cokernel
projection from the structure sheaf. -/
theorem idealModuleCokernelTransport_π
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    cokernel.π (IdealSheafDataModule.idealModuleToUnit I) ≫
      (eqToIso (congrArg
        (fun K : X.IdealSheafData =>
          cokernel (IdealSheafDataModule.idealModuleToUnit K)) h)).hom =
    cokernel.π (IdealSheafDataModule.idealModuleToUnit J) := by
  cases h
  simp

/-- Closed immersions with equal image-defined ideal sheaves have
isomorphic pushforward structure sheaves. -/
noncomputable def closedImmersionPushforwardIsoOfKernelEq
    {X Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : i.ker = j.ker) :
    (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf) ≅
    (Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit W.ringCatSheaf) := by
  let e : cokernel (IdealSheafDataModule.closedImmersionModuleToUnit i) ≅
      cokernel (IdealSheafDataModule.closedImmersionModuleToUnit j) :=
    eqToIso (congrArg
      (fun K : X.IdealSheafData =>
        cokernel (IdealSheafDataModule.idealModuleToUnit K)) h)
  exact (closedImmersionPushforwardCokernelIso i).symm ≪≫
    e ≪≫ closedImmersionPushforwardCokernelIso j

/-- The quotient presentation and the literal affine fibre product have
the same pushforward structure sheaf over `Spec B`. -/
noncomputable def affineFibreProductPushforwardIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    let ψ : CommRingCat.of B ⟶ CommRingCat.of (B ⧸ K) :=
      CommRingCat.ofHom (Ideal.Quotient.mk K)
    let f := Spec.map (CommRingCat.ofHom g)
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (Scheme.Modules.pushforward (Spec.map ψ)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ K))).ringCatSheaf) ≅
    (Scheme.Modules.pushforward (pullback.fst f i)).obj
      (SheafOfModules.unit (pullback f i).ringCatSheaf) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let ψ := CommRingCat.ofHom (Ideal.Quotient.mk K)
  let f := Spec.map (CommRingCat.ofHom g)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : IsClosedImmersion (Spec.map ψ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of B) K
  letI : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  exact closedImmersionPushforwardIsoOfKernelEq
    (Spec.map ψ) (pullback.fst f i) (affineFibreProductIdealDataEq g I)

/-- Flat affine base change of a quotient pushforward is isomorphic to the
pushforward from the literal fibre-product closed immersion. -/
noncomputable def flatAffineClosedImmersionPushforwardBaseChangeIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    let f := Spec.map (CommRingCat.ofHom g)
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (pullback.fst f i)).obj
      (SheafOfModules.unit (pullback f i).ringCatSheaf) := by
  exact flatAffineQuotientPushforwardPullbackIso g hg I ≪≫
    affineFibreProductPushforwardIso g I

end PfaffianDescent
