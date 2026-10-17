import PfaffianDescent.SchemeModuleStalkMono

/-! Open-immersion pullback preserves monomorphisms of scheme modules. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

/-- A natural isomorphism transports monicity of an individual mapped
morphism. -/
theorem mono_map_of_natIso
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (φ : M ⟶ N)
    (h : Mono (F.map φ)) : Mono (G.map φ) := by
  let eM := e.app M
  let eN := e.app N
  have h₁ : Mono eM.inv :=
    mono_of_mono_fac (f := eM.hom) eM.inv_hom_id
  have h₂ : Mono eN.hom :=
    mono_of_mono_fac (f := eN.inv) eN.hom_inv_id
  have hcomp : Mono (eM.inv ≫ F.map φ ≫ eN.hom) :=
    mono_comp' h₁ (mono_comp' h h₂)
  have hn := e.hom.naturality φ
  change F.map φ ≫ eN.hom = eM.hom ≫ G.map φ at hn
  have heq : eM.inv ≫ F.map φ ≫ eN.hom = G.map φ := by
    calc
      eM.inv ≫ F.map φ ≫ eN.hom =
          eM.inv ≫ (F.map φ ≫ eN.hom) := rfl
      _ = eM.inv ≫ (eM.hom ≫ G.map φ) := by rw [hn]
      _ = G.map φ := by rw [← Category.assoc, eM.inv_hom_id, Category.id_comp]
  exact heq ▸ hcomp

/-- Monicity of a scheme-module map can be checked after restriction to
the members of an open cover. -/
theorem schemeModule_mono_of_openCover_restrict_mono
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {M N : X.Modules}
    (φ : M ⟶ N)
    (h : ∀ i : 𝒰.I₀, Mono ((Scheme.Modules.restrictFunctor (𝒰.f i)).map φ)) :
    Mono φ := by
  apply schemeModule_mono_of_stalk_mono φ
  intro x
  rcases 𝒰.exists_eq x with ⟨i, y, rfl⟩
  haveI : Mono ((Scheme.Modules.restrictFunctor (𝒰.f i)).map φ) := h i
  have hlocal : Mono ((schemeModuleStalkFunctor (𝒰.X i) y).map
      ((Scheme.Modules.restrictFunctor (𝒰.f i)).map φ)) :=
    schemeModuleStalkFunctor_map_mono _ y
  have hglobal : Mono ((schemeModuleStalkFunctor X ((𝒰.f i) y)).map φ) :=
    mono_map_of_natIso (Scheme.Modules.restrictStalkNatIso (𝒰.f i) y) φ hlocal
  exact hglobal

/-- Monicity of pullback along a chart's composite map gives monicity
of the restriction of the original pullback to that chart. -/
theorem restrict_pullback_map_mono_of_comp
    {U X Y : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion u] {M N : Y.Modules} (φ : M ⟶ N)
    (h : Mono ((Scheme.Modules.pullback (u ≫ f)).map φ)) :
    Mono ((Scheme.Modules.restrictFunctor u).map
      ((Scheme.Modules.pullback f).map φ)) := by
  let e : (Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor u) ≅
      Scheme.Modules.pullback (u ≫ f) :=
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback u) ≪≫
        Scheme.Modules.pullbackComp u f
  exact mono_map_of_natIso e.symm φ h

/-- To prove the global pulled-back ideal is the pulled-back quotient
kernel, it suffices to check monicity of the ideal inclusion on an
open cover of the source. -/
theorem isIso_closedImmersionIdealPullbackKernelComparison_of_openCover_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] (𝒰 : X.OpenCover)
    (h : ∀ a : 𝒰.I₀, Mono ((Scheme.Modules.restrictFunctor (𝒰.f a)).map
      ((Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i)))) :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  haveI : Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) :=
    schemeModule_mono_of_openCover_restrict_mono 𝒰 _ h
  exact isIso_closedImmersionIdealPullbackKernelComparison_of_mono f i

/-- The global ideal-kernel comparison is invertible if the pullback
along each composite chart map preserves the ideal inclusion's
monicity. -/
theorem isIso_closedImmersionIdealPullbackKernelComparison_of_openCover_comp_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] (𝒰 : X.OpenCover)
    (h : ∀ a : 𝒰.I₀, Mono
      ((Scheme.Modules.pullback ((𝒰.f a) ≫ f)).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i))) :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  apply isIso_closedImmersionIdealPullbackKernelComparison_of_openCover_mono
    f i 𝒰
  intro a
  exact restrict_pullback_map_mono_of_comp (𝒰.f a) f _ (h a)

/-- Restriction of scheme modules along an open immersion preserves
monomorphisms, checked on stalks. -/
theorem openImmersionRestrictFunctor_map_mono
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((Scheme.Modules.restrictFunctor f).map φ) := by
  apply schemeModule_mono_of_stalk_mono
  intro x
  haveI : (Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).PreservesMonomorphisms :=
    inferInstanceAs ((schemeModuleStalkFunctor Y (f x)).PreservesMonomorphisms)
  letI : (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (Scheme.Modules.restrictStalkNatIso f x).symm
  change Mono (((Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ))
  exact Functor.map_mono _ φ

/-- Pullback along an open immersion preserves monomorphisms. -/
noncomputable instance openImmersionPullback_preservesMonomorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.pullback f).PreservesMonomorphisms := by
  haveI : (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms :=
    ⟨fun φ => openImmersionRestrictFunctor_map_mono f φ⟩
  exact Functor.PreservesMonomorphisms.of_iso
    (Scheme.Modules.restrictFunctorIsoPullback f)

/-- On an open chart, pulling back the actual ideal module of a closed
immersion identifies it with the kernel of the pulled-back quotient. -/
theorem isIso_openImmersionClosedImmersionIdealPullbackKernelComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsOpenImmersion f] [IsClosedImmersion i] :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  have hj : Mono j := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  haveI : Mono ((Scheme.Modules.pullback f).map j) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.pullback f) inferInstance _ _ j hj
  exact isIso_closedImmersionIdealPullbackKernelComparison_of_mono f i

/-- A flat morphism from any affine source to an affine target
preserves the actual ideal inclusion of a closed immersion into the
target. -/
theorem flatAffineSourceClosedImmersionIdealModulePullback_mono
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
  let e := X.isoSpec
  let g : A →+* Γ(X, ⊤) := (Spec.preimage (e.inv ≫ f)).hom
  have hg : g.Flat := by
    haveI : Flat (e.inv ≫ f) := inferInstance
    apply (Flat.SpecMap_iff (f := Spec.preimage (e.inv ≫ f))).mp
    rw [Spec.map_preimage]
    infer_instance
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  have hAffine : Mono ((Scheme.Modules.pullback (e.inv ≫ f)).map j) := by
    rw [← Spec.map_preimage (e.inv ≫ f)]
    exact flatAffineClosedImmersionIdealModulePullback_mono_of_closed g hg i
  haveI : IsOpenImmersion e.hom := inferInstance
  have hComposed : Mono
      ((Scheme.Modules.pullback e.hom).map
        ((Scheme.Modules.pullback (e.inv ≫ f)).map j)) := by
    exact @Functor.map_mono _ _ _ _ (Scheme.Modules.pullback e.hom)
      (openImmersionPullback_preservesMonomorphisms e.hom) _ _ _ hAffine
  have hFinal : Mono
      ((Scheme.Modules.pullback (e.hom ≫ (e.inv ≫ f))).map j) :=
    mono_map_of_natIso (Scheme.Modules.pullbackComp e.hom (e.inv ≫ f))
      j hComposed
  have heq : e.hom ≫ (e.inv ≫ f) = f := by
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  rw [heq] at hFinal
  exact hFinal

/-- For a flat map to an affine scheme, the actual ideal module of
any closed immersion into the target is the kernel of the pulled-back
quotient, without an affine hypothesis on the source. -/
theorem isIso_flatToSpecClosedImmersionIdealPullbackKernelComparison
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  apply isIso_closedImmersionIdealPullbackKernelComparison_of_openCover_comp_mono
    f i X.affineCover
  intro a
  haveI : Flat ((X.affineCover.f a) ≫ f) := inferInstance
  exact flatAffineSourceClosedImmersionIdealModulePullback_mono
    ((X.affineCover.f a) ≫ f) i

/-- Flat pullback to an affine target preserves the inclusion of the
actual ideal module into the structure sheaf, for an arbitrary source
scheme. -/
theorem flatToSpecClosedImmersionIdealModulePullback_mono
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
  apply schemeModule_mono_of_openCover_restrict_mono X.affineCover
  intro a
  haveI : Flat ((X.affineCover.f a) ≫ f) := inferInstance
  exact restrict_pullback_map_mono_of_comp
    (X.affineCover.f a) f _
    (flatAffineSourceClosedImmersionIdealModulePullback_mono
      ((X.affineCover.f a) ≫ f) i)

end PfaffianDescent
