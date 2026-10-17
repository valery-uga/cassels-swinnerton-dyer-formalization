import PfaffianDescent.AffineQuotientModuleBaseChange
import PfaffianDescent.ClosedImmersionPushforwardBaseChange
import PfaffianDescent.ClosedImmersionIdealBaseChange
import Mathlib.RingTheory.FiniteType

/-! Epimorphic endomorphisms of affine tilde sheaves of finite modules. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- An epimorphic endomorphism of the affine tilde sheaf of a finite module
is an isomorphism. -/
theorem tildeEpiEndomorphismIsIso
    {B : Type u} [CommRing B] (M : ModuleCat B) [Module.Finite B M]
    (v : (tilde.functor (CommRingCat.of B)).obj M ⟶
      (tilde.functor (CommRingCat.of B)).obj M) [Epi v] :
    IsIso v := by
  let F := tilde.functor (CommRingCat.of B)
  letI : F.Full := tilde.fullyFaithfulFunctor.full
  letI : F.Faithful := tilde.fullyFaithfulFunctor.faithful
  let w := F.preimage v
  have hmap : F.map w = v := F.map_preimage v
  have hw : Epi w := by
    constructor
    intro Z a b hab
    apply F.map_injective
    apply (cancel_epi v).mp
    have h := congrArg F.map hab
    simpa only [F.map_comp, hmap] using h
  have hsurj : Function.Surjective w.hom :=
    (ModuleCat.epi_iff_surjective w).mp hw
  have hbij : Function.Bijective w.hom :=
    OrzechProperty.bijective_of_surjective_endomorphism w.hom hsurj
  haveI : IsIso w := (ConcreteCategory.isIso_iff_bijective w).mpr hbij
  haveI : IsIso (F.map w) := Functor.map_isIso F w
  rw [← hmap]
  infer_instance

/-- In particular, the tilde sheaf of any quotient ring is Hopfian under
epimorphic sheaf endomorphisms. -/
theorem affineQuotientTildeEpiEndomorphismIsIso
    {B : Type u} [CommRing B] (I : Ideal B)
    (v : (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (B ⧸ I)) ⟶
      (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (B ⧸ I)))
    [Epi v] : IsIso v := by
  letI : Module.Finite B (B ⧸ I) := inferInstance
  exact tildeEpiEndomorphismIsIso (ModuleCat.of B (B ⧸ I)) v

/-- The Hopfian property transfers across an isomorphism of sheaf modules. -/
theorem epiEndomorphismIsIsoOfAffineQuotientTildeIso
    {B : Type u} [CommRing B] (I : Ideal B)
    (X : (Spec (CommRingCat.of B)).Modules)
    (e : X ≅ (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (B ⧸ I)))
    (u : X ⟶ X) [Epi u] : IsIso u := by
  let v := e.inv ≫ u ≫ e.hom
  haveI : Epi v := inferInstance
  haveI : IsIso v := affineQuotientTildeEpiEndomorphismIsIso I v
  have h : u = e.hom ≫ v ≫ e.inv := by
    simp [v, Category.assoc]
  rw [h]
  infer_instance

/-- An epimorphism between isomorphic affine sheaf modules is invertible
when its source is a finite cyclic quotient tilde sheaf. No compatibility
between the two chosen isomorphisms is required. -/
theorem epiIsIsoOfAffineQuotientTildeSourceAndTargetIso
    {B : Type u} [CommRing B] (I : Ideal B)
    {X Y : (Spec (CommRingCat.of B)).Modules}
    (eS : X ≅ (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (B ⧸ I)))
    (eT : X ≅ Y) (m : X ⟶ Y) [Epi m] : IsIso m := by
  let v := m ≫ eT.inv
  haveI : Epi v := inferInstance
  haveI : IsIso v := epiEndomorphismIsIsoOfAffineQuotientTildeIso I X eS v
  have h : m = v ≫ eT.hom := by
    simp [v, Category.assoc]
  rw [h]
  infer_instance

/-- The canonical flat affine base-change map for a quotient closed
immersion is an isomorphism. The proof uses its epimorphism property and
the Hopfian property of the finite cyclic affine quotient sheaf. -/
theorem isIso_flatAffineClosedImmersionPushforwardBaseChangeHom
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
    IsIso (closedImmersionPushforwardBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let f := Spec.map (CommRingCat.ofHom g)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  let eS := flatAffineQuotientPushforwardPullbackIso g hg I ≪≫
    (affineQuotientTildePushforwardIso K).symm
  let eT := flatAffineClosedImmersionPushforwardBaseChangeIso g hg I
  let m := closedImmersionPushforwardBaseChangeHom f i
  let v := m ≫ eT.inv
  haveI : Epi m := closedImmersionPushforwardBaseChangeHom_epi f i
  haveI : Epi v := inferInstance
  haveI : IsIso v :=
    epiEndomorphismIsIsoOfAffineQuotientTildeIso K _ eS v
  have h : m = v ≫ eT.hom := by
    simp [v, Category.assoc]
  change IsIso m
  rw [h]
  infer_instance

/-- The canonical affine base-change map for a quotient closed immersion
is an isomorphism for an arbitrary affine ring map. -/
theorem isIso_affineClosedImmersionPushforwardBaseChangeHom
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
    IsIso (closedImmersionPushforwardBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let f := Spec.map (CommRingCat.ofHom g)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  let eS := affineQuotientPushforwardPullbackIso g I ≪≫
    (affineQuotientTildePushforwardIso K).symm
  let eT := affineQuotientPushforwardPullbackIso g I ≪≫
    affineFibreProductPushforwardIso g I
  let m := closedImmersionPushforwardBaseChangeHom f i
  let v := m ≫ eT.inv
  haveI : Epi m := closedImmersionPushforwardBaseChangeHom_epi f i
  haveI : Epi v := inferInstance
  haveI : IsIso v :=
    epiEndomorphismIsIsoOfAffineQuotientTildeIso K _ eS v
  have h : m = v ≫ eT.hom := by
    simp [v, Category.assoc]
  change IsIso m
  rw [h]
  infer_instance

/-- Isomorphism of the canonical quotient base-change map forces the
induced map on quotient kernels to be an isomorphism. -/
theorem isIso_closedImmersionPushforwardBaseChangeKernelMap_of_pushforward
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [IsIso (closedImmersionPushforwardBaseChangeHom f i)] :
    IsIso (closedImmersionPushforwardBaseChangeKernelMap f i) := by
  let b := closedImmersionPushforwardBaseChangeHom f i
  let u := BundleSectionZeroLocus.pullbackUnitComparison f
  let q := (Scheme.Modules.pullback f).map
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)
  let q' := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (pullback.fst f i)
  haveI : IsIso u := BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  let e := kernel.mapIso q q' (asIso u) (asIso b)
    (closedImmersionPushforwardBaseChangeHom_quotient f i)
  change IsIso e.hom
  exact e.isIso_hom

/-- Under flat base change, isomorphism of the canonical quotient map
also gives isomorphism of the canonical actual ideal-module map. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_pushforward
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [IsIso (closedImmersionPushforwardBaseChangeHom f i)] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  let a := closedImmersionIdealPullbackKernelComparison f i
  let k := closedImmersionPushforwardBaseChangeKernelMap f i
  let m := IdealSheafDataModule.closedImmersionModuleToKernelIso
    (pullback.fst f i)
  have ha : IsIso a := isIso_flatClosedImmersionIdealPullbackKernelComparison f i
  have hk : IsIso k :=
    isIso_closedImmersionPushforwardBaseChangeKernelMap_of_pushforward f i
  have hm : IsIso m.inv := m.isIso_inv
  have hak : IsIso (a ≫ k) :=
    IsIso.comp_isIso' (f := a) (h := k) ha hk
  change IsIso (a ≫ k ≫ m.inv)
  exact IsIso.comp_isIso' (f := a ≫ k) (h := m.inv) hak hm

/-- The actual ideal-module base-change map is an isomorphism on flat
affine quotient presentations. -/
theorem isIso_flatAffineClosedImmersionIdealBaseChangeHom
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  let f := Spec.map (CommRingCat.ofHom g)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : Flat f := Flat.SpecMap_iff.mpr hg
  letI : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  letI : IsIso (closedImmersionPushforwardBaseChangeHom f i) :=
    isIso_affineClosedImmersionPushforwardBaseChangeHom g I
  exact isIso_closedImmersionIdealBaseChangeHom_of_pushforward f i

/-- A closed immersion into an affine scheme has the same image-defined
ideal sheaf as a quotient-spectrum immersion. -/
theorem affineClosedImmersion_exists_quotient_kernelEq
    {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    ∃ I : Ideal A,
      i.ker = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker := by
  obtain ⟨I, e, hi⟩ :=
    (IsClosedImmersion.Spec_iff (R := CommRingCat.of A) (f := i)).mp inferInstance
  refine ⟨I, ?_⟩
  rw [hi]
  exact Scheme.Hom.ker_comp_of_isIso e.hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- The canonical pushforward base-change map is an isomorphism for any closed
immersion into an affine scheme and any affine base-change map. -/
theorem isIso_affineClosedImmersionPushforwardBaseChangeHom_general
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionPushforwardBaseChangeHom
      (Spec.map (CommRingCat.ofHom g)) i) := by
  obtain ⟨I, hker⟩ := affineClosedImmersion_exists_quotient_kernelEq i
  let f := Spec.map (CommRingCat.ofHom g)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  let eOrig := closedImmersionPushforwardIsoOfKernelEq i q hker
  have hbase : (pullback.fst f i).ker = (pullback.fst f q).ker := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, hker]
  let eBase := closedImmersionPushforwardIsoOfKernelEq
    (pullback.fst f i) (pullback.fst f q) hbase
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let eSrc := (Scheme.Modules.pullback f).mapIso eOrig ≪≫
    affineQuotientPushforwardPullbackIso g I ≪≫
    (affineQuotientTildePushforwardIso K).symm
  let eT := (Scheme.Modules.pullback f).mapIso eOrig ≪≫
    affineQuotientPushforwardPullbackIso g I ≪≫
    affineFibreProductPushforwardIso g I ≪≫ eBase.symm
  let m := closedImmersionPushforwardBaseChangeHom f i
  let v := m ≫ eT.inv
  haveI : Epi m := closedImmersionPushforwardBaseChangeHom_epi f i
  haveI : Epi v := inferInstance
  haveI : IsIso v :=
    epiEndomorphismIsIsoOfAffineQuotientTildeIso K _ eSrc v
  have h : m = v ≫ eT.hom := by
    simp [v, Category.assoc]
  change IsIso m
  rw [h]
  infer_instance

/-- Affine base change identifies the kernel of the pulled-back quotient
with the kernel of the quotient of the actual fibre product. -/
theorem isIso_affineClosedImmersionPushforwardBaseChangeKernelMap_general
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionPushforwardBaseChangeKernelMap
      (Spec.map (CommRingCat.ofHom g)) i) := by
  letI : IsIso (closedImmersionPushforwardBaseChangeHom
      (Spec.map (CommRingCat.ofHom g)) i) :=
    isIso_affineClosedImmersionPushforwardBaseChangeHom_general g i
  exact isIso_closedImmersionPushforwardBaseChangeKernelMap_of_pushforward
    (Spec.map (CommRingCat.ofHom g)) i

/-- Flat affine base change identifies the actual ideal modules of any
closed immersion into an affine scheme. -/
theorem isIso_flatAffineClosedImmersionIdealBaseChangeHom_general
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g)) i) := by
  let f := Spec.map (CommRingCat.ofHom g)
  letI : Flat f := Flat.SpecMap_iff.mpr hg
  letI : IsIso (closedImmersionPushforwardBaseChangeHom f i) :=
    isIso_affineClosedImmersionPushforwardBaseChangeHom_general g i
  exact isIso_closedImmersionIdealBaseChangeHom_of_pushforward f i

/-- The affine theorem applies to any morphism of affine spectra, expressed
through the equivalence between such morphisms and ring homomorphisms. -/
theorem isIso_affineSpectraClosedImmersionPushforwardBaseChangeHom
    {A B : Type u} [CommRing A] [CommRing B]
    (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion i] :
    IsIso (closedImmersionPushforwardBaseChangeHom f i) := by
  let g : A →+* B := (Spec.homEquiv f).hom
  have hf : f = Spec.map (CommRingCat.ofHom g) :=
    (Spec.homEquiv.symm_apply_apply f).symm
  rw [hf]
  exact isIso_affineClosedImmersionPushforwardBaseChangeHom_general g i

/-- The actual ideal-module comparison is an isomorphism along an arbitrary
flat morphism between affine spectra. -/
theorem isIso_flatAffineSpectraClosedImmersionIdealBaseChangeHom
    {A B : Type u} [CommRing A] [CommRing B]
    (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    [Flat f] {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  let g : A →+* B := (Spec.homEquiv f).hom
  have hf : f = Spec.map (CommRingCat.ofHom g) :=
    (Spec.homEquiv.symm_apply_apply f).symm
  have hg : g.Flat := by
    exact Flat.SpecMap_iff.mp (hf ▸ inferInstance)
  rw [hf]
  exact isIso_flatAffineClosedImmersionIdealBaseChangeHom_general g hg i

/-- On every canonical affine chart of a flat source over an affine target,
the actual ideal-module base-change map is an isomorphism. -/
theorem isIso_flatAffineSourceChartClosedImmersionIdealBaseChangeHom
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i]
    (a : X.affineCover.I₀) :
    IsIso (closedImmersionIdealBaseChangeHom
      (X.affineCover.f a ≫ f) i) := by
  exact @isIso_flatAffineSpectraClosedImmersionIdealBaseChangeHom
    A _ _ _ (X.affineCover.f a ≫ f) (Flat.comp (X.affineCover.f a) f) _ i _

/-- On every affine source chart over an affine target, the canonical
pushforward base-change map is already an isomorphism. -/
theorem isIso_affineSourceChartClosedImmersionPushforwardBaseChangeHom
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i]
    (a : X.affineCover.I₀) :
    IsIso (closedImmersionPushforwardBaseChangeHom
      (X.affineCover.f a ≫ f) i) := by
  exact isIso_affineSpectraClosedImmersionPushforwardBaseChangeHom
    (X.affineCover.f a ≫ f) i

/-- The pushed-forward structure sheaf of any closed immersion into an
affine scheme is the tilde of a finite cyclic quotient module. -/
noncomputable def affineClosedImmersionPushforward_exists_quotientTildeIso
    {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    Σ I : Ideal A,
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) ≅
      (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (A ⧸ I)) := by
  let I := Classical.choose (affineClosedImmersion_exists_quotient_kernelEq i)
  have hker := Classical.choose_spec (affineClosedImmersion_exists_quotient_kernelEq i)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  exact ⟨I, closedImmersionPushforwardIsoOfKernelEq i q hker ≪≫
    (affineQuotientTildePushforwardIso I).symm⟩

/-- The source object of affine closed-immersion base change is itself the
tilde of a finite cyclic quotient over the new affine base. -/
noncomputable def affineClosedImmersionPushforwardPullback_exists_quotientTildeIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    Σ K : Ideal B,
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (B ⧸ K)) := by
  let I := Classical.choose (affineClosedImmersion_exists_quotient_kernelEq i)
  have hker := Classical.choose_spec (affineClosedImmersion_exists_quotient_kernelEq i)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  let eOrig := closedImmersionPushforwardIsoOfKernelEq i q hker
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  exact ⟨K, (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso eOrig ≪≫
    affineQuotientPushforwardPullbackIso g I ≪≫
    (affineQuotientTildePushforwardIso K).symm⟩

/-- The quotient-tilde model also applies when the affine scheme morphism is
given directly, rather than as an explicit `Spec.map` term. -/
noncomputable def affineSpectraClosedImmersionPushforwardPullback_exists_quotientTildeIso
    {A B : Type u} [CommRing A] [CommRing B]
    (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    {Z : Scheme.{u}}
    (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i] :
    Σ K : Ideal B,
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (B ⧸ K)) := by
  let g : A →+* B := (Spec.homEquiv f).hom
  have hf : f = Spec.map (CommRingCat.ofHom g) :=
    (Spec.homEquiv.symm_apply_apply f).symm
  rw [hf]
  exact affineClosedImmersionPushforwardPullback_exists_quotientTildeIso g i

end PfaffianDescent
