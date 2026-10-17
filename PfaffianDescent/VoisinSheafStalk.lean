import PfaffianDescent.VoisinGaloisOrbitLocus
import AllCharacteristics.RegularPairDimension
import AllCharacteristics.SmoothSchemeRegularity
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Module structures on the stalks used in Voisin's local calculation

Mathlib gives a scheme module a presheaf-of-modules structure over the
underlying presheaf of rings.  The scheme structure sheaf itself is valued in
commutative rings, so its stalk is formed in `CommRingCat`, whereas the module
presheaf uses the underlying `RingCat` stalk.  This file transports the latter
module structure across the canonical filtered-colimit isomorphism.  It makes
the local Serre calculation apply to the literal stalk of an actual scheme
module.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open BundleSectionZeroLocus
open scoped nonZeroDivisors

universe u v w

namespace IdealSheafDataModule

noncomputable section

variable {X : Scheme.{u}}

set_option linter.style.haveILetI false in
/-- An affine section of the closed-immersion ideal lifts to the literal
kernel module.  The construction uses the evaluation-preserves-kernels
comparison, so the result is an actual section of the sheaf kernel rather
than an assumed presentation. -/
theorem exists_closedImmersionKernelModule_section_of_affine_mem
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens)
    (F : X.presheaf.obj (Opposite.op V.1))
    (hF : F ∈ i.ker.ideal V) :
    ∃ t : (closedImmersionKernelModule i).val.presheaf.obj (Opposite.op V.1),
      (closedImmersionKernelModuleToUnit i).val.app (Opposite.op V.1) t = F := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V.1)
  letI : E.PreservesZeroMorphisms := by
    dsimp [E, SheafOfModules.evaluation]
    infer_instance
  let q := closedImmersionUnitToPushforwardUnit i
  let fV := E.map q
  let κ := ModuleCat.kernelIsoKer fV
  let e := PreservesKernel.iso E q
  have hzero : fV.hom F = 0 := by
    change i.app V F = 0
    rw [Scheme.Hom.ker_apply] at hF
    exact hF
  let z : fV.hom.ker := ⟨F, hzero⟩
  let zk : (kernel fV).carrier := ConcreteCategory.hom κ.inv z
  let tk : (closedImmersionKernelModule i).val.obj (Opposite.op V.1) :=
    ConcreteCategory.hom e.inv zk
  refine ⟨tk, ?_⟩
  change (E.map (kernel.ι q)).hom tk = F
  have he := PreservesKernel.iso_inv_ι E q
  have he' := ConcreteCategory.congr_hom he
  have he'' := he' (ConcreteCategory.hom κ.inv z)
  change (E.map (kernel.ι q)).hom (ConcreteCategory.hom e.inv
      (ConcreteCategory.hom κ.inv z)) =
    (kernel.ι fV).hom (ConcreteCategory.hom κ.inv z) at he''
  rw [he'']
  have hk := ModuleCat.kernelIsoKer_inv_kernel_ι fV
  have hk' := ConcreteCategory.congr_hom hk
  have hk'' := hk' z
  change (kernel.ι fV).hom (ConcreteCategory.hom κ.inv z) = F at hk''
  simpa [z] using hk''

set_option linter.style.haveILetI false in
/-- The image-defined ideal module has the same affine sections as the
literal kernel module.  This is obtained by transporting a kernel section
through the canonical image/kernel isomorphism. -/
theorem exists_closedImmersionModule_section_of_affine_mem
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens)
    (F : X.presheaf.obj (Opposite.op V.1))
    (hF : F ∈ i.ker.ideal V) :
    ∃ t : (closedImmersionModule i).val.presheaf.obj (Opposite.op V.1),
      (closedImmersionModuleToUnit i).val.app (Opposite.op V.1) t = F := by
  obtain ⟨t, ht⟩ := exists_closedImmersionKernelModule_section_of_affine_mem i V F hF
  let e := closedImmersionModuleToKernelIso i
  let m := ConcreteCategory.hom (e.inv.val.app (Opposite.op V.1)) t
  refine ⟨m, ?_⟩
  have hfac := congrArg (fun q => q.val.app (Opposite.op V.1))
    (closedImmersionModuleToKernel_comp i)
  have hfac' := ConcreteCategory.congr_hom hfac
  have hfac'' := hfac' m
  have he := congrArg (fun q => q.val.app (Opposite.op V.1)) e.inv_hom_id
  have he' := ConcreteCategory.congr_hom he
  have he'' := he' t
  change (closedImmersionModuleToKernel i).val.app (Opposite.op V.1)
      ((e.inv.val.app (Opposite.op V.1)) t) = t at he''
  change (closedImmersionKernelModuleToUnit i).val.app (Opposite.op V.1)
      ((closedImmersionModuleToKernel i).val.app (Opposite.op V.1) m) =
    (closedImmersionModuleToUnit i).val.app (Opposite.op V.1) m at hfac''
  rw [← hfac'']
  have hem : (closedImmersionModuleToKernel i).val.app (Opposite.op V.1) m = t := by
    simpa [m] using he''
  rw [hem]
  exact ht

/-- Every affine section of the closed-immersion ideal module maps into
the affine ideal recorded by the immersion's actual kernel ideal sheaf. -/
theorem closedImmersionModule_section_mem_ker_ideal
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens)
    (m : (closedImmersionModule i).val.presheaf.obj (Opposite.op V.1)) :
    ((closedImmersionModuleToUnit i).val.app (Opposite.op V.1)) m ∈
      i.ker.ideal V := by
  let e := closedImmersionModuleToKernelIso i
  let t := (e.hom.val.app (Opposite.op V.1)) m
  have hfac := congrArg (fun q => q.val.app (Opposite.op V.1))
    (closedImmersionModuleToKernel_comp i)
  have hfac' := ConcreteCategory.congr_hom hfac
  have hfac'' := hfac' m
  change (closedImmersionKernelModuleToUnit i).val.app (Opposite.op V.1)
      ((closedImmersionModuleToKernel i).val.app (Opposite.op V.1) m) =
    (closedImmersionModuleToUnit i).val.app (Opposite.op V.1) m at hfac''
  rw [Scheme.Hom.ker_apply]
  have hcond := congrArg (fun q => q.val.app (Opposite.op V.1))
    (kernel.condition (closedImmersionUnitToPushforwardUnit i))
  have hcond' := ConcreteCategory.congr_hom hcond
  have hcond'' := hcond' t
  change i.app V ((closedImmersionKernelModuleToUnit i).val.app
      (Opposite.op V.1) t) = 0 at hcond''
  rw [← hfac'']
  change i.app V ((closedImmersionKernelModuleToUnit i).val.app
      (Opposite.op V.1)
      ((closedImmersionModuleToKernel i).val.app (Opposite.op V.1) m)) = 0
  simpa [t, e, closedImmersionModuleToKernelIso] using hcond''

/-- On an affine open, sections of the closed-immersion ideal module are
linearly equivalent to the corresponding ideal of structure-sheaf sections. -/
noncomputable def closedImmersionModule_affineSectionsLinearEquivIdeal
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens) :
    letI : Module (Γ(X, V.1))
        ((closedImmersionModule i).val.presheaf.obj (Opposite.op V.1)) := by
      change Module ((X.ringCatSheaf.obj).obj (Opposite.op V.1))
        ((closedImmersionModule i).val.presheaf.obj (Opposite.op V.1))
      infer_instance
    (closedImmersionModule i).val.presheaf.obj (Opposite.op V.1) ≃ₗ[Γ(X, V.1)]
      i.ker.ideal V := by
  letI : Module (Γ(X, V.1))
      ((closedImmersionModule i).val.presheaf.obj (Opposite.op V.1)) := by
    change Module ((X.ringCatSheaf.obj).obj (Opposite.op V.1))
      ((closedImmersionModule i).val.presheaf.obj (Opposite.op V.1))
    infer_instance
  let f : (closedImmersionModule i).val.presheaf.obj (Opposite.op V.1) →ₗ[Γ(X, V.1)]
      Γ(X, V.1) := ((closedImmersionModuleToUnit i).val.app (Opposite.op V.1)).hom
  let g : (closedImmersionModule i).val.presheaf.obj (Opposite.op V.1) →ₗ[Γ(X, V.1)]
      i.ker.ideal V :=
    f.codRestrict (i.ker.ideal V) (closedImmersionModule_section_mem_ker_ideal i V)
  apply LinearEquiv.ofBijective g
  constructor
  · have hmono : Mono (closedImmersionModuleToUnit i) := by
      change Mono (idealModuleToUnit i.ker)
      infer_instance
    let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V.1)
    have hmonoV : Mono (E.map (closedImmersionModuleToUnit i)) := inferInstance
    have hinj := (ModuleCat.mono_iff_injective
      (E.map (closedImmersionModuleToUnit i))).mp hmonoV
    intro a b hab
    apply hinj
    exact congrArg Subtype.val hab
  · intro y
    obtain ⟨m, hm⟩ := exists_closedImmersionModule_section_of_affine_mem i V y.1 y.2
    exact ⟨m, Subtype.ext hm⟩

end

end IdealSheafDataModule

/-- The canonical action of the local ring `𝒪_{X,x}` on the stalk of a scheme
module.  Mathlib constructs it directly from the `CommRingCat` structure
presheaf and the corresponding presheaf of modules. -/
@[instance_reducible]
noncomputable def schemeModuleStalkModule {X : Scheme.{u}} (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  let R : TopCat.Presheaf CommRingCat X.toTopCat := X.presheaf
  let N : _root_.PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) := M.val
  exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N x

/-- The additive-group-valued stalk functor on scheme modules.  It is the
categorical form of the literal module stalk used below.  In particular, it
is the functor to which Ext functoriality can be applied once the needed
exactness comparison for sheaves of modules is supplied. -/
noncomputable def schemeModuleStalkFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{u}) x

/-- The scheme-module stalk functor is additive. -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkFunctor X x).Additive where
  map_add := by
    intro M N f g
    change (TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{u}) x).map
      ((Scheme.Modules.toPresheaf X).map (f + g)) = _
    change (TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{u}) x).map
      ((Scheme.Modules.toPresheaf X).map f + (Scheme.Modules.toPresheaf X).map g) = _
    exact Functor.map_add _

/-- On objects, `schemeModuleStalkFunctor` is the literal additive-group
stalk of the given scheme module. -/
@[simp]
theorem schemeModuleStalkFunctor_obj (X : Scheme.{u}) (x : X) (M : X.Modules) :
    (schemeModuleStalkFunctor X x).obj M = AddCommGrpCat.of (M.presheaf.stalk x) := rfl

/-- Taking the literal additive-group stalk of a short exact sequence of
scheme modules preserves exactness.  The proof first uses left exactness of
forgetting the module structure, then exactness of abelian sheaves on stalks.
This gives the reusable exactness input needed to apply Ext functoriality to
actual scheme-module sequences. -/
theorem schemeModuleStalkFunctor_map_exact_of_shortExact
    {X : Scheme.{u}} (x : X) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (schemeModuleStalkFunctor X x)).Exact := by
  let pzero : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms :=
    { map_zero := by intro M N; rfl }
  let hfin : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := by
    infer_instance
  let hshape : PreservesLimitsOfShape WalkingParallelPair
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
    hfin.preservesFiniteLimits WalkingParallelPair
  let hlim : PreservesLimit (parallelPair S.g 0)
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := hshape.preservesLimit
  let S' := @ShortComplex.map _ _ _ _ _ _ S
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) pzero
  have hT : S'.Exact := by
    dsimp [S']
    exact @ShortComplex.Exact.map_of_mono_of_preservesKernel _ _ _ _ _ _ _ _ hS.exact
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) pzero (by infer_instance) hS.mono_f hlim
  have hG := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S').mp hT x
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : G.Additive := by
    dsimp [G]
    infer_instance
  let pzeroG : G.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive G
  change (@ShortComplex.map _ _ _ _ _ _ S' G pzeroG).Exact
  exact hG

/-- A section which restricts to zero along a scheme morphism has a
nonunit germ at the corresponding source point.  The proof uses only that
stalk maps are local ring homomorphisms; it is the local-ring bridge used to
put the two coordinates of a zero-locus section into the maximal ideal. -/
theorem schemeHom_germ_mem_maximalIdeal_of_app_eq_zero
    {X Z : Scheme.{u}} (f : Z ⟶ X) (z : Z) (U : X.Opens)
    (hz : f z ∈ U) (s : X.presheaf.obj (Opposite.op U))
    (hs : f.app U s = 0) :
    X.presheaf.germ U (f z) hz s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (f z)) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hmap : IsUnit ((f.stalkMap z).hom
      (X.presheaf.germ U (f z) hz s)) :=
    RingHom.isUnit_map _ hunit
  have hzero : (f.stalkMap z).hom
      (X.presheaf.germ U (f z) hz s) = 0 := by
    rw [Scheme.Hom.germ_stalkMap_apply, hs]
    simp
  rw [hzero] at hmap
  exact not_isUnit_zero hmap

/-- The same conclusion is packaged directly for a section of the kernel
ideal of a scheme morphism on an affine open.  This is the interface used by
the scheme-theoretic zero locus of a rank-two section. -/
theorem schemeHom_germ_mem_maximalIdeal_of_mem_kerIdeal
    {X Z : Scheme.{u}} (f : Z ⟶ X) [QuasiCompact f] (V : X.affineOpens)
    (s : X.presheaf.obj (Opposite.op V.1)) (hs : s ∈ f.ker.ideal V)
    (z : Z) (hz : f z ∈ V.1) :
    X.presheaf.germ V.1 (f z) hz s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (f z)) := by
  apply schemeHom_germ_mem_maximalIdeal_of_app_eq_zero f z V.1 hz s
  rw [Scheme.Hom.ker_apply] at hs
  exact hs

namespace BundleSectionZeroLocus

set_option linter.style.haveILetI false in
/-- At a point of the rank-two scheme-theoretic zero locus, each displayed
coordinate germ belongs to the ambient maximal ideal.  This specializes the
kernel-ideal stalk bridge to the actual local trivialization used by the
Serre calculation. -/
theorem localSectionZeroSubschemeOfOver_germ_coordinate_mem_maximalIdeal
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s)
    (j : ULift (Fin 2)) :
    let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
    let x := i z
    (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
        (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
          (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
          (restrictSectionToOpen (X := X) U s) j) ∈
      IsLocalRing.maximalIdeal ((U : Scheme.{u}).presheaf.stalk x) := by
  dsimp
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  let x := i z
  let e := localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t
  let sr := restrictSectionToOpen (X := X) U s
  let F := sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
    e sr j
  letI : IsClosedImmersion i := by
    exact isClosedImmersion_localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  have hF : F ∈ i.ker.ideal
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (U : Scheme.{u})⟩ := by
    change F ∈ (localSectionZeroSubschemeOfOverι (X := X) U
      (ULift (Fin 2)) t s).ker.ideal
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (U : Scheme.{u})⟩
    unfold localSectionZeroSubschemeOfOverι localSectionZeroSubschemeOfOver
    rw [Scheme.IdealSheafData.ker_subschemeι]
    change F ∈ (sectionZeroIdealOfFreeIso (X := (U : Scheme.{u}))
      (ULift (Fin 2)) e sr).ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top (U : Scheme.{u})⟩
    exact sectionCoordinateOfFreeIso_mem_zeroIdeal (X := (U : Scheme.{u}))
      (ULift (Fin 2)) e sr j
  exact schemeHom_germ_mem_maximalIdeal_of_mem_kerIdeal i
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top (U : Scheme.{u})⟩ F hF z
    (Set.mem_univ x)

end BundleSectionZeroLocus

set_option linter.style.haveILetI false in
/-- The local non-freeness implication for the literal stalk of a scheme
module.  The presentation equivalence is the remaining geometric input in
Voisin's Lemma 3.1; after it is supplied, the residue-coordinate conclusion
uses no model replacement of the middle sheaf. -/
theorem localSerreExtension_coordinate_eq_zero_mod_maximalIdeal_of_nonfree_sheafStalk
    {X : Scheme.{u}} (E : X.Modules) (x : X)
    (f g c : X.presheaf.stalk x) :
    letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) := schemeModuleStalkModule E x
    ∀ (_e : (E.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        localSerreExtensionPresentation f g c),
      ¬ Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) →
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) c = 0 := by
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) := schemeModuleStalkModule E x
  intro e hfree
  exact localSerreExtension_coordinate_eq_zero_mod_maximalIdeal_of_not_free_of_linearEquiv
    f g c e hfree

set_option linter.style.haveILetI false in
/- At a zero of a rank-two section, the two displayed germs lie in the
maximal ideal.  The sharpened local algebra criterion then transfers across
the stalk presentation equivalence: the actual middle stalk is free exactly
when the Serre coordinate is a unit. -/
theorem localSerreExtensionPresentation_free_iff_isUnit_of_sheafStalk
    {X : Scheme.{u}} (E : X.Modules) (x : X)
    (f g c : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
      schemeModuleStalkModule E x
    ∀ (e : (E.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      localSerreExtensionPresentation f g c),
      Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) ↔ IsUnit c := by
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    schemeModuleStalkModule E x
  intro e
  constructor
  · intro hfree
    letI : Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) := hfree
    letI : Module.Free (X.presheaf.stalk x)
        (localSerreExtensionPresentation f g c) := Module.Free.of_equiv e
    exact (localSerreExtensionPresentation_free_iff_isUnit f g c hf hfm hgm).mp
      inferInstance
  · intro hc
    letI : Module.Free (X.presheaf.stalk x)
        (localSerreExtensionPresentation f g c) :=
      localSerreExtensionPresentation_free_of_isUnit f g c hc
    letI : Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) :=
      Module.Free.of_equiv e.symm
    exact inferInstance

/- The cotangent/Jacobian version of the preceding criterion.  It is useful
   when the two displayed germs are supplied by a transverse calculation:
   regular-local cotangent independence produces the two non-zero-divisor
   hypotheses internally. -/
theorem localSerreExtensionPresentation_free_iff_isUnit_of_cotangentIndependent_parameters
    {R E : Type u} [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup E] [Module R E]
    (f g c : R)
    (hfm : f ∈ IsLocalRing.maximalIdeal R)
    (hgm : g ∈ IsLocalRing.maximalIdeal R)
    (hfsquare : f ∉ IsLocalRing.maximalIdeal R ^ 2)
    (hglinear : g ∉ Ideal.span ({f} : Set R) ⊔ IsLocalRing.maximalIdeal R ^ 2)
    (e : E ≃ₗ[R] localSerreExtensionPresentation f g c) :
    Module.Free R E ↔ IsUnit c := by
  obtain ⟨hf, _hg⟩ :=
    AllCharacteristics.local_nonZeroDivisors_of_cotangentIndependentParameters
      f g hfm hfsquare hglinear
  constructor
  · intro hfree
    letI : Module.Free R E := hfree
    letI : Module.Free R (localSerreExtensionPresentation f g c) :=
      Module.Free.of_equiv e
    exact (localSerreExtensionPresentation_free_iff_isUnit f g c hf hfm hgm).mp
      inferInstance
  · intro hc
    letI : Module.Free R (localSerreExtensionPresentation f g c) :=
      localSerreExtensionPresentation_free_of_isUnit f g c hc
    letI : Module.Free R E := Module.Free.of_equiv e.symm
    exact inferInstance

/- A chart Jacobian normally supplies independence of the two residue-field
   cotangent classes directly.  This form consumes that differential
   certificate without making the caller unpack it into the two ideal
   non-membership statements first. -/
theorem localSerreExtensionPresentation_free_iff_isUnit_of_linearIndependent_cotangent_classes
    {R E : Type u} [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup E] [Module R E]
    (f g c : R)
    (hfm : f ∈ IsLocalRing.maximalIdeal R)
    (hgm : g ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      ![(IsLocalRing.maximalIdeal R).toCotangent ⟨f, hfm⟩,
       (IsLocalRing.maximalIdeal R).toCotangent ⟨g, hgm⟩])
    (e : E ≃ₗ[R] localSerreExtensionPresentation f g c) :
    Module.Free R E ↔ IsUnit c := by
  obtain ⟨hf, hg⟩ :=
    AllCharacteristics.cotangentIndependentParameters_of_linearIndependent_cotangent_classes
      f g hfm hgm hli
  exact localSerreExtensionPresentation_free_iff_isUnit_of_cotangentIndependent_parameters
    f g c hfm hgm hf hg e

set_option linter.style.haveILetI false in
/-- A nonunit Serre coordinate forces the literal middle stalk to be
nonfree once its local presentation has been identified.  This is the
pointwise implication used when the bad embedding locus is defined by
failure of local freeness of the actual sheaf extension. -/
theorem not_free_sheafStalk_of_localSerreExtensionPresentation_of_not_isUnit
    {X : Scheme.{u}} (E : X.Modules) (x : X)
    (f g c : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hc : ¬ IsUnit c) :
    letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
      schemeModuleStalkModule E x
    ∀ (e : (E.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      localSerreExtensionPresentation f g c),
      ¬ Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) := by
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    schemeModuleStalkModule E x
  intro e
  intro hfree
  exact hc ((localSerreExtensionPresentation_free_iff_isUnit_of_sheafStalk
    E x f g c hf hfm hgm e).mp hfree)

set_option linter.style.haveILetI false in
/- The fully differential form of the preceding implication.  A local
   Jacobian certificate supplies the first non-zero-divisor condition through
   the regular-local cotangent calculation, leaving only the nonunit Serre
   coordinate and the actual stalk presentation as geometric input. -/
theorem
    not_free_sheafStalk_of_localSerreExtensionPresentation_of_not_isUnit_of_linearIndependent_cotangent_classes
    {X : Scheme.{u}} (E : X.Modules) (x : X)
    (f g c : X.presheaf.stalk x)
    (hregular : IsRegularLocalRing (X.presheaf.stalk x))
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hli : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk x))
      ![(IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨f, hfm⟩,
       (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨g, hgm⟩])
    (hc : ¬ IsUnit c) :
    letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
      schemeModuleStalkModule E x
    ∀ (e : (E.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      localSerreExtensionPresentation f g c),
      ¬ Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) := by
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    schemeModuleStalkModule E x
  intro e hfree
  letI : IsRegularLocalRing (X.presheaf.stalk x) := hregular
  obtain ⟨hf, _hg⟩ :=
    AllCharacteristics.cotangentIndependentParameters_of_linearIndependent_cotangent_classes
      f g hfm hgm hli
  exact hc ((localSerreExtensionPresentation_free_iff_isUnit_of_cotangentIndependent_parameters
    f g c hfm hgm hf _hg e).mp hfree)

set_option linter.style.haveILetI false in
/-- The Galois local-freeness argument applied directly to literal stalks of
an actual Serre extension.  The local presentation and non-freeness
hypotheses are expressed for the middle sheaf `e.E` itself at the points of
the embedding orbit; the canonical stalk module structures are supplied by
`schemeModuleStalkModule`.

This removes the type-level gap between the local calculation and the
Galois argument in Voisin's Lemma 3.1.  The still-open geometric input is to
construct the displayed presentation equivalences and identify the local-Ext
components with their coordinates. -/
theorem galoisEmbedding_badLocus_eq_empty_of_sheafStalkPresentationEquivs
    {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L] [Normal K L]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)]
    [Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwistSequence i T).X₂
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (center : Spec (.of A) ⟶ X)
    (f g c : ∀ φ : A →ₐ[K] L, X.presheaf.stalk
      (galoisEmbeddingPoint (K := K) center φ))
    (components : ∀ φ : A →ₐ[K] L,
      CategoryTheory.Abelian.Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+
        (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ) ⧸
          IsLocalRing.maximalIdeal
            (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))))
    (hcomponents : ∀ z : CategoryTheory.Abelian.Ext.{u}
        (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hcoordinate : ∀ φ : A →ₐ[K] L,
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal
          (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))) (c φ))
    (hpresentation : ∀ φ : A →ₐ[K] L,
      letI : Module (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))
          ((show X.Modules from e.E).presheaf.stalk
            (galoisEmbeddingPoint (K := K) center φ)) :=
        schemeModuleStalkModule (show X.Modules from e.E)
          (galoisEmbeddingPoint (K := K) center φ)
      ((show X.Modules from e.E).presheaf.stalk
        (galoisEmbeddingPoint (K := K) center φ)) ≃ₗ[
        X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ)]
        localSerreExtensionPresentation (f φ) (g φ) (c φ))
    (hbad : ∀ φ : A →ₐ[K] L, φ ∈ B →
      letI : Module (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))
          ((show X.Modules from e.E).presheaf.stalk
            (galoisEmbeddingPoint (K := K) center φ)) :=
        schemeModuleStalkModule (show X.Modules from e.E)
          (galoisEmbeddingPoint (K := K) center φ)
      ¬ Module.Free (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))
        ((show X.Modules from e.E).presheaf.stalk
          (galoisEmbeddingPoint (K := K) center φ))) :
    B = ∅ := by
  let R : (A →ₐ[K] L) → Type u := fun φ ↦
    X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ)
  let E : (A →ₐ[K] L) → Type u := fun φ ↦
    (show X.Modules from e.E).presheaf.stalk
      (galoisEmbeddingPoint (K := K) center φ)
  letI : ∀ φ, CommRing (R φ) := fun φ ↦ by
    dsimp [R]
    infer_instance
  letI : ∀ φ, IsLocalRing (R φ) := fun φ ↦ by
    dsimp [R]
    infer_instance
  letI : ∀ φ, AddCommGroup (E φ) := fun φ ↦ by
    dsimp [E]
    infer_instance
  letI : ∀ φ, Module (R φ) (E φ) := fun φ ↦ by
    exact schemeModuleStalkModule (show X.Modules from e.E)
      (galoisEmbeddingPoint (K := K) center φ)
  apply galoisEmbedding_badLocus_eq_empty_of_localSerreExtensionPresentationEquivs
    (R := R) (E := E) i T e B hstable he f g c components hcomponents hcoordinate
  · intro φ
    simpa only [R, E] using hpresentation φ
  · intro φ hφ
    simpa only [R, E] using hbad φ hφ

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The literal-stalk Galois argument with an inhabited presentation space.
Classical choice supplies the equivalence required by the preceding theorem;
this is the form produced by the stalk presentation construction. -/
theorem galoisEmbedding_badLocus_eq_empty_of_sheafStalkPresentationNonempty
    {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L] [Normal K L]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)]
    [Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwistSequence i T).X₂
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (center : Spec (.of A) ⟶ X)
    (f g c : ∀ φ : A →ₐ[K] L, X.presheaf.stalk
      (galoisEmbeddingPoint (K := K) center φ))
    (components : ∀ φ : A →ₐ[K] L,
      CategoryTheory.Abelian.Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+
        (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ) ⧸
          IsLocalRing.maximalIdeal
            (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))))
    (hcomponents : ∀ z : CategoryTheory.Abelian.Ext.{u}
        (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hcoordinate : ∀ φ : A →ₐ[K] L,
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal
          (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))) (c φ))
    (hpresentation : ∀ φ : A →ₐ[K] L,
      letI : Module (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))
          ((show X.Modules from e.E).presheaf.stalk
            (galoisEmbeddingPoint (K := K) center φ)) :=
        schemeModuleStalkModule (show X.Modules from e.E)
          (galoisEmbeddingPoint (K := K) center φ)
      Nonempty (((show X.Modules from e.E).presheaf.stalk
        (galoisEmbeddingPoint (K := K) center φ)) ≃ₗ[
        X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ)]
        localSerreExtensionPresentation (f φ) (g φ) (c φ)))
    (hbad : ∀ φ : A →ₐ[K] L, φ ∈ B →
      letI : Module (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))
          ((show X.Modules from e.E).presheaf.stalk
            (galoisEmbeddingPoint (K := K) center φ)) :=
        schemeModuleStalkModule (show X.Modules from e.E)
          (galoisEmbeddingPoint (K := K) center φ)
      ¬ Module.Free (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))
        ((show X.Modules from e.E).presheaf.stalk
          (galoisEmbeddingPoint (K := K) center φ))) :
    B = ∅ := by
  apply galoisEmbedding_badLocus_eq_empty_of_sheafStalkPresentationEquivs
    (i := i) (T := T) (e := e) B hstable he center f g c components hcomponents
      hcoordinate
  · intro φ
    exact Classical.choice (hpresentation φ)
  · exact hbad

set_option linter.style.haveILetI false in
/- The preceding stalk theorem can discharge the bad-locus hypothesis from
the local regularity data used to construct the Serre presentation.  This
corollary is the form needed once the geometric construction has produced
nonunit coordinates at the chosen orbit points. -/
theorem galoisEmbedding_badLocus_eq_empty_of_sheafStalkPresentationEquivs_of_nonunit_coordinates
    {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L] [Normal K L]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)]
    [Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (closedImmersionIdealTwistSequence i T).X₂
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (center : Spec (.of A) ⟶ X)
    (f g c : ∀ φ : A →ₐ[K] L, X.presheaf.stalk
      (galoisEmbeddingPoint (K := K) center φ))
    (components : ∀ φ : A →ₐ[K] L,
      CategoryTheory.Abelian.Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+
        (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ) ⧸
          IsLocalRing.maximalIdeal
            (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))))
    (hcomponents : ∀ z : CategoryTheory.Abelian.Ext.{u}
        (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hcoordinate : ∀ φ : A →ₐ[K] L,
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal
          (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))) (c φ))
    (hpresentation : ∀ φ : A →ₐ[K] L,
      letI : Module (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))
          ((show X.Modules from e.E).presheaf.stalk
            (galoisEmbeddingPoint (K := K) center φ)) :=
        schemeModuleStalkModule (show X.Modules from e.E)
          (galoisEmbeddingPoint (K := K) center φ)
      ((show X.Modules from e.E).presheaf.stalk
        (galoisEmbeddingPoint (K := K) center φ)) ≃ₗ[
        X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ)]
        localSerreExtensionPresentation (f φ) (g φ) (c φ))
    (hf : ∀ φ : A →ₐ[K] L,
      f φ ∈ (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ))⁰)
    (hfm : ∀ φ : A →ₐ[K] L,
      f φ ∈ IsLocalRing.maximalIdeal
        (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ)))
    (hgm : ∀ φ : A →ₐ[K] L,
      g φ ∈ IsLocalRing.maximalIdeal
        (X.presheaf.stalk (galoisEmbeddingPoint (K := K) center φ)))
    (hnonunit : ∀ φ : A →ₐ[K] L, φ ∈ B → ¬ IsUnit (c φ)) :
    B = ∅ := by
  apply galoisEmbedding_badLocus_eq_empty_of_sheafStalkPresentationEquivs
    (i := i) (T := T) (e := e) B hstable he center f g c components hcomponents
      hcoordinate hpresentation
  intro φ hφ
  exact not_free_sheafStalk_of_localSerreExtensionPresentation_of_not_isUnit
    (show X.Modules from e.E)
    (galoisEmbeddingPoint (K := K) center φ) (f φ) (g φ) (c φ)
    (hf φ) (hfm φ) (hgm φ) (hnonunit φ hφ) (hpresentation φ)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism of presheaves of modules commutes with the scalar action on
germs at a point.  The stalk map is the literal colimit map of underlying
additive groups, while the scalar action is Mathlib's `CommRingCat` stalk
action.  This is the germ-level linearity needed to turn the additive stalk
exactness of a Serre extension into an exact sequence of local modules. -/
theorem presheafOfModules_stalkMap_germ_smul
    {Y : TopCat.{u}} {R : Y.Presheaf CommRingCat.{u}}
    {M N : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (y : Y) (U : Opens Y) (hy : y ∈ U)
    (r : R.obj (Opposite.op U)) (m : M.obj (Opposite.op U)) :
    letI : Module (R.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj M) y) := by
      change Module (R.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y)
      exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier M y
    letI : Module (R.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N) y) := by
      change Module (R.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf y)
      exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N y
    letI : Module (R.stalk y)
        ((TopCat.Presheaf.stalkFunctor Ab y).obj
          ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N)) := by
      change Module (R.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf y)
      exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N y
    (TopCat.Presheaf.stalkFunctor Ab y).map
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ)
      (R.germ U y hy r • TopCat.Presheaf.germ
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj M) U y hy m) =
      R.germ U y hy r •
        (TopCat.Presheaf.stalkFunctor Ab y).map
          ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ)
          (TopCat.Presheaf.germ
            ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj M) U y hy m) := by
  dsimp
  letI : Module (R.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N) y) := by
    change Module (R.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf y)
    exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N y
  letI : Module (R.stalk y)
      ((TopCat.Presheaf.stalkFunctor Ab y).obj
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N)) := by
    change Module (R.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf y)
    exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N y
  erw [← PresheafOfModules.germ_smul M y U hy r m]
  change (TopCat.Presheaf.stalkFunctor Ab y).map
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ)
      (TopCat.Presheaf.germ
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj M) U y hy (r • m)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ N.presheaf U y hy ((φ.app (Opposite.op U)) (r • m)) = _
  rw [LinearMap.map_smul]
  rw [PresheafOfModules.germ_smul N y U hy r]
  change R.germ U y hy r • TopCat.Presheaf.germ
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N) U y hy
      (((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ).app
        (Opposite.op U) m) =
    R.germ U y hy r •
      (TopCat.Presheaf.stalkFunctor Ab y).map
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ)
        (TopCat.Presheaf.germ
          ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj M) U y hy m)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The map on stalks induced by a morphism of presheaves of modules is
linear over the stalk of the presheaf of rings.  The proof represents the
scalar and module element by germs and restricts the latter to a neighborhood
on which both are represented. -/
theorem presheafOfModules_stalkMap_smul
    {Y : TopCat.{u}} {R : Y.Presheaf CommRingCat.{u}}
    {M N : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (y : Y) :
    letI : Module (R.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y) := by
      exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier M y
    letI : Module (R.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf y) := by
      exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N y
    letI : Module (R.stalk y)
        ((TopCat.Presheaf.stalkFunctor Ab y).obj
          ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N)) := by
      change Module (R.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf y)
      exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N y
    ∀ (a : R.stalk y) (n : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y),
      (TopCat.Presheaf.stalkFunctor Ab y).map
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ) (a • n) =
      a • (TopCat.Presheaf.stalkFunctor Ab y).map
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map φ) n := by
  dsimp
  intro a n
  obtain ⟨U, hyU, r, rfl⟩ := R.exists_germ_eq a
  obtain ⟨V, hVU, hyV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.presheaf n hyU
  erw [← R.germ_res_apply (homOfLE hVU) y hyV r]
  exact presheafOfModules_stalkMap_germ_smul φ y V hyV
    (R.map (homOfLE hVU).op r) m

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A scheme-module morphism induces a linear map on literal stalks.  This
specializes `presheafOfModules_stalkMap_smul` to the structure sheaf of a
scheme and the underlying morphism of additive sheaves. -/
theorem schemeModule_stalkMap_smul
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) := schemeModuleStalkModule N x
    letI : Module (X.presheaf.stalk x)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj N).obj) := by
      change Module (X.presheaf.stalk x) (N.presheaf.stalk x)
      exact schemeModuleStalkModule N x
    ∀ (a : X.presheaf.stalk x) (n : M.presheaf.stalk x),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom (a • n) =
      a • (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom n := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj
        ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).obj N.val)) := by
    change Module (X.presheaf.stalk x) (N.presheaf.stalk x)
    exact schemeModuleStalkModule N x
  change ∀ (a : X.presheaf.stalk x)
    (n : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat) M.val.presheaf x),
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map φ.val)
      (a • n) =
    a • (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map φ.val) n
  exact presheafOfModules_stalkMap_smul φ.val x

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The literal stalk map of a scheme-module morphism, equipped with its
canonical local-ring linearity. -/
noncomputable def schemeModuleStalkLinearMap
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) := schemeModuleStalkModule N x
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x := by
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) := schemeModuleStalkModule N x
  let F := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom
  change M.presheaf.stalk x ⟶ N.presheaf.stalk x at F
  let f : M.presheaf.stalk x →+ N.presheaf.stalk x := F.hom
  refine
    { toFun := f
      map_add' := f.map_add
      map_smul' := ?_ }
  exact schemeModule_stalkMap_smul φ x

/-- The categorical stalk functor acts by the same map as the canonical
local-ring-linear map on literal stalk modules. -/
@[simp]
theorem schemeModuleStalkFunctor_map_apply
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (m : M.presheaf.stalk x) :
    (schemeModuleStalkFunctor X x).map φ m =
      (schemeModuleStalkLinearMap φ x) m := rfl

/-- The literal stalk functor with its canonical local-ring module structure. -/
noncomputable def schemeModuleStalkModuleFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat (X.presheaf.stalk x) where
  obj M := by
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    exact ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)
  map {M N} f := by
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
      schemeModuleStalkModule N x
    exact ModuleCat.ofHom (schemeModuleStalkLinearMap f x)
  map_id := by
    intro M
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (schemeModuleStalkFunctor X x).map (𝟙 M) m = m
    rw [(schemeModuleStalkFunctor X x).map_id]
    rfl
  map_comp := by
    intro M N P f g
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
      schemeModuleStalkModule N x
    letI : Module (X.presheaf.stalk x) (P.presheaf.stalk x) :=
      schemeModuleStalkModule P x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (schemeModuleStalkFunctor X x).map (f ≫ g) m =
      (schemeModuleStalkFunctor X x).map g ((schemeModuleStalkFunctor X x).map f m)
    rw [(schemeModuleStalkFunctor X x).map_comp]
    rfl

/-- The local-ring-valued stalk functor is additive. -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkModuleFunctor X x).Additive where
  map_add := by
    intro M N f g
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
      schemeModuleStalkModule N x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (schemeModuleStalkFunctor X x).map (f + g) m =
      (schemeModuleStalkFunctor X x).map f m + (schemeModuleStalkFunctor X x).map g m
    rw [(schemeModuleStalkFunctor X x).map_add]
    rfl

/-- Taking literal local-ring module stalks preserves exactness of short exact
sequences of scheme modules. -/
theorem schemeModuleStalkModuleFunctor_map_exact_of_shortExact
    {X : Scheme.{u}} (x : X) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (schemeModuleStalkModuleFunctor X x)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact
    ((schemeModuleStalkFunctor X x).map S.f)
    ((schemeModuleStalkFunctor X x).map S.g)
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (schemeModuleStalkFunctor_map_exact_of_shortExact x S hS)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The filtered-colimit comparison between the structure-ring stalk and the
stalk of its rank-one unit module, as an additive equivalence. -/
noncomputable def presheafOfModules_unitStalkAddEquiv
    {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) (y : Y) :
    R.stalk y ≃+ TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y)
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf y := by
  let D := (OpenNhds.inclusion y).op ⋙ R
  exact (preservesColimitIso
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) D).addCommGroupIsoToAddEquiv

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The unit-stalk comparison sends the germ of a ring section to the germ of
the same section in the unit module. -/
lemma presheafOfModules_unitStalkAddEquiv_germ
    {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) (y : Y)
    (U : Opens Y) (hy : y ∈ U) (r : R.obj (Opposite.op U)) :
    presheafOfModules_unitStalkAddEquiv R y (R.germ U y hy r) =
      TopCat.Presheaf.germ
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf U y hy r := by
  let D := (OpenNhds.inclusion y).op ⋙ R
  let i : (OpenNhds y)ᵒᵖ := Opposite.op ⟨U, hy⟩
  let r' : (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (D.obj i) := r
  change (preservesColimitIso
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) D).hom
      ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (colimit.ι D i) r') =
    colimit.ι (D ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) i r'
  letI : PreservesColimit D (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) := by
    dsimp [D]
    infer_instance
  rw [← ConcreteCategory.comp_apply,
    ← ι_preservesColimitIso_hom (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) D i] <;> rfl

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The rank-one unit-module stalk is canonically the structure-ring stalk as
a module over that local ring. -/
noncomputable def presheafOfModules_unitStalkLinearEquiv
    {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) (y : Y) :
    letI : Module (R.stalk y)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y)
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) y
    R.stalk y ≃ₗ[R.stalk y]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y)
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf y := by
  letI : Module (R.stalk y)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y)
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) y
  refine { toAddEquiv := presheafOfModules_unitStalkAddEquiv R y, map_smul' := ?_ }
  intro a b
  obtain ⟨U, hyU, r, rfl⟩ := R.exists_germ_eq a
  obtain ⟨V, hVU, hyV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq R b hyU
  let rV : R.obj (Opposite.op V) := R.map (homOfLE hVU).op r
  let rU : (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf.obj
      (Opposite.op V) := rV
  let mU : (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf.obj
      (Opposite.op V) := m
  letI : Module (R.obj (Opposite.op V))
      ((PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf.obj
        (Opposite.op V)) := by
    change Module (R.obj (Opposite.op V))
      ((PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))
    infer_instance
  erw [← R.germ_res_apply (homOfLE hVU) y hyV r]
  change presheafOfModules_unitStalkAddEquiv R y
    (R.germ V y hyV rV * R.germ V y hyV m) = _
  rw [← map_mul]
  rw [presheafOfModules_unitStalkAddEquiv_germ R y V hyV (rV * m)]
  change TopCat.Presheaf.germ
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf V y hyV
      (rV • mU) =
    R.germ V y hyV rV • presheafOfModules_unitStalkAddEquiv R y (R.germ V y hyV m)
  have hm : presheafOfModules_unitStalkAddEquiv R y (R.germ V y hyV m) =
      TopCat.Presheaf.germ
        (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf V y hyV mU := by
    simpa [mU] using presheafOfModules_unitStalkAddEquiv_germ R y V hyV m
  rw [hm]
  exact PresheafOfModules.germ_smul
    (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) y V hyV rV mU

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The structure-sheaf stalk, as produced by the scheme-module stalk
functor, is canonically the local ring regarded as a module over itself. -/
noncomputable def schemeModuleUnitStalkIso (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkModuleFunctor X x).obj
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  exact LinearEquiv.toModuleIso
    (presheafOfModules_unitStalkLinearEquiv X.presheaf x).symm

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical section of a Serre extension, with its source identified
with the literal structure-ring stalk. -/
noncomputable def serreExtensionStalkCanonicalSection
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    X.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      ((show X.Modules from e.E).presheaf.stalk x) := by
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let i := schemeModuleStalkLinearMap e.inclusion x
  change X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at u
  change TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
    (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x →ₗ[
      X.presheaf.stalk x] ((show X.Modules from e.E).presheaf.stalk x) at i
  change X.presheaf.stalk x →ₗ[X.presheaf.stalk x]
    ((show X.Modules from e.E).presheaf.stalk x)
  exact LinearMap.comp i u.toLinearMap

set_option linter.style.haveILetI false in
/-- The exact sequence of a Serre extension is exact on the literal
underlying additive-group stalks.  This applies finite-limit preservation of
the underlying-sheaf functor to the kernel description of the inclusion, then
uses exactness of sheaves on stalks.  It does not assume an unproved passage
from global Ext to local Ext. -/
theorem serreExtension_stalk_function_exact
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    Function.Exact
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map e.inclusion).hom)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map e.projection).hom) := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.Additive := by
    dsimp [T]
    infer_instance
  letI : T.PreservesZeroMorphisms := by
    dsimp [T]
    infer_instance
  letI : PreservesFiniteLimits T := by
    dsimp [T]
    infer_instance
  let S := ShortComplex.mk e.inclusion e.projection e.zero
  let S' := S.map T
  have hT : S'.Exact := by
    dsimp [S']
    apply e.shortExact.exact.map_of_mono_of_preservesKernel
    · infer_instance
    · infer_instance
  have hG := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S').mp hT x
  exact (ShortComplex.ab_exact_iff_function_exact _).mp hG

set_option linter.style.haveILetI false in
/-- The maps of an actual Serre extension form an exact sequence after taking
stalks as modules over the local ring.  The underlying exactness is the
sheaf-theoretic stalk exactness above; the maps have been equipped with their
canonical linear structures by `schemeModuleStalkLinearMap`. -/
theorem serreExtension_stalk_linear_exact
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from M).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from M) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
    Function.Exact (schemeModuleStalkLinearMap e.inclusion x)
      (schemeModuleStalkLinearMap e.projection x) := by
  dsimp [schemeModuleStalkLinearMap]
  exact serreExtension_stalk_function_exact e x

set_option linter.style.haveILetI false in
/-- The canonical section of an actual Serre extension is injective on the
literal local modules.  The underlying sheaf functor preserves monomorphisms
because it preserves finite limits, and stalks preserve monomorphisms of
sheaves of abelian groups. -/
theorem serreExtension_stalk_inclusion_injective
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    Function.Injective (schemeModuleStalkLinearMap e.inclusion x) := by
  dsimp [schemeModuleStalkLinearMap]
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.Additive := by
    dsimp [T]
    infer_instance
  letI : T.PreservesZeroMorphisms := by
    dsimp [T]
    infer_instance
  letI : PreservesFiniteLimits T := by
    dsimp [T]
    infer_instance
  letI : T.PreservesMonomorphisms :=
    NormalEpiCategory.preservesMonomorphisms_of_preservesKernels T
  have hmap : Mono (T.map e.inclusion) := Functor.map_mono T e.inclusion
  have hstalk : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (T.map e.inclusion).hom) :=
    @TopCat.Presheaf.stalk_mono_of_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (T.map e.inclusion) hmap x
  exact (AddCommGrpCat.mono_iff_injective _).mp hstalk

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- After identifying the source unit stalk with the local ring, the
canonical section of a Serre extension remains injective. -/
theorem serreExtensionStalkCanonicalSection_injective
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    Function.Injective (serreExtensionStalkCanonicalSection e x) := by
  dsimp [serreExtensionStalkCanonicalSection]
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let i := schemeModuleStalkLinearMap e.inclusion x
  change X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at u
  change TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
    (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x →ₗ[
      X.presheaf.stalk x] ((show X.Modules from e.E).presheaf.stalk x) at i
  change Function.Injective (LinearMap.comp i u.toLinearMap)
  exact (serreExtension_stalk_inclusion_injective e x).comp u.injective

/-! ### Stalks of closed-immersion ideals -/

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The literal stalk map of a module subsheaf of the structure sheaf, after
identifying the target unit-module stalk with the local ring. -/
noncomputable def schemeModuleStalkToRingLinearMap
    {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let j := schemeModuleStalkLinearMap φ x
  change X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at u
  change M.presheaf.stalk x →ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at j
  exact LinearMap.comp u.symm.toLinearMap j

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of a module inclusion is computed on a germ by applying the
section map first and then taking the ordinary structure-sheaf germ.  This
is the concrete formula used below to transport affine generator
calculations to the local ring. -/
lemma schemeModuleStalkToRingLinearMap_germ
    {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X)
    (U : Opens X) (hxU : x ∈ U)
    (m : M.presheaf.obj (Opposite.op U)) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    schemeModuleStalkToRingLinearMap φ x
      (TopCat.Presheaf.germ M.presheaf U x hxU m) =
      X.presheaf.germ U x hxU ((φ.val.app (Opposite.op U)) m) := by
  dsimp [schemeModuleStalkToRingLinearMap]
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let j := schemeModuleStalkLinearMap φ x
  change u.symm (j (TopCat.Presheaf.germ M.presheaf U x hxU m)) = _
  have hmap : j (TopCat.Presheaf.germ M.presheaf U x hxU m) =
      TopCat.Presheaf.germ
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf U x hxU
        ((φ.val.app (Opposite.op U)) m) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map φ.val)
      (TopCat.Presheaf.germ
        ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).obj M.val)
          U x hxU m) = _
    have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
      (C := AddCommGrpCat)
      (F := (PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).obj M.val)
      (G := (PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).obj
        (SheafOfModules.unit X.ringCatSheaf).val)
      (f := (PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map φ.val)
      U x hxU m
    convert hgerm using 1 <;> rfl
  rw [hmap]
  have hunit : u.symm
      (TopCat.Presheaf.germ
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf U x hxU
        ((φ.val.app (Opposite.op U)) m)) =
      X.presheaf.germ U x hxU ((φ.val.app (Opposite.op U)) m) := by
    apply u.injective
    rw [u.apply_symm_apply]
    exact (presheafOfModules_unitStalkAddEquiv_germ X.presheaf x U hxU
      ((φ.val.app (Opposite.op U)) m)).symm
  exact hunit

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a global regular function becomes multiplication by
its germ after identifying the unit-module stalk with the local ring. -/
theorem schemeModuleStalkToRingLinearMap_unitEndomorphismOfRegularFunction
    {X : Scheme.{u}} (r : Γ(X, ⊤)) (x : X) (y : X.presheaf.stalk x) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    schemeModuleStalkToRingLinearMap
        (unitEndomorphismOfRegularFunction r) x
        (presheafOfModules_unitStalkLinearEquiv X.presheaf x y) =
      X.presheaf.germ ⊤ x (Set.mem_univ x) r * y := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let a := schemeModuleStalkToRingLinearMap
    (unitEndomorphismOfRegularFunction r) x
  let m : (show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.obj
      (Opposite.op ⊤) := (1 : Γ(X, ⊤))
  have hu1 : u (1 : X.presheaf.stalk x) =
      TopCat.Presheaf.germ
        (PresheafOfModules.unit
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf
        ⊤ x (Set.mem_univ x) m := by
    have hring : X.presheaf.germ ⊤ x (Set.mem_univ x) (1 : Γ(X, ⊤)) = 1 :=
      map_one _
    calc
      u (1 : X.presheaf.stalk x) =
          u (X.presheaf.germ ⊤ x (Set.mem_univ x) (1 : Γ(X, ⊤))) := by
        exact congrArg u hring.symm
      _ = _ := presheafOfModules_unitStalkAddEquiv_germ
        X.presheaf x ⊤ (Set.mem_univ x) (1 : Γ(X, ⊤))
  have ha1 : a (u (1 : X.presheaf.stalk x)) =
      X.presheaf.germ ⊤ x (Set.mem_univ x) r := by
    rw [hu1]
    have hgem := schemeModuleStalkToRingLinearMap_germ
      (X := X)
      (M := (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
      (unitEndomorphismOfRegularFunction r) x ⊤ (Set.mem_univ x)
      m
    change a
        (TopCat.Presheaf.germ
          (PresheafOfModules.unit
            (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf
          ⊤ x (Set.mem_univ x) m) =
      X.presheaf.germ ⊤ x (Set.mem_univ x)
        ((unitEndomorphismOfRegularFunction r).val.app (Opposite.op ⊤) m) at hgem
    rw [hgem]
    have hr := unitEndomorphismValue_ofRegularFunction (X := X) r
    change ((unitEndomorphismOfRegularFunction r).val.app (Opposite.op ⊤)).hom m = r at hr
    exact congrArg (X.presheaf.germ ⊤ x (Set.mem_univ x)) hr
  calc
    a (u y) = a (y • u (1 : X.presheaf.stalk x)) := by
      rw [← u.map_smul, smul_eq_mul, mul_one]
    _ = y • a (u (1 : X.presheaf.stalk x)) := a.map_smul y _
    _ = y • X.presheaf.germ ⊤ x (Set.mem_univ x) r := by rw [ha1]
    _ = X.presheaf.germ ⊤ x (Set.mem_univ x) r * y := by
      simp [smul_eq_mul, mul_comm]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A monomorphism of scheme modules is injective after taking literal stalks
with their canonical local-ring linear structures. -/
theorem schemeModuleStalkLinearMap_injective_of_mono
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (x : X) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) := schemeModuleStalkModule N x
    Function.Injective (schemeModuleStalkLinearMap φ x) := by
  dsimp [schemeModuleStalkLinearMap]
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.Additive := by
    dsimp [T]
    infer_instance
  letI : T.PreservesZeroMorphisms := by
    dsimp [T]
    infer_instance
  letI : PreservesFiniteLimits T := by
    dsimp [T]
    infer_instance
  letI : T.PreservesMonomorphisms :=
    NormalEpiCategory.preservesMonomorphisms_of_preservesKernels T
  have hmap : Mono (T.map φ) := Functor.map_mono T φ
  have hstalk : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (T.map φ).hom) :=
    @TopCat.Presheaf.stalk_mono_of_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (T.map φ) hmap x
  exact (AddCommGrpCat.mono_iff_injective _).mp hstalk

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The local-ring-valued stalk map of a subsheaf of the structure sheaf is
injective. -/
theorem schemeModuleStalkToRingLinearMap_injective_of_mono
    {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] (x : X) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    Function.Injective (schemeModuleStalkToRingLinearMap φ x) := by
  dsimp [schemeModuleStalkToRingLinearMap]
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let j := schemeModuleStalkLinearMap φ x
  change X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at u
  change M.presheaf.stalk x →ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at j
  change Function.Injective (LinearMap.comp u.symm.toLinearMap j)
  exact u.symm.injective.comp (schemeModuleStalkLinearMap_injective_of_mono φ x)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- If the local image of a module subsheaf of the structure sheaf is the
ideal `(f,g)`, its literal stalk is canonically linearly equivalent to that
ideal. -/
noncomputable def schemeModuleStalkLinearEquivOfRangeEq
    {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] (x : X) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.range (schemeModuleStalkToRingLinearMap φ x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) := by
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  intro f g hrange
  let j := schemeModuleStalkToRingLinearMap φ x
  change M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x at j
  exact (LinearEquiv.ofInjective j (schemeModuleStalkToRingLinearMap_injective_of_mono φ x)).trans
    (LinearEquiv.ofEq _ _ hrange)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk inclusion of the actual ideal module of a closed immersion,
viewed as a linear map to the local ring. -/
noncomputable def closedImmersionModuleStalkToRingLinearMap
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) →ₗ[
      X.presheaf.stalk x] X.presheaf.stalk x :=
  schemeModuleStalkToRingLinearMap (IdealSheafDataModule.closedImmersionModuleToUnit i) x

noncomputable section

set_option linter.style.haveILetI false in
/-- The actual ideal sequence of a closed immersion remains exact on literal
additive stalks.  This derives the local ideal calculation from the proved
sheaf-theoretic closed-immersion sequence, rather than assuming an affine
stalk presentation. -/
theorem closedImmersionModule_stalk_function_exact
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    Function.Exact
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
          (IdealSheafDataModule.closedImmersionModuleToUnit i)).hom)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).hom) := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.Additive := by
    dsimp [T]
    infer_instance
  letI : T.PreservesZeroMorphisms := by
    dsimp [T]
    infer_instance
  letI : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms := by
    infer_instance
  letI : PreservesFiniteLimits T := by
    dsimp [T]
    infer_instance
  letI : HasZeroMorphisms X.Modules := inferInstance
  let f := IdealSheafDataModule.closedImmersionModuleToUnit i
  let g := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  letI : Zero (IdealSheafDataModule.closedImmersionModule i ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) :=
    HasZeroMorphisms.zero _ _
  have hzero : f ≫ g = 0 := by
    exact (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).zero
  let S := ShortComplex.mk f g hzero
  have hS : S.Exact := by
    dsimp [S, f, g, hzero]
    exact (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i).exact
  letI : Mono S.f := by
    dsimp [S, f]
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  let S' := S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  have hT : S'.Exact := by
    apply hS.map_of_mono_of_preservesKernel
    · infer_instance
    · infer_instance
  have hG := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S').mp hT x
  exact (ShortComplex.ab_exact_iff_function_exact _).mp hG

set_option linter.style.haveILetI false in
/-- The ideal sequence of a closed immersion is exact after taking its
literal stalks as modules over the local ring. -/
theorem closedImmersionModule_stalk_linear_exact
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    Function.Exact
      (schemeModuleStalkLinearMap (IdealSheafDataModule.closedImmersionModuleToUnit i) x)
      (schemeModuleStalkLinearMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x) := by
  dsimp [schemeModuleStalkLinearMap]
  exact closedImmersionModule_stalk_function_exact i x

set_option linter.style.haveILetI false in
/-- The quotient map of a closed immersion on literal stalks, expressed with
the structure-ring stalk as its source. -/
noncomputable def closedImmersionPushforwardStalkFromRingLinearMap
    {X Z : Scheme.{u}} (i : Z ⟶ X) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    X.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) := by
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let g := schemeModuleStalkLinearMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x
  change X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at u
  change TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x →ₗ[
        X.presheaf.stalk x]
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) at g
  exact g.comp u.toLinearMap

/-- A surjective local quotient map with a prescribed kernel identifies the
literal quotient by that kernel with the target stalk.  This is the abstract
algebraic part of the quotient-stalk comparison used in Voisin's local
calculation; the remaining geometric work is to prove surjectivity and the
two-generator kernel equality for the particular closed immersion. -/
noncomputable def quotientStalkLinearEquivOfSurjectiveAndKernelEq
    {R S : Type u} [CommRing R] [AddCommGroup S] [Module R S]
    (I : Ideal R) (f : R →ₗ[R] S)
    (hsurj : Function.Surjective f)
    (hker : LinearMap.ker f = I) : (R ⧸ I) ≃ₗ[R] S := by
  have hrange : LinearMap.range f = (⊤ : Submodule R S) :=
    LinearMap.range_eq_top.mpr hsurj
  have e₁ : (R ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
    LinearMap.quotKerEquivRange f
  have e₂ : LinearMap.range f ≃ₗ[R] (⊤ : Submodule R S) :=
    LinearEquiv.ofEq _ _ hrange
  exact (Submodule.quotEquivOfEq (I : Submodule R R) (LinearMap.ker f) hker.symm).trans
    (e₁.trans (e₂.trans Submodule.topEquiv))

/-- The quotient map for a closed immersion is locally surjective on the
underlying additive sheaves.  On an affine neighbourhood this is exactly the
surjectivity of the defining map on sections; shrinking to an affine open
proves the local-surjectivity condition. -/
theorem closedImmersionUnitToPushforwardUnit_isLocallySurjective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    TopCat.Presheaf.IsLocallySurjective
      (((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).hom) := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  refine ⟨V, hVU, ?_, hxV⟩
  let sV := ((Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map (homOfLE hVU).op s
  obtain ⟨t, ht⟩ := i.app_surjective V hV sV
  refine ⟨t, ?_⟩
  change i.app V t = _
  rw [ht]
  rfl

/-- The locally surjective quotient map remains surjective after passing to a
literal stalk.  The source stalk is then identified with the structure-ring
stalk through the canonical unit-module equivalence. -/
theorem closedImmersionPushforwardStalkFromRingLinearMap_surjective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    Function.Surjective (closedImmersionPushforwardStalkFromRingLinearMap i x) := by
  have hs := (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
    (((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).hom)).mp
    (closedImmersionUnitToPushforwardUnit_isLocallySurjective i) x
  dsimp [closedImmersionPushforwardStalkFromRingLinearMap]
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let g := schemeModuleStalkLinearMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x
  change Function.Surjective (g.comp u.toLinearMap)
  have hg : Function.Surjective g := by
    change Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).hom)
    exact hs
  exact hg.comp u.surjective

/-- Specialization of the preceding algebra lemma to the pushforward stalk of
a closed immersion.  Once the closed-immersion stalk map is shown surjective
and its kernel is generated by the two local equations, this supplies the
quotient-stalk equivalence needed by the local Serre presentation. -/
noncomputable def closedImmersionPushforwardStalkQuotientLinearEquivOfSurjectiveAndKernelEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X)
    (hsurj : Function.Surjective (closedImmersionPushforwardStalkFromRingLinearMap i x)) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      (X.presheaf.stalk x ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))) ≃ₗ[
        X.presheaf.stalk x]
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel
  exact quotientStalkLinearEquivOfSurjectiveAndKernelEq
    (Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
    (closedImmersionPushforwardStalkFromRingLinearMap i x) hsurj hkernel

/-- The closed-immersion stalk quotient equivalence with surjectivity supplied
internally by the preceding stalk theorem.  Its only remaining geometric
premise is the claimed two-generator equality for the kernel. -/
noncomputable def closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      (X.presheaf.stalk x ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))) ≃ₗ[
        X.presheaf.stalk x]
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel
  exact closedImmersionPushforwardStalkQuotientLinearEquivOfSurjectiveAndKernelEq
    i x (closedImmersionPushforwardStalkFromRingLinearMap_surjective i x) f g hkernel

set_option linter.style.haveILetI false in
/-- After identifying the unit-module stalk with the structure-ring stalk,
the closed-immersion ideal is the kernel of its literal quotient map. -/
theorem closedImmersionModule_stalk_linear_exact_from_ring
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    Function.Exact (closedImmersionModuleStalkToRingLinearMap i x)
      (closedImmersionPushforwardStalkFromRingLinearMap i x) := by
  dsimp [closedImmersionModuleStalkToRingLinearMap,
    closedImmersionPushforwardStalkFromRingLinearMap]
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let f := schemeModuleStalkLinearMap (IdealSheafDataModule.closedImmersionModuleToUnit i) x
  let g := schemeModuleStalkLinearMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x
  change X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at u
  change ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) →ₗ[
      X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x at f
  change TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x →ₗ[
        X.presheaf.stalk x]
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) at g
  change Function.Exact (u.symm.toLinearMap.comp f) (g.comp u.toLinearMap)
  have h := closedImmersionModule_stalk_linear_exact i x
  change Function.Exact f g at h
  intro a
  constructor
  · intro ha
    have hga : g (u a) = 0 := ha
    obtain ⟨b, hb⟩ := (h (u a)).mp hga
    refine ⟨b, ?_⟩
    apply u.injective
    simpa [LinearMap.comp_apply] using hb
  · rintro ⟨b, hb⟩
    have hu : f b = u a := by
      have happly := congrArg u hb
      simpa [LinearMap.comp_apply] using happly
    change g (u a) = 0
    rw [← hu]
    exact (h (f b)).mpr ⟨b, rfl⟩

set_option linter.style.haveILetI false in
/-- The literal stalk of the ideal sheaf of a closed immersion is precisely
the kernel of the literal local quotient map. -/
theorem closedImmersionModule_stalk_range_eq_ker_from_ring
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    LinearMap.range (closedImmersionModuleStalkToRingLinearMap i x) =
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  exact (LinearMap.exact_iff.mp
    (closedImmersionModule_stalk_linear_exact_from_ring i x)).symm

end

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- If the sections of a module inclusion are locally generated by two
sections `F` and `G`, then the image on the stalk is the ideal generated by
their germs.  The hypotheses are an explicit affine-local interface for the
remaining geometric calculation in Voisin's construction. -/
theorem schemeModuleStalk_range_eq_span_of_local_generators
    {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] (x : X)
    (U : Opens X) (hxU : x ∈ U)
    (F G : X.presheaf.obj (Opposite.op U))
    (hgen : ∀ (V : Opens X) (hVU : V ≤ U) (hxV : x ∈ V)
      (m : M.presheaf.obj (Opposite.op V)),
      ∃ a b : X.presheaf.obj (Opposite.op V),
        (φ.val.app (Opposite.op V)) m =
          a * (X.presheaf.map (homOfLE hVU).op) F +
            b * (X.presheaf.map (homOfLE hVU).op) G)
    (hF : ∃ mF : M.presheaf.obj (Opposite.op U),
      (φ.val.app (Opposite.op U)) mF = F)
    (hG : ∃ mG : M.presheaf.obj (Opposite.op U),
      (φ.val.app (Opposite.op U)) mG = G) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    LinearMap.range (schemeModuleStalkToRingLinearMap φ x) =
      Ideal.span ({X.presheaf.germ U x hxU F, X.presheaf.germ U x hxU G} :
        Set (X.presheaf.stalk x)) := by
  dsimp
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨m, rfl⟩
    obtain ⟨V, hVU, hxV, mV, hmV⟩ :=
      M.presheaf.exists_le_germ_eq m hxU
    obtain ⟨a, b, hab⟩ := hgen V hVU hxV mV
    rw [← hmV, schemeModuleStalkToRingLinearMap_germ]
    apply (Ideal.mem_span_pair).2
    refine ⟨X.presheaf.germ V x hxV a, X.presheaf.germ V x hxV b, ?_⟩
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV F,
      ← X.presheaf.germ_res_apply (homOfLE hVU) x hxV G]
    calc
      (X.presheaf.germ V x hxV) a * (X.presheaf.germ V x hxV)
            ((X.presheaf.map (homOfLE hVU).op) F) +
          (X.presheaf.germ V x hxV) b * (X.presheaf.germ V x hxV)
            ((X.presheaf.map (homOfLE hVU).op) G) =
        (X.presheaf.germ V x hxV)
          (a * (X.presheaf.map (homOfLE hVU).op) F +
            b * (X.presheaf.map (homOfLE hVU).op) G) := by
        rw [map_add, map_mul, map_mul]
      _ = (X.presheaf.germ V x hxV) ((φ.val.app (Opposite.op V)) mV) := by rw [hab]
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨mF, hmF⟩ := hF
      refine ⟨TopCat.Presheaf.germ M.presheaf U x hxU mF, ?_⟩
      rw [schemeModuleStalkToRingLinearMap_germ, hmF]
    · obtain ⟨mG, hmG⟩ := hG
      refine ⟨TopCat.Presheaf.germ M.presheaf U x hxU mG, ?_⟩
      rw [schemeModuleStalkToRingLinearMap_germ, hmG]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Affine-local version of the preceding range calculation.  Every stalk
representative can be restricted to an affine basis neighborhood, so the
generator condition only needs to be checked on affine opens, as in
`IdealSheafData`. -/
theorem schemeModuleStalk_range_eq_span_of_affine_local_generators
    {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1)
    (F G : X.presheaf.obj (Opposite.op U.1))
    (hgen : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U.1) (hxV : x ∈ V.1)
      (m : M.presheaf.obj (Opposite.op V.1)),
      ∃ a b : X.presheaf.obj (Opposite.op V.1),
        (φ.val.app (Opposite.op V.1)) m =
          a * (X.presheaf.map (homOfLE hVU).op) F +
            b * (X.presheaf.map (homOfLE hVU).op) G)
    (hF : ∃ mF : M.presheaf.obj (Opposite.op U.1),
      (φ.val.app (Opposite.op U.1)) mF = F)
    (hG : ∃ mG : M.presheaf.obj (Opposite.op U.1),
      (φ.val.app (Opposite.op U.1)) mG = G) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
    LinearMap.range (schemeModuleStalkToRingLinearMap φ x) =
      Ideal.span ({X.presheaf.germ U.1 x hxU F, X.presheaf.germ U.1 x hxU G} :
        Set (X.presheaf.stalk x)) := by
  dsimp
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨m, rfl⟩
    obtain ⟨V₀, hV₀U, hxV₀, m₀, hm₀⟩ :=
      M.presheaf.exists_le_germ_eq m hxU
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVV₀⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV₀ V₀.2
    let VA : X.affineOpens := ⟨V, hV⟩
    let mV := M.presheaf.map (homOfLE hVV₀).op m₀
    have hmV : (TopCat.Presheaf.germ M.presheaf V x hxV) mV = m := by
      calc
        (TopCat.Presheaf.germ M.presheaf V x hxV) mV =
            (TopCat.Presheaf.germ M.presheaf V₀ x hxV₀) m₀ := by
          exact M.presheaf.germ_res_apply (homOfLE hVV₀) x hxV m₀
        _ = m := hm₀
    obtain ⟨a, b, hab⟩ := hgen VA (hVV₀.trans hV₀U) hxV mV
    rw [← hmV, schemeModuleStalkToRingLinearMap_germ]
    apply (Ideal.mem_span_pair).2
    refine ⟨X.presheaf.germ V x hxV a, X.presheaf.germ V x hxV b, ?_⟩
    rw [← X.presheaf.germ_res_apply (homOfLE (hVV₀.trans hV₀U)) x hxV F,
      ← X.presheaf.germ_res_apply (homOfLE (hVV₀.trans hV₀U)) x hxV G]
    calc
      (X.presheaf.germ V x hxV) a * (X.presheaf.germ V x hxV)
            ((X.presheaf.map (homOfLE (hVV₀.trans hV₀U)).op) F) +
          (X.presheaf.germ V x hxV) b * (X.presheaf.germ V x hxV)
            ((X.presheaf.map (homOfLE (hVV₀.trans hV₀U)).op) G) =
        (X.presheaf.germ V x hxV)
          (a * (X.presheaf.map (homOfLE (hVV₀.trans hV₀U)).op) F +
            b * (X.presheaf.map (homOfLE (hVV₀.trans hV₀U)).op) G) := by
        rw [map_add, map_mul, map_mul]
      _ = (X.presheaf.germ V x hxV) ((φ.val.app (Opposite.op V)) mV) := by
        exact congrArg (X.presheaf.germ V x hxV) hab.symm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨mF, hmF⟩ := hF
      refine ⟨TopCat.Presheaf.germ M.presheaf U.1 x hxU mF, ?_⟩
      rw [schemeModuleStalkToRingLinearMap_germ, hmF]
    · obtain ⟨mG, hmG⟩ := hG
      refine ⟨TopCat.Presheaf.germ M.presheaf U.1 x hxU mG, ?_⟩
      rw [schemeModuleStalkToRingLinearMap_germ, hmG]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk kernel of a closed immersion's quotient map is generated by two
local equations whenever the associated ideal module has the displayed
local two-generator description.  This is the exact bridge used by the
subsequent Serre stalk presentation. -/
theorem closedImmersionPushforwardStalk_ker_eq_span_of_local_generators
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X)
    (U : Opens X) (hxU : x ∈ U)
    (F G : X.presheaf.obj (Opposite.op U))
    (hgen : ∀ (V : Opens X) (hVU : V ≤ U) (hxV : x ∈ V)
      (m : (show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.obj
        (Opposite.op V)),
      ∃ a b : X.presheaf.obj (Opposite.op V),
        ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op V)) m =
          a * (X.presheaf.map (homOfLE hVU).op) F +
            b * (X.presheaf.map (homOfLE hVU).op) G)
    (hF : ∃ mF : (show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.obj
        (Opposite.op U),
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op U)) mF = F)
    (hG : ∃ mG : (show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.obj
        (Opposite.op U),
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op U)) mG = G) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({X.presheaf.germ U x hxU F, X.presheaf.germ U x hxU G} :
        Set (X.presheaf.stalk x)) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  have hrange := schemeModuleStalk_range_eq_span_of_local_generators
    (X := X) (M := show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    (IdealSheafDataModule.closedImmersionModuleToUnit i) x U hxU F G hgen hF hG
  have hrange' : LinearMap.range (closedImmersionModuleStalkToRingLinearMap i x) =
      Ideal.span ({X.presheaf.germ U x hxU F, X.presheaf.germ U x hxU G} :
        Set (X.presheaf.stalk x)) := by
    simpa [closedImmersionModuleStalkToRingLinearMap] using hrange
  have hker := closedImmersionModule_stalk_range_eq_ker_from_ring i x
  exact hker.symm.trans hrange'

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Affine-open specialization of the closed-immersion kernel bridge.  This
is the form intended for a concrete affine coordinate calculation of
Voisin's finite subscheme. -/
theorem closedImmersionPushforwardStalk_ker_eq_span_of_affine_local_generators
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1)
    (F G : X.presheaf.obj (Opposite.op U.1))
    (hgen : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U.1) (hxV : x ∈ V.1)
      (m : (show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.obj
        (Opposite.op V.1)),
      ∃ a b : X.presheaf.obj (Opposite.op V.1),
        ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op V.1)) m =
          a * (X.presheaf.map (homOfLE hVU).op) F +
            b * (X.presheaf.map (homOfLE hVU).op) G)
    (hF : ∃ mF : (show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.obj
        (Opposite.op U.1),
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op U.1)) mF = F)
    (hG : ∃ mG : (show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.obj
        (Opposite.op U.1),
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op U.1)) mG = G) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({X.presheaf.germ U.1 x hxU F, X.presheaf.germ U.1 x hxU G} :
        Set (X.presheaf.stalk x)) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  have hrange := schemeModuleStalk_range_eq_span_of_affine_local_generators
    (X := X) (M := show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    (IdealSheafDataModule.closedImmersionModuleToUnit i) x U hxU F G hgen hF hG
  have hrange' : LinearMap.range (closedImmersionModuleStalkToRingLinearMap i x) =
      Ideal.span ({X.presheaf.germ U.1 x hxU F, X.presheaf.germ U.1 x hxU G} :
        Set (X.presheaf.stalk x)) := by
    simpa [closedImmersionModuleStalkToRingLinearMap] using hrange
  have hker := closedImmersionModule_stalk_range_eq_ker_from_ring i x
  exact hker.symm.trans hrange'

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The local two-generator bridge can be fed directly by the affine ideal
data.  Thus the stalk kernel calculation no longer assumes that sections of
the abstract image module have already been presented by the two equations:
membership in the affine kernel ideal supplies the coefficients, and the
canonical kernel/image isomorphism supplies the required module lifts. -/
theorem closedImmersionPushforwardStalk_ker_eq_span_of_affine_ideal_eq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1)
    (F G : X.presheaf.obj (Opposite.op U.1))
    (hideal : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U.1),
      i.ker.ideal V = Ideal.span ({
        X.presheaf.map (homOfLE hVU).op F,
        X.presheaf.map (homOfLE hVU).op G} : Set (X.presheaf.obj (Opposite.op V.1)))) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({X.presheaf.germ U.1 x hxU F, X.presheaf.germ U.1 x hxU G} :
        Set (X.presheaf.stalk x)) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  apply closedImmersionPushforwardStalk_ker_eq_span_of_affine_local_generators
    i x U hxU F G
  · intro V hVU hxV m
    let e := IdealSheafDataModule.closedImmersionModuleToKernelIso i
    let t := ConcreteCategory.hom (e.hom.val.app (Opposite.op V.1)) m
    have hfac := congrArg (fun q => q.val.app (Opposite.op V.1))
      (IdealSheafDataModule.closedImmersionModuleToKernel_comp i)
    have hfac' := ConcreteCategory.congr_hom hfac
    have hfac'' := hfac' m
    change (IdealSheafDataModule.closedImmersionKernelModuleToUnit i).val.app
        (Opposite.op V.1)
        ((IdealSheafDataModule.closedImmersionModuleToKernel i).val.app
          (Opposite.op V.1) m) =
      (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op V.1) m at hfac''
    have hs : ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op V.1)) m ∈ i.ker.ideal V := by
      rw [Scheme.Hom.ker_apply]
      have hcond := congrArg (fun q => q.val.app (Opposite.op V.1))
        (kernel.condition (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i))
      have hcond' := ConcreteCategory.congr_hom hcond
      have hcond'' := hcond' t
      change i.app V ((IdealSheafDataModule.closedImmersionKernelModuleToUnit i).val.app
          (Opposite.op V.1) t) = 0 at hcond''
      have hzero_s : i.app V ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op V.1) m) = 0 := by
        rw [← hfac'']
        simpa [t, e, IdealSheafDataModule.closedImmersionModuleToKernelIso] using hcond''
      exact hzero_s
    let s : X.presheaf.obj (Opposite.op V.1) :=
      (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op V.1) m
    have hs' : s ∈ i.ker.ideal V := by exact hs
    have hspan : s ∈ Ideal.span ({
          X.presheaf.map (homOfLE hVU).op F,
          X.presheaf.map (homOfLE hVU).op G} :
          Set (X.presheaf.obj (Opposite.op V.1))) := by
      rw [← hideal V hVU]
      exact hs'
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hspan
    refine ⟨a, b, ?_⟩
    change s = a * (X.presheaf.map (homOfLE hVU).op) F +
      b * (X.presheaf.map (homOfLE hVU).op) G
    exact hab.symm
  · have hFmem : F ∈ i.ker.ideal U := by
      rw [hideal U le_rfl]
      exact Ideal.subset_span (by simp)
    obtain ⟨mF, hmF⟩ :=
      IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem i U F hFmem
    exact ⟨mF, hmF⟩
  · have hGmem : G ∈ i.ker.ideal U := by
      rw [hideal U le_rfl]
      exact Ideal.subset_span (by simp)
    obtain ⟨mG, hmG⟩ :=
      IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem i U G hGmem
    exact ⟨mG, hmG⟩

/-- The kernel ideal of the subscheme cut out by a global two-generator ideal
is the span of the restricted generators on every affine open. -/
theorem idealTop_subscheme_ker_ideal_eq_span_pair_restriction
    {X : Scheme.{u}}
    (F G : X.presheaf.obj (Opposite.op ⊤))
    (U : X.affineOpens) (hU : U.1 ≤ (⊤ : X.Opens)) :
    ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.span ({F, G} : Set (X.presheaf.obj (Opposite.op ⊤))))).subschemeι).ker.ideal U =
      Ideal.span ({X.presheaf.map (homOfLE hU).op F,
        X.presheaf.map (homOfLE hU).op G} :
        Set (X.presheaf.obj (Opposite.op U.1))) := by
  rw [Scheme.IdealSheafData.ker_subschemeι]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  rw [Ideal.map_span]
  rw [Set.image_pair]

namespace BundleSectionZeroLocus

/-- The affine ideal of the rank-two free-section zero locus is generated by
the two displayed scalar coordinates. -/
theorem sectionZeroSubschemeOfFreeIso_ker_ideal_eq_span_pair_restriction
    {X : Scheme.{u}} {E : X.Modules}
    (e : SheafOfModules.free (R := X.ringCatSheaf) (ULift (Fin 2)) ≅ E)
    (s : E.sections)
    (U : X.affineOpens) (hU : U.1 ≤ (⊤ : X.Opens)) :
    (sectionZeroSubschemeOfFreeIsoι (X := X) (ULift (Fin 2)) e s).ker.ideal U =
      Ideal.span ({
        X.presheaf.map (homOfLE hU).op
          (sectionCoordinateOfFreeIso (X := X) (ULift (Fin 2)) e s (ULift.up 0)),
        X.presheaf.map (homOfLE hU).op
          (sectionCoordinateOfFreeIso (X := X) (ULift (Fin 2)) e s (ULift.up 1))} :
        Set (X.presheaf.obj (Opposite.op U.1))) := by
  change (sectionZeroIdealOfFreeIso (X := X) (ULift (Fin 2)) e s).subschemeι.ker.ideal U = _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  change (sectionZeroIdealOfFreeIso (X := X) (ULift (Fin 2)) e s).ideal U = _
  rw [sectionZeroIdealOfFreeIso_ulift_fin_two_eq]
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal]
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  rw [Set.image_singleton, Set.image_singleton]
  rw [Ideal.span_insert]

/-- The preceding affine calculation feeds directly into the literal stalk of
the local rank-two zero scheme used on an affine trivialization. -/
theorem localSectionZeroSubschemeOfOver_stalk_ker_eq_span_pair
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (x : (U : Scheme.{u})) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk x)
        ((show (U : Scheme.{u}).Modules from
          (Scheme.Modules.pushforward
            (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)).obj
            (SheafOfModules.unit
              (localSectionZeroSubschemeOfOver U (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
    LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({
        (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
          (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
            (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
            (restrictSectionToOpen (X := X) U s) (ULift.up 0)),
        (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
          (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
            (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
            (restrictSectionToOpen (X := X) U s) (ULift.up 1))} :
        Set ((U : Scheme.{u}).presheaf.stalk x)) := by
  dsimp
  let XU : Scheme := (U : Scheme.{u})
  let e := localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t
  let sr := restrictSectionToOpen (X := X) U s
  let F := sectionCoordinateOfFreeIso (X := XU) (ULift (Fin 2)) e sr (ULift.up 0)
  let G := sectionCoordinateOfFreeIso (X := XU) (ULift (Fin 2)) e sr (ULift.up 1)
  let Utop : XU.affineOpens := ⟨⊤, AlgebraicGeometry.isAffineOpen_top XU⟩
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  letI : IsClosedImmersion i := by
    exact isClosedImmersion_localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  have hxUtop : x ∈ Utop.1 := Set.mem_univ x
  apply closedImmersionPushforwardStalk_ker_eq_span_of_affine_ideal_eq
    i x Utop hxUtop F G
  intro W hWtop
  change (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s).ker.ideal W = _
  unfold localSectionZeroSubschemeOfOverι localSectionZeroSubschemeOfOver
  have hz := sectionZeroSubschemeOfFreeIso_ker_ideal_eq_span_pair_restriction
    (X := XU) e sr W hWtop
  unfold sectionZeroSubschemeOfFreeIsoι sectionZeroSubschemeOfFreeIso at hz
  rw [Scheme.IdealSheafData.ker_subschemeι] at hz
  simpa [XU, e, sr, F, G, localSectionZeroIdealOfOver] using hz


end BundleSectionZeroLocus

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A local image computation for a closed immersion identifies the actual
ideal-module stalk with the computed two-generator ideal. -/
noncomputable def closedImmersionModuleStalkLinearEquivOfRangeEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.range (closedImmersionModuleStalkToRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) ≃ₗ[
        X.presheaf.stalk x] Ideal.span ({f, g} : Set (X.presheaf.stalk x)) := by
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  exact schemeModuleStalkLinearEquivOfRangeEq
    (IdealSheafDataModule.closedImmersionModuleToUnit i) x

set_option linter.style.haveILetI false in
/-- A two-generator kernel computation for the literal quotient map gives
the required two-generator presentation of the actual closed-immersion ideal
stalk.  This packages the proved kernel/range comparison with the local
generator calculation. -/
noncomputable def closedImmersionModuleStalkLinearEquivOfQuotientKernelEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) ≃ₗ[
        X.presheaf.stalk x] Ideal.span ({f, g} : Set (X.presheaf.stalk x)) := by
  intro f g hker
  exact closedImmersionModuleStalkLinearEquivOfRangeEq i x f g
    ((closedImmersionModule_stalk_range_eq_ker_from_ring i x).trans hker)

set_option linter.style.haveILetI false in
/-- The quotient stalk of the actual rank-two zero scheme is the literal
quotient by its two coordinate germs.  The kernel equality is supplied by
the affine ideal calculation above, while surjectivity is the intrinsic
closed-immersion stalk property. -/
noncomputable def localSectionZeroSubschemeOfOver_pushforwardStalkQuotientLinearEquiv
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections) (x : (U : Scheme.{u})) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk x)
        ((show (U : Scheme.{u}).Modules from
          (Scheme.Modules.pushforward
            (BundleSectionZeroLocus.localSectionZeroSubschemeOfOverι
              (X := X) U (ULift (Fin 2)) t s)).obj
            (SheafOfModules.unit
              (BundleSectionZeroLocus.localSectionZeroSubschemeOfOver
                U (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    ((U : Scheme.{u}).presheaf.stalk x ⧸
      Ideal.span ({
        (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
          (BundleSectionZeroLocus.sectionCoordinateOfFreeIso
            (X := (U : Scheme.{u})) (ULift (Fin 2))
            (BundleSectionZeroLocus.localFreeIsoOfOver
              (X := X) U (ULift (Fin 2)) t)
            (BundleSectionZeroLocus.restrictSectionToOpen (X := X) U s)
            (ULift.up 0)),
        (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
          (BundleSectionZeroLocus.sectionCoordinateOfFreeIso
            (X := (U : Scheme.{u})) (ULift (Fin 2))
            (BundleSectionZeroLocus.localFreeIsoOfOver
              (X := X) U (ULift (Fin 2)) t)
            (BundleSectionZeroLocus.restrictSectionToOpen (X := X) U s)
            (ULift.up 1))} :
        Set ((U : Scheme.{u}).presheaf.stalk x))) ≃ₗ[
          (U : Scheme.{u}).presheaf.stalk x]
      ((show (U : Scheme.{u}).Modules from
        (Scheme.Modules.pushforward
          (BundleSectionZeroLocus.localSectionZeroSubschemeOfOverι
            (X := X) U (ULift (Fin 2)) t s)).obj
          (SheafOfModules.unit
            (BundleSectionZeroLocus.localSectionZeroSubschemeOfOver
              U (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) := by
  dsimp
  let XU : Scheme := (U : Scheme.{u})
  let i := BundleSectionZeroLocus.localSectionZeroSubschemeOfOverι
    (X := X) U (ULift (Fin 2)) t s
  let F := XU.presheaf.germ ⊤ x (Set.mem_univ x)
    (BundleSectionZeroLocus.sectionCoordinateOfFreeIso
      (X := XU) (ULift (Fin 2))
      (BundleSectionZeroLocus.localFreeIsoOfOver
        (X := X) U (ULift (Fin 2)) t)
      (BundleSectionZeroLocus.restrictSectionToOpen (X := X) U s)
      (ULift.up 0))
  let G := XU.presheaf.germ ⊤ x (Set.mem_univ x)
    (BundleSectionZeroLocus.sectionCoordinateOfFreeIso
      (X := XU) (ULift (Fin 2))
      (BundleSectionZeroLocus.localFreeIsoOfOver
        (X := X) U (ULift (Fin 2)) t)
      (BundleSectionZeroLocus.restrictSectionToOpen (X := X) U s)
      (ULift.up 1))
  letI : IsClosedImmersion i := by
    exact BundleSectionZeroLocus.isClosedImmersion_localSectionZeroSubschemeOfOverι
      U (ULift (Fin 2)) t s
  exact closedImmersionPushforwardStalkQuotientLinearEquivOfSurjectiveAndKernelEq
    i x (closedImmersionPushforwardStalkFromRingLinearMap_surjective i x) F G
    (BundleSectionZeroLocus.localSectionZeroSubschemeOfOver_stalk_ker_eq_span_pair
      U t s x)

/-! ### The actual Serre stalk in standard local form -/

/-- Precomposing the left map in an exact pair by a surjective map preserves
exactness. -/
lemma functionExact_precomp_of_surjective {A B C D : Type u} [Zero C]
    (f : B → C) (h : A → B) (g : C → D) [Zero D]
    (hexact : Function.Exact f g) (hsurj : Function.Surjective h) :
    Function.Exact (f ∘ h) g := by
  intro y
  constructor
  · intro hy
    obtain ⟨b, hb⟩ := (hexact y).mp hy
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨a, by rw [Function.comp_apply, ha, hb]⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact (hexact _).mpr ⟨h a, rfl⟩

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A local quotient identification and two compatible lifts put the literal
stalk of an actual Serre extension in the standard local Serre presentation.

The quotient equivalence, generator lifts, and their relation are precisely
the remaining local-geometric input.  Exactness, linearity, and injectivity
of the canonical section are supplied here from the actual extension. -/
noncomputable def serreExtension_stalkPresentationEquiv_of_quotientEquiv_of_lifts
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from M).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from M) x
    ∀ (f g c : X.presheaf.stalk x)
      (q : ((show X.Modules from M).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk x)),
      q (schemeModuleStalkLinearMap e.projection x e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩ →
      q (schemeModuleStalkLinearMap e.projection x e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩ →
      (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c →
      IsRegular f →
      IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      ((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        localSerreExtensionPresentation f g c := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from M).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from M) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
  intro f g c q e₁ e₂ hq₁ hq₂ hrel hf hg
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let i := schemeModuleStalkLinearMap e.inclusion x
  let i' := serreExtensionStalkCanonicalSection e x
  let p₀ := schemeModuleStalkLinearMap e.projection x
  let p := q.toLinearMap.comp p₀
  apply localSerreExtensionPresentationEquiv_of_exact_of_lifts i' f g c p e₁ e₂
  · have hraw := serreExtension_stalk_linear_exact e x
    have hpre : Function.Exact (i ∘ u) p₀ :=
      functionExact_precomp_of_surjective i u p₀ hraw u.surjective
    exact hpre.comp_injective q q.injective (map_zero q)
  · exact serreExtensionStalkCanonicalSection_injective e x
  · exact hq₁
  · exact hq₂
  · rw [hrel, ← i'.map_smul]
    simp
    rfl
  · exact isRegular_iff_mem_nonZeroDivisors.mp hf
  · exact isRegular_iff_mem_nonZeroDivisors.mp hg

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The presentation equivalence of an actual Serre stalk extends to a
morphism from the entire stalk short complex to the standard local Serre
complex.  Thus it records compatibility with both the canonical section and
the projection to the ideal, which is the data required by Ext naturality. -/
noncomputable def
    serreExtension_stalkComplexComparison_of_quotientEquiv_of_lifts
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from M).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from M) x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive
        (schemeModuleStalkModuleFunctor X x)
    ∀ (f g c : X.presheaf.stalk x)
      (q : ((show X.Modules from M).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk x)),
      q (schemeModuleStalkLinearMap e.projection x e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩ →
      q (schemeModuleStalkLinearMap e.projection x e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩ →
      (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c →
      IsRegular f →
      IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      (e.complex.map (schemeModuleStalkModuleFunctor X x) ⟶
        localSerreExtensionModuleComplex f g c) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from M).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from M) x
  letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive
      (schemeModuleStalkModuleFunctor X x)
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (PresheafOfModules.unit
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)) x
  intro f g c q e₁ e₂ hq₁ hq₂ hrel hf hg
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let i := schemeModuleStalkLinearMap e.inclusion x
  let i' := serreExtensionStalkCanonicalSection e x
  let p₀ := schemeModuleStalkLinearMap e.projection x
  let p := q.toLinearMap.comp p₀
  have hexact : Function.Exact i' p := by
    have hraw := serreExtension_stalk_linear_exact e x
    have hpre : Function.Exact (i ∘ u) p₀ :=
      functionExact_precomp_of_surjective i u p₀ hraw u.surjective
    exact hpre.comp_injective q q.injective (map_zero q)
  have hinj : Function.Injective i' :=
    serreExtensionStalkCanonicalSection_injective e x
  have hf' : f ∈ (X.presheaf.stalk x)⁰ :=
    isRegular_iff_mem_nonZeroDivisors.mp hf
  have hg' : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰ :=
    isRegular_iff_mem_nonZeroDivisors.mp hg
  have hrel' : (-g) • e₁ + f • e₂ = c • i' 1 := by
    rw [hrel, ← i'.map_smul]
    simp
    rfl
  let qE := localSerreExtensionPresentationEquiv_of_exact_of_lifts
    i' f g c p e₁ e₂ hexact hinj hq₁ hq₂ hrel' hf' hg'
  refine ShortComplex.homMk
    (schemeModuleUnitStalkIso X x).hom
    (LinearEquiv.toModuleIso qE).hom
    (LinearEquiv.toModuleIso q).hom ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change localSerreExtensionFromRing f g c (u.symm a) = qE (i a)
    have ha : i a = i' (u.symm a) := by
      dsimp [i', serreExtensionStalkCanonicalSection]
      rw [u.apply_symm_apply]
      rfl
    rw [ha]
    exact (localSerreExtensionPresentationEquiv_of_exact_of_lifts_inclusion
      i' f g c p e₁ e₂ hexact hinj hq₁ hq₂ hrel' hf' hg' (u.symm a)).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change localSerreExtensionToIdeal f g c (qE y) = q (p₀ y)
    exact localSerreExtensionPresentationEquiv_of_exact_of_lifts_projection
      i' f g c p e₁ e₂ hexact hinj hq₁ hq₂ hrel' hf' hg' y

set_option linter.style.haveILetI false in
/-- The local Serre presentation for an actual closed-immersion ideal can be
obtained directly from a kernel calculation for its literal quotient stalk.
The only local inputs left are the two-generator kernel calculation and the
two compatible lifts in the extension; no separate identification of the
ideal-sheaf stalk range is required. -/
noncomputable def
    serreExtension_stalkPresentationEquiv_of_closedImmersionQuotientKernelEq_of_lifts
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (e : SerreExtensionSequenceData X
      (show X.Modules from IdealSheafDataModule.closedImmersionModule i)) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g c : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk x)),
      (closedImmersionModuleStalkLinearEquivOfQuotientKernelEq i x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩ →
      (closedImmersionModuleStalkLinearEquivOfQuotientKernelEq i x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩ →
      (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c →
      IsRegular f →
      IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      ((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        localSerreExtensionPresentation f g c := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g c hkernel e₁ e₂ he₁ he₂ hrel hf hg
  exact serreExtension_stalkPresentationEquiv_of_quotientEquiv_of_lifts e x f g c
    (closedImmersionModuleStalkLinearEquivOfQuotientKernelEq i x f g hkernel)
    e₁ e₂ he₁ he₂ hrel hf hg

noncomputable section

open CategoryTheory.Abelian
variable {X : Scheme.{u}}

theorem schemeModule_epi_isLocallySurjective {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val) := by
  letI : HasSheafify (Opens.grothendieckTopology (↑X.toPresheafedSpace)) AddCommGrpCat.{u} := inferInstance
  letI : HasWeakSheafify (Opens.grothendieckTopology (↑X.toPresheafedSpace)) AddCommGrpCat.{u} := inferInstance
  letI : (Opens.grothendieckTopology (↑X.toPresheafedSpace)).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let P : X.PresheafOfModules := Abelian.image f.val
  let a : M.val ⟶ P := Abelian.factorThruImage f.val
  let b : P ⟶ N.val := Abelian.image.ι f.val
  have hab : a ≫ b = f.val := Abelian.image.fac f.val
  have ha : Epi a := by infer_instance
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let S : X.Modules := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P
  let T : X.Modules := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val
  let c : T ⟶ M := adj.counit.app M
  have hc : IsIso adj.counit := by dsimp [adj]; infer_instance
  have hca : IsIso c := (NatTrans.isIso_iff_isIso_app adj.counit).mp hc M
  letI : IsIso c := hca
  let r : M ⟶ S := @inv _ _ _ _ c hca ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map a
  let z : S ⟶ N := (adj.homEquiv P N).symm b
  let φ := CategoryTheory.toSheafify (Opens.grothendieckTopology (↑X.toPresheafedSpace)) P.presheaf
  have hz_unit : adj.unit.app P ≫
      (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map z = b := by
    rw [← adj.homEquiv_unit P N z]
    exact (adj.homEquiv P N).apply_symm_apply b
  have hnat0 : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f.val ≫
        adj.counit.app N = adj.counit.app M ≫ f := by
    exact adj.counit.naturality f
  have hnat : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f.val ≫
        adj.counit.app N = c ≫ f := by
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f.val ≫
      adj.counit.app N = adj.counit.app M ≫ f
    exact hnat0
  have hmap : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map a ≫ z = c ≫ f := by
    apply (adj.homEquiv M.val N).injective
    rw [adj.homEquiv_naturality_left a z]
    have hleft : a ≫ (adj.homEquiv P N) z = f.val := by
      rw [adj.homEquiv_unit P N z, hz_unit]
      exact hab
    rw [hleft]
    apply (adj.homEquiv M.val N).symm.injective
    rw [adj.homEquiv_counit M.val N f.val]
    have hcancel : (adj.homEquiv M.val N).symm ((adj.homEquiv M.val N) (c ≫ f)) = c ≫ f :=
      (adj.homEquiv M.val N).symm_apply_apply (c ≫ f)
    exact hnat.trans hcancel.symm
  have hz_fac : r ≫ z = f := by
    calc
      r ≫ z = @inv _ _ _ _ c hca ≫
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map a ≫ z) := by
            dsimp [r]
            exact Category.assoc _ _ _
      _ = @inv _ _ _ _ c hca ≫ (c ≫ f) := by
            exact congrArg (fun q => @inv _ _ _ _ c hca ≫ q) hmap
      _ = f := by exact IsIso.inv_hom_id_assoc c f
  have hz_epi : Epi z := epi_of_epi_fac hz_fac
  have hlocb : Presheaf.IsLocallyInjective (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map b) := by
    apply Presheaf.isLocallyInjective_of_injective
    intro U
    apply (AddCommGrpCat.mono_iff_injective _).mp
    infer_instance
  have hlocφi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology (↑X.toPresheafedSpace)) φ := by
    infer_instance
  have hlocφs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (↑X.toPresheafedSpace)) φ := by
    infer_instance
  have hzcomp :
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map b =
        φ ≫ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val := by
    have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (𝟙 X.ringCatSheaf.obj) z
    change (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((adj.homEquiv P N) z) = _ at h
    rw [(adj.homEquiv P N).apply_symm_apply b] at h
    exact h
  have hlocz : Presheaf.IsLocallyInjective (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val) := by
    letI : Presheaf.IsLocallyInjective
        (Opens.grothendieckTopology (↑X.toPresheafedSpace)) φ := hlocφi
    letI : Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology (↑X.toPresheafedSpace)) φ := hlocφs
    apply (Presheaf.comp_isLocallyInjective_iff
      (Opens.grothendieckTopology (↑X.toPresheafedSpace)) φ
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val)).mp
    rw [← hzcomp]
    exact hlocb
  have hz_mono : Mono z := by
    have hz_forget_mono : Mono ((SheafOfModules.forget X.ringCatSheaf).map z) := by
      apply (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).mono_of_mono_map
      apply (NatTrans.mono_iff_mono_app _).2
      intro U
      change Mono (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val).app U)
      apply (AddCommGrpCat.mono_iff_injective _).mpr
      have hsep : Presieve.IsSeparated (Opens.grothendieckTopology (↑X.toPresheafedSpace))
          (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj S.val) ⋙ (forget Ab)) := by
        exact Presieve.IsSheaf.isSeparated
          ((isSheaf_iff_isSheaf_of_type
            (Opens.grothendieckTopology (↑X.toPresheafedSpace))
            (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj S.val) ⋙ (forget Ab))).mp
            ((Presheaf.isSheaf_iff_isSheaf_forget
              (Opens.grothendieckTopology (↑X.toPresheafedSpace))
              ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj S.val) (forget Ab)).mp S.isSheaf))
      exact ((Presheaf.isLocallyInjective_iff_injective_of_separated
        (Opens.grothendieckTopology (↑X.toPresheafedSpace))
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val) hsep).mp hlocz) U
    exact (Functor.reflectsMonomorphisms_of_faithful
      (SheafOfModules.forget X.ringCatSheaf)).reflects z hz_forget_mono
  have hz_iso : IsIso z := isIso_of_mono_of_epi z
  letI : IsIso z := hz_iso
  have hzval_iso : IsIso z.val := by
    change IsIso ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map z)
    exact Functor.map_isIso _ z
  letI : IsIso z.val := hzval_iso
  letI : IsIso ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val) :=
    Functor.map_isIso _ z.val
  have hloczsurj : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    infer_instance
  have hloc_comp : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      (φ ≫ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val) := by
    constructor
    intro U s
    have hle : (Sieve.bind
        (Presheaf.imageSieve ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val) s)
        (fun _ _ h => Presheaf.imageSieve φ h.choose)) ≤
          Presheaf.imageSieve
            (φ ≫ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val) s := by
      rintro V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩
      refine ⟨t', ?_⟩
      simp only [ConcreteCategory.comp_apply]
      rw [op_comp, Functor.map_comp]
      change (ConcreteCategory.hom
          (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val).app (Opposite.op V)))
          ((ConcreteCategory.hom (φ.app (Opposite.op V))) t') = _
      rw [ht']
      change (ConcreteCategory.hom
          (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map z.val).app (Opposite.op V)))
          ((ConcreteCategory.hom
            (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj S.val).map i.op))
            (Exists.choose H)) = _
      rw [NatTrans.naturality_apply, H.choose_spec]
      rfl
    apply (Opens.grothendieckTopology (↑X.toPresheafedSpace)).superset_covering hle
    apply (Opens.grothendieckTopology (↑X.toPresheafedSpace)).bind_covering
    · exact hloczsurj.imageSieve_mem s
    · intro V i hi
      exact hlocφs.imageSieve_mem hi.choose
  rw [← hab, Functor.map_comp]
  have hloc_a : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map a) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    infer_instance
  letI : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map a) := hloc_a
  letI : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map b) := by
    rw [hzcomp]
    exact hloc_comp
  infer_instance



/-- An epimorphism of scheme modules induces a surjection on every literal
stalk.  The proof combines the sheaf-level local-surjectivity theorem above
with the stalk characterization of local surjectivity. -/
theorem schemeModule_epi_stalkMap_surjective
    {M N : X.Modules} (f : M ⟶ N) [Epi f] (x : X) :
    Function.Surjective (schemeModuleStalkLinearMap f x) := by
  dsimp [schemeModuleStalkLinearMap]
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have hloc : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val) :=
    schemeModule_epi_isLocallySurjective f
  have hloc' : TopCat.Presheaf.IsLocallySurjective ((T.map f).hom) := by
    change Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)
    exact hloc
  have hs := (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      ((T.map f).hom)).mp hloc' x
  exact hs

/-- The literal additive-group stalk functor sends epimorphisms of scheme
modules to epimorphisms. -/
theorem schemeModuleStalkFunctor_map_epi
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Epi f] (x : X) :
    Epi ((schemeModuleStalkFunctor X x).map f) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  change Function.Surjective (schemeModuleStalkLinearMap f x)
  exact schemeModule_epi_stalkMap_surjective f x

noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkFunctor X x).PreservesEpimorphisms where
  preserves f := by
    exact schemeModuleStalkFunctor_map_epi f x

/-- The literal additive-group stalk functor sends monomorphisms of scheme
modules to monomorphisms. -/
theorem schemeModuleStalkFunctor_map_mono
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f] (x : X) :
    Mono ((schemeModuleStalkFunctor X x).map f) := by
  rw [AddCommGrpCat.mono_iff_injective]
  change Function.Injective (schemeModuleStalkLinearMap f x)
  exact schemeModuleStalkLinearMap_injective_of_mono f x

noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkFunctor X x).PreservesMonomorphisms where
  preserves f := by
    exact schemeModuleStalkFunctor_map_mono f x

/-- Literal additive-group stalks preserve finite colimits of scheme modules. -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    PreservesFiniteColimits (schemeModuleStalkFunctor X x) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (schemeModuleStalkFunctor X x)).mpr
  intro S hS
  letI : Epi S.g := hS.epi_g
  exact ⟨schemeModuleStalkFunctor_map_exact_of_shortExact x S hS,
    Functor.map_epi (schemeModuleStalkFunctor X x) S.g⟩

/-- Literal additive-group stalks preserve finite limits of scheme modules. -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (schemeModuleStalkFunctor X x) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (schemeModuleStalkFunctor X x)).mpr
  intro S hS
  letI : Mono S.f := hS.mono_f
  exact ⟨schemeModuleStalkFunctor_map_exact_of_shortExact x S hS,
    Functor.map_mono (schemeModuleStalkFunctor X x) S.f⟩

/-- The map on Ext groups induced by taking the literal additive-group stalk
of a scheme module.  The target Ext group has the one-higher universe forced
by `AddCommGrpCat`. -/
noncomputable def schemeModuleStalkExtMap (X : Scheme.{u}) (x : X)
    [HasExt.{u} (X.Modules)] [HasExt.{u + 1} AddCommGrpCat]
    (M N : X.Modules) (n : ℕ) :
    CategoryTheory.Abelian.Ext.{u} M N n →+
      CategoryTheory.Abelian.Ext.{u + 1}
        ((schemeModuleStalkFunctor X x).obj M)
        ((schemeModuleStalkFunctor X x).obj N) n :=
  Functor.mapExtAddHom (schemeModuleStalkFunctor X x) M N n

/-- Taking the literal stalk carries the extension class of a short exact
sequence to the extension class of its exact stalk sequence. -/
theorem schemeModuleStalkExtMap_extClass
    {X : Scheme.{u}} (x : X) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [HasExt.{u} (X.Modules)] [HasExt.{u + 1} AddCommGrpCat] :
    schemeModuleStalkExtMap X x S.X₃ S.X₁ 1 hS.extClass =
      (hS.map_of_exact (schemeModuleStalkFunctor X x)).extClass := by
  exact CategoryTheory.Abelian.Ext.mapExactFunctor_extClass
    (F := schemeModuleStalkFunctor X x) hS

/-- Literal local-ring module stalks send epimorphisms of scheme modules to
 epimorphisms. -/
theorem schemeModuleStalkModuleFunctor_map_epi
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Epi f] (x : X) :
    Epi ((schemeModuleStalkModuleFunctor X x).map f) := by
  rw [ModuleCat.epi_iff_surjective]
  change Function.Surjective (schemeModuleStalkLinearMap f x)
  exact schemeModule_epi_stalkMap_surjective f x

noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkModuleFunctor X x).PreservesEpimorphisms where
  preserves f := by
    intro hf
    letI : Epi f := hf
    exact schemeModuleStalkModuleFunctor_map_epi f x

/-- Literal local-ring module stalks send monomorphisms of scheme modules to
 monomorphisms. -/
theorem schemeModuleStalkModuleFunctor_map_mono
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f] (x : X) :
    Mono ((schemeModuleStalkModuleFunctor X x).map f) := by
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective (schemeModuleStalkLinearMap f x)
  exact schemeModuleStalkLinearMap_injective_of_mono f x

noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkModuleFunctor X x).PreservesMonomorphisms where
  preserves f := by
    intro hf
    letI : Mono f := hf
    exact schemeModuleStalkModuleFunctor_map_mono f x

/-- Literal local-ring module stalks preserve finite colimits. -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    PreservesFiniteColimits (schemeModuleStalkModuleFunctor X x) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (schemeModuleStalkModuleFunctor X x)).mpr
  intro S hS
  letI : Epi S.g := hS.epi_g
  exact ⟨schemeModuleStalkModuleFunctor_map_exact_of_shortExact x S hS,
    Functor.map_epi (schemeModuleStalkModuleFunctor X x) S.g⟩

/-- Literal local-ring module stalks preserve finite limits. -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (schemeModuleStalkModuleFunctor X x) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (schemeModuleStalkModuleFunctor X x)).mpr
  intro S hS
  letI : Mono S.f := hS.mono_f
  exact ⟨schemeModuleStalkModuleFunctor_map_exact_of_shortExact x S hS,
    Functor.map_mono (schemeModuleStalkModuleFunctor X x) S.f⟩

/-- The map from global scheme-module Ext to Ext over the local ring induced
by the literal stalk functor. -/
noncomputable def schemeModuleStalkModuleExtMap (X : Scheme.{u}) (x : X)
    [HasExt.{u} (X.Modules)]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (n : ℕ) :
    CategoryTheory.Abelian.Ext.{u} M N n →+
      CategoryTheory.Abelian.Ext.{u + 1}
        ((schemeModuleStalkModuleFunctor X x).obj M)
        ((schemeModuleStalkModuleFunctor X x).obj N) n :=
  Functor.mapExtAddHom (schemeModuleStalkModuleFunctor X x) M N n

/-- The local-ring stalk map sends a global short exact sequence's extension
class to the extension class of its stalk sequence. -/
theorem schemeModuleStalkModuleExtMap_extClass
    {X : Scheme.{u}} (x : X) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [HasExt.{u} (X.Modules)]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    schemeModuleStalkModuleExtMap X x S.X₃ S.X₁ 1 hS.extClass =
      (hS.map_of_exact (schemeModuleStalkModuleFunctor X x)).extClass := by
  exact CategoryTheory.Abelian.Ext.mapExactFunctor_extClass
    (F := schemeModuleStalkModuleFunctor X x) hS

/-- The local-ring stalk map on Ext is compatible with Yoneda products. -/
theorem schemeModuleStalkModuleExtMap_comp
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    {A B C : X.Modules} {m n p : ℕ}
    (α : CategoryTheory.Abelian.Ext.{u} A B m)
    (β : CategoryTheory.Abelian.Ext.{u} B C n) (h : m + n = p) :
    schemeModuleStalkModuleExtMap X x A C p (α.comp β h) =
      (schemeModuleStalkModuleExtMap X x A B m α).comp
        (schemeModuleStalkModuleExtMap X x B C n β) h := by
  exact CategoryTheory.Abelian.Ext.mapExactFunctor_comp
    (F := schemeModuleStalkModuleFunctor X x) α β h

/-- Taking a stalk and then comparing its exact complex with any other short
exact local complex transports the global extension class by the two endpoint
maps.  This combines stalk functoriality with extension-class naturality in
the form needed for the Serre presentation comparison. -/
theorem schemeModuleStalkModuleExtMap_extClass_naturality
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (T : ShortComplex (ModuleCat (X.presheaf.stalk x))) (hT : T.ShortExact)
    (a : S.map (schemeModuleStalkModuleFunctor X x) ⟶ T) :
    (schemeModuleStalkModuleExtMap X x S.X₃ S.X₁ 1 hS.extClass).comp
        (Ext.mk₀ a.τ₁) (add_zero 1) =
      (Ext.mk₀ a.τ₃).comp hT.extClass (zero_add 1) := by
  rw [schemeModuleStalkModuleExtMap_extClass]
  exact ShortComplex.ShortExact.extClass_naturality
    (hS.map_of_exact (schemeModuleStalkModuleFunctor X x)) hT a

/-- Two transported degree-one classes compose after the common middle
endpoint is identified.  This is the formal Yoneda-product bookkeeping used
to combine the two stalk comparisons below. -/
theorem ext_comp_transport_of_common_middle
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {A B C₀ A' B' C' : C}
    (qA : A ≅ A') (qC : C₀ ≅ C') (k : B ⟶ B')
    (alpha : Ext A B 1) (beta : Ext B C₀ 1)
    (alpha₀ : Ext A' B' 1) (beta₀ : Ext B' C' 1)
    (halpha : alpha.comp (Ext.mk₀ k) (add_zero 1) =
      (Ext.mk₀ qA.hom).comp alpha₀ (zero_add 1))
    (hbeta : beta.comp (Ext.mk₀ qC.hom) (add_zero 1) =
      (Ext.mk₀ k).comp beta₀ (zero_add 1)) :
    (Ext.mk₀ qA.inv).comp
      ((alpha.comp beta (show 1 + 1 = 2 by omega)).comp
        (Ext.mk₀ qC.hom) (add_zero 2)) (zero_add 2) =
      alpha₀.comp beta₀ (show 1 + 1 = 2 by omega) := by
  calc
    _ = (Ext.mk₀ qA.inv).comp
        (alpha.comp (beta.comp (Ext.mk₀ qC.hom) (add_zero 1))
          (show 1 + 1 = 2 by omega)) (zero_add 2) := by
      rw [Ext.comp_assoc_of_third_deg_zero]
    _ = (Ext.mk₀ qA.inv).comp
        (alpha.comp ((Ext.mk₀ k).comp beta₀ (zero_add 1))
          (show 1 + 1 = 2 by omega)) (zero_add 2) := by rw [hbeta]
    _ = (Ext.mk₀ qA.inv).comp
        ((alpha.comp (Ext.mk₀ k) (add_zero 1)).comp beta₀
          (show 1 + 1 = 2 by omega)) (zero_add 2) := by
      rw [Ext.comp_assoc_of_second_deg_zero]
    _ = (Ext.mk₀ qA.inv).comp
        (((Ext.mk₀ qA.hom).comp alpha₀ (zero_add 1)).comp beta₀
          (show 1 + 1 = 2 by omega)) (zero_add 2) := by rw [halpha]
    _ = (Ext.mk₀ qA.inv).comp
        ((Ext.mk₀ qA.hom).comp
          (alpha₀.comp beta₀ (show 1 + 1 = 2 by omega)) (zero_add 2))
        (zero_add 2) := by
      rw [Ext.comp_assoc _ _ _ (zero_add 1)
        (show 1 + 1 = 2 by omega) (by omega)]
    _ = alpha₀.comp beta₀ (show 1 + 1 = 2 by omega) := by
      rw [Ext.mk₀_comp_mk₀_assoc, qA.inv_hom_id, Ext.mk₀_id_comp]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- For compatible generator lifts, the actual Serre extension class becomes
the standard local Serre `Ext¹` class after taking the stalk and transporting
along the canonical comparison of short complexes. -/
theorem schemeModuleStalkModuleExtMap_serreExtensionClass_of_lifts
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X)
    [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from M).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from M) x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive
        (schemeModuleStalkModuleFunctor X x)
    ∀ (f g c : X.presheaf.stalk x)
      (q : ((show X.Modules from M).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk x))
      (hq₁ : q (schemeModuleStalkLinearMap e.projection x e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩)
      (hq₂ : q (schemeModuleStalkLinearMap e.projection x e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩)
      (hrel : (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c)
      (hf : IsRegular f)
      (hg : IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g)),
      let a := serreExtension_stalkComplexComparison_of_quotientEquiv_of_lifts
        e x f g c q e₁ e₂ hq₁ hq₂ hrel hf hg
      (schemeModuleStalkModuleExtMap X x
          (show X.Modules from M)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1
          (@SerreExtensionSequenceData.extensionClass.{u} X M e hExt)).comp
        (Ext.mk₀ a.τ₁) (add_zero 1) =
        (Ext.mk₀ a.τ₃).comp
          (localSerreExtensionModuleComplex_shortExact
            f g c (isRegular_iff_mem_nonZeroDivisors.mp hf)
              (isRegular_iff_mem_nonZeroDivisors.mp hg)).extClass
          (zero_add 1) := by
  dsimp
  intro f g c q e₁ e₂ hq₁ hq₂ hrel hf hg
  let a := serreExtension_stalkComplexComparison_of_quotientEquiv_of_lifts
    e x f g c q e₁ e₂ hq₁ hq₂ hrel hf hg
  exact schemeModuleStalkModuleExtMap_extClass_naturality x
    e.complex e.shortExact (localSerreExtensionModuleComplex f g c)
    (localSerreExtensionModuleComplex_shortExact
      f g c (isRegular_iff_mem_nonZeroDivisors.mp hf)
        (isRegular_iff_mem_nonZeroDivisors.mp hg)) a

/-- Transport a global degree-two Ext class to the local Ext group supplied
directly by the stalk functor, identifying both endpoint modules. -/
noncomputable def schemeModuleExtLocalClassLarge
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (z : CategoryTheory.Abelian.Ext.{u} M N 2) :
    CategoryTheory.Abelian.Ext.{u + 1}
      (ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
      (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) 2 :=
  (Ext.mk₀ qM.inv).comp
    ((schemeModuleStalkModuleExtMap X x M N 2 z).comp
      (Ext.mk₀ qN.hom) (add_zero 2))
    (zero_add 2)

/-- Transport a global degree-two Ext class to the small-universe local Ext
group after taking its stalk and identifying the two endpoint modules. -/
noncomputable def schemeModuleExtLocalClass
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (z : CategoryTheory.Abelian.Ext.{u} M N 2) :
    CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
      (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) 2 :=
  extChgUnivAddEquiv (schemeModuleExtLocalClassLarge x M N f g qM qN z)

/-- The residue component formed directly in the stalk functor's Ext
universe.  Keeping this universe avoids any universe-change bookkeeping in
the concrete Yoneda-product comparison. -/
noncomputable def schemeModuleExtLocalResidueComponentLarge
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    CategoryTheory.Abelian.Ext.{u} M N 2 →+
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) where
  toFun z :=
    localExtTwoResidueCoordinate.{u, u + 1} f g hf hg hfm hgm
      (schemeModuleExtLocalClassLarge x M N f g qM qN z)
  map_zero' := by simp [schemeModuleExtLocalClassLarge]
  map_add' := by intro z z'; simp [schemeModuleExtLocalClassLarge]

/-- Precomposing a global degree-two class by an endomorphism which, after
localization and identification of the source, is multiplication by `a`
precomposes the transported local class by the same scalar. -/
theorem schemeModuleExtLocalClassLarge_precomp_of_conjugate_eq_smul
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (phi : M ⟶ M) (a : X.presheaf.stalk x)
    (hphi : qM.inv ≫ (schemeModuleStalkModuleFunctor X x).map phi ≫ qM.hom =
      a • 𝟙 _) (z : Ext.{u} M N 2) :
    schemeModuleExtLocalClassLarge x M N f g qM qN
        ((Ext.mk₀ phi).comp z (zero_add 2)) =
      (Ext.mk₀ (a • 𝟙 _)).comp
        (schemeModuleExtLocalClassLarge x M N f g qM qN z) (zero_add 2) := by
  have hphi' : qM.inv ≫ (schemeModuleStalkModuleFunctor X x).map phi =
      (a • 𝟙 _) ≫ qM.inv := by
    apply (cancel_mono qM.hom).1
    simpa [Category.assoc] using hphi
  unfold schemeModuleExtLocalClassLarge
  rw [schemeModuleStalkModuleExtMap_comp]
  simp only [schemeModuleStalkModuleExtMap, Functor.mapExtAddHom_apply,
    Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.mk₀_comp_mk₀_assoc]
  rw [hphi']
  rw [← Ext.mk₀_comp_mk₀_assoc]

/-- Under the same localized scalar hypothesis, the complete-intersection
residue coordinate scales by `a`. -/
theorem schemeModuleExtLocalResidueComponentLarge_precomp_of_conjugate_eq_smul
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (phi : M ⟶ M) (a : X.presheaf.stalk x)
    (hphi : qM.inv ≫ (schemeModuleStalkModuleFunctor X x).map phi ≫ qM.hom =
      a • 𝟙 _) (z : Ext.{u} M N 2) :
    schemeModuleExtLocalResidueComponentLarge x M N f g hf hg hfm hgm qM qN
        ((Ext.mk₀ phi).comp z (zero_add 2)) =
      a • schemeModuleExtLocalResidueComponentLarge x M N f g hf hg hfm hgm qM qN z := by
  change localExtTwoResidueCoordinate.{u, u + 1} f g hf hg hfm hgm
      (schemeModuleExtLocalClassLarge x M N f g qM qN
        ((Ext.mk₀ phi).comp z (zero_add 2))) =
    a • localExtTwoResidueCoordinate.{u, u + 1} f g hf hg hfm hgm
      (schemeModuleExtLocalClassLarge x M N f g qM qN z)
  rw [schemeModuleExtLocalClassLarge_precomp_of_conjugate_eq_smul
    x M N f g qM qN phi a hphi z]
  exact localExtTwoResidueCoordinate_precomp_smul_id f g hf hg hfm hgm a _

/-- The large-universe residue component evaluates on the standard local
Serre two-extension as its coefficient modulo the maximal ideal. -/
theorem schemeModuleExtLocalResidueComponentLarge_eq_serre_coordinate
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g c : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (z : CategoryTheory.Abelian.Ext.{u} M N 2)
    (hz : schemeModuleExtLocalClassLarge x M N f g qM qN z =
      localSerreExtTwoClass.{u, u + 1} f g c hf hg) :
    schemeModuleExtLocalResidueComponentLarge x M N f g hf hg hfm hgm qM qN z =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) c := by
  change localExtTwoResidueCoordinate.{u, u + 1} f g hf hg hfm hgm _ = _
  rw [hz]
  exact localExtTwoResidueCoordinate_localSerreExtTwoClass.{u, u + 1}
    f g c hf hg hfm hgm

/-- A global degree-two Ext class has a canonical residue component once the
source stalk is identified with `R/(f,g)` and the target stalk with `R`.
The construction is the actual stalk map on Ext followed by transport of
both endpoints and the complete-intersection residue coordinate. -/
noncomputable def schemeModuleExtLocalResidueComponent
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    CategoryTheory.Abelian.Ext.{u} M N 2 →+
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) where
  toFun z :=
    localExtTwoResidueCoordinate.{u, u} f g hf hg hfm hgm
      (schemeModuleExtLocalClass x M N f g qM qN z)
  map_zero' := by
    simp [schemeModuleExtLocalClass, schemeModuleExtLocalClassLarge]
  map_add' := by
    intro z w
    simp [schemeModuleExtLocalClass, schemeModuleExtLocalClassLarge]

/-- Evaluating the preceding global component reduces to the local
coefficient calculation as soon as the transported stalk class has been
identified with the standard local Serre two-extension. -/
theorem schemeModuleExtLocalResidueComponent_eq_serre_coordinate
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g c : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (z : CategoryTheory.Abelian.Ext.{u} M N 2)
    (hz : schemeModuleExtLocalClass x M N f g qM qN z =
      (show CategoryTheory.Abelian.Ext.{u}
          (ModuleCat.of (X.presheaf.stalk x)
            ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
          (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) 2 from
        localSerreExtTwoClass.{u, u} f g c hf hg)) :
    schemeModuleExtLocalResidueComponent x M N f g hf hg hfm hgm qM qN z =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) c := by
  change localExtTwoResidueCoordinate.{u, u} f g hf hg hfm hgm _ = _
  rw [hz]
  exact localExtTwoResidueCoordinate_localSerreExtTwoClass.{u, u}
    f g c hf hg hfm hgm

/-- A scheme-module isomorphism induces a literal linear equivalence on every
stalk.  Injectivity comes from the mono instance, and surjectivity from the
stalk-surjectivity theorem for epimorphisms. -/
noncomputable def schemeModuleStalkLinearEquivOfIso
    {M N : X.Modules} (e : M ≅ N) (x : X) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
      schemeModuleStalkModule N x
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x := by
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) := schemeModuleStalkModule N x
  apply LinearEquiv.ofBijective (schemeModuleStalkLinearMap e.hom x)
  constructor
  · exact schemeModuleStalkLinearMap_injective_of_mono e.hom x
  · have hepi : Epi e.hom := by infer_instance
    exact @schemeModule_epi_stalkMap_surjective X M N e.hom hepi x

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Stalk equivalences induced by isomorphisms respect a commuting square. -/
theorem schemeModuleStalkLinearEquivOfIso_naturality
    {X : Scheme.{u}} {M N M' N' : X.Modules}
    (eM : M ≅ M') (eN : N ≅ N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : f ≫ eN.hom = eM.hom ≫ g) (x : X) (y : M.presheaf.stalk x) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
      schemeModuleStalkModule N x
    letI : Module (X.presheaf.stalk x) (M'.presheaf.stalk x) :=
      schemeModuleStalkModule M' x
    letI : Module (X.presheaf.stalk x) (N'.presheaf.stalk x) :=
      schemeModuleStalkModule N' x
    schemeModuleStalkLinearEquivOfIso eN x
        (schemeModuleStalkLinearMap f x y) =
      schemeModuleStalkLinearMap g x
        (schemeModuleStalkLinearEquivOfIso eM x y) := by
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
    schemeModuleStalkModule N x
  letI : Module (X.presheaf.stalk x) (M'.presheaf.stalk x) :=
    schemeModuleStalkModule M' x
  letI : Module (X.presheaf.stalk x) (N'.presheaf.stalk x) :=
    schemeModuleStalkModule N' x
  change ((schemeModuleStalkModuleFunctor X x).map f ≫
      (schemeModuleStalkModuleFunctor X x).map eN.hom) y =
    ((schemeModuleStalkModuleFunctor X x).map eM.hom ≫
      (schemeModuleStalkModuleFunctor X x).map g) y
  rw [← (schemeModuleStalkModuleFunctor X x).map_comp,
    h, (schemeModuleStalkModuleFunctor X x).map_comp]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Trivializing a right tensor factor commutes on stalks with every
morphism in the untwisted variable. -/
theorem schemeModuleStalkLinearEquiv_tensorRightIsoUnit_naturality
    {X : Scheme.{u}} {T : X.Modules}
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    {M N : X.Modules} (f : M ⟶ N) (x : X)
    (y : (schemeModuleTensor M T).presheaf.stalk x) :
    letI : Module (X.presheaf.stalk x)
        ((schemeModuleTensor M T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((schemeModuleTensor N T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
      schemeModuleStalkModule N x
    schemeModuleStalkLinearEquivOfIso
        ((schemeModuleTensorRightIsoUnit eT).app N) x
        (schemeModuleStalkLinearMap
          ((schemeModuleTensorRight T).map f) x y) =
      schemeModuleStalkLinearMap f x
        (schemeModuleStalkLinearEquivOfIso
          ((schemeModuleTensorRightIsoUnit eT).app M) x y) := by
  letI : Module (X.presheaf.stalk x)
      ((schemeModuleTensor M T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((schemeModuleTensor N T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
    schemeModuleStalkModule N x
  exact schemeModuleStalkLinearEquivOfIso_naturality
    ((schemeModuleTensorRightIsoUnit eT).app M)
    ((schemeModuleTensorRightIsoUnit eT).app N)
    ((schemeModuleTensorRight T).map f) f
    ((schemeModuleTensorRightIsoUnit eT).hom.naturality f) x y

/-- A globally trivial twist transports the untwisted two-generator quotient
identification to the twisted ideal stalk. -/
noncomputable def closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (closedImmersionIdealTwist i T)).presheaf.stalk x) :=
      schemeModuleStalkModule (closedImmersionIdealTwist i T) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      ((show X.Modules from (closedImmersionIdealTwist i T)).presheaf.stalk x) ≃ₗ[
        X.presheaf.stalk x] Ideal.span ({f, g} : Set (X.presheaf.stalk x)) := by
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
    schemeModuleStalkModule (closedImmersionIdealTwist i T) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel
  let twistIso := (schemeModuleTensorRightIsoUnit eT).app
    (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
  let q0 := closedImmersionModuleStalkLinearEquivOfQuotientKernelEq i x f g hkernel
  exact (schemeModuleStalkLinearEquivOfIso twistIso x).trans q0

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk of the untwisted closed-immersion ideal sequence is the
standard local ideal-quotient sequence once the local defining ideal is
identified with `(f,g)`.  All three comparison maps are the canonical ones:
the actual ideal embeds as `(f,g)`, the structure-sheaf stalk is the local
ring, and the pushforward stalk is the quotient by `(f,g)`. -/
noncomputable def closedImmersionModule_stalkComplexComparison_of_kernelEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).map
          (schemeModuleStalkModuleFunctor X x) ⟶
        localSerreIdealQuotientComplex f g := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  intro f g hkernel
  unfold IdealSheafDataModule.closedImmersionModulePushforwardSequence
  let qI := closedImmersionModuleStalkLinearEquivOfQuotientKernelEq
    i x f g hkernel
  let qQ := closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq
    i x f g hkernel
  refine ShortComplex.homMk
    (ModuleCat.ofHom qI.toLinearMap)
    (schemeModuleUnitStalkIso X x).hom
    (ModuleCat.ofHom qQ.symm.toLinearMap) ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change ((qI y : Ideal.span ({f, g} : Set (X.presheaf.stalk x))) :
        X.presheaf.stalk x) =
      (presheafOfModules_unitStalkLinearEquiv X.presheaf x).symm
        (schemeModuleStalkLinearMap
          (IdealSheafDataModule.closedImmersionModuleToUnit i) x y)
    rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
    change Ideal.Quotient.mk (Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
        (u.symm y) =
      qQ.symm (schemeModuleStalkLinearMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x y)
    have hq := congrArg (fun z ↦ qQ.symm z)
      (show closedImmersionPushforwardStalkFromRingLinearMap i x (u.symm y) =
        schemeModuleStalkLinearMap
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x y by
        dsimp [closedImmersionPushforwardStalkFromRingLinearMap]
        rw [u.apply_symm_apply]
        rfl)
    rw [← hq]
    apply qQ.injective
    rw [LinearEquiv.apply_symm_apply]
    rfl

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Under the preceding comparison, the stalk of the actual untwisted
closed-immersion extension class is the standard local ideal-quotient
`Ext¹` class. -/
theorem schemeModuleStalkModuleExtMap_closedImmersionClass_of_kernelEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : X)
    [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      let a := closedImmersionModule_stalkComplexComparison_of_kernelEq
        i x f g hkernel
      (schemeModuleStalkModuleExtMap X x
          (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).X₃
          (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).X₁ 1
          (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i).extClass).comp
        (Ext.mk₀ a.τ₁) (add_zero 1) =
      (Ext.mk₀ a.τ₃).comp
        (localSerreIdealQuotientComplex_shortExact f g).extClass
        (zero_add 1) := by
  dsimp
  intro f g hkernel
  let a := closedImmersionModule_stalkComplexComparison_of_kernelEq
    i x f g hkernel
  exact schemeModuleStalkModuleExtMap_extClass_naturality x
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence i)
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i)
    (localSerreIdealQuotientComplex f g)
    (localSerreIdealQuotientComplex_shortExact f g) a

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Trivializing the twisting module transports the stalk of the twisted
closed-immersion sequence to the untwisted stalk sequence and hence to the
standard local ideal-quotient complex. -/
noncomputable def
    closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} [PreservesFiniteLimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      (closedImmersionIdealTwistSequence i T).map
          (schemeModuleStalkModuleFunctor X x) ⟶
        localSerreIdealQuotientComplex f g := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  intro f g hkernel
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  let b := (schemeModuleStalkModuleFunctor X x).mapShortComplex.map
    (S.mapNatTrans (schemeModuleTensorRightIsoUnit eT).hom)
  let a := closedImmersionModule_stalkComplexComparison_of_kernelEq
    i x f g hkernel
  exact b ≫ a

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The right endpoint of the preceding comparison, recorded as a linear
equivalence from the twisted pushforward stalk to `R/(f,g)`. -/
noncomputable def
    closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      ((show X.Modules from schemeModuleTensor
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) ≃ₗ[
          X.presheaf.stalk x]
        (X.presheaf.stalk x ⧸
          Ideal.span ({f, g} : Set (X.presheaf.stalk x))) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from schemeModuleTensor
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  intro f g hkernel
  let twistIso := (schemeModuleTensorRightIsoUnit eT).app
    (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf))
  exact (schemeModuleStalkLinearEquivOfIso twistIso x).trans
    (closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq
      i x f g hkernel).symm

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem
    closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq_τ₁
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} [PreservesFiniteLimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      (closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq
        i eT x f g hkernel).τ₁ =
      ModuleCat.ofHom
        (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel).toLinearMap := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  intro f g hkernel
  rfl

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem
    closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq_τ₃
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} [PreservesFiniteLimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      (closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq
        i eT x f g hkernel).τ₃ =
      ModuleCat.ofHom
        (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel).toLinearMap := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from schemeModuleTensor
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  intro f g hkernel
  rfl

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk of the actual twisted ideal-quotient extension class is the
standard local ideal-quotient `Ext¹` class after trivializing the twist and
using the two local equations. -/
theorem schemeModuleStalkModuleExtMap_closedImmersionIdealTwistClass_of_isoUnit_of_kernelEq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules}
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) (x : X)
    [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      let a :=
        closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq
          i eT x f g hkernel
      (schemeModuleStalkModuleExtMap X x
          (closedImmersionIdealTwistSequence i T).X₃
          (closedImmersionIdealTwistSequence i T).X₁ 1
          (closedImmersionIdealTwistSequence_shortExact i T).extClass).comp
        (Ext.mk₀ a.τ₁) (add_zero 1) =
      (Ext.mk₀ a.τ₃).comp
        (localSerreIdealQuotientComplex_shortExact f g).extClass
        (zero_add 1) := by
  dsimp
  intro f g hkernel
  let a :=
    closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq
      i eT x f g hkernel
  exact schemeModuleStalkModuleExtMap_extClass_naturality x
    (closedImmersionIdealTwistSequence i T)
    (closedImmersionIdealTwistSequence_shortExact i T)
    (localSerreIdealQuotientComplex f g)
    (localSerreIdealQuotientComplex_shortExact f g) a

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleExtLocalClassLarge_serreYonedaProduct_of_isoUnit_of_kernelEq_of_lifts
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules}
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    (x : X) [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) := schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g c : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f,g} : Set (X.presheaf.stalk x)))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk x))
      (hq₁ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩)
      (hq₂ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩)
      (hrel : (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c)
      (hf : IsRegular f)
      (hg : IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g)),
      let qM := LinearEquiv.toModuleIso
        (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
      let qN := schemeModuleUnitStalkIso X x
      schemeModuleExtLocalClassLarge x
        (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
        f g qM qN
        ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          (@SerreExtensionSequenceData.extensionClass.{u} X
            (closedImmersionIdealTwist i T) e hExt)
          (show 1 + 1 = 2 by omega)) =
      localSerreExtTwoClass.{u,u+1} f g c
        (isRegular_iff_mem_nonZeroDivisors.mp hf)
        (isRegular_iff_mem_nonZeroDivisors.mp hg) := by
  dsimp
  intro f g c hkernel e₁ e₂ hq₁ hq₂ hrel hf hg
  let qI := closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
    i eT x f g hkernel
  let a := closedImmersionIdealTwist_stalkComplexComparison_of_isoUnit_of_kernelEq
    i eT x f g hkernel
  let b := serreExtension_stalkComplexComparison_of_quotientEquiv_of_lifts
    e x f g c qI e₁ e₂ hq₁ hq₂ hrel hf hg
  let qM := LinearEquiv.toModuleIso
    (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
      i eT x f g hkernel)
  let qN := schemeModuleUnitStalkIso X x
  let alpha := schemeModuleStalkModuleExtMap X x
    (closedImmersionIdealTwistSequence i T).X₃
    (closedImmersionIdealTwistSequence i T).X₁ 1
    (closedImmersionIdealTwistSequence_shortExact i T).extClass
  let beta := schemeModuleStalkModuleExtMap X x
    e.complex.X₃ e.complex.X₁ 1
    (@SerreExtensionSequenceData.extensionClass.{u} X
      (closedImmersionIdealTwist i T) e hExt)
  let alpha₀ := (localSerreIdealQuotientComplex_shortExact f g).extClass
  let beta₀ := (localSerreExtensionModuleComplex_shortExact f g c
    (isRegular_iff_mem_nonZeroDivisors.mp hf)
    (isRegular_iff_mem_nonZeroDivisors.mp hg)).extClass
  have halpha : alpha.comp (Ext.mk₀ a.τ₁) (add_zero 1) =
      (Ext.mk₀ a.τ₃).comp alpha₀ (zero_add 1) := by
    exact schemeModuleStalkModuleExtMap_closedImmersionIdealTwistClass_of_isoUnit_of_kernelEq
      i eT x f g hkernel
  have hbeta : beta.comp (Ext.mk₀ b.τ₁) (add_zero 1) =
      (Ext.mk₀ b.τ₃).comp beta₀ (zero_add 1) := by
    exact schemeModuleStalkModuleExtMap_serreExtensionClass_of_lifts
      e x f g c qI e₁ e₂ hq₁ hq₂ hrel hf hg
  have hmid : a.τ₁ = b.τ₃ := by rfl
  have hqM : qM.hom = a.τ₃ := by rfl
  have hqN : qN.hom = b.τ₁ := by rfl
  change (Ext.mk₀ qM.inv).comp
    ((schemeModuleStalkModuleExtMap X x _ _ 2
      ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} X
          (closedImmersionIdealTwist i T) e hExt)
        (show 1 + 1 = 2 by omega))).comp
      (Ext.mk₀ qN.hom) (add_zero 2)) (zero_add 2) = _
  rw [schemeModuleStalkModuleExtMap_comp]
  rw [← hqM] at halpha
  rw [← hqN, ← hmid] at hbeta
  change (Ext.mk₀ qM.inv).comp
    ((alpha.comp beta (show 1 + 1 = 2 by omega)).comp
      (Ext.mk₀ qN.hom) (add_zero 2)) (zero_add 2) =
    alpha₀.comp beta₀ (show 1 + 1 = 2 by omega)
  exact ext_comp_transport_of_common_middle
    qM qN a.τ₁ alpha beta alpha₀ beta₀ halpha hbeta

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual global Yoneda product has local residue coordinate `c` at a
point where the twist is trivialized and the closed immersion is cut out by
the regular pair `(f,g)`.  This discharges the local coordinate calculation
in Voisin's argument from concrete stalk data. -/
theorem schemeModuleExtLocalResidueComponentLarge_serreYonedaProduct_eq_coordinate
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules}
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    (x : X) [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) := schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g c : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk x))
      (hq₁ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩)
      (hq₂ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩)
      (hrel : (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c)
      (hf : IsRegular f)
      (hg : IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g))
      (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)),
      let hf' := isRegular_iff_mem_nonZeroDivisors.mp hf
      let hg' := isRegular_iff_mem_nonZeroDivisors.mp hg
      let qM := LinearEquiv.toModuleIso
        (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
      let qN := schemeModuleUnitStalkIso X x
      schemeModuleExtLocalResidueComponentLarge x
        (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
        f g hf' hg' hfm hgm qM qN
        ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          (@SerreExtensionSequenceData.extensionClass.{u} X
            (closedImmersionIdealTwist i T) e hExt)
          (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) c := by
  dsimp
  intro f g c hkernel e₁ e₂ hq₁ hq₂ hrel hf hg hfm hgm
  let qM := LinearEquiv.toModuleIso
    (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
      i eT x f g hkernel)
  let qN := schemeModuleUnitStalkIso X x
  apply schemeModuleExtLocalResidueComponentLarge_eq_serre_coordinate
    x (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    f g c
      (isRegular_iff_mem_nonZeroDivisors.mp hf)
      (isRegular_iff_mem_nonZeroDivisors.mp hg)
    hfm hgm qM qN
  exact
    schemeModuleExtLocalClassLarge_serreYonedaProduct_of_isoUnit_of_kernelEq_of_lifts
      i eT e x f g c hkernel e₁ e₂ hq₁ hq₂ hrel hf hg

set_option linter.style.haveILetI false in
/-- The canonical residue component of the global degree-two Ext group at a
two-generator lci point.  This packages the actual stalk functor, the local
trivialization of the twist, the quotient-stalk identification, and the
complete-intersection residue coordinate into the component used in Voisin's
global-to-local argument. -/
noncomputable def serreYonedaResidueComponent
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} [PreservesFiniteLimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    ∀
    (f g : X.presheaf.stalk x)
    (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)),
    CategoryTheory.Abelian.Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+
      (X.presheaf.stalk x ⧸
        IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  dsimp
  intro f g hkernel hf hg hfm hgm
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from schemeModuleTensor
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  exact
  schemeModuleExtLocalResidueComponentLarge x
    (closedImmersionIdealTwistSequence i T).X₃
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    f g hf hg hfm hgm
    (LinearEquiv.toModuleIso
      (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
        i eT x f g hkernel))
    (schemeModuleUnitStalkIso X x)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical residue component sends the actual Yoneda product defining
the Serre obstruction to its local coefficient modulo the maximal ideal. -/
theorem serreYonedaResidueComponent_serreYonedaProduct_eq_coordinate
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules}
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    (x : X) [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) := schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g c : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk x))
      (hq₁ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩)
      (hq₂ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT x f g hkernel)
          (schemeModuleStalkLinearMap e.projection x e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩)
      (hrel : (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c)
      (hf : IsRegular f)
      (hg : IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g))
      (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)),
      serreYonedaResidueComponent i eT x f g hkernel
        (isRegular_iff_mem_nonZeroDivisors.mp hf)
        (isRegular_iff_mem_nonZeroDivisors.mp hg) hfm hgm
        ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          (@SerreExtensionSequenceData.extensionClass.{u} X
            (closedImmersionIdealTwist i T) e hExt)
          (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) c := by
  dsimp [serreYonedaResidueComponent]
  intro f g c hkernel e₁ e₂ hq₁ hq₂ hrel hf hg hfm hgm
  exact
    schemeModuleExtLocalResidueComponentLarge_serreYonedaProduct_eq_coordinate
      i eT e x f g c hkernel e₁ e₂ hq₁ hq₂ hrel hf hg hfm hgm

/-- In particular, the projection in any actual Serre extension is surjective
on every literal stalk, since the sequence data carries an epimorphism. -/
theorem serreExtension_projection_stalkMap_surjective
    {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    Function.Surjective (schemeModuleStalkLinearMap e.projection x) := by
  have hepi : Epi e.projection := e.shortExact.epi_g
  letI : Epi e.projection := hepi
  exact @schemeModule_epi_stalkMap_surjective X _ _ e.projection hepi x

set_option linter.style.haveILetI false in
/-- Once the quotient stalk is identified with a two-generator ideal, the
literal stalk-surjectivity theorem supplies lifts of both generators.  Exactness
then forces their Koszul combination to be the canonical section for some local
scalar `c`; this packages the compatible-lift relation needed by the local
Serre presentation. -/
theorem serreExtension_stalk_exists_generator_lifts_with_relation
    {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from M).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from M) x
    ∀ (f g : X.presheaf.stalk x)
      (q : ((show X.Modules from M).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      ∃ e₁ e₂ c,
        q (schemeModuleStalkLinearMap e.projection x e₁) =
          ⟨f, Ideal.subset_span (by simp)⟩ ∧
        q (schemeModuleStalkLinearMap e.projection x e₂) =
          ⟨g, Ideal.subset_span (by simp)⟩ ∧
        (-g) • e₁ + f • e₂ = serreExtensionStalkCanonicalSection e x c := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from M).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from M) x
  intro f g q
  have hepi : Epi e.projection := e.shortExact.epi_g
  letI : Epi e.projection := hepi
  have hsurj := @schemeModule_epi_stalkMap_surjective X _ _ e.projection hepi x
  obtain ⟨e₁, he₁⟩ := hsurj
    (q.symm ⟨f, Ideal.subset_span (by simp)⟩)
  obtain ⟨e₂, he₂⟩ := hsurj
    (q.symm ⟨g, Ideal.subset_span (by simp)⟩)
  let p := schemeModuleStalkLinearMap e.projection x
  let i' := serreExtensionStalkCanonicalSection e x
  have hpy : p ((-g) • e₁ + f • e₂) = 0 := by
    apply q.injective
    rw [map_zero q, map_add, map_smul, map_smul, he₁, he₂]
    ext
    simp [mul_comm]
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let i := schemeModuleStalkLinearMap e.inclusion x
  have hraw := serreExtension_stalk_linear_exact e x
  have hpre : Function.Exact (i ∘ u) p := by
    exact functionExact_precomp_of_surjective i u p hraw u.surjective
  obtain ⟨c, hc⟩ := (hpre _).mp hpy
  have hq₁ : q (p e₁) = ⟨f, Ideal.subset_span (by simp)⟩ := by
    rw [he₁, q.apply_symm_apply]
  have hq₂ : q (p e₂) = ⟨g, Ideal.subset_span (by simp)⟩ := by
    rw [he₂, q.apply_symm_apply]
  refine ⟨e₁, e₂, c, hq₁, hq₂, ?_⟩
  have hcanon : serreExtensionStalkCanonicalSection e x c =
      (i (u c)) := by
    dsimp [serreExtensionStalkCanonicalSection, i, u]
    rfl
  exact hcanon ▸ hc.symm

set_option linter.style.haveILetI false in
/-- The local presentation follows once the quotient stalk is identified and
its two displayed germs are regular.  Exactness and stalk-surjectivity supply
the lifts and the canonical-section parameter automatically. -/
theorem serreExtension_stalkPresentation_nonempty_of_quotientEquiv_of_regular_generators
    {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from M).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from M) x
    ∀ (f g : X.presheaf.stalk x)
      (q : ((show X.Modules from M).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      IsRegular f → IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      ∃ c, Nonempty (((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        localSerreExtensionPresentation f g c) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from M).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from M) x
  intro f g q hf hg
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let i := schemeModuleStalkLinearMap e.inclusion x
  let i' := serreExtensionStalkCanonicalSection e x
  let p₀ := schemeModuleStalkLinearMap e.projection x
  let p := q.toLinearMap.comp p₀
  apply exists_localSerreExtensionPresentationEquiv_of_exact_of_surjective i' f g p
  · have hraw := serreExtension_stalk_linear_exact e x
    have hpre : Function.Exact (i ∘ u) p₀ :=
      functionExact_precomp_of_surjective i u p₀ hraw u.surjective
    exact hpre.comp_injective q q.injective (map_zero q)
  · exact serreExtensionStalkCanonicalSection_injective e x
  · have hepi : Epi e.projection := e.shortExact.epi_g
    letI : Epi e.projection := hepi
    exact q.surjective.comp
      (@schemeModule_epi_stalkMap_surjective X _ _ e.projection hepi x)
  · exact isRegular_iff_mem_nonZeroDivisors.mp hf
  · exact isRegular_iff_mem_nonZeroDivisors.mp hg

set_option linter.style.haveILetI false in
/-- At a locally free lci stalk, the literal canonical section of an actual
Serre extension has free coordinates whose ideal is the displayed quotient
ideal.  This is the stalk-level zero-locus conclusion of Voisin's Lemma 3.1:
exactness supplies the local presentation automatically. -/
theorem serreExtension_stalk_exists_freeCoordinates_of_quotientEquiv_at_lci_point
    {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from M).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from M) x
    ∀ (f g : X.presheaf.stalk x)
      (q : ((show X.Modules from M).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))),
      f ∈ (X.presheaf.stalk x)⁰ →
      Ideal.Quotient.mk (Ideal.span {f}) g ∈
        ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰ →
      f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
      g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
      Module.Free (X.presheaf.stalk x) ((show X.Modules from e.E).presheaf.stalk x) →
      ∃ t : ((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
          (X.presheaf.stalk x) × (X.presheaf.stalk x),
        Ideal.span ({(t (serreExtensionStalkCanonicalSection e x 1)).1,
          (t (serreExtensionStalkCanonicalSection e x 1)).2} : Set (X.presheaf.stalk x)) =
          Ideal.span ({f, g} : Set (X.presheaf.stalk x)) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from M).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from M) x
  intro f g q hf hg hfm hgm hfree
  letI : Module.Free (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) := hfree
  let u := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let i := schemeModuleStalkLinearMap e.inclusion x
  let i' := serreExtensionStalkCanonicalSection e x
  let p₀ := schemeModuleStalkLinearMap e.projection x
  let p := q.toLinearMap.comp p₀
  apply exists_freeCoordinates_of_exact_of_surjective_of_free_at_lci_point i' f g p
  · have hraw := serreExtension_stalk_linear_exact e x
    have hpre : Function.Exact (i ∘ u) p₀ :=
      functionExact_precomp_of_surjective i u p₀ hraw u.surjective
    exact hpre.comp_injective q q.injective (map_zero q)
  · exact serreExtensionStalkCanonicalSection_injective e x
  · have hepi : Epi e.projection := e.shortExact.epi_g
    letI : Epi e.projection := hepi
    exact q.surjective.comp
      (@schemeModule_epi_stalkMap_surjective X _ _ e.projection hepi x)
  · exact hf
  · exact hg
  · exact hfm
  · exact hgm

set_option linter.style.haveILetI false in
/-- Closed-immersion version of the preceding presentation theorem.  The
literal quotient/kernel equivalence is supplied by the two-generator kernel
calculation, while all lift and relation obligations are discharged by stalk
surjectivity and exactness.  The actual local Serre presentation is nonempty
under the explicit closed-immersion kernel equality and regularity hypotheses. -/
theorem serreExtension_stalkPresentation_nonempty_of_closedImmersionQuotientKernelEq_of_regular_generators
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (e : SerreExtensionSequenceData X
      (show X.Modules from IdealSheafDataModule.closedImmersionModule i)) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      IsRegular f → IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      ∃ c, Nonempty (((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        localSerreExtensionPresentation f g c) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel hf hg
  let q := closedImmersionModuleStalkLinearEquivOfQuotientKernelEq i x f g hkernel
  exact serreExtension_stalkPresentation_nonempty_of_quotientEquiv_of_regular_generators
    e x f g q hf hg

set_option linter.style.haveILetI false in
/-- If the twist is globally trivial, the closed-immersion kernel calculation
alone supplies the quotient equivalence needed for the local Serre
presentation. -/
theorem serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_regular_generators
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T)) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      IsRegular f → IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      ∃ c, Nonempty (((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        localSerreExtensionPresentation f g c) := by
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) := schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  intro f g hkernel hf hg
  let q := closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit i eT x f g hkernel
  exact serreExtension_stalkPresentation_nonempty_of_quotientEquiv_of_regular_generators
    e x f g q hf hg

set_option linter.style.haveILetI false in
/- The Jacobian form of the local input is often stated as independence in
   the cotangent space, rather than as two separate non-zero-divisor
   assertions.  In a regular local stalk, the checked local algebra in
   `RegularPairDimension` converts that cotangent condition into the two
   regularity hypotheses consumed by the presentation theorem above. -/
theorem serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_cotangentIndependent_generators
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T)) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      IsRegularLocalRing (X.presheaf.stalk x) →
      f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
      f ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 →
      g ∉ Ideal.span ({f} : Set (X.presheaf.stalk x)) ⊔
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 →
      ∃ c, Nonempty (((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[
        X.presheaf.stalk x] localSerreExtensionPresentation f g c) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel hregular hfmax hfsquare hglinear
  letI : IsRegularLocalRing (X.presheaf.stalk x) := hregular
  obtain ⟨hf, hg⟩ :=
    AllCharacteristics.local_nonZeroDivisors_of_cotangentIndependentParameters
      f g hfmax hfsquare hglinear
  exact serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_regular_generators
    i eT e x f g hkernel
    (isRegular_iff_mem_nonZeroDivisors.mpr hf)
    (isRegular_iff_mem_nonZeroDivisors.mpr hg)

set_option linter.style.haveILetI false in
/- The direct Jacobian form of the preceding presentation theorem.  This
   keeps the natural residue-field cotangent certificate at the actual stalk
   boundary and performs the ideal-theoretic conversion internally. -/
theorem serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_linearIndependent_cotangent_classes
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T)) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from
        (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      IsRegularLocalRing (X.presheaf.stalk x) →
      ∀ (hfmax : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)),
        ∀ (hgmax : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)),
          LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk x))
            ![(IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent
                ⟨f, hfmax⟩,
             (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent
                ⟨g, hgmax⟩] →
      ∃ c, Nonempty (((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[
        X.presheaf.stalk x] localSerreExtensionPresentation f g c) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel hregular hfmax hgmax hli
  letI : IsRegularLocalRing (X.presheaf.stalk x) := hregular
  obtain ⟨hfsquare, hglinear⟩ :=
    AllCharacteristics.cotangentIndependentParameters_of_linearIndependent_cotangent_classes
      f g hfmax hgmax hli
  exact serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_cotangentIndependent_generators
    i eT e x f g hkernel hregular hfmax hfsquare hglinear

set_option linter.style.haveILetI false in
/- The preceding presentation theorem can be fed directly into the local
Galois calculation.  A nonfree actual stalk supplies the residue-coordinate
vanishing, while the same witness retains the standard presentation needed
to compare the actual module with the local Serre model. -/
theorem serreExtension_stalk_coordinate_eq_zero_mod_maximalIdeal_of_closedImmersionIdealTwist_isoUnit_of_not_free
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T)) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      IsRegular f → IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      ¬ Module.Free (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) →
      ∃ c, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) c = 0 ∧
        Nonempty (((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
          localSerreExtensionPresentation f g c) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel hf hg hfree
  obtain ⟨c, ⟨hpresentation⟩⟩ :=
    serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_regular_generators
      i eT e x f g hkernel hf hg
  refine ⟨c, ?_, ⟨hpresentation⟩⟩
  exact localSerreExtension_coordinate_eq_zero_mod_maximalIdeal_of_not_free_of_linearEquiv
    f g c hpresentation hfree

set_option linter.style.haveILetI false in
/-- The same local calculation packages the coordinate as a nonunit together
with its presentation.  This is the existential form used when local
coordinates are chosen independently at the points of a Galois orbit. -/
theorem serreExtension_stalk_exists_nonunit_coordinate_and_presentation_of_closedImmersionIdealTwist_isoUnit_of_not_free
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T)) (x : X) :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from e.E) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x),
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x)) →
      IsRegular f → IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g) →
      ¬ Module.Free (X.presheaf.stalk x)
        ((show X.Modules from e.E).presheaf.stalk x) →
      ∃ c, ¬ IsUnit c ∧ Nonempty
        (((show X.Modules from e.E).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
          localSerreExtensionPresentation f g c) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from e.E) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from closedImmersionIdealTwist i T) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  intro f g hkernel hf hg hfree
  obtain ⟨c, hc, hpresentation⟩ :=
    serreExtension_stalk_coordinate_eq_zero_mod_maximalIdeal_of_closedImmersionIdealTwist_isoUnit_of_not_free
      i eT e x f g hkernel hf hg hfree
  refine ⟨c, ?_, hpresentation⟩
  intro hunit
  have hnotmem : c ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.notMem_maximalIdeal.mpr hunit
  exact hnotmem (Ideal.Quotient.eq_zero_iff_mem.mp hc)


namespace BundleSectionZeroLocus

set_option linter.style.haveILetI false in
/-- The rank-two local zero-locus calculation supplies the coordinate-normalized
Serre presentation at every nonfree stalk satisfying the regularity hypotheses. -/
theorem localSectionZeroSubschemeOfOver_stalk_coordinate_eq_zero_mod_maximalIdeal_of_not_free
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (x : (U : Scheme.{u})) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk x)
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E) x
    let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0))
    let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 1))
    IsRegular F → IsRegular (Ideal.Quotient.mk (Ideal.span {F}) G) →
    ¬ Module.Free ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) →
    ∃ c, Ideal.Quotient.mk (IsLocalRing.maximalIdeal ((U : Scheme.{u}).presheaf.stalk x)) c = 0 ∧
      Nonempty (((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) ≃ₗ[(U : Scheme.{u}).presheaf.stalk x]
        localSerreExtensionPresentation F G c) := by
  dsimp
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E) x
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  letI : IsClosedImmersion i := by
    exact isClosedImmersion_localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 0))
  let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 1))
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  have hker : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({F, G} : Set ((U : Scheme.{u}).presheaf.stalk x)) := by
    exact localSectionZeroSubschemeOfOver_stalk_ker_eq_span_pair U t s x
  intro hf hg hfree
  exact serreExtension_stalk_coordinate_eq_zero_mod_maximalIdeal_of_closedImmersionIdealTwist_isoUnit_of_not_free
    i (Iso.refl _) e x F G hker hf hg hfree

set_option linter.style.haveILetI false in
/- The quotient-kernel calculation for the local zero locus also supplies the
   actual stalk presentation itself.  This specialization leaves only the
   successive regularity of the two coordinate germs as geometric input. -/
theorem localSectionZeroSubschemeOfOver_stalk_presentation_nonempty_of_regular_generators
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
    let F := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0))
    let G := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 1))
    IsRegular F → IsRegular (Ideal.Quotient.mk (Ideal.span {F}) G) →
      ∃ c, Nonempty (((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ≃ₗ[
          (U : Scheme.{u}).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)]
        localSerreExtensionPresentation F G c) := by
  dsimp
  letI : Module ((U : Scheme.{u}).presheaf.stalk
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
    schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  let x := i z
  let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 0))
  let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 1))
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (localSectionZeroSubschemeOfOver (X := X) U
            (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  have hker : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({F, G} : Set ((U : Scheme.{u}).presheaf.stalk x)) := by
    exact localSectionZeroSubschemeOfOver_stalk_ker_eq_span_pair U t s x
  intro hf hg
  simpa [F, G, x, i] using
    (serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_regular_generators
      i (Iso.refl _) e x F G hker hf hg)

set_option linter.style.haveILetI false in
/- The directly geometric form takes the Jacobian certificate at the zero
   locus: regularity of the ambient stalk together with cotangent-space
   independence of the two displayed coordinates.  The coordinate
   maximal-ideal membership is supplied by the zero-locus theorem itself. -/
theorem localSectionZeroSubschemeOfOver_stalk_presentation_nonempty_of_cotangentIndependent_parameters
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
    let F := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0))
    let G := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 1))
    IsRegularLocalRing
        ((U : Scheme.{u}).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) →
      F ∉ IsLocalRing.maximalIdeal
        ((U : Scheme.{u}).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ^ 2 →
      G ∉ Ideal.span ({F} : Set
          ((U : Scheme.{u}).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))) ⊔
        IsLocalRing.maximalIdeal
          ((U : Scheme.{u}).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ^ 2 →
      ∃ c, Nonempty (((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ≃ₗ[
          (U : Scheme.{u}).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)]
        localSerreExtensionPresentation F G c) := by
  dsimp
  letI : Module ((U : Scheme.{u}).presheaf.stalk
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
    schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  let x := i z
  let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 0))
  let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 1))
  letI : IsClosedImmersion i := by
    exact isClosedImmersion_localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (localSectionZeroSubschemeOfOver (X := X) U
            (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  have hker : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({F, G} : Set ((U : Scheme.{u}).presheaf.stalk x)) := by
    exact localSectionZeroSubschemeOfOver_stalk_ker_eq_span_pair U t s x
  have hFmax : F ∈ IsLocalRing.maximalIdeal
      ((U : Scheme.{u}).presheaf.stalk x) := by
    simpa [F, x, i] using
      (localSectionZeroSubschemeOfOver_germ_coordinate_mem_maximalIdeal
        (X := X) U t s z (ULift.up 0))
  intro hregular hfsquare hglinear
  simpa [F, G, x, i] using
    (serreExtension_stalkPresentation_nonempty_of_closedImmersionIdealTwist_isoUnit_of_cotangentIndependent_generators
      i (Iso.refl _) e x F G hker hregular hFmax hfsquare hglinear)

set_option linter.style.haveILetI false in
/-- At a zero-locus point, the actual Serre stalk is free exactly when its
local extension coordinate is a unit.  The coordinate maximal-ideal
hypotheses are supplied by the scheme-theoretic zero-locus itself; the
remaining input is the displayed presentation equivalence and the first
coordinate's non-zero-divisor property. -/
theorem localSectionZeroSubschemeOfOver_stalk_presentation_free_iff_isUnit_at_zero
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
    ∀ (c : (U : Scheme.{u}).presheaf.stalk
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
    (hpresentation :
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ≃ₗ[
          (U : Scheme.{u}).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)]
        localSerreExtensionPresentation
          ((U : Scheme.{u}).presheaf.germ ⊤
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
            (Set.mem_univ _)
            (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
              (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
              (restrictSectionToOpen (X := X) U s) (ULift.up 0)))
          ((U : Scheme.{u}).presheaf.germ ⊤
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
            (Set.mem_univ _)
            (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
              (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
              (restrictSectionToOpen (X := X) U s) (ULift.up 1))) c)
    (hf : IsRegular ((U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0)))),
    Module.Free ((U : Scheme.{u}).presheaf.stalk
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ↔
      IsUnit c := by
  dsimp
  intro c hpresentation hf
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  let x := i z
  let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 0))
  let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 1))
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E) x
  have hFmax : F ∈ IsLocalRing.maximalIdeal
      ((U : Scheme.{u}).presheaf.stalk x) := by
    simpa [F, x, i] using
      (localSectionZeroSubschemeOfOver_germ_coordinate_mem_maximalIdeal
        (X := X) U t s z (ULift.up 0))
  have hGmax : G ∈ IsLocalRing.maximalIdeal
      ((U : Scheme.{u}).presheaf.stalk x) := by
    simpa [G, x, i] using
      (localSectionZeroSubschemeOfOver_germ_coordinate_mem_maximalIdeal
        (X := X) U t s z (ULift.up 1))
  apply localSerreExtensionPresentation_free_iff_isUnit_of_sheafStalk
    (show (U : Scheme.{u}).Modules from e.E) x F G
  · exact isRegular_iff_mem_nonZeroDivisors.mp (by simpa [F, x, i] using hf)
  · exact hFmax
  · exact hGmax
  · simpa [F, G, x, i] using hpresentation

set_option linter.style.haveILetI false in
/-- The pointwise form used by the Galois argument: after the two coordinate
regularity conditions are supplied, failure of freeness is equivalent to the
existence of a nonunit extension coordinate together with its actual stalk
presentation.  This packages the two directions of the local Serre
calculation without replacing the geometric middle sheaf by a model. -/
theorem localSectionZeroSubschemeOfOver_stalk_nonfree_iff_exists_nonunit_coordinate_and_presentation
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
    let F := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0))
    let G := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 1))
    IsRegular F → IsRegular (Ideal.Quotient.mk (Ideal.span {F}) G) →
    (¬ Module.Free ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ↔
      ∃ c, ¬ IsUnit c ∧ Nonempty
        (((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ≃ₗ[
            (U : Scheme.{u}).presheaf.stalk
              ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)]
          localSerreExtensionPresentation F G c)) := by
  dsimp
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  let x := i z
  let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 0))
  let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 1))
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E) x
  letI : IsClosedImmersion i := by
    exact isClosedImmersion_localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (localSectionZeroSubschemeOfOver (X := X) U
            (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  have hker : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
      Ideal.span ({F, G} : Set ((U : Scheme.{u}).presheaf.stalk x)) := by
    exact localSectionZeroSubschemeOfOver_stalk_ker_eq_span_pair U t s x
  intro hf hg
  constructor
  · intro hfree
    obtain ⟨c, hc, hpresentation⟩ :=
      serreExtension_stalk_exists_nonunit_coordinate_and_presentation_of_closedImmersionIdealTwist_isoUnit_of_not_free
        i (Iso.refl _) e x F G hker hf hg hfree
    exact ⟨c, hc, hpresentation⟩
  · rintro ⟨c, hc, hpresentation⟩ hfree
    exact hc ((localSectionZeroSubschemeOfOver_stalk_presentation_free_iff_isUnit_at_zero
      U t s e z c (Classical.choice hpresentation)
      (by simpa [F, x, i] using hf)).mp hfree)

set_option linter.style.haveILetI false in
/- The cotangent/Jacobian form of the preceding pointwise criterion.  This
   is the form needed when the selected sections are known geometrically by
   their first-order independence at the common zero. -/
theorem localSectionZeroSubschemeOfOver_stalk_nonfree_iff_exists_nonunit_coordinate_and_presentation_of_cotangentIndependent_parameters
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
    let F := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0))
    let G := (U : Scheme.{u}).presheaf.germ ⊤
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
      (Set.mem_univ _)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 1))
    IsRegularLocalRing
        ((U : Scheme.{u}).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) →
      F ∉ IsLocalRing.maximalIdeal
        ((U : Scheme.{u}).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ^ 2 →
      G ∉ Ideal.span ({F} : Set
          ((U : Scheme.{u}).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))) ⊔
        IsLocalRing.maximalIdeal
          ((U : Scheme.{u}).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ^ 2 →
      (¬ Module.Free ((U : Scheme.{u}).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ↔
        ∃ c, ¬ IsUnit c ∧ Nonempty
          (((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
            ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) ≃ₗ[
              (U : Scheme.{u}).presheaf.stalk
                ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)]
            localSerreExtensionPresentation F G c)) := by
  dsimp
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  let x := i z
  let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 0))
  let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 1))
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E) x
  letI : IsClosedImmersion i := by
    exact isClosedImmersion_localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (localSectionZeroSubschemeOfOver (X := X) U
            (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  have hFmax : F ∈ IsLocalRing.maximalIdeal
      ((U : Scheme.{u}).presheaf.stalk x) := by
    simpa [F, x, i] using
      (localSectionZeroSubschemeOfOver_germ_coordinate_mem_maximalIdeal
        (X := X) U t s z (ULift.up 0))
  intro hregular hfsquare hglinear
  letI : IsRegularLocalRing ((U : Scheme.{u}).presheaf.stalk x) := hregular
  obtain ⟨hf, hg⟩ :=
    AllCharacteristics.local_nonZeroDivisors_of_cotangentIndependentParameters
      F G hFmax hfsquare hglinear
  have hF : IsRegular F := isRegular_iff_mem_nonZeroDivisors.mpr hf
  have hG : IsRegular (Ideal.Quotient.mk (Ideal.span {F}) G) :=
    isRegular_iff_mem_nonZeroDivisors.mpr hg
  simpa [F, G, x, i] using
    (localSectionZeroSubschemeOfOver_stalk_nonfree_iff_exists_nonunit_coordinate_and_presentation
      U t s e z hF hG)

set_option linter.style.haveILetI false in
/- The fully differential form of the preceding local criterion.  A
   residue-field Jacobian certificate for the two actual coordinate germs is
   converted internally to the successive regularity hypotheses. -/
theorem localSectionZeroSubschemeOfOver_stalk_nonfree_iff_exists_nonunit_coordinate_and_presentation_of_linearIndependent_cotangent_classes
    {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
    let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
    let x := i z
    let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0))
    let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 1))
    IsRegularLocalRing ((U : Scheme.{u}).presheaf.stalk x) →
      ∀ (hFmax : F ∈ IsLocalRing.maximalIdeal
          ((U : Scheme.{u}).presheaf.stalk x)),
        ∀ (hGmax : G ∈ IsLocalRing.maximalIdeal
            ((U : Scheme.{u}).presheaf.stalk x)),
          LinearIndependent (IsLocalRing.ResidueField
              ((U : Scheme.{u}).presheaf.stalk x))
            ![(IsLocalRing.maximalIdeal
                ((U : Scheme.{u}).presheaf.stalk x)).toCotangent
                ⟨F, hFmax⟩,
              (IsLocalRing.maximalIdeal
                ((U : Scheme.{u}).presheaf.stalk x)).toCotangent
                ⟨G, hGmax⟩] →
          (¬ Module.Free ((U : Scheme.{u}).presheaf.stalk x)
              ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) ↔
            ∃ c, ¬ IsUnit c ∧ Nonempty
              (((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) ≃ₗ[
                (U : Scheme.{u}).presheaf.stalk x]
                localSerreExtensionPresentation F G c)) := by
  dsimp
  let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
  let x := i z
  let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 0))
  let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
    (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
      (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
      (restrictSectionToOpen (X := X) U s) (ULift.up 1))
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) :=
    schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E) x
  letI : IsClosedImmersion i := by
    exact isClosedImmersion_localSectionZeroSubschemeOfOverι U (ULift (Fin 2)) t s
  letI : Module ((U : Scheme.{u}).presheaf.stalk x)
      ((show (U : Scheme.{u}).Modules from
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (localSectionZeroSubschemeOfOver (X := X) U
            (ULift (Fin 2)) t s).ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  have hFmax : F ∈ IsLocalRing.maximalIdeal
      ((U : Scheme.{u}).presheaf.stalk x) := by
    simpa [F, x, i] using
      (localSectionZeroSubschemeOfOver_germ_coordinate_mem_maximalIdeal
        (X := X) U t s z (ULift.up 0))
  have hGmax : G ∈ IsLocalRing.maximalIdeal
      ((U : Scheme.{u}).presheaf.stalk x) := by
    simpa [G, x, i] using
      (localSectionZeroSubschemeOfOver_germ_coordinate_mem_maximalIdeal
        (X := X) U t s z (ULift.up 1))
  intro hregular hfmax hgmax hli
  letI : IsRegularLocalRing ((U : Scheme.{u}).presheaf.stalk x) := hregular
  obtain ⟨hfsquare, hglinear⟩ :=
    AllCharacteristics.cotangentIndependentParameters_of_linearIndependent_cotangent_classes
      F G hfmax hgmax hli
  exact localSectionZeroSubschemeOfOver_stalk_nonfree_iff_exists_nonunit_coordinate_and_presentation_of_cotangentIndependent_parameters
    U t s e z hregular hfsquare hglinear

set_option linter.style.haveILetI false in
/- On a smooth affine chart over a field, regularity of the ambient stalk is
   automatic.  This specialization leaves the selected-section Jacobian
   certificate as the only local input to the differential criterion. -/
theorem localSectionZeroSubschemeOfOver_stalk_nonfree_iff_exists_nonunit_coordinate_and_presentation_of_linearIndependent_cotangent_classes_of_smooth
    {K : Type u} [Field K] {X : Scheme.{u}} {E : X.Modules}
    (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (f : (U : Scheme.{u}) ⟶ (Spec (.of K) : Scheme.{u})) (hf : Smooth f)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift (Fin 2)) ≅ E.over U)
    (s : E.sections)
    [IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)]
    (e : SerreExtensionSequenceData (U : Scheme.{u})
      (closedImmersionIdealTwist
        (localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s)
        (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)))
    (z : localSectionZeroSubschemeOfOver (X := X) U (ULift (Fin 2)) t s) :
    letI : Module ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z))
        ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk
          ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
      schemeModuleStalkModule (show (U : Scheme.{u}).Modules from e.E)
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
    let i := localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s
    let x := i z
    let F := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 0))
    let G := (U : Scheme.{u}).presheaf.germ ⊤ x (Set.mem_univ x)
      (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) (ULift (Fin 2))
        (localFreeIsoOfOver (X := X) U (ULift (Fin 2)) t)
        (restrictSectionToOpen (X := X) U s) (ULift.up 1))
    ∀ (hFmax : F ∈ IsLocalRing.maximalIdeal
        ((U : Scheme.{u}).presheaf.stalk x)),
      ∀ (hGmax : G ∈ IsLocalRing.maximalIdeal
          ((U : Scheme.{u}).presheaf.stalk x)),
        LinearIndependent (IsLocalRing.ResidueField
            ((U : Scheme.{u}).presheaf.stalk x))
          ![(IsLocalRing.maximalIdeal
              ((U : Scheme.{u}).presheaf.stalk x)).toCotangent
              ⟨F, hFmax⟩,
            (IsLocalRing.maximalIdeal
              ((U : Scheme.{u}).presheaf.stalk x)).toCotangent
              ⟨G, hGmax⟩] →
        (¬ Module.Free ((U : Scheme.{u}).presheaf.stalk x)
            ((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) ↔
          ∃ c, ¬ IsUnit c ∧ Nonempty
            (((show (U : Scheme.{u}).Modules from e.E).presheaf.stalk x) ≃ₗ[
              (U : Scheme.{u}).presheaf.stalk x]
              localSerreExtensionPresentation F G c)) := by
  dsimp
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : Smooth f := hf
  intro hfmax hgmax hli
  have hregular : IsRegularLocalRing
      ((U : Scheme.{u}).presheaf.stalk
        ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)) :=
    AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine f
      ((localSectionZeroSubschemeOfOverι (X := X) U (ULift (Fin 2)) t s) z)
  exact localSectionZeroSubschemeOfOver_stalk_nonfree_iff_exists_nonunit_coordinate_and_presentation_of_linearIndependent_cotangent_classes
    U t s e z hregular hfmax hgmax hli


end BundleSectionZeroLocus
end

end PfaffianDescent
