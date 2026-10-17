import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Topology.Sheaves.LocallySurjective

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace IdealSheafDataModule

variable {X : Scheme.{u}}

/-!
`Scheme.IdealSheafData` is deliberately affine-local in Mathlib.  This file
turns such data into an actual module sheaf: a section belongs to the
underlying subpresheaf exactly when all of its affine restrictions lie in the
specified ideals, and then that presheaf is sheafified.  The construction is
used as the concrete ideal-sheaf module needed by the Serre step of Voisin's
argument.
-/

/-- The subpresheaf of the structure sheaf selected by affine-local ideal data. -/
noncomputable def presheafSubmodule (I : X.IdealSheafData) :
    PresheafOfModules.Submodule (SheafOfModules.unit X.ringCatSheaf).val where
  obj U :=
    { carrier := { s | ∀ (V : X.affineOpens) (hVU : V.1 ≤ U.unop),
        (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE hVU).op s ∈ I.ideal V }
      add_mem' := by
        intro a b ha hb V hVU
        change ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE hVU).op).hom (a + b) ∈ I.ideal V
        rw [LinearMap.map_add]
        exact (I.ideal V).add_mem (ha V hVU) (hb V hVU)
      zero_mem' := by
        intro V hVU
        change ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE hVU).op).hom 0 ∈ I.ideal V
        rw [LinearMap.map_zero]
        exact (I.ideal V).zero_mem
      smul_mem' := by
        intro r a ha V hVU
        rw [PresheafOfModules.map_smul]
        exact (I.ideal V).mul_mem_left _ (ha V hVU) }
  map {U V} f := by
    intro s hs W hWV
    let M : PresheafOfModules X.ringCatSheaf.obj := (SheafOfModules.unit X.ringCatSheaf).val
    let hWU : W.1 ≤ U.unop := hWV.trans f.unop.le
    change M.map (homOfLE hWV).op (M.map f s) ∈ I.ideal W
    have hmap : M.map (f ≫ (homOfLE hWV).op) s =
        M.map (homOfLE hWV).op (M.map f s) :=
      M.map_comp_apply f (homOfLE hWV).op s
    rw [← hmap]
    have heq : f ≫ (homOfLE hWV).op = (homOfLE hWU).op := Subsingleton.elim _ _
    rw [heq]
    exact hs W hWU

/-- The actual module sheaf associated to affine-local ideal data. -/
noncomputable def moduleSheaf (I : X.IdealSheafData) :
    SheafOfModules X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (presheafSubmodule I).toPresheafOfModules

/-- The canonical map from the associated ideal module to the structure sheaf. -/
noncomputable def moduleSheafToUnit (I : X.IdealSheafData) :
    moduleSheaf I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (presheafSubmodule I).toPresheafOfModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (presheafSubmodule I).ι

/-- The associated ideal module as a literal subobject of the structure
sheaf. Taking the image retains the canonical inclusion after sheafification. -/
noncomputable def idealModule (I : X.IdealSheafData) :
    SheafOfModules X.ringCatSheaf :=
  Abelian.image (moduleSheafToUnit I)

/-- The inclusion of the associated ideal module into the structure sheaf. -/
noncomputable def idealModuleToUnit (I : X.IdealSheafData) :
    idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  Abelian.image.ι (moduleSheafToUnit I)

instance (I : X.IdealSheafData) : Mono (idealModuleToUnit I) := by
  change Mono (kernel.ι (cokernel.π (moduleSheafToUnit I)))
  constructor
  intro Z g h w
  apply equalizer.hom_ext
  exact w

/-- The sheafified ideal presheaf factors through the actual ideal submodule. -/
noncomputable def moduleSheafToIdealModule (I : X.IdealSheafData) :
    moduleSheaf I ⟶ idealModule I :=
  Abelian.factorThruImage (moduleSheafToUnit I)

/-- Sheafifying the affine-local ideal presheaf maps epimorphically onto its
actual image inside the structure sheaf.  Thus `idealModule` retains precisely
the associated ideal submodule, while `moduleSheaf` remains available for
descent calculations on the affine-local presentation. -/
instance (I : X.IdealSheafData) : Epi (moduleSheafToIdealModule I) := by
  change Epi (Abelian.factorThruImage (moduleSheafToUnit I))
  infer_instance

@[reassoc]
theorem moduleSheafToIdealModule_comp (I : X.IdealSheafData) :
    moduleSheafToIdealModule I ≫ idealModuleToUnit I = moduleSheafToUnit I :=
  Abelian.image.fac (moduleSheafToUnit I)

/-- The canonical quotient sequence of the ideal module inside the structure
sheaf. -/
noncomputable def idealModuleCokernelSequence (I : X.IdealSheafData) :
    ShortComplex (SheafOfModules X.ringCatSheaf) :=
  ShortComplex.cokernelSequence (idealModuleToUnit I)

/-- The ideal module, the structure sheaf, and its quotient form a short exact
sequence. -/
theorem idealModuleCokernelSequence_shortExact (I : X.IdealSheafData) :
    (idealModuleCokernelSequence I).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (idealModuleToUnit I)
  mono_f := by
    change Mono (idealModuleToUnit I)
    infer_instance
  epi_g := by
    change Epi (cokernel.π (idealModuleToUnit I))
    infer_instance



/-- On an affine open, the underlying ideal presheaf is exactly the recorded ideal. -/
theorem mem_presheafSubmodule_affine (I : X.IdealSheafData) (U : X.affineOpens)
    (s : Γ(X, U.1)) :
    s ∈ (presheafSubmodule I).obj (.op U.1) ↔ s ∈ I.ideal U := by
  constructor
  · intro hs
    let M : PresheafOfModules X.ringCatSheaf.obj := (SheafOfModules.unit X.ringCatSheaf).val
    have h := hs U le_rfl
    change M.map (homOfLE (show U.1 ≤ U.1 from le_rfl)).op s ∈ I.ideal U at h
    have hId : (homOfLE (show U.1 ≤ U.1 from le_rfl)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [hId, M.map_id] at h
    exact h
  · intro hs V hVU
    change X.presheaf.map (homOfLE hVU).op s ∈ I.ideal V
    rw [← I.map_ideal hVU]
    exact Ideal.mem_map_of_mem _ hs

/-- The actual ideal-module sheaf associated with a closed immersion.  This is
the `𝓘_Z` input to the Serre construction when the immersion is the finite
subscheme `Z ↪ X`. -/
noncomputable def closedImmersionModule {Z : Scheme.{u}} (i : Z ⟶ X) :
    SheafOfModules X.ringCatSheaf :=
  idealModule i.ker

/-- The literal inclusion of the ideal module of a closed immersion into the
structure sheaf. -/
noncomputable def closedImmersionModuleToUnit {Z : Scheme.{u}} (i : Z ⟶ X) :
    closedImmersionModule i ⟶ SheafOfModules.unit X.ringCatSheaf :=
  idealModuleToUnit i.ker

/-- The quotient sequence attached to the actual ideal module of a closed
immersion. This is the untwisted exact sequence that precedes the Serre
extension in Voisin's construction. -/
noncomputable def closedImmersionModuleCokernelSequence {Z : Scheme.{u}}
    (i : Z ⟶ X) : ShortComplex (SheafOfModules X.ringCatSheaf) :=
  idealModuleCokernelSequence i.ker

/-- The untwisted ideal sequence of a closed immersion is short exact. -/
theorem closedImmersionModuleCokernelSequence_shortExact {Z : Scheme.{u}}
    (i : Z ⟶ X) :
    (closedImmersionModuleCokernelSequence i).ShortExact :=
  idealModuleCokernelSequence_shortExact i.ker

/-- The affine sections of the ideal presheaf for a closed immersion are the
kernel ideals of its maps on affine coordinate rings. -/
theorem mem_closedImmersionPresheafSubmodule_affine {Z : Scheme.{u}}
    (i : Z ⟶ X) (U : X.affineOpens) (s : Γ(X, U.1)) :
    s ∈ (presheafSubmodule i.ker).obj (.op U.1) ↔ s ∈ i.ker.ideal U :=
  mem_presheafSubmodule_affine i.ker U s

/-- The canonical quotient map from the structure sheaf to the pushed-forward
structure sheaf of a closed subscheme.  It is induced directly by the morphism
of locally ringed spaces, so it provides the quotient side of the ideal
sequence without choosing affine presentations. -/
noncomputable def closedImmersionUnitToPushforwardUnit {Z : Scheme.{u}}
    (i : Z ⟶ X) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

/-- Before sheafification, the affine-local ideal subpresheaf of a closed
immersion maps trivially to the pushed-forward structure sheaf.  The proof is
local on the target: on an affine open it is exactly membership in the kernel
of the coordinate-ring quotient. -/
theorem presheafSubmoduleToPushforwardUnit_eq_zero {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (presheafSubmodule i.ker).ι ≫
      (closedImmersionUnitToPushforwardUnit i).val = 0 := by
  apply PresheafOfModules.Hom.ext
  ext U s
  apply TopCat.Presheaf.IsSheaf.section_ext
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).isSheaf
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.unop.2
  refine ⟨V, hVU, hxV, ?_⟩
  let m := (presheafSubmodule i.ker).ι ≫
    (closedImmersionUnitToPushforwardUnit i).val
  have hnat := m.naturality (homOfLE hVU).op
  have hnat' := ConcreteCategory.congr_hom hnat s
  simp only [PresheafOfModules.zero_app, ModuleCat.hom_zero, LinearMap.zero_apply]
  change m.app (.op V)
      ((presheafSubmodule i.ker).toPresheafOfModules.map (homOfLE hVU).op s) =
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
      (homOfLE hVU).op (m.app U s) at hnat'
  have hreszero :
      (ConcreteCategory.hom
        (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
          (homOfLE hVU).op)) 0 = 0 := by
    exact map_zero _
  calc
    (ConcreteCategory.hom
        (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
          (homOfLE hVU).op))
        ((ModuleCat.Hom.hom
          (((presheafSubmodule i.ker).ι ≫ (closedImmersionUnitToPushforwardUnit i).val).app U))
          s) = 0 := by
      change ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (homOfLE hVU).op (m.app U s) = 0
      rw [← hnat']
      change i.app V (X.presheaf.map (homOfLE hVU).op s.1) = 0
      have hsV := s.2 ⟨V, hV⟩ hVU
      change X.presheaf.map (homOfLE hVU).op s.1 ∈ i.ker.ideal ⟨V, hV⟩ at hsV
      rw [Scheme.Hom.ker_apply] at hsV
      exact hsV
    _ = (ConcreteCategory.hom
        (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
          (homOfLE hVU).op)) 0 := hreszero.symm

/-- The structure-sheaf map of a closed immersion is epimorphic as a map of
module sheaves.  Surjectivity is proved on affine neighbourhoods, where it is
the surjectivity on coordinate rings, and sheaf locality then promotes the
local lifts to categorical epimorphy. -/
instance {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (closedImmersionUnitToPushforwardUnit i) := by
  constructor
  intro W g h H
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  ext U s
  apply TopCat.Presheaf.IsSheaf.section_ext W.isSheaf
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.unop.2
  refine ⟨V, hVU, hxV, ?_⟩
  let sV := ((Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map (homOfLE hVU).op s
  obtain ⟨t, ht⟩ := i.app_surjective V hV sV
  change i.app V t = sV at ht
  let g' := Scheme.Modules.Hom.mapPresheaf g
  let h' := Scheme.Modules.Hom.mapPresheaf h
  have hg := g'.naturality (homOfLE hVU).op
  have hh := h'.naturality (homOfLE hVU).op
  have hg' := ConcreteCategory.congr_hom hg s
  have hh' := ConcreteCategory.congr_hom hh s
  change g'.app (.op V)
      (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (g'.app U s) at hg'
  change h'.app (.op V)
      (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (h'.app U s) at hh'
  have hgsec : g'.app (.op V)
      (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (g'.app U s) := hg'
  have hhsec : h'.app (.op V)
      (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (h'.app U s) := hh'
  change W.val.presheaf.map (homOfLE hVU).op (g'.app U s) =
    W.val.presheaf.map (homOfLE hVU).op (h'.app U s)
  have hmiddle : g'.app (.op V) sV = h'.app (.op V) sV := by
    rw [← ht]
    have hH := congrArg (fun q => (Scheme.Modules.Hom.mapPresheaf q).app (.op V)) H
    have hH' := ConcreteCategory.congr_hom hH t
    change g'.app (.op V) (i.app V t) = h'.app (.op V) (i.app V t) at hH'
    exact hH'
  exact hgsec.symm.trans (hmiddle.trans hhsec)

/-- The ideal module of a closed immersion, defined directly as the kernel of
the structure-sheaf map to the pushed-forward structure sheaf.  This is the
canonical sheaf-theoretic model of `𝓘_Z` used in the untwisted Serre sequence. -/
noncomputable def closedImmersionKernelModule {Z : Scheme.{u}} (i : Z ⟶ X) :
    SheafOfModules X.ringCatSheaf :=
  kernel (closedImmersionUnitToPushforwardUnit i)

/-- The canonical inclusion of the kernel ideal module into the structure
sheaf. -/
noncomputable def closedImmersionKernelModuleToUnit {Z : Scheme.{u}} (i : Z ⟶ X) :
    closedImmersionKernelModule i ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι _

instance {Z : Scheme.{u}} (i : Z ⟶ X) :
    Mono (closedImmersionKernelModuleToUnit i) := by
  change Mono (kernel.ι _)
  constructor
  intro Y f g h
  apply equalizer.hom_ext
  exact h

noncomputable section

/-- Sheafification preserves the vanishing of the affine-local ideal in the
closed subscheme.  This is the compatibility needed to compare the ideal
module used by the Serre construction with the canonical kernel ideal. -/
theorem moduleSheafToUnit_comp_closedImmersionUnitToPushforwardUnit
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    let T : SheafOfModules X.ringCatSheaf :=
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let q : SheafOfModules.unit X.ringCatSheaf ⟶ T :=
      closedImmersionUnitToPushforwardUnit i
    moduleSheafToUnit i.ker ≫ q = 0 := by
  let T : SheafOfModules X.ringCatSheaf :=
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let q : SheafOfModules.unit X.ringCatSheaf ⟶ T :=
    closedImmersionUnitToPushforwardUnit i
  change moduleSheafToUnit i.ker ≫ q = 0
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := (presheafSubmodule i.ker).toPresheafOfModules) (F := T)).injective
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    ((presheafSubmodule i.ker).toPresheafOfModules) T)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        ((presheafSubmodule i.ker).toPresheafOfModules)
        (SheafOfModules.unit X.ringCatSheaf)).symm
        (presheafSubmodule i.ker).ι ≫ q) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      ((presheafSubmodule i.ker).toPresheafOfModules) T) 0
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  have hE :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        ((presheafSubmodule i.ker).toPresheafOfModules)
        (SheafOfModules.unit X.ringCatSheaf))
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
          ((presheafSubmodule i.ker).toPresheafOfModules)
          (SheafOfModules.unit X.ringCatSheaf)).symm
          (presheafSubmodule i.ker).ι) = (presheafSubmodule i.ker).ι :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      ((presheafSubmodule i.ker).toPresheafOfModules)
      (SheafOfModules.unit X.ringCatSheaf) |>.apply_symm_apply _
  rw [hE]
  letI : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_adjoint_additive
  have hzero :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        ((presheafSubmodule i.ker).toPresheafOfModules) T) 0 = 0 :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homAddEquiv_zero _ _
  rw [hzero]
  change (presheafSubmodule i.ker).ι ≫
    (closedImmersionUnitToPushforwardUnit i).val = 0
  exact presheafSubmoduleToPushforwardUnit_eq_zero i

/-- The sheafified affine-local ideal module maps canonically to the direct
kernel ideal of a closed immersion. -/
noncomputable def moduleSheafToClosedImmersionKernelModule {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    moduleSheaf i.ker ⟶ closedImmersionKernelModule i :=
  kernel.lift (closedImmersionUnitToPushforwardUnit i) (moduleSheafToUnit i.ker)
    (moduleSheafToUnit_comp_closedImmersionUnitToPushforwardUnit i)

@[reassoc]
theorem moduleSheafToClosedImmersionKernelModule_comp {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    moduleSheafToClosedImmersionKernelModule i ≫ closedImmersionKernelModuleToUnit i =
      moduleSheafToUnit i.ker :=
  kernel.lift_ι _ _ _

/-- The image-defined ideal module maps canonically into the direct kernel
ideal.  It is obtained by descending the sheafified ideal map along its
epimorphism onto the image. -/
noncomputable def closedImmersionModuleToKernel {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionModule i ⟶ closedImmersionKernelModule i :=
  Abelian.epiDesc (moduleSheafToIdealModule i.ker)
    (moduleSheafToClosedImmersionKernelModule i) (by
      apply (cancel_mono (closedImmersionKernelModuleToUnit i)).mp
      rw [Category.assoc, moduleSheafToClosedImmersionKernelModule_comp,
        ← moduleSheafToIdealModule_comp]
      simp)

@[reassoc]
theorem moduleSheafToIdealModule_comp_closedImmersionModuleToKernel
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    moduleSheafToIdealModule i.ker ≫ closedImmersionModuleToKernel i =
      moduleSheafToClosedImmersionKernelModule i := by
  unfold closedImmersionModuleToKernel
  exact Abelian.comp_epiDesc _ _ _

/-- The comparison from the affine-local ideal module to the direct kernel
commutes with their inclusions into the structure sheaf. -/
@[reassoc]
theorem closedImmersionModuleToKernel_comp {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionModuleToKernel i ≫ closedImmersionKernelModuleToUnit i =
      closedImmersionModuleToUnit i := by
  apply (cancel_epi (moduleSheafToIdealModule i.ker)).mp
  change moduleSheafToIdealModule i.ker ≫
    (closedImmersionModuleToKernel i ≫ closedImmersionKernelModuleToUnit i) =
      moduleSheafToIdealModule i.ker ≫ closedImmersionModuleToUnit i
  calc
    moduleSheafToIdealModule i.ker ≫
        (closedImmersionModuleToKernel i ≫ closedImmersionKernelModuleToUnit i) =
      (moduleSheafToIdealModule i.ker ≫ closedImmersionModuleToKernel i) ≫
        closedImmersionKernelModuleToUnit i := (Category.assoc _ _ _).symm
    _ = moduleSheafToClosedImmersionKernelModule i ≫
        closedImmersionKernelModuleToUnit i := by
      rw [moduleSheafToIdealModule_comp_closedImmersionModuleToKernel]
    _ = moduleSheafToUnit i.ker :=
      moduleSheafToClosedImmersionKernelModule_comp i
    _ = moduleSheafToIdealModule i.ker ≫ closedImmersionModuleToUnit i :=
      (moduleSheafToIdealModule_comp i.ker).symm

/-- The affine-local ideal module embeds in the direct geometric kernel
ideal.  Surjectivity of this comparison, equivalently identification of the
two modules, remains the affine-local sheafification task. -/
instance {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Mono (closedImmersionModuleToKernel i) := by
  constructor
  intro Y f g h
  apply (cancel_mono (idealModuleToUnit i.ker)).mp
  change f ≫ closedImmersionModuleToUnit i = g ≫ closedImmersionModuleToUnit i
  have h' := congrArg (fun q => q ≫ closedImmersionKernelModuleToUnit i) h
  change f ≫ (closedImmersionModuleToKernel i ≫
    closedImmersionKernelModuleToUnit i) =
      g ≫ (closedImmersionModuleToKernel i ≫
        closedImmersionKernelModuleToUnit i) at h'
  rw [closedImmersionModuleToKernel_comp] at h'
  exact h'

/-- A section of the direct kernel ideal on an affine open belongs to the
original affine-local ideal subpresheaf. -/
private theorem kernelSectionMemPresheafSubmodule {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens)
    (t : (closedImmersionKernelModule i).val.presheaf.obj (.op V.1)) :
    (closedImmersionKernelModuleToUnit i).val.app (.op V.1) t ∈
      (presheafSubmodule i.ker).obj (.op V.1) := by
  apply (mem_closedImmersionPresheafSubmodule_affine i V
    ((closedImmersionKernelModuleToUnit i).val.app (.op V.1) t)).mpr
  rw [Scheme.Hom.ker_apply]
  have hcond := congrArg (fun q => q.val.app (.op V.1))
    (kernel.condition (closedImmersionUnitToPushforwardUnit i))
  have hcond' := ConcreteCategory.congr_hom hcond t
  change i.app V ((closedImmersionKernelModuleToUnit i).val.app (.op V.1) t) = 0 at hcond'
  exact hcond'

/-- Every affine section of the direct kernel ideal lifts through the
sheafification of the affine-local ideal presentation. -/
theorem exists_moduleSheafToClosedImmersionKernelModule_preimage_affine
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens)
    (t : (closedImmersionKernelModule i).val.presheaf.obj (.op V.1)) :
    ∃ s : (moduleSheaf i.ker).val.presheaf.obj (.op V.1),
      (moduleSheafToClosedImmersionKernelModule i).val.app (.op V.1) s = t := by
  let α : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj := 𝟙 _
  let adj := PresheafOfModules.sheafificationAdjunction α
  let P := (presheafSubmodule i.ker).toPresheafOfModules
  let a : (presheafSubmodule i.ker).toPresheafOfModules.obj (.op V.1) :=
    ⟨(closedImmersionKernelModuleToUnit i).val.app (.op V.1) t,
      kernelSectionMemPresheafSubmodule i V t⟩
  let s : (moduleSheaf i.ker).val.obj (.op V.1) :=
    (ModuleCat.restrictScalarsId'App
      (α.app (.op V.1)).hom (by dsimp [α])
      ((moduleSheaf i.ker).val.obj (.op V.1))).hom
      (ConcreteCategory.hom (adj.unit.app P |>.app (.op V.1)) a)
  refine ⟨s, ?_⟩
  let E := SheafOfModules.evaluation X.ringCatSheaf (.op V.1)
  haveI : Mono (kernel.ι (closedImmersionUnitToPushforwardUnit i)) := by
    change Mono (closedImmersionKernelModuleToUnit i)
    infer_instance
  haveI : Mono ((closedImmersionKernelModuleToUnit i).val.app (.op V.1)) := by
    change Mono (E.map (kernel.ι (closedImmersionUnitToPushforwardUnit i)))
    exact Functor.map_mono E (kernel.ι (closedImmersionUnitToPushforwardUnit i))
  apply (ModuleCat.mono_iff_injective
    ((closedImmersionKernelModuleToUnit i).val.app (.op V.1))).mp (by infer_instance)
  have hfac := congrArg (fun q => q.val.app (.op V.1))
    (moduleSheafToClosedImmersionKernelModule_comp i)
  have hfac' := ConcreteCategory.congr_hom hfac s
  change (closedImmersionKernelModuleToUnit i).val.app (.op V.1)
      ((moduleSheafToClosedImmersionKernelModule i).val.app (.op V.1) s) =
    (moduleSheafToUnit i.ker).val.app (.op V.1) s at hfac'
  rw [hfac']
  have hm : adj.homEquiv P (SheafOfModules.unit X.ringCatSheaf)
      (moduleSheafToUnit i.ker) = (presheafSubmodule i.ker).ι := by
    dsimp [adj, P, α, moduleSheafToUnit]
    exact ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv
        ((presheafSubmodule i.ker).toPresheafOfModules)
        (SheafOfModules.unit X.ringCatSheaf)).apply_symm_apply _
  have hunit : adj.unit.app P ≫
      (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).map (moduleSheafToUnit i.ker) =
      (presheafSubmodule i.ker).ι :=
    (adj.homEquiv_unit P (SheafOfModules.unit X.ringCatSheaf)
      (moduleSheafToUnit i.ker)).symm.trans hm
  have hunitV := congrArg (fun q => q.app (.op V.1)) hunit
  have hunitV' := ConcreteCategory.congr_hom hunitV a
  change (ModuleCat.restrictScalars (α.app (.op V.1)).hom).map
      ((moduleSheafToUnit i.ker).val.app (.op V.1))
      (ConcreteCategory.hom (adj.unit.app P |>.app (.op V.1)) a) = a.1 at hunitV'
  have hnat := ModuleCat.restrictScalarsId'App_hom_naturality
    (f := (α.app (.op V.1)).hom) (hf := by dsimp [α])
    ((moduleSheafToUnit i.ker).val.app (.op V.1))
  have hnat' := ConcreteCategory.congr_hom hnat
    (ConcreteCategory.hom (adj.unit.app P |>.app (.op V.1)) a)
  change
    (ModuleCat.restrictScalarsId'App (α.app (.op V.1)).hom (by dsimp [α])
      ((SheafOfModules.unit X.ringCatSheaf).val.obj (.op V.1))).hom
      ((ModuleCat.restrictScalars (α.app (.op V.1)).hom).map
        ((moduleSheafToUnit i.ker).val.app (.op V.1))
        (ConcreteCategory.hom (adj.unit.app P |>.app (.op V.1)) a)) =
    (moduleSheafToUnit i.ker).val.app (.op V.1)
      ((ModuleCat.restrictScalarsId'App (α.app (.op V.1)).hom (by dsimp [α])
        ((moduleSheaf i.ker).val.obj (.op V.1))).hom
        (ConcreteCategory.hom (adj.unit.app P |>.app (.op V.1)) a)) at hnat'
  calc
    (moduleSheafToUnit i.ker).val.app (.op V.1) s =
      (ModuleCat.restrictScalarsId'App (α.app (.op V.1)).hom (by dsimp [α])
        ((SheafOfModules.unit X.ringCatSheaf).val.obj (.op V.1))).hom
        ((ModuleCat.restrictScalars (α.app (.op V.1)).hom).map
          ((moduleSheafToUnit i.ker).val.app (.op V.1))
          (ConcreteCategory.hom (adj.unit.app P |>.app (.op V.1)) a)) := by
        simpa only [s] using hnat'.symm
    _ = (ModuleCat.restrictScalarsId'App (α.app (.op V.1)).hom (by dsimp [α])
        ((SheafOfModules.unit X.ringCatSheaf).val.obj (.op V.1))).hom a.1 := by
        rw [hunitV']
    _ = a.1 := by simp
    _ = (closedImmersionKernelModuleToUnit i).val.app (.op V.1) t := rfl

/-- The sheafified affine-local ideal module surjects onto the direct kernel
ideal.  Affine-local lifts suffice by sheaf locality. -/
instance {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (moduleSheafToClosedImmersionKernelModule i) := by
  constructor
  intro W g h H
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  ext U s
  apply TopCat.Presheaf.IsSheaf.section_ext W.isSheaf
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.unop.2
  refine ⟨V, hVU, hxV, ?_⟩
  let sV := (closedImmersionKernelModule i).val.presheaf.map (homOfLE hVU).op s
  obtain ⟨t, ht⟩ :=
    exists_moduleSheafToClosedImmersionKernelModule_preimage_affine i ⟨V, hV⟩ sV
  let g' := Scheme.Modules.Hom.mapPresheaf g
  let h' := Scheme.Modules.Hom.mapPresheaf h
  have hg := g'.naturality (homOfLE hVU).op
  have hh := h'.naturality (homOfLE hVU).op
  have hg' := ConcreteCategory.congr_hom hg s
  have hh' := ConcreteCategory.congr_hom hh s
  change g'.app (.op V)
      ((closedImmersionKernelModule i).val.presheaf.map (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (g'.app U s) at hg'
  change h'.app (.op V)
      ((closedImmersionKernelModule i).val.presheaf.map (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (h'.app U s) at hh'
  have hgsec : g'.app (.op V)
      ((closedImmersionKernelModule i).val.presheaf.map (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (g'.app U s) := hg'
  have hhsec : h'.app (.op V)
      ((closedImmersionKernelModule i).val.presheaf.map (homOfLE hVU).op s) =
      W.val.presheaf.map (homOfLE hVU).op (h'.app U s) := hh'
  change W.val.presheaf.map (homOfLE hVU).op (g'.app U s) =
    W.val.presheaf.map (homOfLE hVU).op (h'.app U s)
  have hmiddle : g'.app (.op V) sV = h'.app (.op V) sV := by
    rw [← ht]
    have hH := congrArg (fun q => (Scheme.Modules.Hom.mapPresheaf q).app (.op V)) H
    have hH' := ConcreteCategory.congr_hom hH t
    change g'.app (.op V)
      ((moduleSheafToClosedImmersionKernelModule i).val.app (.op V) t) =
      h'.app (.op V)
        ((moduleSheafToClosedImmersionKernelModule i).val.app (.op V) t) at hH'
    exact hH'
  exact hgsec.symm.trans (hmiddle.trans hhsec)

/-- The comparison from the affine-local ideal module to the direct kernel is
surjective, and therefore an isomorphism. -/
instance {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (closedImmersionModuleToKernel i) := by
  constructor
  intro W g h H
  apply (cancel_epi (moduleSheafToClosedImmersionKernelModule i)).mp
  rw [← moduleSheafToIdealModule_comp_closedImmersionModuleToKernel]
  calc
    (moduleSheafToIdealModule i.ker ≫ closedImmersionModuleToKernel i) ≫ g =
      moduleSheafToIdealModule i.ker ≫ (closedImmersionModuleToKernel i ≫ g) :=
        Category.assoc _ _ _
    _ = moduleSheafToIdealModule i.ker ≫ (closedImmersionModuleToKernel i ≫ h) :=
      congrArg (fun q => moduleSheafToIdealModule i.ker ≫ q) H
    _ = (moduleSheafToIdealModule i.ker ≫ closedImmersionModuleToKernel i) ≫ h :=
      (Category.assoc _ _ _).symm

noncomputable instance {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (closedImmersionModuleToKernel i) :=
  isIso_of_mono_of_epi _

/-- The affine-local and direct-kernel models of the ideal module of a closed
immersion are canonically isomorphic. -/
noncomputable def closedImmersionModuleToKernelIso {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionModule i ≅ closedImmersionKernelModule i :=
  asIso (closedImmersionModuleToKernel i)

/-- The geometric untwisted ideal sequence for a closed immersion.  This is
written in `X.Modules` so that the pushforward target and the ideal module use
the same scheme-module category instance. -/
noncomputable def closedImmersionModulePushforwardSequence {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ShortComplex X.Modules := by
  let I : X.Modules := closedImmersionModule i
  let K : X.Modules := closedImmersionKernelModule i
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let T : X.Modules := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let m : I ⟶ K := closedImmersionModuleToKernel i
  let k : K ⟶ O := closedImmersionKernelModuleToUnit i
  let f : I ⟶ O := closedImmersionModuleToUnit i
  let q : O ⟶ T := closedImmersionUnitToPushforwardUnit i
  have hfac : m ≫ k = f := closedImmersionModuleToKernel_comp i
  have hkernel : k ≫ q = 0 := by
    change kernel.ι q ≫ q = 0
    exact kernel.condition q
  exact ShortComplex.mk f q (by
    calc
      f ≫ q = (m ≫ k) ≫ q := congrArg (fun r => r ≫ q) hfac.symm
      _ = m ≫ (k ≫ q) := Category.assoc _ _ _
      _ = m ≫ 0 := congrArg (fun r => m ≫ r) hkernel
      _ = 0 := by simp)

/-- The image-defined ideal module, the structure sheaf, and the actual
pushforward structure sheaf form the canonical untwisted short exact
sequence of a closed immersion. -/
theorem closedImmersionModulePushforwardSequence_shortExact {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionModulePushforwardSequence i).ShortExact := by
  let I : X.Modules := closedImmersionModule i
  let K : X.Modules := closedImmersionKernelModule i
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let T : X.Modules := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let m : I ⟶ K := closedImmersionModuleToKernel i
  let k : K ⟶ O := closedImmersionKernelModuleToUnit i
  let f : I ⟶ O := closedImmersionModuleToUnit i
  let q : O ⟶ T := closedImmersionUnitToPushforwardUnit i
  let e₁ : I ≅ K := closedImmersionModuleToKernelIso i
  have hfac : m ≫ k = f := closedImmersionModuleToKernel_comp i
  haveI : Mono f := by
    change Mono (idealModuleToUnit i.ker)
    infer_instance
  haveI : Epi q := by
    change Epi (closedImmersionUnitToPushforwardUnit i)
    infer_instance
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · let e : closedImmersionModulePushforwardSequence i ≅
      ShortComplex.kernelSequence q :=
      ShortComplex.isoMk e₁ (Iso.refl _) (Iso.refl _) (by
        change m ≫ k = f ≫ 𝟙 _
        exact hfac.trans (Category.comp_id f).symm)
        (by
          change 𝟙 _ ≫ q = q ≫ 𝟙 _
          simp)
    exact ShortComplex.exact_of_iso e.symm (ShortComplex.kernelSequence_exact q)
  · change Mono f
    infer_instance
  · change Epi q
    infer_instance

end

/-- The exact sequence formed by the direct kernel ideal, the structure sheaf,
and its canonical cokernel. -/
noncomputable def closedImmersionKernelModuleCokernelSequence {Z : Scheme.{u}}
    (i : Z ⟶ X) : ShortComplex (SheafOfModules X.ringCatSheaf) :=
  ShortComplex.cokernelSequence (closedImmersionKernelModuleToUnit i)

/-- The direct kernel ideal of every closed immersion has a short exact
quotient sequence. -/
theorem closedImmersionKernelModuleCokernelSequence_shortExact {Z : Scheme.{u}}
    (i : Z ⟶ X) :
    (closedImmersionKernelModuleCokernelSequence i).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (closedImmersionKernelModuleToUnit i)
  mono_f := by
    change Mono (closedImmersionKernelModuleToUnit i)
    infer_instance
  epi_g := by
    change Epi (cokernel.π (closedImmersionKernelModuleToUnit i))
    infer_instance

/-- The canonical exact ideal sequence through the actual pushed-forward
structure sheaf of the closed subscheme. -/
noncomputable def closedImmersionKernelExactSequence {Z : Scheme.{u}}
    (i : Z ⟶ X) : ShortComplex (SheafOfModules X.ringCatSheaf) :=
  ShortComplex.kernelSequence (closedImmersionUnitToPushforwardUnit i)

/-- Exactness at the structure sheaf in the canonical closed-immersion ideal
sequence. -/
theorem closedImmersionKernelExactSequence_exact {Z : Scheme.{u}} (i : Z ⟶ X) :
    (closedImmersionKernelExactSequence i).Exact :=
  ShortComplex.kernelSequence_exact (closedImmersionUnitToPushforwardUnit i)

/-- For a closed immersion, the canonical ideal sequence is short exact with
quotient equal to the pushed-forward structure sheaf of the closed subscheme. -/
theorem closedImmersionKernelExactSequence_shortExact {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionKernelExactSequence i).ShortExact where
  exact := closedImmersionKernelExactSequence_exact i
  mono_f := by
    change Mono (kernel.ι _)
    constructor
    intro Y f g h
    apply equalizer.hom_ext
    exact h
  epi_g := by
    change Epi (closedImmersionUnitToPushforwardUnit i)
    infer_instance


end IdealSheafDataModule

end PfaffianDescent
