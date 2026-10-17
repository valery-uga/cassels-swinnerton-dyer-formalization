import PfaffianDescent.AffineClosedImmersionIdealKernel
import PfaffianDescent.VoisinSheafStalk
import PfaffianDescent.SchemeModuleSectionOnOpen

/-!
# Affine freeness of the ideal module of a regular-principal immersion

The actual ideal module of a closed immersion has sections equal to its
kernel ideal on affine opens. A regular-principal affine chart therefore
trivializes the ideal module as a rank-one module of sections.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- The affine open in the original target supplied by one chart of a
regular-principal immersion. -/
noncomputable def RegularPrincipalImmersion.targetAffineOpen
    {X Z : Scheme.{u}} {f : Z ⟶ X}
    (H : RegularPrincipalImmersion f) (j : H.Index) : X.affineOpens := by
  letI : IsOpenImmersion (H.target j) := H.targetOpen j
  exact ⟨(H.target j).opensRange, isAffineOpen_opensRange _⟩

/-- The target affine opens of a regular-principal immersion cover the
entire original target scheme. -/
theorem RegularPrincipalImmersion.targetAffineOpens_coversTop
    {X Z : Scheme.{u}} {f : Z ⟶ X}
    (H : RegularPrincipalImmersion f) :
    (Opens.grothendieckTopology X).CoversTop
      (fun j : H.Index => (H.targetAffineOpen j).1) := by
  apply (Opens.coversTop_iff _ _).mpr
  apply TopologicalSpace.IsOpenCover.mk
  apply le_antisymm le_top
  intro x _
  obtain ⟨j, y, hy⟩ := H.cover x
  rw [TopologicalSpace.Opens.mem_iSup]
  refine ⟨j, ?_⟩
  letI : IsOpenImmersion (H.target j) := H.targetOpen j
  change x ∈ (H.target j).opensRange
  exact Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩

/-- A regular generator of the actual ideal of a closed immersion gives the
corresponding explicit basis of sections of its ideal module.  In particular,
the basis vector maps to the chosen defining equation under the canonical
inclusion into the structure sheaf. -/
noncomputable def closedImmersionModule_affineSectionsLinearEquivPrincipal
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (V : X.affineOpens) (z : Γ(X, V.1)) (hz : IsRegular z)
    (hprincipal : f.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1))) :
    letI : Module (Γ(X, V.1))
        ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
          (Opposite.op V.1)) := by
      change Module ((X.ringCatSheaf.obj).obj (Opposite.op V.1))
        ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
          (Opposite.op V.1))
      infer_instance
    Γ(X, V.1) ≃ₗ[Γ(X, V.1)]
      (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op V.1) := by
  letI : Module (Γ(X, V.1))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op V.1)) := by
    change Module ((X.ringCatSheaf.obj).obj (Opposite.op V.1))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op V.1))
    infer_instance
  let e₂ := IdealSheafDataModule.closedImmersionModule_affineSectionsLinearEquivIdeal f V
  have e₂' : Ideal.span ({z} : Set Γ(X, V.1)) ≃ₗ[Γ(X, V.1)]
      (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op V.1) := by
    rw [← hprincipal]
    exact e₂.symm
  exact (regularPrincipalIdealLinearEquiv z hz).trans e₂'

/-- The canonical inclusion of the closed-immersion ideal module commutes
with restriction of a section to a smaller open. -/
theorem closedImmersionModuleToUnit_restrict
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    {U V : X.Opens} (hVU : V ≤ U)
    (t : (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
      (Opposite.op U)) :
    ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
      (Opposite.op V))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.map
        (homOfLE hVU).op t) =
    X.presheaf.map (homOfLE hVU).op
      (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op U)) t) := by
  let φ := IdealSheafDataModule.closedImmersionModuleToUnit f
  have hnat := φ.val.naturality (homOfLE hVU).op
  have hnat' := ConcreteCategory.congr_hom hnat t
  exact hnat'

/-- The local structure-sheaf morphism defined by a section of the actual
closed-immersion ideal module has, on every smaller open, precisely the
restriction of that section's image in the ambient structure sheaf. -/
theorem closedImmersionModule_sectionOnOpenHom_restrict_image
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (U : X.Opens)
    (t : (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
      (Opposite.op U)) (V : (U : Scheme.{u}).Opens) :
    let hVU : U.ι ''ᵁ V ≤ U := by
      simpa only [U.ι_image_top] using
        (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))
    let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
    ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
      (Opposite.op (U.ι ''ᵁ V)))
      ((M.restrictAppIso U.ι V).hom
        (((schemeModuleSectionOnOpenHom M U t).val.app
          (Opposite.op V)) (1 : Γ((U : Scheme.{u}), V)))) =
    X.presheaf.map (homOfLE hVU).op
      (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op U)) t) := by
  dsimp only
  let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
  let hVU : U.ι ''ᵁ V ≤ U := by
    simpa only [U.ι_image_top] using
      (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))
  have h := schemeModuleSectionOnOpenHom_restrict_value' M U t V
  have h' := congrArg
    (fun m => ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
      (Opposite.op (U.ι ''ᵁ V))) m) h
  exact h'.trans (closedImmersionModuleToUnit_restrict f hVU t)

/-- Restrict the actual ideal-module inclusion along an open immersion,
then identify the restricted structure sheaf with the structure sheaf
of the open subscheme. -/
noncomputable def closedImmersionModuleRestrictToUnit
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) :
    (show X.Modules from IdealSheafDataModule.closedImmersionModule f).restrict U.ι ⟶
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
  (Scheme.Modules.restrictFunctor U.ι).map
    (IdealSheafDataModule.closedImmersionModuleToUnit f) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom

/-- On a smaller open, the restricted inclusion is the original inclusion
followed by the open immersion's structure-ring isomorphism. -/
theorem closedImmersionModuleRestrictToUnit_apply
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) (V : (U : Scheme.{u}).Opens)
    (m : ((show X.Modules from IdealSheafDataModule.closedImmersionModule f).restrict
      U.ι).presheaf.obj (Opposite.op V)) :
    ((closedImmersionModuleRestrictToUnit f U).val.app (Opposite.op V)) m =
      (U.ι.appIso V).hom
        (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
          (Opposite.op (U.ι ''ᵁ V)))
          (((show X.Modules from IdealSheafDataModule.closedImmersionModule f).restrictAppIso
            U.ι V).hom m)) := by
  rfl

/-- The restricted ideal-module inclusion is injective on every open
whose image is affine in the ambient scheme. -/
theorem closedImmersionModuleRestrictToUnit_injective_at_affine
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) (V : (U : Scheme.{u}).Opens)
    (hV : IsAffineOpen (U.ι ''ᵁ V)) :
    Function.Injective
      (((closedImmersionModuleRestrictToUnit f U).val.app (Opposite.op V)).hom) := by
  let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
  let W : X.affineOpens := ⟨U.ι ''ᵁ V, hV⟩
  intro a b hab
  have h₁ : (U.ι.appIso V).hom
      (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op W.1)) ((M.restrictAppIso U.ι V).hom a)) =
      (U.ι.appIso V).hom
      (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op W.1)) ((M.restrictAppIso U.ι V).hom b)) := by
    exact (closedImmersionModuleRestrictToUnit_apply f U V a).symm.trans
      (hab.trans (closedImmersionModuleRestrictToUnit_apply f U V b))
  have h₂ := (ConcreteCategory.bijective_of_isIso (U.ι.appIso V).hom).1 h₁
  apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso U.ι V).hom).1
  apply (IdealSheafDataModule.closedImmersionModule_affineSectionsLinearEquivIdeal f W).injective
  apply Subtype.ext
  exact h₂

/-- An affine component of a local structure-sheaf-to-ideal-module map is
an isomorphism when the ambient immersion ideal has a regular generator
there and the map sends `1` to that generator. This form works directly
for the ideal module restricted to an open subscheme. -/
theorem closedImmersionModule_restrictedAffineGeneratorHom_isIso
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) (V : (U : Scheme.{u}).Opens)
    (hV : IsAffineOpen (U.ι ''ᵁ V))
    (z : Γ(X, U.ι ''ᵁ V))
    (hz : IsRegular ((U.ι.appIso V).hom z))
    (hprincipal : f.ker.ideal (⟨U.ι ''ᵁ V, hV⟩ : X.affineOpens) =
      Ideal.span ({z} : Set Γ(X, U.ι ''ᵁ V)))
    (φ : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ⟶
      (show X.Modules from IdealSheafDataModule.closedImmersionModule f).restrict U.ι)
    (himage : ((closedImmersionModuleRestrictToUnit f U).val.app (Opposite.op V))
        (φ.val.app (Opposite.op V) (1 : Γ((U : Scheme.{u}), V))) =
      (U.ι.appIso V).hom z) :
    IsIso (φ.val.app (Opposite.op V)) := by
  let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
  let W : X.affineOpens := ⟨U.ι ''ᵁ V, hV⟩
  let e := U.ι.appIso V
  let ψ := closedImmersionModuleRestrictToUnit f U
  let q : Γ((U : Scheme.{u}), V) →ₗ[Γ((U : Scheme.{u}), V)]
      Γ((U : Scheme.{u}), V) :=
    (φ.val.app (Opposite.op V) ≫ ψ.val.app (Opposite.op V)).hom
  have hq1 : q 1 = e.hom z := himage
  have hq (a : Γ((U : Scheme.{u}), V)) : q a = a * e.hom z := by
    calc
      q a = q (a • (1 : Γ((U : Scheme.{u}), V))) := by simp [smul_eq_mul]
      _ = a • q 1 := q.map_smul a 1
      _ = a * e.hom z := by rw [hq1]; rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    have hh : q a = q b := congrArg (fun m => ψ.val.app (Opposite.op V) m) hab
    let aR : Γ((U : Scheme.{u}), V) := a
    let bR : Γ((U : Scheme.{u}), V) := b
    have hhR : q aR = q bR := hh
    rw [hq, hq] at hhR
    exact hz.right hhR
  · intro m
    let mX := (M.restrictAppIso U.ι V).hom m
    have hy : (show Γ(X, W.1) from
        ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
          (Opposite.op W.1)) mX) ∈ Ideal.span ({z} : Set Γ(X, W.1)) := by
      rw [← hprincipal]
      exact IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal f W mX
    obtain ⟨aX, ha⟩ := Ideal.mem_span_singleton.mp hy
    let aU : Γ((U : Scheme.{u}), V) := e.hom aX
    refine ⟨aU, ?_⟩
    apply closedImmersionModuleRestrictToUnit_injective_at_affine f U V hV
    change q aU = (show Γ((U : Scheme.{u}), V) from ψ.val.app (Opposite.op V) m)
    rw [hq]
    calc
      aU * e.hom z = e.hom (z * aX) := by simp [aU, mul_comm]
      _ = e.hom (show Γ(X, W.1) from
          ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
            (Opposite.op W.1)) mX) := congrArg e.hom ha.symm
      _ = (show Γ((U : Scheme.{u}), V) from ψ.val.app (Opposite.op V) m) :=
        (closedImmersionModuleRestrictToUnit_apply f U V m).symm

/-- The chart equation has a lift to the actual ideal module, and that same
equation generates the kernel ideal on every smaller affine open.  This
packages the section and restriction data needed for a sheaf morphism. -/
theorem RegularPrincipalImmersion.exists_closedImmersionModule_chart_generator
    {X Z : Scheme.{u}} {f : Z ⟶ X} [IsClosedImmersion f]
    (H : RegularPrincipalImmersion f) (j : H.Index)
    [IsOpenImmersion (H.target j)] :
    let W : (Spec (H.A j)).affineOpens :=
      ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
    let U : X.affineOpens :=
      ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
    ∃ (z : Γ(X, U.1))
      (t : (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op U.1)),
      IsRegular z ∧
      ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op U.1)) t = z ∧
      ∀ (V : X.affineOpens) (hVU : V.1 ≤ U.1),
        ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
          (Opposite.op V.1))
          ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.map
            (homOfLE hVU).op t) =
            X.presheaf.map (homOfLE hVU).op z ∧
        f.ker.ideal V =
          Ideal.span ({X.presheaf.map (homOfLE hVU).op z} : Set Γ(X, V.1)) := by
  dsimp only
  let W : (Spec (H.A j)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
  let U : X.affineOpens :=
    ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  obtain ⟨z, hz, hgen⟩ := H.idealSheaf_affineOpen_generatesOnSubopens j
  have hzmem : z ∈ f.ker.ideal U := by
    rw [hgen U le_rfl]
    have hmap : X.presheaf.map (homOfLE (le_refl U.1)).op z = z := by simp
    rw [hmap]
    exact Ideal.subset_span (Set.mem_singleton z)
  obtain ⟨t, ht⟩ :=
    IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem
      f U z hzmem
  refine ⟨z, t, hz, ht, ?_⟩
  intro V hVU
  constructor
  · rw [closedImmersionModuleToUnit_restrict, ht]
  · exact hgen V hVU

/-- The local morphism from the structure sheaf to the actual ideal module
induced by a regular-principal chart's defining section. -/
noncomputable def RegularPrincipalImmersion.chartIdealModuleHom
    {X Z : Scheme.{u}} {f : Z ⟶ X} [IsClosedImmersion f]
    (H : RegularPrincipalImmersion f) (j : H.Index)
    [IsOpenImmersion (H.target j)] :
    let W : (Spec (H.A j)).affineOpens :=
      ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
    let U : X.affineOpens :=
      ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
    SheafOfModules.unit (U.1 : Scheme.{u}).ringCatSheaf ⟶
      (show X.Modules from
        IdealSheafDataModule.closedImmersionModule f).restrict U.1.ι := by
  dsimp only
  let W : (Spec (H.A j)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
  let U : X.affineOpens :=
    ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  let data := H.exists_closedImmersionModule_chart_generator j
  let z := Classical.choose data
  let t := Classical.choose (Classical.choose_spec data)
  exact schemeModuleSectionOnOpenHom
    (IdealSheafDataModule.closedImmersionModule f) U.1 t

/-- On an affine open, a map from the structure sheaf to the actual ideal
module is an isomorphism as soon as its value at `1` maps to a regular
generator of the immersion's kernel ideal. -/
theorem closedImmersionModule_affineGeneratorHom_isIso
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (V : X.affineOpens) (z : Γ(X, V.1)) (hz : IsRegular z)
    (hprincipal : f.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1)))
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶
      IdealSheafDataModule.closedImmersionModule f)
    (himage : ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
      (Opposite.op V.1)) (φ.val.app (Opposite.op V.1) (1 : Γ(X, V.1))) = z) :
    IsIso (φ.val.app (Opposite.op V.1)) := by
  let q : Γ(X, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1) :=
    (φ.val.app (Opposite.op V.1) ≫
      (IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op V.1)).hom
  have hq1 : q 1 = z := himage
  have hq (a : Γ(X, V.1)) : q a = a * z := by
    calc
      q a = q (a • (1 : Γ(X, V.1))) := by simp [smul_eq_mul]
      _ = a • q 1 := q.map_smul a 1
      _ = a * z := by rw [hq1]; rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    have hh : q a = q b := congrArg
      (fun m => ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op V.1)) m) hab
    let aR : Γ(X, V.1) := a
    let bR : Γ(X, V.1) := b
    have hhR : q aR = q bR := hh
    rw [hq, hq] at hhR
    exact hz.right hhR
  · intro m
    have hy : (show Γ(X, V.1) from
        ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
          (Opposite.op V.1)) m) ∈ Ideal.span ({z} : Set Γ(X, V.1)) := by
      rw [← hprincipal]
      exact IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal f V m
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    let aR : Γ(X, V.1) := a
    refine ⟨aR, ?_⟩
    apply (IdealSheafDataModule.closedImmersionModule_affineSectionsLinearEquivIdeal f V).injective
    apply Subtype.ext
    change q aR = ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
      (Opposite.op V.1)) m
    rw [hq]
    calc
      aR * z = z * aR := mul_comm aR z
      _ = _ := ha.symm

/-- On each affine open from a regular-principal presentation of a closed
immersion, the actual closed-immersion ideal module has free rank-one
sections over the structure ring of that open. -/
theorem RegularPrincipalImmersion.closedImmersionModule_affineOpen_free
    {X Z : Scheme.{u}} {f : Z ⟶ X} [IsClosedImmersion f]
    (H : RegularPrincipalImmersion f) (j : H.Index)
    [IsOpenImmersion (H.target j)] :
    let W : (Spec (H.A j)).affineOpens :=
      ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
    let U : X.affineOpens :=
      ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
    letI : Module (Γ(X, U.1))
        ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
          (Opposite.op U.1)) := by
      change Module ((X.ringCatSheaf.obj).obj (Opposite.op U.1))
        ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
          (Opposite.op U.1))
      infer_instance
    Module.Free (Γ(X, U.1))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op U.1)) := by
  let W : (Spec (H.A j)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
  let U : X.affineOpens :=
    ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  letI : Module (Γ(X, U.1))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op U.1)) := by
    change Module ((X.ringCatSheaf.obj).obj (Opposite.op U.1))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op U.1))
    infer_instance
  obtain ⟨z, hz, hprincipal⟩ := H.idealSheaf_affineOpen_regularPrincipal j
  have e : Γ(X, U.1) ≃ₗ[Γ(X, U.1)]
      (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op U.1) :=
    closedImmersionModule_affineSectionsLinearEquivPrincipal f U z hz hprincipal
  exact Module.Free.of_equiv e

/-- The actual ideal module has free rank-one sections on every principal
affine open inside each regular-principal chart. -/
theorem RegularPrincipalImmersion.closedImmersionModule_basicOpen_free
    {X Z : Scheme.{u}} {f : Z ⟶ X} [IsClosedImmersion f]
    (H : RegularPrincipalImmersion f) (j : H.Index)
    [IsOpenImmersion (H.target j)] :
    let W : (Spec (H.A j)).affineOpens :=
      ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
    let U : X.affineOpens :=
      ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
    ∀ r : Γ(X, U.1),
      let V : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
      letI : Module (Γ(X, V.1))
          ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
            (Opposite.op V.1)) := by
        change Module ((X.ringCatSheaf.obj).obj (Opposite.op V.1))
          ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
            (Opposite.op V.1))
        infer_instance
      Module.Free (Γ(X, V.1))
        ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
          (Opposite.op V.1)) := by
  dsimp only
  let W : (Spec (H.A j)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
  let U : X.affineOpens :=
    ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  obtain ⟨z, hz, hgen⟩ := H.idealSheaf_affineOpen_generatesOnSubopens j
  intro r
  let V : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
  letI : Module (Γ(X, V.1))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op V.1)) := by
    change Module ((X.ringCatSheaf.obj).obj (Opposite.op V.1))
      ((IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
        (Opposite.op V.1))
    infer_instance
  have hreg : IsRegular (X.presheaf.map (homOfLE (X.basicOpen_le r)).op z) :=
    isRegular_affineBasicOpen_restriction U.1 U.2 r z hz
  have hideal := hgen V (X.basicOpen_le r)
  exact Module.Free.of_equiv
    (closedImmersionModule_affineSectionsLinearEquivPrincipal f V _ hreg hideal)


/-- A regular principal equation on an affine open trivializes the actual
closed-immersion ideal module as a sheaf on that open. -/
theorem closedImmersionModule_sectionOnAffineOpen_isIso {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (U : X.affineOpens) (z : Γ(X,U.1)) (hz : IsRegular z)
    (hgen : ∀ (W : X.affineOpens) (hWU : W.1 ≤ U.1),
      f.ker.ideal W = Ideal.span
        ({X.presheaf.map (homOfLE hWU).op z} : Set Γ(X,W.1)))
    (t : (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
      (Opposite.op U.1))
    (ht : ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
      (Opposite.op U.1)) t = z) :
    IsIso (schemeModuleSectionOnOpenHom
      (IdealSheafDataModule.closedImmersionModule f) U.1 t) := by
  let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
  let φ := schemeModuleSectionOnOpenHom M U.1 t
  apply schemeModuleHom_isIso_of_basis
    (SheafOfModules.unit (U.1 : Scheme.{u}).ringCatSheaf)
    (M.restrict U.1.ι) φ
    ((U.1 : Scheme.{u}).basicOpen)
    (isBasis_basicOpen (U.1 : Scheme.{u}))
  intro r
  let V : (U.1 : Scheme.{u}).Opens := (U.1 : Scheme.{u}).basicOpen r
  let rX : Γ(X,U.1) := U.1.topIso.hom r
  have hr0 := U.1.ι_image_basicOpen_topIso_inv rX
  have he := ConcreteCategory.congr_hom U.1.topIso.hom_inv_id r
  change U.1.topIso.inv (U.1.topIso.hom r) = r at he
  have hr : U.1.ι ''ᵁ V = X.basicOpen rX := by
    simpa only [V, rX, he] using hr0
  have hV : IsAffineOpen (U.1.ι ''ᵁ V) := by
    rw [hr]
    exact U.2.basicOpen rX
  let W : X.affineOpens := ⟨U.1.ι ''ᵁ V, hV⟩
  let hWU : W.1 ≤ U.1 := by
    simpa only [U.1.ι_image_top] using
      (Scheme.Hom.image_mono U.1.ι (show V ≤ ⊤ from le_top))
  let zW : Γ(X,W.1) := X.presheaf.map (homOfLE hWU).op z
  have hprincipal : f.ker.ideal W = Ideal.span ({zW} : Set Γ(X,W.1)) :=
    hgen W hWU
  have hzW : IsRegular zW := by
    have hreg := isRegular_affineBasicOpen_restriction U.1 U.2 rX z hz
    have hreg_of_eq (T : X.Opens) (hT : T = X.basicOpen rX)
        (hTU : T ≤ U.1) :
        IsRegular (X.presheaf.map (homOfLE hTU).op z) := by
      subst T
      simpa only [Subsingleton.elim hTU (X.basicOpen_le rX)] using hreg
    exact hreg_of_eq W.1 hr hWU
  have hzV : IsRegular ((U.1.ι.appIso V).hom zW) := by
    let e := (U.1.ι.appIso V).commRingCatIsoToRingEquiv
    apply isRegular_of_injective_ringHom e.symm.toRingHom e.symm.injective
    change IsRegular (e.symm (e zW))
    rw [e.symm_apply_apply]
    exact hzW
  have hvalue : ((closedImmersionModuleRestrictToUnit f U.1).val.app
      (Opposite.op V)) (φ.val.app (Opposite.op V)
      (1 : Γ((U.1 : Scheme.{u}),V))) = (U.1.ι.appIso V).hom zW := by
    let m := φ.val.app (Opposite.op V) (1 : Γ((U.1 : Scheme.{u}),V))
    have h₁ := closedImmersionModuleRestrictToUnit_apply f U.1 V m
    have h₂ := closedImmersionModule_sectionOnOpenHom_restrict_image f U.1 t V
    have h₂' := congrArg (fun y => (U.1.ι.appIso V).hom y) h₂
    change ((U.1.ι.appIso V).hom
      (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
        (Opposite.op W.1)) ((M.restrictAppIso U.1.ι V).hom m))) =
      (U.1.ι.appIso V).hom
        (X.presheaf.map (homOfLE hWU).op
          (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
            (Opposite.op U.1)) t)) at h₂'
    rw [ht] at h₂'
    exact h₁.trans h₂'
  exact closedImmersionModule_restrictedAffineGeneratorHom_isIso
    f U.1 V hV zW hzV hprincipal φ hvalue

/-- Every regular-principal chart gives a sheaf-level trivialization of
the actual closed-immersion ideal module. -/
theorem RegularPrincipalImmersion.chartIdealModuleHom_isIso
    {X Z : Scheme.{u}} {f : Z ⟶ X} [IsClosedImmersion f]
    (H : RegularPrincipalImmersion f) (j : H.Index)
    [IsOpenImmersion (H.target j)] :
    IsIso (H.chartIdealModuleHom j) := by
  let W : (Spec (H.A j)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
  let U : X.affineOpens :=
    ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  let data := H.exists_closedImmersionModule_chart_generator j
  let z := Classical.choose data
  let t := Classical.choose (Classical.choose_spec data)
  have hdata := Classical.choose_spec (Classical.choose_spec data)
  obtain ⟨hz, ht, hrest⟩ := hdata
  have hgen (V : X.affineOpens) (hVU : V.1 ≤ U.1) :
      f.ker.ideal V = Ideal.span
        ({X.presheaf.map (homOfLE hVU).op z} : Set Γ(X,V.1)) :=
    (hrest V hVU).2
  exact closedImmersionModule_sectionOnAffineOpen_isIso f U z hz hgen t ht


end PfaffianDescent
