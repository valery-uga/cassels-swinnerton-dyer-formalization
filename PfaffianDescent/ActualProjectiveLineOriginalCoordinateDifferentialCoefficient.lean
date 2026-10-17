import Lean.Meta.Tactic.Replace
import Lean.Meta.Transform
import PfaffianDescent.ActualProjectiveLinePolynomialChartImageCoordinateNormalization
import PfaffianDescent.ActualProjectiveLinePolynomialChartDifferentialSectionComparison
import PfaffianDescent.ActualOneVariableAffineDifferentialFrameAction

/- SOURCE ONLY. Original P1 named differential coefficient in the SAME actual
native restriction chart; no supplied generator or differential-comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary open equality carries the genuine universal differential of the
SAME original ring section, with no equality of differential maps as premise. -/
theorem actualRelativeDifferentialSection_eqToHom
    {K : Type u} [CommRing K] {X : Scheme.{u}} (g : X ⟶ Spec (.of K))
    {V U : X.Opens} (h : V = U) (r : Γ(X, U)) :
    actualRelativeDifferentialSection g V (X.presheaf.map (eqToHom h).op r) =
      (schemeRelativeDifferentials g).val.map (eqToHom h).op
        (actualRelativeDifferentialSection g U r) := by
  cases h
  exact (actualRelativeDifferentialSection_restrict g le_rfl r).symm

/-- Abstract affine native evaluation; the scalar change alters the module
structure, while keeping this SAME top-section function. -/
private theorem originalAffineNativeMap_top_apply
    {R : Type u} [CommRing R] {M N : (Spec (.of R)).Modules}
    (f : M ⟶ N) (x : M.val.obj (op ⊤)) :
    (moduleSpecΓFunctor (R := .of R)).map f x = f.val.app (op ⊤) x := by
  rfl

/-- Abstract affine unit inverse; the installed linear equivalence uses the
SAME original Gamma-Spec inverse function. -/
private theorem originalAffineNativeUnit_inverse_value
    {R : Type u} [CommRing R] (r : R) :
    (affineGlobalSectionsUnitLinearEquiv (A := R)).symm r =
      (Scheme.ΓSpecIso (.of R)).inv.hom r := by
  rfl

/-- Separate the native affine coefficient action from insertion of the
original P1 chart, open-equality and entire frame-chain factories. -/
private theorem originalAffineFrameCoefficient_native
    {K : Type u} [CommRing K] {σ : Type} [Subsingleton σ] (a : σ) :
    (actualOneVariableAffineDifferentialFrameIso (K := K) a).hom.val.app (op ⊤)
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))) ⊤
        ((Scheme.ΓSpecIso (.of (MvPolynomial σ K))).inv.hom (MvPolynomial.X a))) =
      (1 : Γ(Spec (.of (MvPolynomial σ K)), ⊤)) := by
  calc
    _ = (moduleSpecΓFunctor (R := .of (MvPolynomial σ K))).map
        (actualOneVariableAffineDifferentialFrameIso (K := K) a).hom
        (actualRelativeDifferentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))) ⊤
          ((Scheme.ΓSpecIso (.of (MvPolynomial σ K))).inv.hom (MvPolynomial.X a))) :=
      (originalAffineNativeMap_top_apply _ _).symm
    _ = (affineGlobalSectionsUnitLinearEquiv (A := MvPolynomial σ K)).symm 1 :=
      actualOneVariableAffineDifferentialFrameIso_D (K := K) a
    _ = (Scheme.ΓSpecIso (.of (MvPolynomial σ K))).inv.hom 1 :=
      originalAffineNativeUnit_inverse_value 1
    _ = _ := map_one _

/-- Carry equality of an abstract original input through the genuine
inverse open-differential map before inserting any P1 coordinate factories. -/
private theorem originalInverseDifferentialCarry009
    {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (V : Y.Opens) (r : Γ(Y, V))
    (z : (schemeRelativeDifferentials g).val.obj (op (f ''ᵁ V)))
    (hz : z = actualRelativeDifferentialSection g (f ''ᵁ V) ((f.appIso V).inv r)) :
    (actualOpenImmersionDifferentialSheafRestrictionIso f g).inv.val.app (op V) z =
      actualRelativeDifferentialSection (f ≫ g) V r := by
  exact (congrArg
    (fun w : (schemeRelativeDifferentials g).val.obj (op (f ''ᵁ V)) =>
      (actualOpenImmersionDifferentialSheafRestrictionIso f g).inv.val.app (op V) w) hz).trans
    (actualOpenImmersionDifferentialSheafIso_inverse_section_D f g V r)

/-- Evaluate a two-frame chain while all native objects/maps are abstract. -/
private theorem nativeOriginalTwoFrameChain_apply017
    {X : Scheme.{u}} {M N : X.Modules}
    (a : M ≅ N) (b : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (V : X.Opens) (z : M.val.obj (op V)) :
    (a ≪≫ b).hom.val.app (op V) z =
      b.hom.val.app (op V) (a.hom.val.app (op V) z) := by
  let F := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)
  change F.map (a ≪≫ b).hom z = F.map b.hom (F.map a.hom z)
  simp only [Iso.trans_hom, Functor.map_comp, ModuleCat.comp_apply]

/-- Factor the EXACT ORIGINAL inverse-open/base-equality/affine frame chain
before inserting P1. The actual native eqToIso hom/component is retained. -/
private def nativeOriginalOpenDFrameFactory017
    {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (g' : Y ⟶ Spec (.of K)) (h : f ≫ g = g')
    (c : schemeRelativeDifferentials g' ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor f).obj (schemeRelativeDifferentials g) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm ≪≫
    eqToIso (congrArg (fun k : Y ⟶ Spec (.of K) => schemeRelativeDifferentials k) h) ≪≫ c

/-- Coefficient1 for the WHOLE ORIGINAL native frame, derived over abstract
schemes. The original coordinate identity and affine coefficient are ordinary
intermediate inputs, derived internally at the concrete P1 endpoint below. -/
private theorem nativeOriginalOpenDFrame_coefficient017
    {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (g' : Y ⟶ Spec (.of K)) (h : f ≫ g = g')
    (V : Y.Opens) (r : Γ(Y, V))
    (c : schemeRelativeDifferentials g' ≅ SheafOfModules.unit Y.ringCatSheaf)
    (z : (schemeRelativeDifferentials g).val.obj (op (f ''ᵁ V)))
    (hz : z = actualRelativeDifferentialSection g (f ''ᵁ V) ((f.appIso V).inv r))
    (hc : c.hom.val.app (op V) (actualRelativeDifferentialSection g' V r) =
      (1 : Γ(Y, V))) :
    (nativeOriginalOpenDFrameFactory017 f g g' h c).hom.val.app (op V) z =
      (1 : Γ(Y, V)) := by
  cases h
  have hi := originalInverseDifferentialCarry009 f g V r z hz
  have hv := nativeOriginalTwoFrameChain_apply017
    (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm c V z
  have he := hv.trans ((congrArg (fun w => c.hom.val.app (op V) w) hi).trans hc)
  simpa only [nativeOriginalOpenDFrameFactory017, eqToIso_refl, Iso.trans_refl,
    Iso.refl_trans] using he

/-- The SAME original native frame and its computed coordinate law, stored
under one constructor head. The value is the exact inverse-open/eqToIso/affine
chain; no frame or coefficient outcome is assumed at the concrete endpoint. -/
private def nativeOriginalOpenDFrameData019
    {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (g' : Y ⟶ Spec (.of K)) (h : f ≫ g = g')
    (V : Y.Opens) (r : Γ(Y, V))
    (c : schemeRelativeDifferentials g' ≅ SheafOfModules.unit Y.ringCatSheaf)
    (z : (schemeRelativeDifferentials g).val.obj (op (f ''ᵁ V)))
    (hz : z = actualRelativeDifferentialSection g (f ''ᵁ V) ((f.appIso V).inv r))
    (hc : c.hom.val.app (op V) (actualRelativeDifferentialSection g' V r) =
      (1 : Γ(Y, V))) :
    { e : (Scheme.Modules.restrictFunctor f).obj (schemeRelativeDifferentials g) ≅
        SheafOfModules.unit Y.ringCatSheaf //
      e.hom.val.app (op V) z = (1 : Γ(Y, V)) } :=
  ⟨nativeOriginalOpenDFrameFactory017 f g g' h c,
    nativeOriginalOpenDFrame_coefficient017 f g g' h V r c z hz hc⟩

/-- Use the EXISTING native restriction carrier Iso; it does not change
the underlying section and does not introduce a module scalar comparison. -/
private def originalRestrictionInputCarrier026
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : Y.Opens) (z : M.val.obj (op (f ''ᵁ V))) :
    ((Scheme.Modules.restrictFunctor f).obj M).val.obj (op V) :=
  (M.restrictAppIso f V).inv z

/-- The native restriction Iso gives EXACTLY the original section value.
This proposition contains no coordinate, differential frame or scalar one. -/
private theorem originalRestrictionInputCarrier026_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : Y.Opens) (z : M.val.obj (op (f ''ᵁ V))) :
    originalRestrictionInputCarrier026 f M V z = z := rfl

/-- ORIGINAL Gamma value in the native unit ModuleCat carrier. Only the
unit's existing section carrier is used; no affine ΓSpec equivalence is inserted. -/
private def originalGammaToUnitCarrier026
    (Y : Scheme.{u}) (V : Y.Opens) (r : Γ(Y, V)) :
    (SheafOfModules.unit Y.ringCatSheaf).val.obj (op V) := r

/-- Carrier comparison only, at ABSTRACT scheme/open/section arguments. -/
private theorem originalGammaToUnitCarrier026_eq
    (Y : Scheme.{u}) (V : Y.Opens) (r : Γ(Y, V)) :
    (show Γ(Y, V) from originalGammaToUnitCarrier026 Y V r) = r := rfl

/-- The ACTUAL native ModuleCat arrow's underlying linear-map function.
Only the installed Ring dictionary is needed; no new CommRing or scalar action. -/
private def originalNativeArrowFunction027
    {R : Type u} [Ring R] {M N : ModuleCat R} (a : M ⟶ N) :
    M.carrier → N.carrier := a.hom'.toFun

/-- Function/coercion comparison at ABSTRACT native ModuleCat arguments. -/
private theorem originalNativeArrowFunction027_apply
    {R : Type u} [Ring R] {M N : ModuleCat R} (a : M ⟶ N) (x : M) :
    originalNativeArrowFunction027 a x = a x := rfl

/-- Native sheaf component as a plain function between the SAME carriers. -/
private def originalNativeComponentFunction027
    {Y : Scheme.{u}} {M N : Y.Modules} (a : M ⟶ N) (V : Y.Opens) :
    (M.val.obj (op V)).carrier → (N.val.obj (op V)).carrier :=
  originalNativeArrowFunction027 (a.val.app (op V))

private theorem originalNativeComponentFunction027_apply
    {Y : Scheme.{u}} {M N : Y.Modules} (a : M ⟶ N) (V : Y.Opens)
    (x : M.val.obj (op V)) :
    originalNativeComponentFunction027 a V x = a.val.app (op V) x := rfl

/-- Composition agrees with the ORIGINAL two native component actions,
proved before any concrete differential/module dictionary is inserted. -/
private theorem originalNativeComponentPairFunction027_apply
    {Y : Scheme.{u}} {M N T : Y.Modules}
    (a : M ⟶ N) (c : N ⟶ T) (V : Y.Opens) (x : M.val.obj (op V)) :
    (originalNativeComponentFunction027 c V ∘
      originalNativeComponentFunction027 a V) x =
        c.val.app (op V) (a.val.app (op V) x) := rfl

/-- Equality of native frame functions, with NO coordinate/value inserted. -/
private theorem originalNativeThreeFrameFunction027_comp
    {Y : Scheme.{u}} {M N T : Y.Modules}
    (a : M ≅ N) (b : N ≅ T)
    (c : T ≅ SheafOfModules.unit Y.ringCatSheaf) (V : Y.Opens) :
    originalNativeComponentFunction027 (a ≪≫ b ≪≫ c).hom V =
      originalNativeComponentFunction027 c.hom V ∘
        (originalNativeComponentFunction027 b.hom V ∘
          originalNativeComponentFunction027 a.hom V) := by
  funext z
  let F := Scheme.Modules.toPresheafOfModules Y ⋙
    PresheafOfModules.evaluation Y.ringCatSheaf.obj (op V)
  change F.map (a ≪≫ b ≪≫ c).hom z =
    F.map c.hom (F.map b.hom (F.map a.hom z))
  simp only [Iso.trans_hom, Functor.map_comp, ModuleCat.comp_apply]

/-- Ordinary function composition of SEPARATELY derived coefficients.
This boundary contains no native categories, module dictionaries or factories. -/
private theorem originalPlainFunctionCoefficient027
    {A B C : Type u} (f : A → B) (g : B → C) (x : A) (y : B) (z : C)
    (hf : f x = y) (hg : g y = z) : (g ∘ f) x = z :=
  (congrArg g hf).trans hg

/-- Compare ONLY original values through fixed plain functions. -/
private theorem originalPlainFunctionValueTransport027
    {A B : Type u} (f : A → B) (x x' : A) (y y' : B)
    (hx : x = x') (hy : y = y') (h : f x = y) : f x' = y' :=
  (congrArg f hx).symm.trans (h.trans hy)

/-- Point-FREE field/DFunLike equality with every linear-map dictionary
fixed before a native categorical object or original frame is substituted. -/
private theorem originalLinearMapPointFree032
    (R : Type u) [s : Ring R] (A B : Type u)
    [gA : AddCommGroup A] [gB : AddCommGroup B]
    [mA : Module R A] [mB : Module R B] (l : A →ₗ[R] B) :
    l.toFun = (l : A → B) := rfl

/-- Point-FREE native Hom comparison with IDENTICAL explicit R/s/M/N.
The same native AddCommGroup/Module fields are supplied on both sides. -/
private theorem originalModuleCatPointFree032
    (R : Type u) [s : Ring R] (M N : @ModuleCat.{u, u} R s)
    (a : @ModuleCat.Hom R s M N) :
    @originalNativeArrowFunction027 R s M N a =
      ((show M ⟶ N from a) : @ModuleCat.carrier R s M → @ModuleCat.carrier R s N) :=
  @originalLinearMapPointFree032 R s
    (@ModuleCat.carrier R s M) (@ModuleCat.carrier R s N)
    (@ModuleCat.isAddCommGroup R s M) (@ModuleCat.isAddCommGroup R s N)
    (@ModuleCat.isModule R s M) (@ModuleCat.isModule R s N)
    (@ModuleCat.Hom.hom' R s M N a)

/-- Direct explicit-native-arrow coefficient for the ORIGINAL three-Iso
chain, computed while the native objects/dictionaries and input are ABSTRACT.
No actual raw/public whole-function conversion enters its concrete endpoint. -/
private theorem originalThreeFrameExplicitArrowCoefficient034
    {Y : Scheme.{u}} {M N T : Y.Modules}
    (a : M ≅ N) (b : N ≅ T)
    (c : T ≅ SheafOfModules.unit Y.ringCatSheaf) (V : Y.Opens)
    (x : M.val.obj (op V)) (y : T.val.obj (op V))
    (z : (SheafOfModules.unit Y.ringCatSheaf).val.obj (op V))
    (hab : (originalNativeComponentFunction027 b.hom V ∘
        originalNativeComponentFunction027 a.hom V) x = y)
    (hc : originalNativeComponentFunction027 c.hom V y = z) :
    @originalNativeArrowFunction027
      (Y.ringCatSheaf.obj.obj (op V)).carrier
      (Y.ringCatSheaf.obj.obj (op V)).ring
      (M.val.obj (op V))
      ((SheafOfModules.unit Y.ringCatSheaf).val.obj (op V))
      ((a ≪≫ b ≪≫ c).hom.val.app (op V)) x = z :=
  (congrFun (originalNativeThreeFrameFunction027_comp a b c V) x).trans
    (originalPlainFunctionCoefficient027
      (originalNativeComponentFunction027 b.hom V ∘
        originalNativeComponentFunction027 a.hom V)
      (originalNativeComponentFunction027 c.hom V) x y z hab hc)

/-- Shared explicit ModuleCat R/s/M/N/a dictionary: use the PASSED
point-FREE equality before values are supplied. The original native arrow is
viewed as the SAME categorical arrow before public CoeFun, never raw Hom. -/
private theorem originalSharedArrowNativeCoefficient034
    (R : Type u) [s : Ring R] (M N : @ModuleCat.{u, u} R s)
    (a : @ModuleCat.Hom R s M N) (x : M) (y : N)
    (h : @originalNativeArrowFunction027 R s M N a x = y) :
    (show M ⟶ N from a) x = y :=
  (congrFun (@originalModuleCatPointFree032 R s M N a) x).symm.trans h

/-- ORIGINAL input-value and unit/Gamma-value transport at ABSTRACT
scheme/module arguments. The arrow is already bundled; no raw-function or
ConcreteCategory coercion equality is introduced at the actual endpoint. -/
private theorem originalNativeUnitComponentValueTransport029
    {Y : Scheme.{u}} {M : Y.Modules}
    (a : M ⟶ SheafOfModules.unit Y.ringCatSheaf) (V : Y.Opens)
    (x x' : M.val.obj (op V))
    (y : (SheafOfModules.unit Y.ringCatSheaf).val.obj (op V)) (r : Γ(Y, V))
    (hx : x = x') (hy : (show Γ(Y, V) from y) = r)
    (h : a.val.app (op V) x = y) : a.val.app (op V) x' = r :=
  (congrArg (fun t : M.val.obj (op V) => a.val.app (op V) t) hx).symm.trans
    (h.trans hy)

/-- Transport a RAW native-arrow coefficient through a CATEGORICAL
arrow identity, with R/s/M/N and native input/output fixed ABSTRACTLY.
Neither arrow is converted into a public whole-function wrapper. -/
private theorem originalRawArrowCoefficientTransport036
    (R : Type u) [s : Ring R] (M N : @ModuleCat.{u, u} R s)
    (a b : @ModuleCat.Hom R s M N) (x : M) (y : N)
    (ha : a = b) (hb : @originalNativeArrowFunction027 R s M N b x = y) :
    @originalNativeArrowFunction027 R s M N a x = y :=
  (congrArg (fun t : @ModuleCat.Hom R s M N =>
    @originalNativeArrowFunction027 R s M N t x) ha).trans hb

/-- Infer the SAME native R/s/M/N/composed arrow/input/output FROM the
already checked staged coefficient producer before supplying public arrow.
The ordinary categorical identity is inserted only in a subsequent stage. -/
private theorem originalInferRawTransportFactory038
    {R : Type u} [s : Ring R] {M N : @ModuleCat.{u, u} R s}
    (b : @ModuleCat.Hom R s M N) (x : M) (y : N)
    (hb : @originalNativeArrowFunction027 R s M N b x = y)
    (a : @ModuleCat.Hom R s M N) (ha : a = b) :
    @originalNativeArrowFunction027 R s M N a x = y :=
  @originalRawArrowCoefficientTransport036 R s M N a b x y ha hb

/-- Infer the SAME native arrow/input/output dictionary from a checked RAW
producer. Native categorical action uses the accepted shared-arrow lemma;
no old explicit whole-function header is reconstructed. -/
private theorem originalInferNativeActionFactory038
    {R : Type u} [s : Ring R] {M N : @ModuleCat.{u, u} R s}
    (a : @ModuleCat.Hom R s M N) (x : M) (y : N)
    (h : @originalNativeArrowFunction027 R s M N a x = y) :
    (show M ⟶ N from a) x = y :=
  @originalSharedArrowNativeCoefficient034 R s M N a x y h

/-- Transport the native top-component coefficient along an equality of
SHEAF isomorphisms while the scheme, modules and all native dictionaries are
still ABSTRACT. This diagram does not compare concrete ModuleCat.Hom
representations. The original scalar and carrier values remain variables. -/
private theorem originalNativeIsoCoefficientDiagram039
    {Y : Scheme} {M N : Y.Modules} (V : Y.Opens)
    (e f : M ≅ N) (h : f = e) :
    ∀ (x : (M.val.obj (op V)).carrier) (y : (N.val.obj (op V)).carrier),
      originalNativeArrowFunction027 (e.hom.val.app (op V)) x = y →
      originalNativeArrowFunction027 (f.hom.val.app (op V)) x = y := by
  cases h
  exact fun _ _ he => he

/-- Ordinary function equality transport only. Infer the native function,
source and target carriers from its ALREADY proved coefficient before a new
input is supplied; no Scheme/module/unit-arrow dictionary is reconstructed. -/
private theorem originalOrdinaryCoefficientInputFactory040
    {A B : Type u} (f : A → B) (x : A) (y : B) (h : f x = y)
    {x' : A} (hx : x = x') : f x' = y :=
  (congrArg f hx).symm.trans h

/-- Ordinary output equality transport only. Infer the function and values
from the checked literal-input coefficient before inserting the native-one
to original Gamma-one identity. There is no scalar or carrier action change. -/
private theorem originalOrdinaryCoefficientOutputFactory040
    {A B : Type u} (f : A → B) (x : A) (y : B) (h : f x = y)
    {y' : B} (hy : y = y') : f x = y' :=
  h.trans hy

/-- Leave the replacement input EXPLICIT in the returned ordinary function.
This preserves the passed040 input lemma while preventing Lean from inserting
an unresolved trailing implicit x' when the actual factory is captured. -/
private theorem originalOrdinaryCoefficientInputExplicitFactory041
    {A B : Type u} (f : A → B) (x : A) (y : B) (h : f x = y) :
    ∀ (x' : A), x = x' → f x' = y :=
  fun x' hx => @originalOrdinaryCoefficientInputFactory040 A B f x y h x' hx

/-- Leave the replacement output EXPLICIT for the same reason. The original
passed040 output lemma is fully supplied only inside this abstract function;
no native Scheme/module/frame dictionary is introduced. -/
private theorem originalOrdinaryCoefficientOutputExplicitFactory041
    {A B : Type u} (f : A → B) (x : A) (y : B) (h : f x = y) :
    ∀ (y' : B), y = y' → f x = y' :=
  fun y' hy => @originalOrdinaryCoefficientOutputFactory040 A B f x y h y' hy

attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- The original normalized coordinate differential, transported only along the
proved chart-image equality, is EXACTLY the universal D used by native chart comparison. -/
theorem actualProjectiveLineCoordinateDifferential_eq_chartUniversalD (b : Bool) :
    let f := actualProjectiveLinePolynomialChartToLine K b
    let hU := actualProjectiveLinePolynomialChartToLine_image_top K b
    (schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map (eqToHom hU).op
      (actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (Proj.basicOpen (grading Iline) (coordinate Iline b))
        ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
          (chartCoordinate Iline b (!b)))) =
    actualRelativeDifferentialSection (projectiveLineProjToBase K) (f ''ᵁ ⊤)
      ((f.appIso ⊤).inv
        ((Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
          (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))))) := by
  have h := actualRelativeDifferentialSection_eqToHom
    (X := projectiveLineProj K) (projectiveLineProjToBase K)
    (actualProjectiveLinePolynomialChartToLine_image_top K b)
    ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
      (chartCoordinate Iline b (!b)))
  have hc := congrArg
    (fun r : Γ(projectiveLineProj K,
        actualProjectiveLinePolynomialChartToLine K b ''ᵁ ⊤) =>
      actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (actualProjectiveLinePolynomialChartToLine K b ''ᵁ ⊤) r)
    (actualProjectiveLinePolynomialChartToLine_appIso_inverse_coordinate K b).symm
  exact h.symm.trans hc

/-- A SINGLE actual original frame+law datum. It supplies the same original
coordinate identity and passed affine coefficient internally, using section K. -/
private def actualNativeCoordinateFrameData019 (b : Bool) :=
  letI : Subsingleton {i : Bool // i ≠ b} :=
    (lineProjectiveVariableEquiv b).symm.subsingleton
  nativeOriginalOpenDFrameData019
    (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K))))
    (actualProjectiveLinePolynomialChartToLine_toBase K b) ⊤
    ((Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
      (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))))
    (actualOneVariableAffineDifferentialFrameIso (K := K)
      (lineProjectiveVariableEquiv b (0, 0)))
    ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
      (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
      (actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (Proj.basicOpen (grading Iline) (coordinate Iline b))
        ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
          (chartCoordinate Iline b (!b)))))
    (actualProjectiveLineCoordinateDifferential_eq_chartUniversalD K b)
    (originalAffineFrameCoefficient_native (K := K) (lineProjectiveVariableEquiv b (0, 0)))

/-- Genuine SAME native restriction frame, retaining the actual module scalar
structure instead of replacing it by a pullback/transport certificate. -/
def actualProjectiveLinePolynomialDifferentialRestrictionFrameIso (b : Bool) :
    (Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
      (schemeRelativeDifferentials (projectiveLineProjToBase K)) ≅
      SheafOfModules.unit
        (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf := by
  exact (actualNativeCoordinateFrameData019 K b).val

/-- EXACT original normalized-coordinate differential in the explicit
native source carrier, through the existing identity restriction Iso. -/
private def originalProjectiveCoordinateNativeInput026 (b : Bool) :
    ((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
      (schemeRelativeDifferentials (projectiveLineProjToBase K))).val.obj (op ⊤) :=
  originalRestrictionInputCarrier026
    (actualProjectiveLinePolynomialChartToLine K b)
    (schemeRelativeDifferentials (projectiveLineProjToBase K)) ⊤
    ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
      (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
      (actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (Proj.basicOpen (grading Iline) (coordinate Iline b))
        ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
          (chartCoordinate Iline b (!b)))))

/-- Native INPUT comparison only, preserving the EXACT original raw
coordinate value. No native frame or target-output equality appears. -/
private theorem originalProjectiveCoordinateNativeInput026_eq (b : Bool) :
    originalProjectiveCoordinateNativeInput026 K b =
      (schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
        (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
        (actualRelativeDifferentialSection (projectiveLineProjToBase K)
          (Proj.basicOpen (grading Iline) (coordinate Iline b))
          ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
            (chartCoordinate Iline b (!b)))) :=
  originalRestrictionInputCarrier026_eq
    (actualProjectiveLinePolynomialChartToLine K b)
    (schemeRelativeDifferentials (projectiveLineProjToBase K)) ⊤ _

/-- EXACT original ΓSpec ONE in the explicit native unit target carrier.
There is no input-coordinate or native frame datum to normalize. -/
private def originalProjectiveGammaOneNativeOutput026 (b : Bool) :
    (SheafOfModules.unit
      (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf).val.obj (op ⊤) :=
  originalGammaToUnitCarrier026
    (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))) ⊤
    (1 : Γ(Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)), ⊤))

/-- Native OUTPUT comparison only, to the SAME original ΓSpec ONE.
This does not claim that a coordinate differential maps to it. -/
private theorem originalProjectiveGammaOneNativeOutput026_eq (b : Bool) :
    (show Γ(Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)), ⊤) from
      originalProjectiveGammaOneNativeOutput026 K b) =
        (1 : Γ(Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)), ⊤)) :=
  originalGammaToUnitCarrier026_eq
    (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))) ⊤ _

/-- The SAME affine frame factor used by actualNativeCoordinateFrameData019.
Its native module objects and original Subsingleton instance are retained. -/
private def originalAffineFrameIso027 (b : Bool) :
    schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K)))) ≅
      SheafOfModules.unit
        (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf := by
  letI : Subsingleton {i : Bool // i ≠ b} :=
    (lineProjectiveVariableEquiv b).symm.subsingleton
  exact actualOneVariableAffineDifferentialFrameIso (K := K)
    (lineProjectiveVariableEquiv b (0, 0))

/-- The ORIGINAL inverse-open and base-equality factors as a plain function.
No frame/datum.property is projected and no coefficient value is inserted. -/
private def originalOpenAffineFunction027 (b : Bool) :
    (((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
      (schemeRelativeDifferentials (projectiveLineProjToBase K))).val.obj (op ⊤)).carrier →
    ((schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K))))).val.obj (op ⊤)).carrier :=
  originalNativeComponentFunction027
    (eqToIso (congrArg (fun k => schemeRelativeDifferentials k)
      (actualProjectiveLinePolynomialChartToLine_toBase K b))).hom ⊤ ∘
    originalNativeComponentFunction027
      (actualOpenImmersionDifferentialSheafRestrictionIso
        (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)).inv ⊤

/-- The original affine frame's native top function, with fixed carriers. -/
private def originalAffineUnitFunction027 (b : Bool) :
    ((schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K))))).val.obj (op ⊤)).carrier →
    ((SheafOfModules.unit
      (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf).val.obj (op ⊤)).carrier :=
  originalNativeComponentFunction027 (originalAffineFrameIso027 K b).hom ⊤

/-- The ORIGINAL public frame's native top function, without evaluation. -/
private def originalPublicFrameFunction027 (b : Bool) :
    (((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
      (schemeRelativeDifferentials (projectiveLineProjToBase K))).val.obj (op ⊤)).carrier →
    ((SheafOfModules.unit
      (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf).val.obj (op ⊤)).carrier :=
  originalNativeComponentFunction027
    (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom ⊤

/-- Map identity only: the public ORIGINAL frame is EXACTLY the three
original native factors. No coordinate input or scalar output occurs. -/
private theorem originalPublicFrameFunction027_eq_comp (b : Bool) :
    originalPublicFrameFunction027 K b =
      originalAffineUnitFunction027 K b ∘ originalOpenAffineFunction027 K b := by
  letI : Subsingleton {i : Bool // i ≠ b} :=
    (lineProjectiveVariableEquiv b).symm.subsingleton
  exact originalNativeThreeFrameFunction027_comp
    (actualOpenImmersionDifferentialSheafRestrictionIso
      (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)).symm
    (eqToIso (congrArg (fun k => schemeRelativeDifferentials k)
      (actualProjectiveLinePolynomialChartToLine_toBase K b)))
    (actualOneVariableAffineDifferentialFrameIso (K := K)
      (lineProjectiveVariableEquiv b (0, 0))) ⊤

/-- The SAME affine universal differential of the SAME coordinate variable.
This is the middle value, distinct from the final frame/one proposition. -/
private def originalAffineVariableDifferential027 (b : Bool) :
    (schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K))))).val.obj (op ⊤) :=
  actualRelativeDifferentialSection
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K)))) ⊤
    ((Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
      (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))))

/-- FIRST independent action: ORIGINAL coordinate input to original affine D.
The accepted chart comparison is used after the PASSED input-carrier identity;
there is no final affine frame, scalar one or datum.property extraction. -/
private theorem originalOpenAffineFunction027_coordinate (b : Bool) :
    originalOpenAffineFunction027 K b (originalProjectiveCoordinateNativeInput026 K b) =
      originalAffineVariableDifferential027 K b := by
  have hz := (originalProjectiveCoordinateNativeInput026_eq K b).trans
    (actualProjectiveLineCoordinateDifferential_eq_chartUniversalD K b)
  have hcarry := congrArg (originalOpenAffineFunction027 K b) hz
  have hpair := originalNativeComponentPairFunction027_apply
    (actualOpenImmersionDifferentialSheafRestrictionIso
      (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)).inv
    (eqToIso (congrArg (fun k => schemeRelativeDifferentials k)
      (actualProjectiveLinePolynomialChartToLine_toBase K b))).hom ⊤
    (actualRelativeDifferentialSection (projectiveLineProjToBase K)
      (actualProjectiveLinePolynomialChartToLine K b ''ᵁ ⊤)
      (((actualProjectiveLinePolynomialChartToLine K b).appIso ⊤).inv
        ((Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
          (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))))))
  exact hcarry.trans (hpair.trans
    (actualProjectiveLinePolynomialChartDifferential_toAffine_D K b ⊤
      ((Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
        (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))))))

/-- SECOND independent action: original affine D to SAME native ΓSpec one.
No projective coordinate or inverse-open action occurs in this proof. -/
private theorem originalAffineUnitFunction027_coordinate (b : Bool) :
    originalAffineUnitFunction027 K b (originalAffineVariableDifferential027 K b) =
      originalProjectiveGammaOneNativeOutput026 K b := by
  letI : Subsingleton {i : Bool // i ≠ b} :=
    (lineProjectiveVariableEquiv b).symm.subsingleton
  exact (originalNativeComponentFunction027_apply
    (actualOneVariableAffineDifferentialFrameIso (K := K)
      (lineProjectiveVariableEquiv b (0, 0))).hom ⊤
    (originalAffineVariableDifferential027 K b)).trans
      ((originalAffineFrameCoefficient_native (K := K)
        (lineProjectiveVariableEquiv b (0, 0))).trans
          (originalProjectiveGammaOneNativeOutput026_eq K b).symm)

/-- Reconnect the SAME map and computed coefficients using only plain
functions and the two independent native-carrier actions. No paired-data law. -/
private theorem originalPublicFrameFunction027_coordinate (b : Bool) :
    originalPublicFrameFunction027 K b (originalProjectiveCoordinateNativeInput026 K b) =
      originalProjectiveGammaOneNativeOutput026 K b :=
  (congrArg (fun F => F (originalProjectiveCoordinateNativeInput026 K b))
    (originalPublicFrameFunction027_eq_comp K b)).trans
      (originalPlainFunctionCoefficient027
        (originalOpenAffineFunction027 K b) (originalAffineUnitFunction027 K b)
        (originalProjectiveCoordinateNativeInput026 K b)
        (originalAffineVariableDifferential027 K b)
        (originalProjectiveGammaOneNativeOutput026 K b)
        (originalOpenAffineFunction027_coordinate K b)
        (originalAffineUnitFunction027_coordinate K b))

/-- The EXACT original public top arrow, with native scalar RingCat.ring
and source/target ModuleCat objects fixed in its explicit Hom TYPE. -/
private def originalPublicExplicitNativeTopArrow032 (b : Bool) :
    @ModuleCat.Hom
      ((Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf.obj.obj (op ⊤)).carrier
      ((Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf.obj.obj (op ⊤)).ring
      (((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
        (schemeRelativeDifferentials (projectiveLineProjToBase K))).val.obj (op ⊤))
      ((SheafOfModules.unit
        (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf).val.obj (op ⊤)) :=
  (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom.val.app (op ⊤)

/-- The ORIGINAL composed inverse-open/base-equality/affine native top
arrow. No public frame/data factory or original section is inserted here. -/
private def originalComposedNativeTopArrow036 (b : Bool) :
    @ModuleCat.Hom
      ((Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf.obj.obj (op ⊤)).carrier
      ((Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf.obj.obj (op ⊤)).ring
      (((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
        (schemeRelativeDifferentials (projectiveLineProjToBase K))).val.obj (op ⊤))
      ((SheafOfModules.unit
        (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf).val.obj (op ⊤)) :=
  ((actualOpenImmersionDifferentialSheafRestrictionIso
    (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)).symm ≪≫
    eqToIso (congrArg (fun k => schemeRelativeDifferentials k)
      (actualProjectiveLinePolynomialChartToLine_toBase K b)) ≪≫
    originalAffineFrameIso027 K b).hom.val.app (op ⊤)

/-- Categorical frame identity ONLY, before component/coercion/application.
Same original native inverse-open/base-equality/affine frame composition. -/
private theorem originalNativeFrameIso035_eq_threeFactors (b : Bool) :
    actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b =
      (actualOpenImmersionDifferentialSheafRestrictionIso
        (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)).symm ≪≫
        eqToIso (congrArg (fun k => schemeRelativeDifferentials k)
          (actualProjectiveLinePolynomialChartToLine_toBase K b)) ≪≫
        originalAffineFrameIso027 K b := rfl

/-- Categorical native TOP-ARROW identity only, no function or input value.
The original public component is the original three-factor component. -/
private theorem originalNativeTopArrow035_eq_threeFactors (b : Bool) :
    originalPublicExplicitNativeTopArrow032 K b =
      ((actualOpenImmersionDifferentialSheafRestrictionIso
        (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)).symm ≪≫
        eqToIso (congrArg (fun k => schemeRelativeDifferentials k)
          (actualProjectiveLinePolynomialChartToLine_toBase K b)) ≪≫
        originalAffineFrameIso027 K b).hom.val.app (op ⊤) :=
  congrArg (fun e :
    (Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
      (schemeRelativeDifferentials (projectiveLineProjToBase K)) ≅
      SheafOfModules.unit
        (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf =>
      e.hom.val.app (op ⊤))
    (originalNativeFrameIso035_eq_threeFactors K b)

/-- DIAGNOSTIC partial specialization: original Y/M/N/T OBJECTS ONLY.
All Iso/open/value/action arguments remain variables in the inferred type. -/
private def originalSpecializeObjects037 (b : Bool) :=
  @originalThreeFrameExplicitArrowCoefficient034
    (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)))
    ((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj
      (schemeRelativeDifferentials (projectiveLineProjToBase K)))
    (schemeRelativeDifferentials
      (actualProjectiveLinePolynomialChartToLine K b ≫ projectiveLineProjToBase K))
    (schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K)))))

/-- Supply ONLY the original inverse-open differential Iso. -/
private def originalSpecializeInverseOpen037 (b : Bool) :=
  originalSpecializeObjects037 K b
    (actualOpenImmersionDifferentialSheafRestrictionIso
      (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)).symm

/-- Supply ONLY the original base-map equality Iso, after inverse-open. -/
private def originalSpecializeBaseEquality037 (b : Bool) :=
  originalSpecializeInverseOpen037 K b
    (eqToIso (congrArg (fun k => schemeRelativeDifferentials k)
      (actualProjectiveLinePolynomialChartToLine_toBase K b)))

/-- Supply original affine frame Iso, leaving all open/value/action args. -/
private def originalSpecializeAffineFrame037 (b : Bool) :=
  originalSpecializeBaseEquality037 K b (originalAffineFrameIso027 K b)

/-- Supply the original native top open; all three values still variable. -/
private def originalSpecializeTopOpen037 (b : Bool) :=
  originalSpecializeAffineFrame037 K b ⊤

/-- Supply ONLY original native coordinate INPUT, not middle/output/actions. -/
private def originalSpecializeInput037 (b : Bool) :=
  originalSpecializeTopOpen037 K b (originalProjectiveCoordinateNativeInput026 K b)

/-- Supply ONLY original affine-D MIDDLE value after the original input. -/
private def originalSpecializeMiddle037 (b : Bool) :=
  originalSpecializeInput037 K b (originalAffineVariableDifferential027 K b)

/-- Supply native unit ONE; BOTH genuine action proof inputs remain variable. -/
private def originalSpecializeNativeOne037 (b : Bool) :=
  originalSpecializeMiddle037 K b (originalProjectiveGammaOneNativeOutput026 K b)

/-- Supply ONLY original checked open-to-affineD ACTION; affine action remains
an explicit VARIABLE. This is a conditional diagnostic factory, not coverage. -/
private def originalSpecializeOpenAction037 (b : Bool) :=
  originalSpecializeNativeOne037 K b (originalOpenAffineFunction027_coordinate K b)

/-- Supply final original affineD-to-nativeOne action, with inferred original
factory result TYPE. This is diagnostics of specialization; no public target
conversion, original factory/arrow reconstruction or added hypothesis. -/
private def originalSpecializeBothActions037 (b : Bool) :=
  originalSpecializeOpenAction037 K b (originalAffineUnitFunction027_coordinate K b)

/-- FIRST bridge stage: captured INFERRED original native dictionary and
composed coefficient producer. Public arrow/equality stay VARIABLE; this
conditional diagnostic factory is not an endpoint or added public premise. -/
private def originalTransportProducer038 (b : Bool) :=
  originalInferRawTransportFactory038 _ _ _ (originalSpecializeBothActions037 K b)

/-- SECOND bridge stage: supply SAME original explicit public top arrow.
Categorical arrow identity remains VARIABLE in inferred result type. -/
private def originalTransportPublicArrow038 (b : Bool) :=
  originalTransportProducer038 K b (originalPublicExplicitNativeTopArrow032 K b)




/-- FIRST diagram stage: insert the checked ORIGINAL frame Iso equality
before any native scalar, input/output value or coefficient proof is supplied.
The equality lives in the native sheaf category, rather than the concrete
raw ModuleCat.Hom equality consumed by the unsuccessful038 final stage. -/
private def originalNativeFrameDiagram039 (b : Bool) :=
  originalNativeIsoCoefficientDiagram039 ⊤ _ _
    (originalNativeFrameIso035_eq_threeFactors K b)

/-- SECOND diagram stage: supply only the independently checked original
native coordinate input. The native unit and coefficient remain variables. -/
private def originalNativeFrameDiagramInput039 (b : Bool) :=
  originalNativeFrameDiagram039 K b (originalProjectiveCoordinateNativeInput026 K b)

/-- THIRD diagram stage: supply the independently checked original native
unit value. Only the composed native coefficient is still a variable. -/
private def originalNativeFrameDiagramOne039 (b : Bool) :=
  originalNativeFrameDiagramInput039 K b (originalProjectiveGammaOneNativeOutput026 K b)

/-- FOURTH diagram stage: insert the checked ten-step original composed
coefficient producer. The categorical diagram was transported before this
application; no actual raw arrow equality argument is inserted here. -/
private def originalPublicRawCoefficientProducer039 (b : Bool) :=
  originalNativeFrameDiagramOne039 K b (originalSpecializeBothActions037 K b)

/-- FIFTH stage: use the existing abstract raw-to-native action theorem with
all dictionaries inferred from the diagram producer, preserving the SAME
original public component arrow and independently checked native values. -/
private def originalPublicNativeCoefficientProducer039 (b : Bool) :=
  originalInferNativeActionFactory038 _ _ _ (originalPublicRawCoefficientProducer039 K b)





/-- FIRST ordinary-value stage: infer the passed original native coefficient
function and carriers. The returned replacement input/equality are explicit
arguments, so neither is inserted while capturing this partial application. -/
private def originalLiteralInputFactory041 (b : Bool) :=
  originalOrdinaryCoefficientInputExplicitFactory041 _ _ _
    (originalPublicNativeCoefficientProducer039 K b)

/-- Supply the replacement literal input and its checked identity together.
The underscore is resolved by the supplied026 equality at this complete
application, rather than being left unsolved at the earlier factory capture. -/
private def originalLiteralInputCoefficient041 (b : Bool) :=
  originalLiteralInputFactory041 K b _ (originalProjectiveCoordinateNativeInput026_eq K b)

/-- Capture output transport with the replacement output/equality explicit
and still VARIABLE. No implicit native-one replacement is inserted here. -/
private def originalLiteralOutputFactory041 (b : Bool) :=
  originalOrdinaryCoefficientOutputExplicitFactory041 _ _ _
    (originalLiteralInputCoefficient041 K b)

/-- Supply only the original Gamma replacement and independent026 identity.
Its underscore is resolved by the actual equality in this complete application. -/
private def originalLiteralValuesCoefficient041 (b : Bool) :=
  originalLiteralOutputFactory041 K b _ (originalProjectiveGammaOneNativeOutput026_eq K b)

/-- Ordinary function replacement with the SAME carriers and values. The
replacement function and its point-free equality are EXPLICIT returned inputs;
no native dictionary or coordinate expression is introduced in this proof. -/
private theorem originalOrdinaryCoefficientFunctionExplicitFactory042
    {A B : Type u} (f : A → B) (x : A) (y : B) (h : f x = y) :
    ∀ (f' : A → B), f = f' → f' x = y :=
  fun f' hf => (congrFun hf x).symm.trans h

/-- The EXACT original public top action as an ordinary function. Only the
input is abstract here, so constructing this value cannot expand the original
coordinate differential or compare a computed coefficient with a new header. -/
private def originalPublicLiteralTopFunction042 (b : Bool) :=
  fun x =>
    (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom.val.app (op ⊤) x

/-- Infer the function and literal values from the checked041 coefficient.
The replacement function and its equality remain explicit returned variables;
this stage performs no conversion to a reconstructed native component. -/
private def originalLiteralFunctionFactory042 (b : Bool) :=
  originalOrdinaryCoefficientFunctionExplicitFactory042 _ _ _
    (originalLiteralValuesCoefficient041 K b)

/-- Supply only the EXACT original public top function. The point-free
function equality is still VARIABLE, independently of the original coordinate
input and Gamma output; this conditional stage adds no public hypothesis. -/
private def originalLiteralFunctionIdentityFactory042 (b : Bool) :=
  originalLiteralFunctionFactory042 K b (originalPublicLiteralTopFunction042 K b)

/-- Compare the categorical component coercion and its literal eta expansion
while the scheme, modules, arrow and open are ABSTRACT. The `show` uses the
same component object dictionary as the native coefficient factory. Only this
small abstract theorem discharges reflexivity; no actual chart is unfolded. -/
private theorem originalNativeComponentLiteralEta043
    {Y : Scheme.{u}} {M N : Y.Modules} (a : M ⟶ N) (V : Y.Opens) :
    ((show M.val.obj (op V) ⟶ N.val.obj (op V) from a.val.app (op V)) :
      (M.val.obj (op V)).carrier → (N.val.obj (op V)).carrier) =
      (fun x => a.val.app (op V) x) := rfl

/-- Supply ONLY the original public frame component to the abstract eta
identity. The open remains an explicit variable, and no coordinate or unit
value occurs in either compared ordinary function. -/
private def originalActualComponentEtaFrame043 (b : Bool) :=
  originalNativeComponentLiteralEta043
    (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom

/-- Supply the original top open to the independently captured component
identity. Its result type is inferred, preserving the native dictionaries
selected before any literal coefficient is consumed. -/
private def originalActualComponentEtaTop043 (b : Bool) :=
  originalActualComponentEtaFrame043 K b ⊤

/-- Fix the function carriers and BOTH functions from their identity FIRST.
The coordinate input, scalar output and coefficient remain explicit returned
variables. This avoids comparing an independently inferred whole-function
Eq type after coordinate values have already fixed a different carrier form. -/
private theorem originalCoefficientFromFunctionIdentityFactory046
    {A B : Type u} {f g : A → B} (hf : f = g) :
    ∀ (x : A) (y : B), f x = y → g x = y :=
  fun x y hc => (congrFun hf x).symm.trans hc

/-- Capture only the PASSED4398 original top-component identity. The native
A/B and component functions are fixed by that checked identity before any
coordinate, Gamma value or coefficient is supplied. No042 literal-top-function
wrapper or expected whole-function-equality factory is applied here. -/
private def originalFunctionIdentityFirstCoefficientFactory046 (b : Bool) :=
  originalCoefficientFromFunctionIdentityFactory046 (originalActualComponentEtaTop043 K b)

/-- Infer the SAME original literal coordinate and Gamma-one values only at
this complete application of the identity-first factory. The independently
PASSED041 coefficient is transported between the already fixed original
component functions; no actual function equality is reconstructed or proved. -/
private def originalFunctionIdentityFirstLiteralCoefficient046 (b : Bool) :=
  originalFunctionIdentityFirstCoefficientFactory046 K b _ _
    (originalLiteralValuesCoefficient041 K b)

/-- Present the native TOP component over `TopologicalSpace.Opens Y`,
rather than the definitionally equal `Scheme.Opens Y`, while scheme, module,
arrow and all coefficient values remain ABSTRACT. This proof changes only
open/typeclass presentation; both sides use the SAME top and native action. -/
private theorem originalComponentTopPresentationFactory047
    {Y : Scheme.{u}} {M N : Y.Modules} (a : M ⟶ N) :
    ∀ (x : M.val.obj (op (⊤ : Y.Opens)))
      (y : N.val.obj (op (⊤ : Y.Opens))),
      a.val.app (op (⊤ : Y.Opens)) x = y →
      a.val.app (op (⊤ : TopologicalSpace.Opens Y)) x = y :=
  fun _ _ h => h

/-- Supply ONLY the exact original frame hom to the abstract top
presentation theorem. Input/output/coefficient remain explicit variables;
no coordinate polynomial, image equality or differential is reconstructed. -/
private def originalTopPresentationCoefficientFactory047 (b : Bool) :=
  originalComponentTopPresentationFactory047
    (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom

/-- Supply the independently PASSED4501 native coefficient after the top
presentation has already been fixed abstractly. Literal coordinate and Gamma
values are inferred at this complete application; no whole public proposition
assignment or fresh actual top-equality proof is performed here. -/
private def originalTopPresentationLiteralCoefficient047 (b : Bool) :=
  originalTopPresentationCoefficientFactory047 K b _ _
    (originalFunctionIdentityFirstLiteralCoefficient046 K b)

/-- Present TOP through the component's OWN inferred index category while
scheme/modules/component/values remain ABSTRACT. The source names Y.Opens;
the target spells exactly `a.val.app (op ⊤)` as the original public header.
No explicit TopologicalSpace.Opens/coercion dictionary is reconstructed. -/
private theorem originalComponentInferredTopPresentationFactory048
    {Y : Scheme.{u}} {M N : Y.Modules} (a : M ⟶ N) :
    ∀ (x : M.val.obj (op (⊤ : Y.Opens)))
      (y : N.val.obj (op (⊤ : Y.Opens))),
      a.val.app (op (⊤ : Y.Opens)) x = y →
      a.val.app (op ⊤) x = y :=
  fun _ _ h => h

/-- Supply ONLY the exact original frame hom. Both coefficient values and
the checked coefficient remain variables; the target top is inferred from
this SAME component category, rather than an independently ascribed Opens. -/
private def originalInferredTopPresentationCoefficientFactory048 (b : Bool) :=
  originalComponentInferredTopPresentationFactory048
    (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom

/-- Supply the independently PASSED4501 native coefficient directly, after
inferred-component TOP presentation is fixed abstractly. The047 explicitly
ascribed top is retained for fidelity but is not an input to this application. -/
private def originalInferredTopPresentationLiteralCoefficient048 (b : Bool) :=
  originalInferredTopPresentationCoefficientFactory048 K b _ _
    (originalFunctionIdentityFirstLiteralCoefficient046 K b)

/-- Fix an ordinary function and its domain FIRST, then capture a checked
coefficient with only replacement-input/value equality still variable. This
lemma has no sheaf, top, scalar dictionary or coordinate expression. -/
private theorem originalFixedFunctionCoordinateTransport049
    {A B : Type u} (f : A → B) :
    ∀ (x : A) (y : B), f x = y →
      ∀ (x' : A), x = x' → f x' = y :=
  fun x y h x' hx => (congrArg f hx).symm.trans h

/-- Construct a value under the SAME ordinary function-domain expected type.
Its value is exactly x, with no map or mathematical transport introduced. -/
private def originalOrdinaryFunctionDomainValue049
    {A B : Type u} (_f : A → B) (x : A) : A := x

/-- Extract the ordinary premise proposition from a checked implication's
TYPE. This is only a proposition value; it proves no construction hypothesis. -/
private def originalOrdinaryImplicationPremise049 {P Q : Prop} (_f : P → Q) : Prop := P

/-- Fix only the EXACT original public component function whose dictionaries
were shown identical in4541. No new top/component equality is constructed;
the existing042 literal function is merely supplied to an ordinary factory. -/
private def originalFixedPublicFunctionCoordinateFactory049 (b : Bool) :=
  originalFixedFunctionCoordinateTransport049 (originalPublicLiteralTopFunction042 K b)

/-- Supply the checked048 coefficient after the exact component/domain has
already been fixed. Replacement input and its equality remain explicit variables;
no original public proposition is assigned at this conditional stage. -/
private def originalNativeCoordinateEqualityFactory049 (b : Bool) :=
  originalFixedPublicFunctionCoordinateFactory049 K b _ _
    (originalInferredTopPresentationLiteralCoefficient048 K b)

/-- The EXACT original raw coordinate expression, now elaborated under the
fixed original PUBLIC function's domain rather than in isolation. It retains
the same original image equality, differential section, away map and variable. -/
private def originalPublicLiteralCoordinateInput049 (b : Bool) :=
  originalOrdinaryFunctionDomainValue049 (originalPublicLiteralTopFunction042 K b)
    ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
      (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
      (actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (Proj.basicOpen (grading Iline) (coordinate Iline b))
        ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
          (chartCoordinate Iline b (!b)))))

/-- Supply only that literal input. The sole remaining premise is equality
of the two original coordinate VALUES under the already fixed function domain;
this is a conditional diagnostic factory, not unconditional coefficient coverage. -/
private def originalLiteralCoordinateEqualityCoefficientFactory049 (b : Bool) :=
  originalNativeCoordinateEqualityFactory049 K b (originalPublicLiteralCoordinateInput049 K b)

/-- Isolate the inferred input-VALUE equality proposition without rebuilding
its carrier or coordinate expressions. It is the exact retained premise of
the checked conditional coefficient factory, not a new final assumption. -/
private def originalCoordinateValueEqualityProposition049 (b : Bool) :=
  originalOrdinaryImplicationPremise049 (originalLiteralCoordinateEqualityCoefficientFactory049 K b)

/-- Ordinary bounded equality cut for ONLY the original coordinate values.
The component, output, top and full public coefficient proposition do not
occur as operands of this equality; no extra coordinate law is assumed. -/
private theorem originalLiteralCoordinateValueEquality049 (b : Bool) :
    originalCoordinateValueEqualityProposition049 K b := by
  rfl

/-- Supply the independently isolated coordinate equality to the retained
coefficient factory. The SAME original component is already fixed and the
Gamma-one output was unchanged throughout the value equality proof cut. -/
private def originalCoordinateValueTransportedCoefficient049 (b : Bool) :=
  originalLiteralCoordinateEqualityCoefficientFactory049 K b (originalLiteralCoordinateValueEquality049 K b)

/-- Ordinary congruence fixing BOTH functions from a proved alias equality
FIRST, then the two input values from their proved alias equality, before any
coefficient is supplied. No schemes, dictionaries, top or coordinates here. -/
private theorem originalOrdinaryAliasCoefficientFactory051
    {A B : Type u} {f g : A → B} (hf : f = g) :
    ∀ {x x' : A}, x = x' → ∀ (y : B), f x = y → g x' = y :=
  fun {x x'} hx y hc =>
    (congrArg g hx).symm.trans ((congrFun hf x).symm.trans hc)

/-- The042 ordinary function naming wrapper versus its literal defining
lambda, with the SAME component/index/top expression. This point-free alias
proposition contains no coordinate or coefficient evaluation. -/
private def originalFunctionAliasEqualityProposition051 (b : Bool) :=
  originalPublicLiteralTopFunction042 K b =
    (fun x =>
      (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom.val.app (op ⊤) x)

/-- The049 coordinate naming wrapper versus its EXACT defining raw input,
under the wrapper's own carrier expected type. All original maps, equalities,
differential, chart variable and dictionaries remain the same. -/
private def originalInputAliasEqualityProposition051 (b : Bool) :=
  originalPublicLiteralCoordinateInput049 K b =
    ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
      (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
      (actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (Proj.basicOpen (grading Iline) (coordinate Iline b))
        ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
          (chartCoordinate Iline b (!b)))))

/-- Prove ONLY the ordinary function naming alias point-free. The defining
lambda delays every actual coordinate evaluation; no new top/map identity. -/
private theorem originalFunctionAliasEquality051 (b : Bool) :
    originalFunctionAliasEqualityProposition051 K b := by
  rfl

/-- Prove ONLY the input naming alias at the already checked original
coordinate value. No native/value equality from049 is reconstructed here. -/
private theorem originalInputAliasEquality051 (b : Bool) :
    originalInputAliasEqualityProposition051 K b := by
  rfl

/-- Capture the separately proved function alias FIRST. Its replacement
function is the LITERAL lambda from that equality, rather than a named wrapper;
ordinary application type inference beta-reduces that substituted lambda. -/
private def originalFunctionAliasCoefficientFactory051 (b : Bool) :=
  @originalOrdinaryAliasCoefficientFactory051 _ _ _ _ (originalFunctionAliasEquality051 K b)

/-- Supply ONLY the separately proved input alias. The replacement input
is now the exact raw coordinate expression from that equality, while the
scalar output and independently checked049 coefficient remain variables. -/
private def originalBothAliasCoefficientFactory051 (b : Bool) :=
  originalFunctionAliasCoefficientFactory051 K b (originalInputAliasEquality051 K b)

/-- Supply the PASSED4594 coefficient only after the literal replacement
function and raw replacement input have been fixed by their own proved aliases.
The resulting TYPE is inferred without any original public expected header. -/
private def originalRawLiteralCoefficient051 (b : Bool) :=
  originalBothAliasCoefficientFactory051 K b _ (originalCoordinateValueTransportedCoefficient049 K b)

/-- Diagnostic/public-conversion boundary: the LITERAL original public
coefficient proposition, inferred as a value so header construction is separate
from conversion of the independently computed native function coefficient. -/
private def originalPublicCoefficientProposition020 (b : Bool) :=
  (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom.val.app (op ⊤)
        ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
          (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
          (actualRelativeDifferentialSection (projectiveLineProjToBase K)
            (Proj.basicOpen (grading Iline) (coordinate Iline b))
            ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
              (chartCoordinate Iline b (!b))))) =
        (1 : Γ(Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)), ⊤))



/-- Capture the independently checked raw coefficient proof POINT-FREE.
Universe, base and CommRing instance are supplied explicitly, while the Bool
chart index remains a universal binder. No coordinate value is applied here. -/
private def originalRawLiteralUniformProof054 :=
  @originalRawLiteralCoefficient051.{u} K ‹CommRing K›

/-- EXACT original literal coefficient statement for ALL chart indices as
a proposition VALUE. It preserves the original result expression under a
Bool quantifier; this declaration alone proves no coefficient. -/
private def originalFinalLiteralUniformProposition054 : Prop :=
  ∀ (b : Bool),
    (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom.val.app (op ⊤)
          ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
            (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
            (actualRelativeDifferentialSection (projectiveLineProjToBase K)
              (Proj.basicOpen (grading Iline) (coordinate Iline b))
              ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
                (chartCoordinate Iline b (!b))))) =
          (1 : Γ(Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)), ⊤))


/-- Capture the checked raw family locally WITHOUT an expected proof type,
then assign its inferred local proof to the exact named literal proposition.
This is the untraced ordinary proof of the checked local-context boundary. -/
private theorem originalFinalLiteralUniformCoefficient054 :
    originalFinalLiteralUniformProposition054 K := by
  have raw := @originalRawLiteralUniformProof054.{u} K ‹CommRing K›
  exact raw

/-- Original public proposition AFTER separately proved alias equalities
have constructed the raw result by ordinary congruence. Its own actual TYPE
must be reviewed against the original proposition VALUE before this boundary. -/
private theorem originalLiteralCoefficientFromAliasEqualities051 (b : Bool) :
    originalPublicCoefficientProposition020 K b :=
  originalRawLiteralCoefficient051 K b

/-- Equality of two proofs of the SAME proposition, before any geometric
expression is assembled or converted. No data-valued instance is equated. -/
private theorem originalSharedProofInstanceEquality065 (P : Prop) (p q : P) : p = q :=
  Subsingleton.elim p q

/-- The exact polynomial submonoid-class proof shared in native frame data
versus its original inline instance. This is a SMALL ordinary proof equality. -/
private theorem originalSubmonoidProofInstanceEquality065 :
    @actualNativeCoordinateFrameData019._proof_3.{u} K ‹CommRing K› =
      (Submodule.addSubmonoidClass :
        AddSubmonoidClass (Submodule K (MvPolynomial Bool K)) (MvPolynomial Bool K)) :=
  originalSharedProofInstanceEquality065 _ _ _

/-- Use the checked shared proof's OWN cached class/type/dictionaries as
the expected type of its inline instance. No CoordinateRing or Iline type is
reconstructed while elaborating this small proof-irrelevance equality. -/
private theorem originalSubgroupProofInstanceEquality065 :
    @actualNativeCoordinateFrameData019._proof_5.{u} K ‹CommRing K› =
      Submodule.addSubgroupClass :=
  originalSharedProofInstanceEquality065 _ _ _

/-- The shared scalar-tower proof and its exact original inline instance.
The checked LEFT proof supplies the entire cached expected TYPE, avoiding any
reconstruction of module, quotient or geometric instance dictionaries. -/
private theorem originalScalarTowerProofInstanceEquality068 :
    @actualNativeCoordinateFrameData019._proof_4.{u} K ‹CommRing K› =
      IsScalarTower.right :=
  originalSharedProofInstanceEquality065 _ _ _

private def proofAlignmentShape065 (e : Lean.Expr) : String :=
  let e := e.consumeMData
  let h := match e.getAppFn with
    | .const n ls => s!"const {n} levels={reprStr ls}"
    | .fvar id => s!"fvar {id.name}"
    | .mvar id => s!"mvar {id.name}"
    | .bvar i => s!"bvar {i}"
    | .forallE n _ _ _ => s!"forall {n}"
    | .lam n _ _ _ => s!"lambda {n}"
    | .sort l => s!"sort {reprStr l}"
    | .letE n _ _ _ _ => s!"let {n}"
    | .proj n i _ => s!"projection {n}.{i}"
    | .lit l => s!"literal {reprStr l}"
    | .app _ _ => "application"
    | .mdata _ _ => "metadata"
  s!"{h} argc={e.getAppArgs.size} hash={e.hash} exprMVar={e.hasExprMVar} levelMVar={e.hasLevelMVar}"

private def firstProofAlignmentDifference065 : Nat → String → Lean.Expr → Lean.Expr → Option (String × Lean.Expr × Lean.Expr)
  | 0, label, e, f =>
    if Lean.Expr.equal e f then none else some (label, e, f)
  | n + 1, label, e, f => Id.run do
    let e := e.consumeMData
    let f := f.consumeMData
    if Lean.Expr.equal e f then return none
    match e, f with
    | .lam _ et eb _, .lam _ ft fb _ =>
      if let some result := firstProofAlignmentDifference065 n (label ++ ".lambdaType") et ft then return some result
      if let some result := firstProofAlignmentDifference065 n (label ++ ".lambdaBody") eb fb then return some result
    | .forallE _ et eb _, .forallE _ ft fb _ =>
      if let some result := firstProofAlignmentDifference065 n (label ++ ".forallType") et ft then return some result
      if let some result := firstProofAlignmentDifference065 n (label ++ ".forallBody") eb fb then return some result
    | .app _ _, .app _ _ =>
      if e.getAppArgs.size == f.getAppArgs.size then
        if let some result := firstProofAlignmentDifference065 n (label ++ ".appFn") e.getAppFn f.getAppFn then
          return some result
        for i in [:e.getAppArgs.size] do
          if let some result := firstProofAlignmentDifference065 n (label ++ s!".arg{i}") e.getAppArgs[i]! f.getAppArgs[i]! then
            return some result
    | _, _ => pure ()
    return some (label, e, f)

/-- Optional compiler phase output; no proof state or mathematical value
is changed. The actual source proof requests no success-stage logging. -/
private def proofAlignmentPhase065 (enabled : Bool) (message : String) : Lean.Elab.Tactic.TacticM Unit := do
  if enabled then
    _root_.liftM <| Lean.Core.liftIOCore do
      IO.eprintln message
      let stream ← IO.getStderr
      stream.flush

/-- Align ONLY exact proof-instance nodes justified by the three local,
independently checked small equality facts (including IsScalarTower). Normal Lean conversion checking
stays ENABLED, and the final public declaration undergoes kernel checking. -/
private def alignOriginalPointwiseProofInstances065 (reportPhases : Bool) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.instantiateMVars (← goal.getType)
    let lctx ← Lean.getLCtx
    let mut rules : Array (Lean.Expr × Lean.Expr) := #[]
    for name in #[`submonoidAlignment, `subgroupAlignment, `scalarTowerAlignment] do
      let some fact := lctx.findFromUserName? name |
        _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError s!"PROOF_INSTANCE_ALIGNMENT_FACT_MISSING065 {name}")
      let type ← Lean.instantiateMVars fact.type
      let arguments := type.consumeMData.getAppArgs
      unless type.consumeMData.getAppFn.constName? == some `Eq && arguments.size == 3 do
        _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError "PROOF_INSTANCE_ALIGNMENT_FACT_NOT_EQUALITY065")
      let className := arguments[0]!.consumeMData.getAppFn.constName?
      unless className == some ``AddSubmonoidClass || className == some ``AddSubgroupClass || className == some ``IsScalarTower do
        _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError "PROOF_INSTANCE_ALIGNMENT_NOT_SMALL_PROP_CLASS065")
      rules := rules.push (arguments[1]!.consumeMData, arguments[2]!.consumeMData)
    proofAlignmentPhase065 reportPhases "PROOF_INSTANCE_SMALL_EQUALITY_RULES_CAPTURED065"
    let some pointwise := lctx.findFromUserName? `pointwise |
      _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError "PROOF_INSTANCE_ALIGNMENT_POINTWISE_MISSING065")
    let oldType ← Lean.instantiateMVars pointwise.type
    let alignedType ← Lean.Core.transform (m := Lean.CoreM) oldType fun expression => do
      for (sharedProof, inlineProof) in rules do
        if Lean.Expr.equal expression.consumeMData sharedProof then return .visit inlineProof
      match expression with
      | .mdata _ body => return .visit body
      | _ => return .continue
    let targetCanonical ← Lean.Core.transform (m := Lean.CoreM) target fun expression => do
      match expression with
      | .mdata _ body => return .visit body
      | _ => return .continue
    unless Lean.Expr.equal alignedType.consumeMData targetCanonical.consumeMData do
      _root_.liftM <| Lean.Core.liftIOCore do
        IO.eprintln s!"PROOF_INSTANCE_ALIGNMENT_INCOMPLETE065 target {proofAlignmentShape065 targetCanonical}"
        IO.eprintln s!"PROOF_INSTANCE_ALIGNMENT_INCOMPLETE065 aligned {proofAlignmentShape065 alignedType}"
        if let some (path, expected, provided) := firstProofAlignmentDifference065 20 "afterThreeProvedSmallRules" targetCanonical alignedType then
          IO.eprintln s!"FIRST_DIFF {path}.expected {proofAlignmentShape065 expected}"
          IO.eprintln s!"FIRST_DIFF {path}.provided {proofAlignmentShape065 provided}"
        let stream ← IO.getStderr
        stream.flush
        throw (IO.userError "PROOF_INSTANCE_ALIGNMENT_INCOMPLETE065")
    proofAlignmentPhase065 reportPhases "PROOF_INSTANCE_LITERAL_TYPE_STRUCTURALLY_ALIGNED065"
    -- Default checkDefEq=true is intentionally retained. No unchecked change API.
    let next ← goal.changeLocalDecl pointwise.fvarId alignedType
    Lean.Elab.Tactic.replaceMainGoal [next]
    proofAlignmentPhase065 reportPhases "PROOF_INSTANCE_DEFAULT_CHECKED_LOCAL_CHANGE_COMPLETE065"

/-- Ordinary equality transport through a proposition-valued context.
The only input equality concerns two inhabitants of the SAME small Prop. -/
private theorem originalSmallProofContextTransport069
    (P : Prop) (C : P → Prop) (p q : P) (h : p = q) (hp : C p) : C q :=
  Eq.mp (congrArg C h) hp

/-- Build an explicit sequence of ordinary context transports, preserving
the original goal and local proof types. Pure construction is gated by exact
syntax; submission uses the standard term embedding and ordinary exact tactic. -/
private def transportOriginalPointwiseProofInstances069
    (reportPhases diagnosticOnly : Bool) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.instantiateMVars (← goal.getType)
    let lctx ← Lean.getLCtx
    let some pointwise := lctx.findFromUserName? `pointwise |
      _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError "PROOF_CONTEXT_POINTWISE_MISSING069")
    let mut currentType ← Lean.instantiateMVars pointwise.type
    currentType ← Lean.Core.transform (m := Lean.CoreM) currentType fun expression => do
      match expression with
      | .mdata _ body => return .visit body
      | _ => return .continue
    let mut currentProof := Lean.mkFVar pointwise.fvarId
    proofAlignmentPhase065 reportPhases "PROOF_CONTEXT_ORIGINAL_POINTWISE_CAPTURED069"
    for name in #[`subgroupAlignment, `scalarTowerAlignment, `submonoidAlignment] do
      let some fact := lctx.findFromUserName? name |
        _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError s!"PROOF_CONTEXT_EQUALITY_MISSING069 {name}")
      let factType ← Lean.instantiateMVars fact.type
      let arguments := factType.consumeMData.getAppArgs
      unless factType.consumeMData.getAppFn.constName? == some `Eq && arguments.size == 3 do
        _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError "PROOF_CONTEXT_FACT_NOT_EQUALITY069")
      let P := arguments[0]!
      let p := arguments[1]!.consumeMData
      let q := arguments[2]!.consumeMData
      let className := P.consumeMData.getAppFn.constName?
      unless className == some ``AddSubmonoidClass || className == some ``AddSubgroupClass || className == some ``IsScalarTower do
        _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError "PROOF_CONTEXT_NOT_SMALL_PROP_CLASS069")
      let (context, nextType) ← Lean.Meta.withLocalDeclD `_proof P fun hole => do
        let body ← Lean.Core.transform (m := Lean.CoreM) currentType fun expression => do
          if Lean.Expr.equal expression.consumeMData p then return .visit hole
          match expression with
          | .mdata _ inside => return .visit inside
          | _ => return .continue
        let context := Lean.mkLambda `_proof Lean.BinderInfo.default P (body.abstract #[hole])
        unless Lean.Expr.equal (context.beta #[p]).consumeMData currentType.consumeMData do
          _root_.liftM <| Lean.Core.liftIOCore <| throw (IO.userError "PROOF_CONTEXT_ORIGINAL_APPLICATION_NOT_EXACT069")
        return (context, context.beta #[q])
      currentProof := Lean.mkAppN (Lean.mkConst ``originalSmallProofContextTransport069)
        #[P, context, p, q, Lean.mkFVar fact.fvarId, currentProof]
      currentType := nextType
      proofAlignmentPhase065 reportPhases s!"PROOF_CONTEXT_EXPLICIT_TRANSPORT_CONSTRUCTED069 {name}"
    let targetCanonical ← Lean.Core.transform (m := Lean.CoreM) target fun expression => do
      match expression with
      | .mdata _ body => return .visit body
      | _ => return .continue
    let structurallyEqual := Lean.Expr.equal currentType.consumeMData targetCanonical.consumeMData
    unless structurallyEqual do
      _root_.liftM <| Lean.Core.liftIOCore do
        if let some (path, expected, provided) := firstProofAlignmentDifference065 20 "afterThreeExplicitContextTransports" targetCanonical currentType then
          IO.eprintln s!"PROOF_CONTEXT_FIRST_DIFFERENCE069 {path}.expected {proofAlignmentShape065 expected}"
          IO.eprintln s!"PROOF_CONTEXT_FIRST_DIFFERENCE069 {path}.provided {proofAlignmentShape065 provided}"
        let stream ← IO.getStderr
        stream.flush
        throw (IO.userError "PROOF_CONTEXT_LITERAL_TYPE_NOT_EXACT069")
    proofAlignmentPhase065 reportPhases "PROOF_CONTEXT_LITERAL_TYPE_STRUCTURALLY_EXACT069"
    if diagnosticOnly then
      _root_.liftM <| Lean.Core.liftIOCore do
        IO.eprintln "DIAGNOSTIC_CONTEXT_TRANSPORT_CONSTRUCTION_COMPLETE069"
        let stream ← IO.getStderr
        stream.flush
        throw (IO.userError "DIAGNOSTIC_ONLY_STOP_BEFORE_ORDINARY_EXACT069")
    proofAlignmentPhase065 reportPhases "PROOF_CONTEXT_BEFORE_STANDARD_TERM_EMBEDDING069"
    let syntaxTerm ← _root_.liftM <| Lean.Elab.Term.exprToSyntax currentProof
    proofAlignmentPhase065 reportPhases "PROOF_CONTEXT_BEFORE_ORDINARY_EXACT069"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $syntaxTerm))
    proofAlignmentPhase065 reportPhases "PROOF_CONTEXT_ORDINARY_EXACT_COMPLETED069"

/-- The ACTUAL ORIGINAL P1 named coordinate D has native chart coefficient1.
All coordinate/image/frame/D data are derived internally; no computed-value premise. -/
theorem actualProjectiveLinePolynomialDifferentialRestrictionFrameIso_coordinate (b : Bool) :
    (actualProjectiveLinePolynomialDifferentialRestrictionFrameIso K b).hom.val.app (op ⊤)
      ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.map
        (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
        (actualRelativeDifferentialSection (projectiveLineProjToBase K)
          (Proj.basicOpen (grading Iline) (coordinate Iline b))
          ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
            (chartCoordinate Iline b (!b))))) =
      (1 : Γ(Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)), ⊤)) := by
  have submonoidAlignment := @originalSubmonoidProofInstanceEquality065.{u} K ‹CommRing K›
  have subgroupAlignment := @originalSubgroupProofInstanceEquality065.{u} K ‹CommRing K›
  have scalarTowerAlignment := @originalScalarTowerProofInstanceEquality068.{u} K ‹CommRing K›
  have closed := @originalFinalLiteralUniformCoefficient054.{u} K ‹CommRing K›
  have pointwise := closed b
  run_tac transportOriginalPointwiseProofInstances069 false false

end PfaffianDescent
end
