import PfaffianDescent.ActualRelativeDifferentialSection
import PfaffianDescent.ActualAffineSheafPointClass
import Mathlib.RingTheory.TensorProduct.Basic

/- SOURCE ONLY / UNVERIFIED. A forward map into the GENUINE differential
fiber, constructed from actual ring differentials, the actual sheafification
unit and actual point adjunction. No sheaf comparison, inverse, quasicoherence
or fiber dimension is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]

private lemma actualAffineTopDifferentialScalarSquare :
    (𝟙 (CommRingCat.of k)) ≫
      (schemeBaseScalarPresheafMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app (op ⊤) =
      CommRingCat.ofHom (algebraMap k R) ≫ (Scheme.ΓSpecIso (.of R)).inv := by
  let X := Spec (CommRingCat.of R)
  have hres : X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op =
      𝟙 _ := by
    rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op (⊤ : X.Opens)) from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  change (𝟙 (CommRingCat.of k)) ≫
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
        X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op) = _
  rw [Category.id_comp, hres, Category.comp_id]
  exact (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap k R))).symm

private def actualKaehlerModuleForAlgebra (a : Algebra k R) : ModuleCat R :=
  letI : Algebra k R := a
  ModuleCat.of R (KaehlerDifferential k R)

private lemma actualKaehlerAlgebraTransport_D
    (a b : Algebra k R) (h : a = b) (r : R) :
    (eqToIso (congrArg (actualKaehlerModuleForAlgebra (k := k) (R := R)) h)).hom
      (letI : Algebra k R := a
       KaehlerDifferential.D k R r) =
      (letI : Algebra k R := b
       KaehlerDifferential.D k R r) := by
  cases h
  rfl

/- Bundled differentials rebuild the algebra from its map. That algebra is
   equal to the original one, but it is not generally definitionally equal. -/
private def actualNativeBundledKaehlerIso :
    ModuleCat.of R (KaehlerDifferential k R) ≅
      CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap k R)) := by
  let a : Algebra k R := inferInstance
  let b : Algebra k R := (algebraMap k R).toAlgebra
  have h : a = b := (@toAlgebra_algebraMap k R _ _ a).symm
  change actualKaehlerModuleForAlgebra a ≅ actualKaehlerModuleForAlgebra b
  exact eqToIso (congrArg (actualKaehlerModuleForAlgebra (k := k) (R := R)) h)

private lemma actualNativeBundledKaehlerIso_D (r : R) :
    (actualNativeBundledKaehlerIso (k := k) (R := R)).hom
      (KaehlerDifferential.D k R r) =
    CommRingCat.KaehlerDifferential.d
      (f := CommRingCat.ofHom (algebraMap k R)) r := by
  let a : Algebra k R := inferInstance
  let b : Algebra k R := (algebraMap k R).toAlgebra
  have h : a = b := (@toAlgebra_algebraMap k R _ _ a).symm
  change (eqToIso (congrArg
      (actualKaehlerModuleForAlgebra (k := k) (R := R)) h)).hom
      (letI : Algebra k R := a
       KaehlerDifferential.D k R r) =
      (letI : Algebra k R := b
       KaehlerDifferential.D k R r)
  exact actualKaehlerAlgebraTransport_D a b h r

/-- The actual top universal differential followed by sheafification.
The top ring square is derived internally; this is a forward map only. -/
def actualAffineDifferentialTopToGenuineSheaf :
    KaehlerDifferential k R →ₗ[R]
      (moduleSpecΓFunctor (R := .of R)).obj
        (schemeRelativeDifferentials
          (Spec.map (CommRingCat.ofHom (algebraMap k R)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let M := schemeRelativeDifferentials g
  let c := (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (.of R)).ringCatSheaf.obj)).unit.app
      (schemeRelativeDifferentialsPresheaf g)
  let v : CommRingCat.KaehlerDifferential
      (CommRingCat.ofHom (algebraMap k R)) ⟶
      (moduleSpecΓFunctor (R := .of R)).obj M :=
    CommRingCat.KaehlerDifferential.map
      (actualAffineTopDifferentialScalarSquare (k := k) (R := R)) ≫
        (ModuleCat.restrictScalars c.hom).map (eta.app (op ⊤))
  exact ((actualNativeBundledKaehlerIso (k := k) (R := R)).hom ≫ v).hom

lemma actualAffineDifferentialTopToGenuineSheaf_D (r : R) :
    actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R)
      (KaehlerDifferential.D k R r) =
    actualRelativeDifferentialSection
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let c := (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (.of R)).ringCatSheaf.obj)).unit.app
      (schemeRelativeDifferentialsPresheaf g)
  let v : CommRingCat.KaehlerDifferential
      (CommRingCat.ofHom (algebraMap k R)) ⟶
      (moduleSpecΓFunctor (R := .of R)).obj (schemeRelativeDifferentials g) :=
    CommRingCat.KaehlerDifferential.map
      (actualAffineTopDifferentialScalarSquare (k := k) (R := R)) ≫
        (ModuleCat.restrictScalars c.hom).map (eta.app (op ⊤))
  have he := actualNativeBundledKaehlerIso_D (k := k) (R := R) r
  have hm := CommRingCat.KaehlerDifferential.map_d
    (actualAffineTopDifferentialScalarSquare (k := k) (R := R)) r
  have hv : v (CommRingCat.KaehlerDifferential.d
      (f := CommRingCat.ofHom (algebraMap k R)) r) =
      actualRelativeDifferentialSection g ⊤ (c.hom r) :=
    congrArg (fun z => eta.app (op ⊤) z) hm
  change v ((actualNativeBundledKaehlerIso (k := k) (R := R)).hom
    (KaehlerDifferential.D k R r)) = _
  exact (congrArg (fun z => v z) he).trans hv

private def actualNativeAffinePointClassLinearMap
    (rho : R →+* L) (M : (Spec (.of R)).Modules) :
    let N := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj M)
    letI : Module R N := Module.compHom N rho
    (moduleSpecΓFunctor (R := .of R)).obj M →ₗ[R] N := by
  let q := Spec.map (CommRingCat.ofHom rho)
  let N := (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M)
  letI : Module R N := Module.compHom N rho
  let G := moduleSpecΓFunctor (R := CommRingCat.of R)
  let point : G.obj M ⟶ (ModuleCat.restrictScalars rho).obj N :=
    G.map ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M) ≫
      (affineGammaPushforwardNatIso (CommRingCat.ofHom rho)).hom.app
        ((Scheme.Modules.pullback q).obj M)
  exact
    { toFun := fun z => point z
      map_add' := fun x y => point.hom.map_add x y
      map_smul' := fun a z => point.hom.map_smul a z }

/-- Canonical forward comparison. It is not asserted to be an equivalence. -/
def actualAffineGenuineDifferentialForwardPointMap (rho : R →+* L) :
    letI : Algebra R L := rho.toAlgebra
    L ⊗[R] KaehlerDifferential k R →ₗ[L]
      (moduleSpecΓFunctor (R := .of L)).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
          (schemeRelativeDifferentials
            (Spec.map (CommRingCat.ofHom (algebraMap k R))))) := by
  letI : Algebra R L := rho.toAlgebra
  let q := Spec.map (CommRingCat.ofHom rho)
  let M := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let N := (moduleSpecΓFunctor (R := .of L)).obj
    ((Scheme.Modules.pullback q).obj M)
  letI : Module R N := Module.compHom N rho
  letI : IsScalarTower R L N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact LinearMap.liftBaseChange L
    ((actualNativeAffinePointClassLinearMap rho M).comp
      (actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R)))

lemma actualAffineGenuineDifferentialForwardPointMap_one_tmul_D
    (rho : R →+* L) (r : R) :
    letI : Algebra R L := rho.toAlgebra
    actualAffineGenuineDifferentialForwardPointMap (k := k) rho
      ((1 : L) ⊗ₜ[R] KaehlerDifferential.D k R r) =
    actualAffineSheafPointClass (CommRingCat.ofHom rho)
      (schemeRelativeDifferentials
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
        ((Scheme.ΓSpecIso (.of R)).inv.hom r)) := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  let q := Spec.map (CommRingCat.ofHom rho)
  let M : (Spec (.of R)).Modules := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let N := (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M)
  letI : Module R N := Module.compHom N rho
  letI : IsScalarTower R L N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let t := actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R)
  let point := actualNativeAffinePointClassLinearMap rho M
  have hlift : LinearMap.liftBaseChange L (point.comp t)
      ((1 : L) ⊗ₜ[R] KaehlerDifferential.D k R r) =
      (point.comp t) (KaehlerDifferential.D k R r) :=
    LinearMap.liftBaseChange_one_tmul L (point.comp t) (KaehlerDifferential.D k R r)
  have heval : (point.comp t) (KaehlerDifferential.D k R r) =
      point (t (KaehlerDifferential.D k R r)) := rfl
  have htop := actualAffineDifferentialTopToGenuineSheaf_D (k := k) (R := R) r
  have hpoint : point (actualRelativeDifferentialSection
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
        ((Scheme.ΓSpecIso (.of R)).inv.hom r)) =
      actualAffineSheafPointClass (CommRingCat.ofHom rho) M
        (actualRelativeDifferentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
            ((Scheme.ΓSpecIso (.of R)).inv.hom r)) := rfl
  change LinearMap.liftBaseChange L (point.comp t)
    ((1 : L) ⊗ₜ[R] KaehlerDifferential.D k R r) = _
  exact hlift.trans (heval.trans
    ((congrArg (fun z => point z) htop).trans hpoint))

end PfaffianDescent
