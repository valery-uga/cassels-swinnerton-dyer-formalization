import PfaffianDescent.SchemeModuleOriginalBaseStalkResidueTower
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u v
variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]
variable {X : Scheme.{u}} (a : Spec (.of B) ⟶ X) [IsOpenImmersion a]

/-- The literal chart localization map to the ORIGINAL stalk. -/
def openChartToOriginalStalk192 (z : Spec (.of B)) :
    B →+* X.presheaf.stalk (a z) :=
  (inv (a.stalkMap z)).hom.comp (StructureSheaf.toStalk B z).hom

/-- Localization is transported through the actual open-immersion stalk
isomorphism, with its action defined by the literal inverse stalk map. -/
lemma openChartToOriginalStalk_isLocalization192 (z : Spec (.of B)) :
    letI : z.asIdeal.IsPrime := z.isPrime
    letI : Algebra B (X.presheaf.stalk (a z)) :=
      (openChartToOriginalStalk192 a z).toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk (a z)) z.asIdeal := by
  letI : z.asIdeal.IsPrime := z.isPrime
  letI : Algebra B ((Spec (.of B)).presheaf.stalk z) :=
    StructureSheaf.stalkAlgebra B z
  letI : IsLocalization.AtPrime ((Spec (.of B)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B z
  letI : Algebra B (X.presheaf.stalk (a z)) :=
    (openChartToOriginalStalk192 a z).toAlgebra
  let e : (Spec (.of B)).presheaf.stalk z ≃ₐ[B] X.presheaf.stalk (a z) :=
    { (asIso (a.stalkMap z)).symm.commRingCatIsoToRingEquiv with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv z.asIdeal.primeCompl e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chart action preserves the independently defined ORIGINAL base
constants. Its compatibility is derived from stalk naturality and the actual
chart/base square; no comparison of algebras is a hypothesis. -/
lemma openChartToOriginalStalk_base192
    (pi : X ⟶ Spec (.of K))
    (ha : a ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (z : Spec (.of B)) :
    (openChartToOriginalStalk192 a z).comp (algebraMap K B) =
      schemeStalkBaseRingHom pi (a z) := by
  letI : IsIso (a.stalkMap z) := inferInstance
  have hcat : CommRingCat.ofHom (algebraMap K B) ≫ StructureSheaf.toStalk B z =
      CommRingCat.ofHom (schemeStalkBaseRingHom pi (a z)) ≫ a.stalkMap z := by
    apply Spec.map_injective
    calc
      Spec.map (CommRingCat.ofHom (algebraMap K B) ≫ StructureSheaf.toStalk B z) =
          Spec.map (StructureSheaf.toStalk B z) ≫
            Spec.map (CommRingCat.ofHom (algebraMap K B)) := Spec.map_comp _ _
      _ = (Spec (.of B)).fromSpecStalk z ≫
          Spec.map (CommRingCat.ofHom (algebraMap K B)) :=
        congrArg (fun q => q ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)))
          (Spec.fromSpecStalk_eq' (.of B) z).symm
      _ = (Spec (.of B)).fromSpecStalk z ≫ (a ≫ pi) :=
        congrArg (fun q => (Spec (.of B)).fromSpecStalk z ≫ q) ha.symm
      _ = ((Spec (.of B)).fromSpecStalk z ≫ a) ≫ pi :=
        (Category.assoc _ _ _).symm
      _ = (Spec.map (a.stalkMap z) ≫ X.fromSpecStalk (a z)) ≫ pi :=
        congrArg (fun q => q ≫ pi)
          (Scheme.SpecMap_stalkMap_fromSpecStalk a (x := z)).symm
      _ = Spec.map (a.stalkMap z) ≫
          Spec.map (CommRingCat.ofHom (schemeStalkBaseRingHom pi (a z))) := by
        rw [Category.assoc, ← schemeStalkBaseRingHom_spec]
      _ = Spec.map (CommRingCat.ofHom (schemeStalkBaseRingHom pi (a z)) ≫
          a.stalkMap z) := (Spec.map_comp _ _).symm
  have hc := congrArg (fun c => c ≫ inv (a.stalkMap z)) hcat
  have hc' : CommRingCat.ofHom (algebraMap K B) ≫ StructureSheaf.toStalk B z ≫
      inv (a.stalkMap z) = CommRingCat.ofHom (schemeStalkBaseRingHom pi (a z)) := by
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using hc
  exact congrArg CommRingCat.Hom.hom hc'

/-- Genuine basis on the ORIGINAL native stalk, using its original base
algebra. Only the ordinary affine-chart basis is consumed here. -/
def openChartOriginalStalkKaehlerBasis192
    (pi : X ⟶ Spec (.of K))
    (ha : a ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (z : Spec (.of B)) {ι : Type v}
    (b : Module.Basis ι B (KaehlerDifferential K B)) :
    letI := schemeStalkBaseAlgebra pi (a z)
    Module.Basis ι (X.presheaf.stalk (a z))
      (KaehlerDifferential K (X.presheaf.stalk (a z))) := by
  let R := X.presheaf.stalk (a z)
  letI : z.asIdeal.IsPrime := z.isPrime
  letI := schemeStalkBaseAlgebra pi (a z)
  letI : Algebra B R := (openChartToOriginalStalk192 a z).toAlgebra
  letI : IsScalarTower K B R :=
    IsScalarTower.of_algebraMap_eq' (openChartToOriginalStalk_base192 a pi ha z).symm
  letI : IsLocalization.AtPrime R z.asIdeal :=
    openChartToOriginalStalk_isLocalization192 a z
  letI : Algebra.FormallyEtale B R :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := R) z.asIdeal.primeCompl
  exact (b.baseChange R).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K B R)

/-- The transported basis vector is the differential of the original chart
coordinate's actual inverse-stalk-map germ. -/
lemma openChartOriginalStalkKaehlerBasis_D192
    (pi : X ⟶ Spec (.of K))
    (ha : a ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (z : Spec (.of B)) {ι : Type v}
    (b : Module.Basis ι B (KaehlerDifferential K B)) (v : ι) (t : B)
    (ht : b v = KaehlerDifferential.D K B t) :
    letI := schemeStalkBaseAlgebra pi (a z)
    openChartOriginalStalkKaehlerBasis192 a pi ha z b v =
      KaehlerDifferential.D K (X.presheaf.stalk (a z))
        (openChartToOriginalStalk192 a z t) := by
  let R := X.presheaf.stalk (a z)
  letI : z.asIdeal.IsPrime := z.isPrime
  letI := schemeStalkBaseAlgebra pi (a z)
  letI : Algebra B R := (openChartToOriginalStalk192 a z).toAlgebra
  letI : IsScalarTower K B R :=
    IsScalarTower.of_algebraMap_eq' (openChartToOriginalStalk_base192 a pi ha z).symm
  letI : IsLocalization.AtPrime R z.asIdeal :=
    openChartToOriginalStalk_isLocalization192 a z
  letI : Algebra.FormallyEtale B R :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := R) z.asIdeal.primeCompl
  change (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K B R)
    ((b.baseChange R) v) = _
  rw [Module.Basis.baseChange_apply, ht,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

end PfaffianDescent.Coray
