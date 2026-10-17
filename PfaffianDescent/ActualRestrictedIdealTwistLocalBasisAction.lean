import PfaffianDescent.ActualRestrictedTwistUnitLocalBasisAction
import PfaffianDescent.ActualModuleLocalTensorSection
import PfaffianDescent.ActualTensorUnitLeftPureTensor
import PfaffianDescent.ActualIdealTwistRestrictionInclusion

/- SOURCE ONLY / UNVERIFIED. LOCAL pure generators in an actual ideal
twist map to SAME untwisted generators under inclusion-compatible chart
refinement. Auxiliary squares are actual derived inclusion laws; the
original caller supplies no comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualRestrictedIdealTwistLocalBasisAction
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (J T : X.Modules) (N : Y.Modules)
    (a : J ⟶ schemeModuleUnit X) (b : N ⟶ schemeModuleUnit Y) [Mono b]
    (v : schemeModuleUnit X ⟶ T)
    (p : (Scheme.Modules.restrictFunctor f).obj T ≅ schemeModuleUnit Y)
    (e : (Scheme.Modules.restrictFunctor f).obj (schemeModuleTensor J T) ≅ N)
    (n : (Scheme.Modules.restrictFunctor f).obj J ≅ N)
    (hb : (Scheme.Modules.restrictFunctor f).map v ≫ p.hom =
      (Scheme.Modules.restrictUnitIso f).hom)
    (he : e.hom ≫ b = (Scheme.Modules.restrictFunctor f).map
      (schemeModuleTensorMap a (𝟙 T) ≫ (schemeModuleTensorUnitLeftIso T).hom) ≫ p.hom)
    (hn : n.hom ≫ b = (Scheme.Modules.restrictFunctor f).map a ≫
      (Scheme.Modules.restrictUnitIso f).hom)
    (U : X.Opens) (m : J.val.obj (op U)) :
    e.hom.val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f).unit.app (schemeModuleTensor J T)).val.app
        (op U) (actualModuleLocalTensorSection J T U m
          (v.val.app (op U) (1 : Γ(X, U))))) =
    n.hom.val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f).unit.app J).val.app (op U) m) := by
  let R := Scheme.Modules.restrictFunctor f
  let eta := (Scheme.Modules.restrictAdjunction f).unit
  let V := f ⁻¹ᵁ U
  let t := v.val.app (op U) (1 : Γ(X, U))
  let z := actualModuleLocalTensorSection J T U m t
  let c := schemeModuleTensorMap a (𝟙 T) ≫ (schemeModuleTensorUnitLeftIso T).hom
  let r := a.val.app (op U) m
  have hc : c.val.app (op U) z = r • t := by
    change (schemeModuleTensorUnitLeftIso T).hom.val.app (op U)
      ((schemeModuleTensorMap a (𝟙 T)).val.app (op U) z) = _
    rw [actualModuleLocalTensorSection_naturality]
    exact actualTensorUnitLeftIso_sheafification_tmul T (op U) r t
  have hec := congrArg (fun h => h.val.app (op V)
    ((eta.app (schemeModuleTensor J T)).val.app (op U) z)) he
  have hnc := congrArg (fun h => h.val.app (op V)
    ((eta.app J).val.app (op U) m)) hn
  have hetaC := congrArg (fun h => h.val.app (op U) z) (eta.naturality c).symm
  have hetaA := congrArg (fun h => h.val.app (op U) m) (eta.naturality a).symm
  change (R.map c).val.app (op V)
      ((eta.app (schemeModuleTensor J T)).val.app (op U) z) =
    (eta.app T).val.app (op U) (c.val.app (op U) z) at hetaC
  change (R.map a).val.app (op V) ((eta.app J).val.app (op U) m) =
    (eta.app (schemeModuleUnit X)).val.app (op U) r at hetaA
  change b.val.app (op V) (e.hom.val.app (op V) _) =
    p.hom.val.app (op V) ((R.map c).val.app (op V) _) at hec
  change b.val.app (op V) (n.hom.val.app (op V) _) =
    (Scheme.Modules.restrictUnitIso f).hom.val.app (op V)
      ((R.map a).val.app (op V) _) at hnc
  rw [hetaC, hc] at hec
  rw [hetaA] at hnc
  have hsmul : (eta.app T).val.app (op U) (r • t) =
      (show Γ(X, f ''ᵁ V) from
        (eta.app (schemeModuleUnit X)).val.app (op U) r) •
        (show T.val.obj (op (f ''ᵁ V)) from
          (eta.app T).val.app (op U) t) := by
    change T.val.map (homOfLE (f.image_preimage_le U)).op (r • t) =
      X.presheaf.map (homOfLE (f.image_preimage_le U)).op r •
        T.val.map (homOfLE (f.image_preimage_le U)).op t
    exact T.val.map_smul _ r t
  rw [hsmul, actualRestrictedTwistUnitLocalScalarAction,
    actualRestrictedTwistUnitLocalBasisAction f T v p hb U] at hec
  have hmul :
      (show Γ(Y, V) from (Scheme.Modules.restrictUnitIso f).hom.val.app (op V)
        ((eta.app (schemeModuleUnit X)).val.app (op U) r)) • (1 : Γ(Y, V)) =
      (show Γ(Y, V) from (Scheme.Modules.restrictUnitIso f).hom.val.app (op V)
        ((eta.app (schemeModuleUnit X)).val.app (op U) r)) := mul_one _
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op V)
  letI : Mono (b.val.app (op V)) := Functor.map_mono E b
  apply (ModuleCat.mono_iff_injective (b.val.app (op V))).mp (by infer_instance)
  exact (hec.trans hmul).trans hnc.symm

end PfaffianDescent
