import PfaffianDescent.NativeNormalizationResidueMaps
import PfaffianDescent.SchemeModuleBaseLinearCategory
import PfaffianDescent.FiniteProjectiveProjectionFormula

/-! Native original-K appLE, original residue spectrum and finite whole-fibre
rank actions. All comparisons are the literal maps of the SAME schemes. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics
universe u
variable {K : Type u} [Field K]
set_option autoImplicit false

/-- Native appLE is K-linear for both independently original structure maps.
The geometric base square and ordinary open containment supply compatibility;
there is no transported/replaced action or desired linearity premise. -/
def originalSectionAppLEAlgHom_of_baseSquare001
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (piY : Y ⟶ Spec (.of K)) (piX : X ⟶ Spec (.of K)) (hBase : f ≫ piY = piX)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    letI : Algebra K Γ(Y, U) := (schemeOpenBaseRingHom piY U).toAlgebra
    letI : Algebra K Γ(X, V) := (schemeOpenBaseRingHom piX V).toAlgebra
    Γ(Y, U) →ₐ[K] Γ(X, V) := by
  letI : Algebra K Γ(Y, U) := (schemeOpenBaseRingHom piY U).toAlgebra
  letI : Algebra K Γ(X, V) := (schemeOpenBaseRingHom piX V).toAlgebra
  refine { toRingHom := (f.appLE U V e).hom, commutes' := ?_ }
  intro k
  change X.presheaf.map (homOfLE e).op
      (f.app U (schemeOpenBaseRingHom piY U k)) = schemeOpenBaseRingHom piX V k
  rw [originalOpenBaseRingHom_section_naturality]
  simpa only [hBase] using
    schemeOpenBaseRingHom_restrict (f ≫ piY) (homOfLE e) k

/-- The ACTUAL residue spectrum's global functions and the SAME actual
residue field are K-algebra equivalent for pointAlgebra and the original
composite map. The equivalence is exactly native GammaSpecIso. -/
def originalPointResidueSpectrumGlobalSectionsAlgEquiv001
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (x : X) :
    let L := X.residueField x
    let ep := X.fromSpecResidueField x
    letI := pointAlgebra pi x
    letI : Algebra K Γ(Spec L, ⊤) := (schemeOpenBaseRingHom (ep ≫ pi) ⊤).toAlgebra
    Γ(Spec L, ⊤) ≃ₐ[K] L := by
  let L := X.residueField x
  let ep := X.fromSpecResidueField x
  letI := pointAlgebra pi x
  letI : Algebra K Γ(Spec L, ⊤) := (schemeOpenBaseRingHom (ep ≫ pi) ⊤).toAlgebra
  let e : Γ(Spec L, ⊤) ≃+* L := (Scheme.ΓSpecIso L).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro k
  change (Scheme.ΓSpecIso L).hom (schemeOpenBaseRingHom (ep ≫ pi) ⊤ k) = algebraMap K L k
  rw [schemeOpenBaseRingHom_top_apply]
  change (Scheme.ΓSpecIso L).hom ((ep ≫ pi).appTop ((Scheme.ΓSpecIso (.of K)).inv k)) = _
  have hBase : ep ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    (pointAlgebra_spec pi x).symm
  rw [hBase]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap K L)))
    ((Scheme.ΓSpecIso (.of K)).inv k)
  change (Scheme.ΓSpecIso L).hom
      ((Spec.map (CommRingCat.ofHom (algebraMap K L))).appTop
        ((Scheme.ΓSpecIso (.of K)).inv k)) =
    algebraMap K L ((Scheme.ΓSpecIso (.of K)).hom ((Scheme.ΓSpecIso (.of K)).inv k)) at h
  simpa using h

/-- Native original base action on the finite scheme's actual ring has
finite dimension equal to its ACTUAL finiteSchemeRank. The canonical finite
coefficient action is explicitly identified before any dimension comparison. -/
theorem finiteScheme_originalOpenTopRing_finite_and_finrank001
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) [IsFinite pi] :
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    Module.Finite K Γ(X, ⊤) ∧ Module.finrank K Γ(X, ⊤) = finiteSchemeRank pi := by
  let a := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  let b := PfaffianDescent.finiteSchemeCoefficientAlgebra pi
  have hMap : schemeOpenBaseRingHom pi ⊤ = @algebraMap K Γ(X, ⊤) _ _ b := by
    have hTop : schemeOpenBaseRingHom pi ⊤ = affineFunctionHom pi := by
      ext k
      exact schemeOpenBaseRingHom_top_apply pi k
    exact hTop.trans (PfaffianDescent.affineFunctionHom_eq_finiteSchemeCoefficient_algebraMap pi)
  have hAlgebra : b = a := Algebra.algebra_ext b a fun k => (RingHom.congr_fun hMap k).symm
  have hFinite : letI := b
      Module.Finite K Γ(X, ⊤) ∧ Module.finrank K Γ(X, ⊤) = finiteSchemeRank pi :=
    ⟨PfaffianDescent.finiteSchemeCoefficient_finite pi,
      PfaffianDescent.finiteSchemeCoefficient_finrank pi⟩
  exact Eq.mp (congrArg (fun t : Algebra K Γ(X, ⊤) =>
    letI := t
    Module.Finite K Γ(X, ⊤) ∧ Module.finrank K Γ(X, ⊤) = finiteSchemeRank pi) hAlgebra) hFinite

end PfaffianDescent.Coray
