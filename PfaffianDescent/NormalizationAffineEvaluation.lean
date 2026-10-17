import PfaffianDescent.CorayGenericNormalizationQuotientAffineSections
import Mathlib.AlgebraicGeometry.ResidueField

/-! Source only. Closed-point evaluation on actual affine neighborhoods.
No residue-preserving normalization lift or defect bound is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual Spec evaluation is onto at a maximal ideal. The proof uses
the literal residue-field isomorphism and its actual algebra-map formula. -/
theorem spec_globalEvaluation_surjective_of_maximal
    (R : CommRingCat.{u}) (y : Spec R) [y.asIdeal.IsMaximal] :
    Function.Surjective ((Spec R).Γevaluation y) := by
  have hs : Function.Surjective
      (CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R y).inv) :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso R y).inv).surjective.comp
      y.asIdeal.algebraMap_residueField_surjective
  rw [Scheme.Spec.algebraMap_residueFieldIso_inv] at hs
  intro z
  obtain ⟨a, ha⟩ := hs z
  exact ⟨(Scheme.ΓSpecIso R).inv a, ha⟩

/-- The actual evaluation on an affine open is onto at every corresponding
closed point. Native fromSpec and native residue maps identify the diagram. -/
theorem affineOpen_evaluation_surjective_fromSpec_of_maximal
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (y : Spec Γ(X, U)) [y.asIdeal.IsMaximal]
    (hy : hU.fromSpec y ∈ U) :
    Function.Surjective (X.evaluation U (hU.fromSpec y) hy) := by
  let f := hU.fromSpec
  have hsurj := spec_globalEvaluation_surjective_of_maximal Γ(X, U) y
  have hinj : Function.Injective (f.residueFieldMap y) :=
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap y)).injective
  intro z
  obtain ⟨s, hs⟩ := hsurj (f.residueFieldMap y z)
  let a : Γ(X, U) := (Scheme.ΓSpecIso Γ(X, U)).hom s
  refine ⟨a, hinj ?_⟩
  rw [Scheme.evaluation_naturality_apply f y hy]
  have happ : f.app U a =
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op s := by
    exact ConcreteCategory.congr_hom hU.ΓSpecIso_hom_fromSpec_app s
  rw [happ]
  change (Spec Γ(X, U)).residue y
    ((Spec Γ(X, U)).presheaf.germ (f ⁻¹ᵁ U) y hy
      ((Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs

/-- Actual native affine evaluation is onto at an actual closed point. -/
theorem affineOpen_evaluation_surjective_at_closedPoint
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (hclosed : IsClosed ({x} : Set X)) :
    Function.Surjective (X.evaluation U x hx) := by
  let y := hU.primeIdealOf ⟨x, hx⟩
  letI : y.asIdeal.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hx⟩ hclosed
  have hxy : hU.fromSpec y = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hy : hU.fromSpec y ∈ U := hxy.symm ▸ hx
  have H : ∀ hz : hU.fromSpec y ∈ U,
      Function.Surjective (X.evaluation U (hU.fromSpec y) hz) :=
    fun hz => affineOpen_evaluation_surjective_fromSpec_of_maximal X U hU y hz
  exact (Eq.mp (congrArg (fun z : X => ∀ hz : z ∈ U,
    Function.Surjective (X.evaluation U z hz)) hxy) H) hx

end PfaffianDescent.Coray
