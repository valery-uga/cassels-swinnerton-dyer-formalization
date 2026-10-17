import AllCharacteristics.PointDegrees
import Mathlib.RingTheory.Length
import Mathlib.AlgebraicGeometry.Artinian

/-!
# Scheme degrees and affine residue fields

These comparisons identify scheme-theoretic local lengths and residue degrees
with the algebraic quantities used in the finite-algebra degree formula.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- Isomorphic rings have equal lengths as modules over themselves. -/
theorem ring_length_eq_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm

/-- The local length at a point of an affine scheme is the length of its
localization at the corresponding prime. -/
theorem affine_stalk_length_eq
    (A : CommRingCat.{u}) (q : PrimeSpectrum A) :
    Module.length ((Spec A).presheaf.stalk q) ((Spec A).presheaf.stalk q) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
  ring_length_eq_of_ringEquiv (Spec.stalkIso A q).commRingCatIsoToRingEquiv

/-- The residue degree of an affine scheme over a field equals the full degree
of the algebraic residue field at its prime. -/
theorem affine_residueDegree_eq_finrank
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] (q : PrimeSpectrum A) :
    (Spec.map (CommRingCat.ofHom (algebraMap k A))).residueDegree q =
      Module.finrank k q.asIdeal.ResidueField := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let r := (Spec (.of k)).fromSpecResidueField (f q)
  let b := Spec.preimage r
  have hr : IsIso r := isIso_fromSpecResidueField_of_field k (f q)
  have : IsIso (Scheme.Spec.map b.op) := by
    change IsIso (Spec.map b)
    simpa only [b, Spec.map_preimage] using hr
  have : IsIso b.op := isIso_of_reflects_iso b.op Scheme.Spec
  have : IsIso b := isIso_of_op b
  let i := (asIso b).commRingCatIsoToRingEquiv
  let j := (Scheme.Spec.residueFieldIso (.of A) q).symm.commRingCatIsoToRingEquiv
  let := (f.residueFieldMap q).hom.toAlgebra
  have hc : b ≫ f.residueFieldMap q =
      CommRingCat.ofHom (algebraMap k q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of A) q).inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    rw [show Spec.map b = r from Spec.map_preimage r]
    change Spec.map (f.residueFieldMap q) ≫
      (Spec (.of k)).fromSpecResidueField (f q) = _
    calc
      _ = (Spec (.of A)).fromSpecResidueField q ≫ f :=
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f q
      _ = _ := by
        have he := congrArg (fun m : Spec ((Spec (.of A)).residueField q) ⟶ Spec (.of A) ↦ m ≫ f)
          (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) q)
        have ha : CommRingCat.ofHom (algebraMap k A) ≫
            CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField) =
            CommRingCat.ofHom (algebraMap k q.asIdeal.ResidueField) := by
          ext a
          exact (IsScalarTower.algebraMap_apply k A q.asIdeal.ResidueField a).symm
        have hc' := congrArg (fun m ↦ m ≫ (Scheme.Spec.residueFieldIso (.of A) q).inv) ha
        simp only [Category.assoc] at hc'
        simpa only [f, Category.assoc, ← Spec.map_comp, hc'] using he.symm
  apply (Algebra.finrank_eq_of_equiv_equiv i j ?_).symm
  exact congrArg CommRingCat.Hom.hom hc

end AllCharacteristics
