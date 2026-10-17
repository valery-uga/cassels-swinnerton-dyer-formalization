import PfaffianDescent.UniversalCyclicMatrixQuotient282
import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.Basic

/-! The actual affine embedded family cut for the original universal
whole quotient. All geometric properties are derived from its genuine
finite basis. No Hilbert representative or family-property premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

lemma affineWholeQuotient_finite_flat_rank289
    {C : Type u} [CommRing C] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) C))
    (b : Module.Basis (Fin n) C (MvPolynomial (Fin m) C ⧸ I)) :
    IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap C (MvPolynomial (Fin m) C ⧸ I)))) ∧
    Flat (Spec.map (CommRingCat.ofHom
      (algebraMap C (MvPolynomial (Fin m) C ⧸ I)))) ∧
    ∀ x : PrimeSpectrum C,
      (Spec.map (CommRingCat.ofHom
        (algebraMap C (MvPolynomial (Fin m) C ⧸ I)))).finrank x = n := by
  letI : Module.Free C (MvPolynomial (Fin m) C ⧸ I) := Module.Free.of_basis b
  letI : Module.Finite C (MvPolynomial (Fin m) C ⧸ I) := Module.Finite.of_basis b
  have hf : (algebraMap C (MvPolynomial (Fin m) C ⧸ I)).Finite :=
    RingHom.finite_algebraMap.mpr inferInstance
  have ht : (algebraMap C (MvPolynomial (Fin m) C ⧸ I)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  refine ⟨(IsFinite.SpecMap_iff _).mpr hf, Flat.SpecMap_iff.mpr ht, ?_⟩
  intro x
  letI : Nontrivial C := x.nontrivial
  rw [Scheme.Hom.finrank_SpecMap_algebraMap]
  rw [congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := C) (M := MvPolynomial (Fin m) C ⧸ I)) x]
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rfl

def affineWholeQuotientHilbertPoint289
    {C : Type u} [CommRing C] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) C))
    (b : Module.Basis (Fin n) C (MvPolynomial (Fin m) C ⧸ I)) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C)))) n := by
  let F := Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C)))
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hfac : i ≫ F = Spec.map (CommRingCat.ofHom
      (algebraMap C (MvPolynomial (Fin m) C ⧸ I))) := by
    dsimp only [i, F]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.mk_comp_algebraMap]
  have h := affineWholeQuotient_finite_flat_rank289 I b
  letI : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective
  letI : IsFinite (i ≫ F) := hfac.symm ▸ h.1
  letI : Flat (i ≫ F) := hfac.symm ▸ h.2.1
  exact closedImmersionHilbertPoint195 F i n (fun x => hfac.symm ▸ h.2.2 x)

lemma affineWholeQuotientHilbertPoint_ideal289
    {C : Type u} [CommRing C] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) C))
    (b : Module.Basis (Fin n) C (MvPolynomial (Fin m) C ⧸ I)) :
    (affineWholeQuotientHilbertPoint289 I b).val =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker := rfl

/-- The actual universal quotient supplies its basis internally, so this
native embedded-family point asks for no finite/flat/rank or basis premise. -/
def universalCyclicAffineHilbertPoint289
    (R : Type u) [CommRing R] (m n : ℕ)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :=
  affineWholeQuotientHilbertPoint289
    (C := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n)
    (universalCyclicWholeAmbientIdeal282 R m n B k)
    (universalCyclicWholeAmbientMonomialBasis282 R m n B k)

end PfaffianDescent
