import PfaffianDescent.VoisinFixedCubicGlobalIdealBaseChange
import PfaffianDescent.VoisinNormalizedFieldPointRegular

/-!
# Global ideal base change for a normalized local equation parameter

A residue-field cubic regular on the fixed cubic surface yields a
normalized equation over the local parameter ring. The canonical
ideal-sheaf map of its global projective intersection is invertible
after any further coefficient change.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_fixedCubic_localProjectiveGlobalIdealBaseChange_any
    {K T S : Type u} [Field K] [CommRing T] [IsLocalRing T]
    [Algebra K T] [CommRing S]
    (g : T →+* S)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (v : Spec (.of T) ⟶ projectiveParameters K (Fin 4) 3)
    (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
    (hp : p.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
    (hpoint : Spec.map (CommRingCat.ofHom
        (algebraMap T (IsLocalRing.ResidueField T))) ≫ v =
      projectiveEquationParameter
        (algebraMap K (IsLocalRing.ResidueField T)) p j hj)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal p)) :
    ∃ f : ParameterChartRing K (Fin 4) 3 j →+* T,
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j = v ∧
      IsRegular (Ideal.Quotient.mk
        (equationIdeal
          (a.map (algebraMap K (IsLocalRing.ResidueField T)))
          (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
        (((normalizedForm K (Fin 4) 3 j).map f).map
          (algebraMap T (IsLocalRing.ResidueField T)))) ∧
      (let q := (normalizedForm K (Fin 4) 3 j).map f
       let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
       let J := equationIdeal (a.map (algebraMap K T))
         (ha.map (algebraMap K T))
       let Q := J ⊔ equationIdeal q hq
       let hJQ : J.toIdeal ≤ Q.toIdeal := by
         rw [HomogeneousIdeal.toIdeal_sup]
         exact le_sup_left
       let cJ := projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
         (coefficientChangedHomogeneousIdeal_toIdeal g J)
       let i := schemeQuotientMap J Q hJQ
       letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion J Q hJQ
       IsIso (closedImmersionIdealBaseChangeHom cJ i)) := by
  obtain ⟨f, hf, hres⟩ :=
    localSpec_projectiveEquationChartMap v p hp j hj hpoint
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  have hreg' : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (q.map (algebraMap T (IsLocalRing.ResidueField T)))) := by
    simpa only [q, MvPolynomial.map_map, hres] using
      (normalizedCubic_fieldPoint_regularModFixedCubic
        (algebraMap K (IsLocalRing.ResidueField T))
        a ha p hp j hj hreg)
  exact ⟨f, hf, hreg',
    isIso_fixedCubicGlobalIdealBaseChange_any g a ha q hq hreg'⟩

end PfaffianDescent
