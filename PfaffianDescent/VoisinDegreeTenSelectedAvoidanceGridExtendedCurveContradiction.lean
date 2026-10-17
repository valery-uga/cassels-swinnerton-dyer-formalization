import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCurveFiniteContradiction
import PfaffianDescent.VoisinFiniteFieldBaseChangeDescent

/-! A finite triple over an extension field excludes a curve defined over
the original field, without requiring the extended ideal to remain prime. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_finiteTriple_not_contained_in_extendedHeightTwoPrime
    {K L : Type u} [Field K] [Field L] [Algebra K L] {a b c : ℕ}
    (p q r : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (hCheight : C.toIdeal.height = 2) :
    let D := HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap K L)) C
    ¬ (p ∈ D.toIdeal ∧ q ∈ D.toIdeal ∧ r ∈ D.toIdeal) := by
  dsimp only
  rintro ⟨hpD, hqD, hrD⟩
  let D := HomogeneousIdeal.map
    (ambientCoefficientGradedRingHom (algebraMap K L)) C
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  have hJD : J ≤ D := by
    change Ideal.span ({p, q, r} : Set _) ≤ D.toIdeal
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl | rfl)
    · exact hpD
    · exact hqD
    · exact hrD
  letI : IsClosedImmersion (schemeQuotientMap J D hJD) :=
    schemeQuotientMap_closedImmersion J D hJD
  haveI : IsFinite (toBase D) := by
    rw [← schemeQuotientMap_toBase J D hJD]
    infer_instance
  have hCD : C.toIdeal.map (MvPolynomial.map (algebraMap K L)) = D.toIdeal := rfl
  let g : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let e : scheme D ≅ pullback (toBase C) g :=
    projectiveBaseChangeIso (algebraMap K L) C D hCD
  have he : e.hom ≫ pullback.snd (toBase C) g = toBase D :=
    projectiveBaseChangeIso_hom_snd (algebraMap K L) C D hCD
  haveI : IsFinite (e.inv ≫ (e.hom ≫ pullback.snd (toBase C) g)) := by
    rw [he]
    infer_instance
  haveI : IsFinite (pullback.snd (toBase C) g) := by
    simpa only [Iso.inv_hom_id_assoc] using
      (inferInstance : IsFinite
        (e.inv ≫ (e.hom ≫ pullback.snd (toBase C) g)))
  haveI : IsFinite (toBase C) :=
    isFinite_of_isFinite_fieldBaseChange (L := L) (toBase C)
  exact voisinDegreeTenSelectedAvoidance_heightTwoPrime_not_finite
    C hCprime hCheight inferInstance

end PfaffianDescent
