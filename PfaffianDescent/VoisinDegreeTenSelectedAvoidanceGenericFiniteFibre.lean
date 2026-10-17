import PfaffianDescent.RelativeHomogeneousTripleIntersectionFamily
import PfaffianDescent.VoisinGenericTripleFinite

/-! # Actual generic finite fibre for arbitrary-degree homogeneous triples -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- A constructed finite generic neighborhood gives a finite native
homogeneous triple after any injective map to a field. The degrees need
not be the old cubic--two-quadrics degrees. -/
theorem voisinDegreeTenSelectedAvoidance_triple_isFinite_at_injectiveFieldPoint
    {R F : Type u} [CommRing R] [IsDomain R] [Field F]
    {a b c : ℕ} (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (V : (Spec (.of R)).Opens) (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ∣_ V)]
    (g : R →+* F) (hg : Function.Injective g) :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map g) (q.map g) (r.map g) (hp.map g) (hq.map g) (hr.map g))) := by
  let f := relativeHomogeneousTripleIntersectionToBase p q r hp hq hr
  let base := Spec.map (CommRingCat.ofHom g)
  have hrange : Set.range base ⊆ Set.range V.ι := by
    rintro y ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint F := Subsingleton.elim x _
    rw [hx, specFieldMap_closedPoint_eq_genericPoint_of_injective g hg]
    rw [V.range_ι]
    exact hη
  let baseV := IsOpenImmersion.lift V.ι base hrange
  have hfac : baseV ≫ V.ι = base := IsOpenImmersion.lift_fac _ _ _
  haveI : IsFinite (pullback.snd f base) := by
    rw [← hfac]
    exact finite_pullback_of_factor_through_finite_open f V baseV
  let J := relativeHomogeneousTripleIntersectionHomogeneousIdeal
    (p.map g) (q.map g) (r.map g) (hp.map g) (hq.map g) (hr.map g)
  let e := relativeHomogeneousTripleIntersectionBaseChangeIso g p q r hp hq hr
  have he : e.hom ≫ pullback.snd f base = toBase J := by
    exact projectiveBaseChangeIso_hom_snd _ _ _
      (relativeHomogeneousTripleIntersectionHomogeneousIdeal_map g p q r hp hq hr)
  haveI : IsFinite (toBase J) := by
    rw [← he]
    infer_instance
  rw [← relativeHomogeneousTripleIntersectionHomogeneousIdeal_eq_triple]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_triple_generic_isFinite
    {R : Type u} [CommRing R] [IsDomain R]
    {a b c : ℕ} (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (V : (Spec (.of R)).Opens) (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ∣_ V)] :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap R (FractionRing R)))
      (q.map (algebraMap R (FractionRing R)))
      (r.map (algebraMap R (FractionRing R)))
      (hp.map (algebraMap R (FractionRing R)))
      (hq.map (algebraMap R (FractionRing R)))
      (hr.map (algebraMap R (FractionRing R))))) := by
  exact voisinDegreeTenSelectedAvoidance_triple_isFinite_at_injectiveFieldPoint
    p q r hp hq hr V hη (algebraMap R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R))

end PfaffianDescent
