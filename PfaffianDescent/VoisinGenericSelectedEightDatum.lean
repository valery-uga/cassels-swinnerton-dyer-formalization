import PfaffianDescent.VoisinGenericTripleEightSubscheme
import PfaffianDescent.TripleCompleteIntersectionToHypersurface
import AllCharacteristics.FiniteSubschemeFromImmersion

/-! The selected eight rational generic points as an ideal-defined datum. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def genericSelectedEightToCubic
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1) :
    (∐ fun _ : ULift.{u} (Fin 8) => Spec (.of (FractionRing R))) ⟶
      hypersurface (p.map (algebraMap R (FractionRing R)))
        (hp.map (algebraMap R (FractionRing R))) :=
  genericTripleIntersectionEightEmbedding
    p q r hp hq hr ell hell x hzero hnorm ≫
    tripleCompleteIntersectionToHypersurface
      (p.map (algebraMap R (FractionRing R)))
      (q.map (algebraMap R (FractionRing R)))
      (r.map (algebraMap R (FractionRing R)))
      (hp.map (algebraMap R (FractionRing R)))
      (hq.map (algebraMap R (FractionRing R)))
      (hr.map (algebraMap R (FractionRing R)))

theorem genericSelectedEightToCubic_isClosedImmersion
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1)
    (hinj : Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm)) :
    IsClosedImmersion (genericSelectedEightToCubic
      p q r hp hq hr ell hell x hzero hnorm) := by
  unfold genericSelectedEightToCubic
  letI := genericTripleIntersectionEightEmbedding_isClosedImmersion
    p q r hp hq hr ell hell x hzero hnorm hinj
  infer_instance

theorem genericSelectedEightToCubic_toBase
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1) :
    let f := algebraMap R (FractionRing R)
    genericSelectedEightToCubic
        p q r hp hq hr ell hell x hzero hnorm ≫
      hypersurfaceToBase (p.map f) (hp.map f) =
      constantCoverToBase (ULift.{u} (Fin 8))
        (Spec (.of (FractionRing R))) := by
  dsimp only
  unfold genericSelectedEightToCubic
  rw [Category.assoc, tripleCompleteIntersectionToHypersurface_toBase]
  exact genericTripleIntersectionEightEmbedding_toBase
    p q r hp hq hr ell hell x hzero hnorm

theorem genericSelectedEightToCubic_etale
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1) :
    Etale (genericSelectedEightToCubic
        p q r hp hq hr ell hell x hzero hnorm ≫
      hypersurfaceToBase
        (p.map (algebraMap R (FractionRing R)))
        (hp.map (algebraMap R (FractionRing R)))) := by
  rw [genericSelectedEightToCubic_toBase]
  exact etale_constantCoverToBase _ _

/-- The selected eight closed sections give an ideal-defined finite étale
rank-eight datum on the generic cubic surface. -/
noncomputable def genericSelectedEightFiniteSubschemeDatum
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x) :
    FiniteSubschemeDatum
      (hypersurfaceToBase
        (p.map (algebraMap R (FractionRing R)))
        (hp.map (algebraMap R (FractionRing R)))) 8 := by
  let hzero := Classical.choose hEight
  let hnorm := Classical.choose (Classical.choose_spec hEight)
  let hinj := Classical.choose_spec (Classical.choose_spec hEight)
  let i := genericSelectedEightToCubic
    p q r hp hq hr ell hell x hzero hnorm
  let b := hypersurfaceToBase
    (p.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
  letI : IsClosedImmersion i :=
    genericSelectedEightToCubic_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm hinj
  letI : Etale (i ≫ b) :=
    genericSelectedEightToCubic_etale
      p q r hp hq hr ell hell x hzero hnorm
  letI : IsFinite (i ≫ b) := by
    rw [genericSelectedEightToCubic_toBase]
    exact isFinite_constantCoverToBase_spec
      (ULift.{u} (Fin 8)) (FractionRing R)
  letI : Flat (i ≫ b) := inferInstance
  letI : LocallyOfFinitePresentation (i ≫ b) := inferInstance
  apply finiteSubschemeDatumOfClosedImmersion i b 8
  intro s
  have hs : s = IsLocalRing.closedPoint (FractionRing R) := Subsingleton.elim _ _
  subst s
  rw [genericSelectedEightToCubic_toBase,
    finrank_constantCoverToBase_spec]
  simp

theorem genericSelectedEightFiniteSubschemeDatum_etale
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x) :
    Etale ((genericSelectedEightFiniteSubschemeDatum
        p q r hp hq hr ell hell x hEight).val.subschemeι ≫
      hypersurfaceToBase
        (p.map (algebraMap R (FractionRing R)))
        (hp.map (algebraMap R (FractionRing R)))) := by
  let hzero := Classical.choose hEight
  let hnorm := Classical.choose (Classical.choose_spec hEight)
  let hinj := Classical.choose_spec (Classical.choose_spec hEight)
  let i := genericSelectedEightToCubic
    p q r hp hq hr ell hell x hzero hnorm
  let b := hypersurfaceToBase
    (p.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
  letI : IsClosedImmersion i :=
    genericSelectedEightToCubic_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm hinj
  letI : Etale (i ≫ b) :=
    genericSelectedEightToCubic_etale
      p q r hp hq hr ell hell x hzero hnorm
  letI : IsFinite (i ≫ b) := by
    rw [genericSelectedEightToCubic_toBase]
    exact isFinite_constantCoverToBase_spec
      (ULift.{u} (Fin 8)) (FractionRing R)
  letI : Flat (i ≫ b) := inferInstance
  letI : LocallyOfFinitePresentation (i ≫ b) := inferInstance
  have hn (s : Spec (.of (FractionRing R))) : (i ≫ b).finrank s = 8 := by
    have hs : s = IsLocalRing.closedPoint (FractionRing R) := Subsingleton.elim _ _
    subst s
    rw [genericSelectedEightToCubic_toBase,
      finrank_constantCoverToBase_spec]
    simp
  change Etale ((finiteSubschemeDatumOfClosedImmersion i b 8 hn).val.subschemeι ≫ b)
  exact finiteSubschemeDatumOfClosedImmersion_toBase_etale i b 8 hn

/-- The canonical ideal-defined datum is isomorphic to the explicitly
constructed eight-point coproduct, and the isomorphism retains its map to
the cubic surface. -/
noncomputable def genericSelectedEightFiniteSubschemeDatumIso
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x) :
    (∐ fun _ : ULift.{u} (Fin 8) => Spec (.of (FractionRing R))) ≅
      (genericSelectedEightFiniteSubschemeDatum
        p q r hp hq hr ell hell x hEight).val.subscheme := by
  let hzero := Classical.choose hEight
  let hnorm := Classical.choose (Classical.choose_spec hEight)
  let hinj := Classical.choose_spec (Classical.choose_spec hEight)
  let i := genericSelectedEightToCubic
    p q r hp hq hr ell hell x hzero hnorm
  let b := hypersurfaceToBase
    (p.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
  letI : IsClosedImmersion i :=
    genericSelectedEightToCubic_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm hinj
  letI : Etale (i ≫ b) :=
    genericSelectedEightToCubic_etale
      p q r hp hq hr ell hell x hzero hnorm
  letI : IsFinite (i ≫ b) := by
    rw [genericSelectedEightToCubic_toBase]
    exact isFinite_constantCoverToBase_spec
      (ULift.{u} (Fin 8)) (FractionRing R)
  letI : Flat (i ≫ b) := inferInstance
  letI : LocallyOfFinitePresentation (i ≫ b) := inferInstance
  have hn (s : Spec (.of (FractionRing R))) : (i ≫ b).finrank s = 8 := by
    have hs : s = IsLocalRing.closedPoint (FractionRing R) := Subsingleton.elim _ _
    subst s
    rw [genericSelectedEightToCubic_toBase,
      finrank_constantCoverToBase_spec]
    simp
  change _ ≅ (finiteSubschemeDatumOfClosedImmersion i b 8 hn).val.subscheme
  exact finiteSubschemeDatumOfClosedImmersionIso i b 8 hn

theorem genericSelectedEightFiniteSubschemeDatumIso_hom_toCubic
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x) :
    (genericSelectedEightFiniteSubschemeDatumIso
        p q r hp hq hr ell hell x hEight).hom ≫
      (genericSelectedEightFiniteSubschemeDatum
        p q r hp hq hr ell hell x hEight).val.subschemeι =
      genericSelectedEightToCubic p q r hp hq hr ell hell x
        (Classical.choose hEight)
        (Classical.choose (Classical.choose_spec hEight)) := by
  let hzero := Classical.choose hEight
  let hnorm := Classical.choose (Classical.choose_spec hEight)
  let hinj := Classical.choose_spec (Classical.choose_spec hEight)
  let i := genericSelectedEightToCubic
    p q r hp hq hr ell hell x hzero hnorm
  let b := hypersurfaceToBase
    (p.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
  letI : IsClosedImmersion i :=
    genericSelectedEightToCubic_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm hinj
  letI : Etale (i ≫ b) :=
    genericSelectedEightToCubic_etale
      p q r hp hq hr ell hell x hzero hnorm
  letI : IsFinite (i ≫ b) := by
    rw [genericSelectedEightToCubic_toBase]
    exact isFinite_constantCoverToBase_spec
      (ULift.{u} (Fin 8)) (FractionRing R)
  letI : Flat (i ≫ b) := inferInstance
  letI : LocallyOfFinitePresentation (i ≫ b) := inferInstance
  have hn (s : Spec (.of (FractionRing R))) : (i ≫ b).finrank s = 8 := by
    have hs : s = IsLocalRing.closedPoint (FractionRing R) := Subsingleton.elim _ _
    subst s
    rw [genericSelectedEightToCubic_toBase,
      finrank_constantCoverToBase_spec]
    simp
  change (finiteSubschemeDatumOfClosedImmersionIso i b 8 hn).hom ≫
    (finiteSubschemeDatumOfClosedImmersion i b 8 hn).val.subschemeι = i
  exact finiteSubschemeDatumOfClosedImmersionIso_hom_ι i b 8 hn

end PfaffianDescent
