import PfaffianDescent.MonomialTripleCoefficientDomain300

noncomputable section
namespace PfaffianDescent
universe u
/-- Transport association through an arbitrary classifier BEFORE substituting
any actual double-localization rings or whole-ideal equivalence. -/
private lemma nativeAlgHomClassifier_compAssoc300
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {X : Type*} (E : (A →ₐ[R] D) → X)
    (f : C →ₐ[R] D) (g : B →ₐ[R] C) (h : A →ₐ[R] B)
    (x : X) (hx : E ((f.comp g).comp h) = x) :
    E (f.comp (g.comp h)) = x :=
  (congrArg E (AlgHom.comp_assoc f g h).symm).trans hx

variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C D : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- The actual coefficient map for cyclic triple rotation is DERIVED from
the represented target triple and the original source's universal triple ideal. -/
def monomialTripleRotationCoefficientMap300 :
    MonomialTripleOverlapCoefficientAlgebra300 R m n C D B kC hkC →ₐ[R]
      MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB :=
  (monomialTripleOverlapAlgHomEquiv300 R m n C D B kC hkC
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)).symm
      (monomialTripleOverlapRotate300 B C D
        (universalMonomialTripleOverlap300 R m n B C D kB hkB))

lemma monomialTripleRotationCoefficientMap_classifies300 :
    monomialTripleOverlapAlgHomEquiv300 R m n C D B kC hkC
        (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
        (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC) =
      monomialTripleOverlapRotate300 B C D
        (universalMonomialTripleOverlap300 R m n B C D kB hkB) :=
  (monomialTripleOverlapAlgHomEquiv300 R m n C D B kC hkC
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)).apply_symm_apply _

/-- Cyclic coefficient rotation has the genuine geometric action at every
original coefficient point, not only at the universal point. -/
lemma monomialTripleRotationCoefficientMap_point300
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB →ₐ[R] A) :
    monomialTripleOverlapAlgHomEquiv300 R m n C D B kC hkC A
        (p.comp (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC)) =
      monomialTripleOverlapRotate300 B C D
        (monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB A p) := by
  let T := MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB
  let f := monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC
  have hidentity : monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB A p =
      monomialTripleOverlapMap300 B C D kB hkB p.toRingHom
        (universalMonomialTripleOverlap300 R m n B C D kB hkB) := by
    have h := monomialTripleOverlapAlgHomEquiv_natural300 R m n B C D kB hkB
      (AlgHom.id R T) p
    rw [AlgHom.comp_id] at h
    exact h
  calc
    _ = monomialTripleOverlapMap300 C D B kC hkC p.toRingHom
        (monomialTripleOverlapAlgHomEquiv300 R m n C D B kC hkC T f) :=
      monomialTripleOverlapAlgHomEquiv_natural300 R m n C D B kC hkC f p
    _ = monomialTripleOverlapMap300 C D B kC hkC p.toRingHom
        (monomialTripleOverlapRotate300 B C D
          (universalMonomialTripleOverlap300 R m n B C D kB hkB)) :=
      congrArg (monomialTripleOverlapMap300 C D B kC hkC p.toRingHom)
        (monomialTripleRotationCoefficientMap_classifies300 R m n B C D kB kC hkB hkC)
    _ = monomialTripleOverlapRotate300 B C D
        (monomialTripleOverlapMap300 B C D kB hkB p.toRingHom
          (universalMonomialTripleOverlap300 R m n B C D kB hkB)) :=
      (monomialTripleOverlapRotate_natural300 B C D kB kC hkB hkC p.toRingHom _).symm
    _ = _ := congrArg (monomialTripleOverlapRotate300 B C D) hidentity.symm

/-- Original first/last edge classification after an arbitrary triple algebra point. -/
lemma monomialTripleOverlapFirstLastCoefficientMap_point300
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB →ₐ[R] A) :
    monomialOverlapLocalizationAlgHomEquiv292 R m n B D kB hkB A
        (p.comp (monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB)) =
      monomialTripleOverlapFirstLast293 B C D
        (monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB A p) := by
  let T := MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB
  let f := monomialTripleOverlapFirstLastCoefficientMap300 R m n B C D kB hkB
  have hidentity : monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB A p =
      monomialTripleOverlapMap300 B C D kB hkB p.toRingHom
        (universalMonomialTripleOverlap300 R m n B C D kB hkB) := by
    have h := monomialTripleOverlapAlgHomEquiv_natural300 R m n B C D kB hkB
      (AlgHom.id R T) p
    rw [AlgHom.comp_id] at h
    exact h
  calc
    _ = monomialWholeIdealChartOverlapMap290 B D kB hkB p.toRingHom
        (monomialOverlapLocalizationAlgHomEquiv292 R m n B D kB hkB T f) :=
      monomialOverlapLocalizationAlgHomEquiv_natural292 R m n B D kB hkB f p
    _ = monomialWholeIdealChartOverlapMap290 B D kB hkB p.toRingHom
        (monomialTripleOverlapFirstLast293 B C D
          (universalMonomialTripleOverlap300 R m n B C D kB hkB)) :=
      congrArg (monomialWholeIdealChartOverlapMap290 B D kB hkB p.toRingHom)
        (monomialTripleOverlapFirstLastCoefficientMap_classifies300 R m n B C D kB hkB)
    _ = monomialTripleOverlapFirstLast293 B C D
        (monomialTripleOverlapMap300 B C D kB hkB p.toRingHom
          (universalMonomialTripleOverlap300 R m n B C D kB hkB)) :=
      (monomialTripleOverlapFirstLast_natural300 B C D kB hkB p.toRingHom _).symm
    _ = _ := congrArg (monomialTripleOverlapFirstLast293 B C D) hidentity.symm

/-- The actual rotation coefficient map restricts to298's SAME inverse
coefficient map on the B/C pair, as a WHOLE algebra homomorphism. -/
lemma monomialTripleRotationCoefficientMap_edge300 :
    (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC).comp
        (monomialTripleOverlapFirstLastCoefficientMap300 R m n C D B kC hkC) =
      (monomialTripleOverlapFirstCoefficientMap300 R m n B C D kB hkB).comp
        (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB) := by
  apply (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)).injective
  calc
    _ = monomialTripleOverlapFirstLast293 C D B
        (monomialTripleOverlapAlgHomEquiv300 R m n C D B kC hkC
          (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
          (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC)) :=
      monomialTripleOverlapFirstLastCoefficientMap_point300
        (R := R) (m := m) (n := n) (B := C) (C := D) (D := B)
        (kB := kC) (hkB := hkC)
        (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC)
    _ = monomialTripleOverlapFirstLast293 C D B
        (monomialTripleOverlapRotate300 B C D
          (universalMonomialTripleOverlap300 R m n B C D kB hkB)) :=
      congrArg (monomialTripleOverlapFirstLast293 C D B)
        (monomialTripleRotationCoefficientMap_classifies300 R m n B C D kB kC hkB hkC)
    _ = monomialWholeIdealOverlapFlip293 B C
        (universalMonomialTripleOverlap300 R m n B C D kB hkB).val :=
      monomialTripleOverlapRotate_firstLast300 B C D _
    _ = monomialWholeIdealOverlapFlip293 B C
        (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
          (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
          (monomialTripleOverlapFirstCoefficientMap300 R m n B C D kB hkB)) :=
      congrArg (monomialWholeIdealOverlapFlip293 B C)
        (monomialTripleOverlapFirstCoefficientMap_classifies300 R m n B C D kB hkB).symm
    _ = _ := (monomialOverlapReverseCoefficient_classifies300 R m n B C kB kC hkB hkC _).symm

variable (kD : Fin n) (hkD : D kD = 0)

/-- Three coefficient rotations compose to the literal identity. This is
proved by injectivity of the actual triple representing equivalence and293's
same-ideal threefold rotation, not assumed as a cocycle certificate. -/
lemma monomialTripleRotationCoefficientMap_cycle300 :
    (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC).comp
        ((monomialTripleRotationCoefficientMap300 R m n C D B kC kD hkC hkD).comp
          (monomialTripleRotationCoefficientMap300 R m n D B C kD kB hkD hkB)) =
      AlgHom.id R (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB) := by
  apply (monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB
    (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)).injective
  calc
    _ = monomialTripleOverlapRotate300 D B C
        (monomialTripleOverlapAlgHomEquiv300 R m n D B C kD hkD
          (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
          ((monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC).comp
            (monomialTripleRotationCoefficientMap300 R m n C D B kC kD hkC hkD))) := by
      exact nativeAlgHomClassifier_compAssoc300
        (fun p => monomialTripleOverlapAlgHomEquiv300 R m n B C D kB hkB
          (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB) p)
        (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC)
        (monomialTripleRotationCoefficientMap300 R m n C D B kC kD hkC hkD)
        (monomialTripleRotationCoefficientMap300 R m n D B C kD kB hkD hkB) _
        (monomialTripleRotationCoefficientMap_point300 R m n D B C kD kB hkD hkB
          ((monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC).comp
            (monomialTripleRotationCoefficientMap300 R m n C D B kC kD hkC hkD)))
    _ = monomialTripleOverlapRotate300 D B C
        (monomialTripleOverlapRotate300 C D B
          (monomialTripleOverlapAlgHomEquiv300 R m n C D B kC hkC
            (MonomialTripleOverlapCoefficientAlgebra300 R m n B C D kB hkB)
            (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC))) :=
      congrArg (monomialTripleOverlapRotate300 D B C)
        (monomialTripleRotationCoefficientMap_point300 R m n C D B kC kD hkC hkD _)
    _ = monomialTripleOverlapRotate300 D B C
        (monomialTripleOverlapRotate300 C D B
          (monomialTripleOverlapRotate300 B C D
            (universalMonomialTripleOverlap300 R m n B C D kB hkB))) :=
      congrArg (fun x => monomialTripleOverlapRotate300 D B C
        (monomialTripleOverlapRotate300 C D B x))
        (monomialTripleRotationCoefficientMap_classifies300 R m n B C D kB kC hkB hkC)
    _ = universalMonomialTripleOverlap300 R m n B C D kB hkB :=
      monomialTripleOverlapRotate_cycle300 B C D _
    _ = _ := rfl

end PfaffianDescent
