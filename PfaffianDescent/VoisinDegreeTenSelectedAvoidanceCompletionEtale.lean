import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceRankThreeEtale
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-! # Étaleness of the actual degree-sixteen completion

In the branch without a rational point, both rank-three completion components
are automatically étale. Their literal disjoint union with an étale
degree-ten datum is consequently étale as well.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The actual ideal datum of two disjoint reduced finite affine schemes
is étale over a characteristic-zero field. -/
theorem voisinDegreeTenSelectedAvoidance_disjointSpecUnion_datum_etale
    {K A B : Type u} [Field K] [CharZero K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Module.Finite K A] [Module.Finite K B]
    [_root_.IsReduced A] [_root_.IsReduced B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (m n : ℕ)
    (hmi : (i ≫ f).finrank (IsLocalRing.closedPoint K) = m)
    (hnj : (j ≫ f).finrank (IsLocalRing.closedPoint K) = n)
    (hij : Disjoint (Set.range i) (Set.range j)) :
    Etale ((finiteSubschemeDatumOfDisjointSpecUnion
      f i j hi hj m n hmi hnj hij).val.subschemeι ≫ f) := by
  let q := disjointSpecUnionMap i j
  letI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K (A × B))) :=
    disjointSpecUnionMap_toBase f i j hi hj
  letI : IsFinite (q ≫ f) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : Algebra.Etale K (A × B) := reduced_finite_algebra_etale
  letI : Etale (q ≫ f) := by
    rw [hqbase]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have hnq : ∀ s : Spec (.of K), (q ≫ f).finrank s = m + n := by
    intro s
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst s
    exact finrank_disjointSpecUnionMap f i j hi hj m n hmi hnj
  change Etale ((finiteSubschemeDatumOfClosedImmersion q f (m + n) hnq).val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfClosedImmersion_toBase_etale q f (m + n) hnq

set_option backward.isDefEq.respectTransparency false in
/-- The same native étaleness conclusion for the literal three-component
disjoint-union datum. -/
theorem voisinDegreeTenSelectedAvoidance_threeDisjointSpecUnion_datum_etale
    {K A B C : Type u} [Field K] [CharZero K]
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    [Module.Finite K A] [Module.Finite K B] [Module.Finite K C]
    [_root_.IsReduced A] [_root_.IsReduced B] [_root_.IsReduced C]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) (l : Spec (.of C) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion l]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (hl : l ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K C)))
    (m n d : ℕ)
    (hmi : (i ≫ f).finrank (IsLocalRing.closedPoint K) = m)
    (hnj : (j ≫ f).finrank (IsLocalRing.closedPoint K) = n)
    (hdl : (l ≫ f).finrank (IsLocalRing.closedPoint K) = d)
    (hij : Disjoint (Set.range i) (Set.range j))
    (hijl : Disjoint (Set.range (disjointSpecUnionMap i j)) (Set.range l)) :
    Etale ((finiteSubschemeDatumOfThreeDisjointSpecUnion
      f i j l hi hj hl m n d hmi hnj hdl hij hijl).val.subschemeι ≫ f) := by
  let q := disjointSpecUnionMap i j
  letI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  exact voisinDegreeTenSelectedAvoidance_disjointSpecUnion_datum_etale
    f q l (disjointSpecUnionMap_toBase f i j hi hj) hl (m + n) d
    (finrank_disjointSpecUnionMap f i j hi hj m n hmi hnj) hdl hijl

set_option backward.isDefEq.respectTransparency false in
/-- The actual rank-sixteen completion of an étale degree-ten datum on a
cubic without a rational point is étale. No extra condition on the two
chosen degree-three components is required. -/
theorem voisinDegreeTenSelectedAvoidance_completion_datum_etale
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    [Etale (D₁₀.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) :
    Etale (C.datum.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let f := hypersurfaceToBase p hp
  letI : IsFinite (D₁₀.val.subschemeι ≫ f) := D₁₀.property.1
  letI : IsFinite (C.first.val.subschemeι ≫ f) := C.first.property.1
  letI : IsFinite (C.second.val.subschemeι ≫ f) := C.second.property.1
  letI := finiteSchemeCoefficientAlgebra (D₁₀.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficientAlgebra (C.first.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficientAlgebra (C.second.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficient_finite (D₁₀.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficient_finite (C.first.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficient_finite (C.second.val.subschemeι ≫ f)
  letI : Algebra.Etale K Γ(D₁₀.val.subscheme, ⊤) :=
    finiteEtaleScheme_coordinateAlgebra_etale (D₁₀.val.subschemeι ≫ f)
  letI : _root_.IsReduced Γ(D₁₀.val.subscheme, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(D₁₀.val.subscheme, ⊤)
  letI : _root_.IsReduced Γ(C.first.val.subscheme, ⊤) :=
    voisinDegreeTenSelectedAvoidance_rankThree_coefficient_reduced p hp hno
      C.first.val.subschemeι (C.first.property.2.2.2 _)
  letI : _root_.IsReduced Γ(C.second.val.subscheme, ⊤) :=
    voisinDegreeTenSelectedAvoidance_rankThree_coefficient_reduced p hp hno
      C.second.val.subschemeι (C.second.property.2.2.2 _)
  exact voisinDegreeTenSelectedAvoidance_threeDisjointSpecUnion_datum_etale f
    (finiteSubschemeDatumSpecMap f D₁₀)
    (finiteSubschemeDatumSpecMap f C.first)
    (finiteSubschemeDatumSpecMap f C.second)
    (finiteSubschemeDatumSpecMap_toBase f D₁₀)
    (finiteSubschemeDatumSpecMap_toBase f C.first)
    (finiteSubschemeDatumSpecMap_toBase f C.second) 10 3 3
    (finiteSubschemeDatumSpecMap_finrank f D₁₀)
    (finiteSubschemeDatumSpecMap_finrank f C.first)
    (finiteSubschemeDatumSpecMap_finrank f C.second)
    C.disjoint_first C.disjoint_second

end PfaffianDescent
